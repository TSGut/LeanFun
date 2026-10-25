"""RevOLVER book layer for the HTML blueprint.

* Shows the Lean statement of every linked declaration under its blueprint node.
  Signatures come from Lean itself (`lake exe revolver_signatures`, see
  scripts/RevolverSignatures.lean): the elaborated binders are printed exactly,
  including section variables and instances, so no hypothesis can be lost.
  Source text (proofs, definition bodies) is read from the declaration range
  reported by Lean. An unknown declaration name fails the build.
* Provides the `supporting` environment: auxiliary results are rendered
  collapsed, so the prose can concentrate on the results that matter downstream.
"""
import html
import json
import re
import os
import subprocess
import sys
from pathlib import Path

from revolver_data import load_catalog, source_notes, citation_terms, mathematical_source, write_reference_pages, highlight_julia, FAVICON

from plasTeX import Command, Environment
from plasTeX.Base.LaTeX.Verbatim import verbatim
from plasTeX.PackageResource import (PackageCss, PackagePreCleanupCB,
                                     PackageProcessFilecontents, PackageTemplateDir)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MATHLIB_GITHUB = 'https://github.com/leanprover-community/mathlib4/blob/{rev}/{path}#L{a}-L{b}'
KEYWORD = {'theorem': 'theorem', 'definition': 'def', 'opaque': 'opaque',
           'axiom': 'axiom', 'inductive': 'inductive'}


class rvRev(Command):
    r"""\rvRev{text}: the "Rev" of RevOLVER, in the logo blue."""
    args = 'self'


class rvAcr(Command):
    r"""\rvAcr{text}: acronym letters of RevOLVER, in the logo orange."""
    args = 'self'


class covertitle(Command):
    r"""\covertitle{title}: decorated title shown on the cover page only."""
    args = 'self'

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.ownerDocument.userdata['covertitle'] = self


class subtitle(Command):
    r"""\subtitle{text}: subtitle shown on the cover page."""
    args = 'self'

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.ownerDocument.userdata['subtitle'] = self


class rvsummary(Command):
    r"""\rvsummary{text}: one-sentence summary of the enclosing part, chapter or
    section, shown in the index on its parent's page (not in its own body)."""
    args = 'text'


def attach_summaries(document):
    """Store each summary on its enclosing sectioning node."""
    count = 0

    def walk(node, section):
        nonlocal count
        for child in node.childNodes or []:
            if getattr(child, 'nodeName', '') in ('part', 'chapter', 'section'):
                walk(child, child)
            elif getattr(child, 'nodeName', '') == 'rvsummary':
                if section is not None and 'rvsummary' not in section.userdata:
                    section.userdata['rvsummary'] = child.attributes['text']
                    count += 1
            else:
                walk(child, section)
    walk(document, None)
    print(f'RevOLVER: attached {count} section summaries')


class supporting(Environment):
    r"""\begin{supporting}[summary] ... \end{supporting}"""
    args = '[title]'
    blockType = True


class juliacode(verbatim):
    """Julia examples, highlighted without executing their contents."""

    @property
    def highlighted(self):
        return highlight_julia(str(self.textContent))


def lean_signatures(names):
    """Ask Lean for the signature, kind and source range of each declaration."""
    subprocess.run(['lake', 'build', 'revolver_signatures'], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    proc = subprocess.run(['lake', 'env', '.lake/build/bin/revolver_signatures'],
                          cwd=ROOT, input='\n'.join(sorted(names)), text=True,
                          capture_output=True)
    if proc.returncode != 0:
        raise RuntimeError('RevOLVER: revolver_signatures failed (is LeanFun built? '
                           'run `lake build`):\n' + proc.stderr[-2000:])
    data = {d['name']: d for d in json.loads(proc.stdout)}
    missing = sorted(n for n, d in data.items() if d.get('missing'))
    if missing:
        raise RuntimeError('RevOLVER: unknown Lean declarations: ' + ', '.join(missing))
    return data


def mathlib_rev():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    return next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')


def ProcessOptions(options, document):
    document.addPackageResource(PackageTemplateDir(path=HERE / 'revolver_templates'))
    document.addPackageResource(PackageCss(path=HERE / 'revolver.css'))
    document.addPackageResource(PackageCss(path=HERE / 'julia.css'))
    if document.config['general']['renderer'] != 'HTML5':
        return

    def copy_logos(renderer):
        import shutil
        names = ['revolver-logo-128.png', 'revolver-logo-512.png']
        for name in names:
            shutil.copyfile(HERE / 'revolver_assets' / name, name)
        # Publish the PDF version next to the web book (CI builds the PDF first).
        pdf = ROOT / 'blueprint' / 'print' / 'print.pdf'
        if pdf.exists():
            shutil.copyfile(pdf, 'LeanFun-RevOLVER.pdf')
        else:
            print('RevOLVER: blueprint/print/print.pdf not found; run leanblueprint pdf first')
        # Binary files must not be returned: returned files are post-processed as text.
        return []
    document.addPackageResource(PackagePreCleanupCB(data=copy_logos))

    # Search and editorial metadata are independent of Lean proof dependencies.
    sources, catalog = load_catalog(HERE)
    notes = source_notes((HERE / 'content.tex').read_text())
    roadmap = json.loads((HERE / 'revolver_catalog.json').read_text()).get('roadmap', {})

    def reference_anchor():
        # A TeX label after a starred part can rename the preceding theorem.
        # Assign only the HTML section ID, leaving mathematical labels alone.
        for section in document.getElementsByTagName('part'):
            if section.title.textContent.strip() == 'References':
                section.id = 'part:references'
    document.addPostParseCallbacks(105, reference_anchor)

    def annotate_catalog():
        for g in document.userdata['dep_graph']['graphs'].values():
            for node in g.nodes:
                if node.id in catalog:
                    node.userdata['rvmeta'] = catalog[node.id]
    document.addPostParseCallbacks(165, annotate_catalog)

    def write_search_index(renderer):
        def text(x):
            return ' '.join((getattr(x, 'textContent', '') or str(x or '')).split())
        entries, seen = [], set()
        # Source order, rather than graph insertion order, makes browsing coherent.
        graph_nodes = {n.id: n for g in document.userdata['dep_graph']['graphs'].values() for n in g.nodes}
        for label, source in sources.items():
            n = graph_nodes[label]
            if not getattr(n, 'url', None):
                raise ValueError(f'Missing search destination: {label}')
            meta = catalog[label]
            status = 'planned' if r'\notready' in source else ('imported' if r'\mathlibok' in source else 'formalised')
            entries.append(dict(meta, kind=text(getattr(n, 'caption', '')), ref=text(getattr(n, 'ref', '')),
                title=text(getattr(n, 'title', '')), label=label, url=n.url,
                chapter=meta['chapter_title'], chapter_label=meta['chapter'],
                lean=list(n.userdata.get('leandecls', [])), text=text(n),
                math=mathematical_source(source + '\n' + notes.get(label, '')),
                citations=citation_terms(source + '\n' + notes.get(label, '')), status=status,
                review=n.userdata.get('statement_review', 'unreviewed')))
        for tag in ('part', 'chapter', 'section'):
            for section in document.getElementsByTagName(tag):
                if not getattr(section, 'url', None): continue
                # Index introductory prose only, never embedded proof/source boxes.
                intro = []
                for child in section.childNodes or []:
                    if getattr(child, 'nodeName', '') in ('theorem','definition','lemma','corollary','supporting','section','chapter'): break
                    intro.append(text(child))
                entries.append(dict(kind=tag.capitalize(), ref=text(getattr(section, 'ref', '')),
                    title=text(section.title), label=getattr(section, 'id', ''), url=section.url,
                    chapter=roadmap.get(getattr(section, 'id', ''), {}).get('chapter_title', ''),
                    chapter_label=roadmap.get(getattr(section, 'id', ''), {}).get('chapter', ''),
                    role='planned' if getattr(section, 'id', '') in roadmap else '',
                    lean=[], text=' '.join(intro),
                    aliases=roadmap.get(getattr(section, 'id', ''), {}).get('aliases', []),
                    topics=roadmap.get(getattr(section, 'id', ''), {}).get('topics', []), citations=[],
                    status='planned' if getattr(section, 'id', '') in roadmap else '', review=''))
        Path('search-index.json').write_text(json.dumps(entries, ensure_ascii=False))
        old = json.loads((HERE / 'revolver_legacy_urls.json').read_text())
        write_reference_pages(entries, HERE, old)
        return []
    document.addPackageResource(PackagePreCleanupCB(data=write_search_index))

    def chapter_guides():
        nodes = {n.id: n for g in document.userdata['dep_graph']['graphs'].values() for n in g.nodes}
        for section in document.getElementsByTagName('chapter'):
            selected = [nodes[label] for label, meta in catalog.items()
                        if meta['chapter'] == section.id and meta['role'] == 'main']
            section.userdata['rv_main'] = selected if len(selected) <= 10 else selected[:7] + selected[-3:]
            section.userdata['rv_count'] = sum(meta['chapter'] == section.id for meta in catalog.values())
    document.addPostParseCallbacks(172, chapter_guides)

    # The stock layout titles pages "Document: Page"; on the cover both are the same.
    def dedupe_title(document, s):
        return re.sub(r'<title>(.+?): \1</title>', r'<title>\1</title>', s, count=1)
    document.addPackageResource(PackageProcessFilecontents(data=dedupe_title))

    # Expose the repository address (\\github in web.tex) and the build version
    # (scripts/version.py) to revolver.js: every page links the repository next to
    # the navigation arrows, and every page shows the version in the top-right corner.
    version_cache = {}

    def version_info(github):
        if 'v' not in version_cache:
            script = [sys.executable, str(ROOT / 'scripts/version.py')]
            run = lambda *a: subprocess.run(script + list(a), capture_output=True, text=True).stdout.strip()
            version_cache['v'] = (run(), run('--url', github) if github else '')
        return version_cache['v']

    def repository_meta(document, s):
        github = document.userdata.get('project_github', '').rstrip('/')
        if '</head>' not in s:
            return s
        version, url = version_info(github)
        meta = '' if 'rel="icon"' in s else FAVICON + '\n'
        if github:
            meta += f'<meta name="rv-repository" content="{html.escape(github)}" />\n'
        if version:
            meta += f'<meta name="rv-version" content="{html.escape(version)}" />\n'
            meta += f'<meta name="rv-version-url" content="{html.escape(url)}" />\n'
        return s.replace('</head>', meta + '</head>', 1)
    document.addPackageResource(PackageProcessFilecontents(data=repository_meta))
    ref = os.environ.get('GITHUB_SHA', 'main')

    def attach():
        github = document.userdata.get('project_github', '').rstrip('/')
        nodes = list({id(n): n for g in document.userdata['dep_graph']['graphs'].values()
                      for n in g.nodes}.values())
        names = {name for node in nodes for name in node.userdata.get('leandecls', [])}
        data = lean_signatures(names)
        rev = mathlib_rev()
        for node in nodes:
            sigs = []
            for name in node.userdata.get('leandecls', []):
                d = data[name]
                module, a, b = d['module'], d['line'], d['endLine']
                local = module == 'LeanFun' or module.startswith('LeanFun.')
                path = module.replace('.', '/') + '.lean'
                source, url = '', ''
                if local and a:
                    lines = (ROOT / path).read_text(encoding='utf-8').splitlines()
                    source = '\n'.join(lines[a - 1:b]).rstrip()
                    url = f"{github}/blob/{ref}/{path}#L{a}-L{b}" if github else ''
                elif module.startswith('Mathlib') and a:
                    url = MATHLIB_GITHUB.format(rev=rev, path=path, a=a, b=b)
                sigs.append({'name': name, 'local': local,
                             'statement': f"{KEYWORD.get(d['kind'], d['kind'])} {d['signature']}",
                             'is_def': d['kind'] != 'theorem', 'source': source,
                             'url': url})
            # For theorem-like nodes, lead with a theorem rather than a definition.
            if sigs and getattr(node, 'thmName', '') != 'definition':
                first = next((i for i, s in enumerate(sigs) if not s['is_def']), 0)
                sigs.insert(0, sigs.pop(first))
            node.userdata['lean_sigs'] = sigs
    document.addPostParseCallbacks(170, attach)
    document.addPostParseCallbacks(171, lambda: attach_summaries(document))
