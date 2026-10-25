"""Pure data helpers for the RevOLVER's reading and reference routes."""
import html
import json
import re
from pathlib import Path

FAVICON = '<link rel="icon" type="image/png" sizes="128x128" href="revolver-logo-128.png">'

NODE = re.compile(r'\\begin\{(theorem|definition|lemma|corollary|proposition)\}(?:\[([^\]]*)\])?.*?\\end\{\1\}', re.S)


def highlight_julia(source):
    """Escape and highlight Julia at build time, preserving the code text."""
    from pygments import highlight
    from pygments.lexers import JuliaLexer
    from pygments.formatters import HtmlFormatter
    return highlight(source, JuliaLexer(stripnl=False, ensurenl=False),
                     HtmlFormatter(nowrap=True))


def source_nodes(text):
    return {re.search(r'\\label\{([^}]+)\}', m[0])[1]: m[0]
            for m in NODE.finditer(text) if re.search(r'\\label\{([^}]+)\}', m[0])}


def source_notes(text):
    """Collect associated prose without making it part of a reviewed statement."""
    notes = {}
    for m in re.finditer(r'\\rvnote\{([^}]+)\}\s*\{', text):
        start, depth, i = m.end(), 1, m.end()
        while depth and i < len(text):
            # TeX escaped braces do not delimit arguments.
            if text[i] == '\\':
                i += 2
                continue
            depth += (text[i] == '{') - (text[i] == '}')
            i += 1
        if depth:
            raise ValueError(f'Unclosed editorial note for {m[1]}')
        notes.setdefault(m[1], []).append(text[start:i-1].strip())
    return {label: '\n\n'.join(parts) for label, parts in notes.items()}


def citation_terms(source):
    return [f'{key.strip()} {locator or ""}'.strip()
            for locator, keys in re.findall(r'\\cite(?:\[([^\]]*)\])?\{([^}]+)\}', source)
            for key in keys.split(',')]


def mathematical_source(source):
    """Search fallback for formulas/citations; exclude Lean links and graph metadata."""
    source = re.sub(r'\\(?:lean|uses|label)\{[^}]*\}|\\(?:leanok|mathlibok|notready)\b', '', source)
    return re.sub(r'\s+', ' ', source).strip()


def load_catalog(directory):
    nodes = source_nodes((directory / 'content.tex').read_text())
    catalog = json.loads((directory / 'revolver_catalog.json').read_text())['nodes']
    if nodes.keys() != catalog.keys():
        raise ValueError(f'Catalog coverage mismatch: {nodes.keys() ^ catalog.keys()}')
    return nodes, catalog


def page(title, body, sidebar=''):
    toggle = ('<svg id="toc-toggle" class="icon icon-list-numbered" role="button" '
              'aria-label="Toggle contents"><use xlink:href="symbol-defs.svg#icon-list-numbered">'
              '</use></svg>') if sidebar else ''
    return ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width, initial-scale=1">'
            f'<title>{html.escape(title)} — LeanFun RevOLVER</title>'
            '<link rel="stylesheet" href="styles/theme-white.css">'
            '<link rel="stylesheet" href="styles/revolver.css">' + FAVICON + '</head>'
            f'<body class="rv-reference-page"><header>{toggle}</header>'
            f'<div class="wrapper">{sidebar}<div class="content">'
            f'<main class="content-wrapper">{body}</main></div></div>'
            '<script src="js/jquery.min.js"></script><script src="js/plastex.js"></script>'
            '<script src="js/svgxuse.js"></script>'
            '<script src="js/revolver.js"></script></body></html>')


def legacy_redirects(old, current):
    """Only redirect known historical targets to a different current URL."""
    return {url: current[label] for label, url in old.items()
            if label in current and current[label] != url}


def write_reference_pages(entries, directory, old):
    # Use the rendered book TOC, so search retains the same chapter navigation.
    home = Path('index.html').read_text()
    toc = re.search(r'<nav class="toc">.*?</nav>', home, re.S)
    if not toc:
        raise ValueError('Rendered homepage is missing the book sidebar')
    sidebar = toc[0]
    current = {e['label']: e['url'] for e in entries}
    redirects = legacy_redirects(old, current)
    for url, label in json.loads((directory / 'revolver_legacy_pages.json').read_text()).items():
        if label not in current: raise ValueError(f'Missing legacy destination: {label}')
        if url != current[label]:
            redirects[url] = current[label]
    Path('legacy-urls.json').write_text(json.dumps(redirects, ensure_ascii=False))
    # Static links remain useful with scripting disabled or an index-load failure.
    def link(label, title=None):
        e = next(e for e in entries if e['label'] == label)
        return f'<a href="{html.escape(e["url"], quote=True)}">{html.escape(title or e["title"])}</a>'
    # Obtain chapter ranges from the book structure and rendered numbering.
    by_label = {e['label']: e for e in entries}
    chapters = {}
    part = None
    for kind, label in re.findall(r'\\(part|chapter)\{[^}]*\}\s*\\label\{([^}]+)\}',
                                  (directory / 'content.tex').read_text()):
        if kind == 'part':
            part = label
            chapters[part] = []
        elif part and label in by_label:
            chapters[part].append(by_label[label]['ref'])
    routes = []
    for label, title in [('part:chebfun', 'Chebfun reading path'),
                         ('part:op', 'Orthogonal polynomials'),
                         ('part:operators', 'ApproxFun reading path'),
                         ('part:beyond', 'Several variables'),
                         ('part:integral-operators', 'Integral operators')]:
        numbers = chapters[label]
        routes.append(link(label, f'{title} · Chapters {numbers[0]}–{numbers[-1]}'))
    body = ('<h1>Advanced search</h1>'
            '<p>Search every mathematical statement, including collapsed results and planned targets.</p>'
            '<nav aria-label="Reading routes" class="rv-topic-links">' + ''.join(routes) + '</nav>'
            '<section id="rv-reference-search" aria-label="Search all results"></section>'
            '<noscript><p>Interactive search requires JavaScript. '
            '<a href="all-results.html">Browse the complete statement index</a>.</p></noscript>')
    Path('reference.html').write_text(page('Advanced search', body, sidebar))
    listing = '<h1>Complete statement index</h1><p><a href="reference.html">Advanced search</a></p>'
    chapter = None
    for e in entries:
        if not e.get('role'): continue
        if e['chapter'] != chapter:
            if chapter is not None: listing+='</ul>'
            chapter=e['chapter'];listing+='<h2>'+html.escape(chapter)+'</h2><ul>'
        listing+='<li>'+link(e['label'])+' <small>'+html.escape(e['role'])+' · '+html.escape(e['status'])+'</small></li>'
    listing+='</ul>'
    Path('all-results.html').write_text(page('Complete statement index', listing, sidebar))
    # Keep old generated pages that no longer have a current section/chapter.
    # Existing pages use the same JS redirect map for old fragment links.
    current_pages = {url.split('#',1)[0] for url in current.values()}
    for oldurl, target in redirects.items():
        filename=oldurl.split('#',1)[0]
        if '/' in filename or not filename.endswith('.html') or filename in current_pages:continue
        destinations={v for k,v in redirects.items() if k.split('#',1)[0]==filename}
        fallback='<h1>This material has moved</h1><p>Follow the current reference:</p><ul>'+''.join('<li><a href="'+html.escape(v,quote=True)+'">'+html.escape(v)+'</a></li>' for v in sorted(destinations))+'</ul>'
        Path(filename).write_text(page('Moved material',fallback))
    return redirects
