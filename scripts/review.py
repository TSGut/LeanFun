#!/usr/bin/env python3
"""Human statement-review ledger. Agents must NEVER approve real declarations."""
import argparse
import datetime
import difflib
import json
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def source_text(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError(f'cyclic blueprint input: {path}')
    text = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
    def include(m):
        child = path.parent / m[1]
        if not child.suffix:
            child = child.with_suffix('.tex')
        return source_text(child, (*stack, path))
    return re.sub(r'\\(?:input|include)\{([^}]+)\}', include, text)


BOOKKEEPING = re.compile(r'\\(?:label|uses|lean)\{[^}]*\}|\\(?:leanok|mathlibok|notready)\b')


def normalise_text(text):
    """Statement text as reviewed: bookkeeping macros dropped, whitespace collapsed."""
    return ' '.join(BOOKKEEPING.sub(' ', text).split())


def blueprint(path=None, with_text=False):
    text = source_text(path or ROOT / 'blueprint/src/content.tex')
    names = set()
    nodes = {}
    texts = {}
    # Node labels belong to theorem-like environments, not chapter/equation labels.
    stack = []
    node_kinds = {'theorem', 'definition', 'lemma', 'corollary', 'proposition', 'conjecture'}
    for m in re.finditer(r'\\(begin|end|label|lean)\{([^}]+)\}', text):
        cmd, value = m[1], m[2].strip()
        if cmd == 'begin':
            stack.append({'kind': value, 'label': None, 'decls': [], 'start': m.end()})
        elif cmd == 'end':
            if stack:
                frame = stack.pop()
                if frame['kind'] in node_kinds and frame['label']:
                    nodes[frame['label']] = frame['decls']
                    texts[frame['label']] = normalise_text(text[frame['start']:m.start()])
        elif cmd == 'label':
            if stack and stack[-1]['kind'] in node_kinds:
                stack[-1]['label'] = value
        else:
            ds = [d.strip() for d in value.split(',') if d.strip()]
            names.update(ds)
            for frame in reversed(stack):
                if frame['kind'] in node_kinds:
                    frame['decls'].extend(ds)
                    break
    if with_text:
        return sorted(names), nodes, texts
    return sorted(names), nodes


def book_for(name, nodes, texts):
    """The book statements linking a declaration, as (node labels, normalised texts)."""
    labels = sorted(label for label, decls in nodes.items() if name in decls)
    return labels, [texts[label] for label in labels]


def load_ledger(path):
    data = tomllib.loads(path.read_text())
    if data.get('schema') not in (1, 2):
        raise ValueError('unsupported ledger schema')
    entries = data.get('statements', [])
    result = {}
    for entry in entries:
        required = {'name', 'fingerprint', 'reviewer', 'date', 'git_commit',
                    'mathlib_commit', 'toolchain', 'rendered', 'external'}
        if not required <= entry.keys() or entry['name'] in result:
            raise ValueError('incomplete or duplicate ledger entry')
        for key in required - {'external'}:
            if not isinstance(entry[key], str) or not entry[key]:
                raise ValueError(f'invalid ledger field {key}')
        if not re.fullmatch(r'[0-9a-f]{64}', entry['fingerprint']):
            raise ValueError('fingerprint must be a full SHA-256 hex digest')
        datetime.date.fromisoformat(entry['date'])
        if not isinstance(entry['external'], list) or not all(isinstance(n, str) for n in entry['external']):
            raise ValueError('external dependencies must be a list of names')
        # Approvals made before schema 2 have no book text; they count as stale.
        if ('book_nodes' in entry) != ('book_texts' in entry):
            raise ValueError('book_nodes and book_texts must be recorded together')
        if 'book_nodes' in entry:
            nodes, texts = entry['book_nodes'], entry['book_texts']
            if not (isinstance(nodes, list) and isinstance(texts, list) and len(nodes) == len(texts)
                    and all(isinstance(x, str) for x in nodes + texts)):
                raise ValueError('book_nodes and book_texts must be equal-length lists of strings')
        result[entry['name']] = entry
    return result


def write_ledger(path, entries):
    # JSON strings and arrays of strings are valid TOML basic strings/arrays.
    parts = ['# Owner-maintained statement approvals.', 'schema = 2', '']
    if not entries:
        parts.append('statements = []')
    for name in sorted(entries):
        parts.append('[[statements]]')
        parts.extend(f'{k} = {json.dumps(v, ensure_ascii=False)}'
                     for k, v in entries[name].items())
        parts.append('')
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, suffix='.tmp', delete=False) as f:
        f.write('\n'.join(parts) + '\n')
        tmp = Path(f.name)
    tmp.replace(path)


def source_snapshot(module=None):
    paths = [ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json',
             ROOT / 'lean-toolchain', ROOT / 'scripts/review_hash.py', ROOT / 'review/Fingerprint.lean']
    if module:
        rel = module.replace('.', '/') + '.lean'
        # Test fixture modules live under test/ (lakefile srcDir).
        paths.append(ROOT / rel if (ROOT / rel).exists() else ROOT / 'test' / rel)
    else:
        paths.append(ROOT / 'LeanFun.lean')
        paths += list((ROOT / 'LeanFun').rglob('*.lean'))
        paths += list((ROOT / 'blueprint/src').rglob('*.tex'))
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path.relative_to(ROOT)).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()


def metadata():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    return {'mathlib_commit': mathlib, 'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
            'git_commit': commit}


def extract(names, module=None, external=()):
    if not names:
        return {}
    cmd = ['lake', 'env', '.lake/build/bin/review_fingerprint']
    if module:
        cmd += ['--module', module, module]
    result = subprocess.run(cmd + sorted(set(names)) + (['--check-external'] + sorted(set(external)) if external else []), cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stderr or result.stdout)
    return {item['name']: item for item in json.loads(result.stdout)}


def book_changed(old, book):
    """Whether the book statements differ from those recorded at approval."""
    if 'book_nodes' not in old:
        return True
    return (old['book_nodes'], old['book_texts']) != (list(book[0]), list(book[1]))


def state(old, new, meta, book=None):
    """Review state; `book` is the current (labels, texts) pair, or None to skip that check."""
    if old is None:
        return 'unreviewed'
    if new is None or new.get('missing') or old['fingerprint'] != new['fingerprint'] or old['toolchain'] != meta['toolchain'] or set(old['external']) & set(new.get('missing_external', [])):
        return 'stale'
    if book is not None and book_changed(old, book):
        return 'stale'
    return 'reviewed-current'


def node_status(names, statuses):
    if any(statuses.get(n) == 'stale' for n in names):
        return 'stale'
    if names and all(statuses.get(n) == 'reviewed-current' for n in names):
        return 'reviewed-current'
    return 'unreviewed'


def statement_diff(old, new):
    before = old['rendered']
    after = new['rendered'] if new and not new.get('missing') else '[declaration missing]'
    diff = ''.join(difflib.unified_diff([line + '\n' for line in before.splitlines()],
                                      [line + '\n' for line in after.splitlines()],
                                      fromfile='reviewed', tofile='current'))
    return diff or 'Root rendering unchanged; a dependency, universe/binder detail, or toolchain changed.\n'


def book_diff(old, book):
    """Differences between the reviewed and current book statements, or '' if none."""
    if 'book_nodes' not in old:
        return 'Book text was not recorded at approval (approved before schema 2); re-approve.\n'
    def lines(labels, texts):
        return [f'[{label}] {text}\n' for label, text in zip(labels, texts)]
    return ''.join(difflib.unified_diff(lines(old['book_nodes'], old['book_texts']),
                                        lines(*book), fromfile='reviewed book text',
                                        tofile='current book text'))


def report(old, new, book):
    """Full explanation of a stale review: Lean statement and book text."""
    text = book_diff(old, book)
    lean_same = new and not new.get('missing') and old['fingerprint'] == new['fingerprint']
    if text and lean_same:
        return text
    return statement_diff(old, new) + text


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, default=ROOT / 'review/statements.toml')
    parser.add_argument('--blueprint', type=Path)
    parser.add_argument('--module', help='fixture module; not for real approvals')
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('names')
    status = sub.add_parser('status')
    status.add_argument('--json', type=Path, help='write machine-readable status')
    sub.add_parser('check')
    diff = sub.add_parser('diff'); diff.add_argument('name')
    approve = sub.add_parser('approve')
    approve.add_argument('names', nargs='+')
    approve.add_argument('--reviewer', required=True)
    approve.add_argument('--fixture', action='store_true', help='test fixture ledger only')
    args = parser.parse_args(argv)
    snapshot = source_snapshot(args.module)
    names, nodes, texts = blueprint(args.blueprint, with_text=True)
    if args.command == 'names':
        print('\n'.join(names)); return 0
    ledger_bytes = args.ledger.read_bytes()
    entries = load_ledger(args.ledger)
    meta = metadata()
    # Unreviewed names need no extraction. Rebuild before checking any recorded
    # fingerprint or preparing an approval; checkdecls checks all blueprint links.
    requested = set(entries)
    if args.command == 'approve': requested.update(args.names)
    if args.command == 'diff' and args.name in entries: requested.add(args.name)
    if requested:
        target = args.module or 'LeanFun'
        subprocess.run(['lake', 'build', target, 'review_fingerprint'], cwd=ROOT,
                       check=True, stdout=sys.stderr)
    current = extract(requested, args.module, [n for e in entries.values() for n in e['external']])
    if args.ledger.read_bytes() != ledger_bytes:
        raise RuntimeError("ledger changed during extraction; retry")
    if requested and snapshot != source_snapshot(args.module):
        raise RuntimeError('sources changed during fingerprint extraction; rebuild and retry')
    books = {n: book_for(n, nodes, texts) for n in requested | set(names)}
    statuses = {n: state(entries.get(n), current.get(n), meta, books[n])
                for n in requested | set(names)}
    warnings = [f'{n}: Mathlib revision changed ({old["mathlib_commit"]} → {meta["mathlib_commit"]})'
                for n, old in entries.items() if old['mathlib_commit'] != meta['mathlib_commit']]
    for warning in warnings: print('WARNING: ' + warning, file=sys.stderr)
    if args.command == 'approve':
        if any(current[n].get('missing') for n in args.names):
            raise ValueError('cannot approve a missing declaration')
        real = (ROOT / 'review/statements.toml').resolve()
        if args.fixture:
            if not args.module or not args.module.startswith('ReviewTests.') or args.ledger.resolve() == real:
                raise ValueError('--fixture requires a ReviewTests module and a separate fixture ledger')
        else:
            if args.module:
                raise ValueError('fixture modules cannot approve the real project')
            if not sys.stdin.isatty():
                raise ValueError('owner approval requires an interactive terminal')
            for n in args.names:
                print(current[n]['rendered'])
                for label, text in zip(*books[n]):
                    print(f'  book [{label}]: {text}')
            if input('Owner only: type "I reviewed these statements" to approve: ') != 'I reviewed these statements':
                raise ValueError('approval cancelled')
        for n in args.names:
            item = current[n]
            entries[n] = {k: item[k] for k in ('name', 'fingerprint', 'rendered', 'external')}
            entries[n].update(meta, reviewer=args.reviewer, date=datetime.date.today().isoformat(),
                              book_nodes=books[n][0], book_texts=books[n][1])
        if snapshot != source_snapshot(args.module):
            raise RuntimeError('sources changed while reviewing; rebuild and retry')
        if args.ledger.read_bytes() != ledger_bytes:
            raise RuntimeError("ledger changed while reviewing; retry")
        write_ledger(args.ledger, entries)
        return 0
    if args.command == 'diff':
        if args.name not in entries: print('Unreviewed: ' + args.name)
        elif statuses[args.name] == 'reviewed-current': print('Review is current: ' + args.name)
        else: print(report(entries[args.name], current.get(args.name), books[args.name]))
        return 0
    stale = [n for n in entries if statuses[n] == 'stale']
    if args.command == 'check':
        for n in stale:
            print('STALE: ' + n)
            print(report(entries[n], current.get(n), books[n]))
        print(f'{len(entries)} ledger entries; {len(stale)} stale.')
        return int(bool(stale))
    data = {'schema': 1, 'declarations': {n: statuses[n] for n in names},
            'nodes': {n: node_status(ds, statuses) for n, ds in nodes.items()},
            'warnings': warnings}
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(data, indent=2) + '\n')
    else:
        for n in names: print(f'{statuses[n]:18} {n}')
        for n, s in data['nodes'].items(): print(f'node {s:18} {n}')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, OSError, subprocess.CalledProcessError) as e:
        print(f'review: {e}', file=sys.stderr)
        sys.exit(1)
