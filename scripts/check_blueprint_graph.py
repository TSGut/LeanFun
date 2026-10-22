#!/usr/bin/env python3
"""Check RevOLVER `\\uses` edges against the Lean declarations they link.

Rules (see CONTRIBUTING.md):
  1. complete:   every book node whose declarations a node's Lean statement or
                 definition body uses must be an ancestor of that node;
  2. reduced:    no `\\uses` entry may already be reachable through another entry;
  3. acyclic:    no cycles, and no node may need a declaration linked downstream.

Usage (repository root, after `source scripts/env.sh` and a successful
`lake build LeanFun`):
  python scripts/check_blueprint_graph.py                 # whole book
  python scripts/check_blueprint_graph.py --nodes L1 L2   # only these nodes
  python scripts/check_blueprint_graph.py --proofs ...    # check proof dependencies and list edges no Lean uses
Exit status is nonzero if any checked node violates rules 1-3.
"""
import argparse, re, subprocess, sys, tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import review  # noqa: E402

KINDS = 'theorem|definition|lemma|corollary|proposition'


def parse():
    text = review.source_text(ROOT / 'blueprint/src/content.tex')
    nodes, order = {}, []
    for m in re.finditer(r'\\begin\{(%s)\}(\[[^\]]*\])?(.*?)\\end\{\1\}' % KINDS, text, re.S):
        body = m[3]
        lab = re.search(r'\\label\{([^}]+)\}', body)
        if not lab:
            continue
        l = lab[1]
        order.append(l)
        nodes[l] = dict(title=(m[2] or '')[1:-1], mathlib='\\mathlibok' in body,
            uses=[u.strip() for g in re.findall(r'\\uses\{([^}]*)\}', body) for u in g.split(',') if u.strip()],
            decls=[d.strip() for g in re.findall(r'\\lean\{([^}]*)\}', body) for d in g.split(',') if d.strip()])
    return nodes, order


def lean_deps(names, proofs=False):
    with tempfile.TemporaryDirectory() as tmp:
        src, out = Path(tmp) / 'names.txt', Path(tmp) / 'deps.tsv'
        src.write_text('\n'.join(names) + '\n')
        cmd = ['lake', 'env', 'lean', '--run', str(ROOT / 'scripts/BlueprintDeps.lean'), str(src), str(out)]
        if proofs:
            cmd.append('proofs')
        subprocess.run(cmd, cwd=ROOT, check=True)
        deps = {}
        for line in out.read_text().splitlines():
            k, _, v = line.partition('\t')
            deps[k] = None if v == '!missing' else [x for x in v.split(',') if x]
        return deps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nodes', nargs='*', help='node labels to check (default: all)')
    ap.add_argument('--proofs', action='store_true', help='check proof dependencies and list edges no Lean uses')
    args = ap.parse_args()
    nodes, order = parse()
    check = args.nodes or order
    unknown = [l for l in check if l not in nodes]
    if unknown:
        sys.exit(f'unknown node labels: {unknown}')
    linkers = defaultdict(list)
    for l in order:
        for d in nodes[l]['decls']:
            linkers[d].append(l)
    names = sorted(linkers)
    deps = lean_deps(names)
    full = lean_deps(names, proofs=True) if args.proofs else {}
    memo = {}
    problems = 0

    def anc(l, stack=()):
        if l in memo:
            return memo[l]
        s = set()
        for u in nodes.get(l, {}).get('uses', []):
            if u in stack:
                raise SystemExit(f'CYCLE: {" -> ".join(stack + (l, u))}')
            s.add(u)
            s |= anc(u, stack + (l,))
        memo[l] = s
        return s

    for l in order:
        anc(l)
    for l in check:
        n = nodes[l]
        out = []
        for u in n['uses']:
            if u not in nodes:
                out.append(f'unknown \\uses target {u}')
        for d in n['decls']:
            if deps.get(d, []) is None:
                out.append(f'declaration {d} not found (unbuilt or misspelt)')
        if not n['mathlib']:
            A = anc(l)
            need = defaultdict(set)
            for d in n['decls']:
                for c in (full if args.proofs else deps).get(d) or []:
                    ls = linkers.get(c, [])
                    if l in ls or not ls or set(ls) & A:
                        continue
                    need[ls[0]].add(c)
            for u, cs in need.items():
                via = ', '.join(sorted(cs)[:3])
                if l in anc(u):
                    out.append(f'needs {u} via {via}, but {u} is downstream: move the declaration link (rule 3)')
                else:
                    out.append(f'missing: add {u} to \\uses (statement uses {via}) (rule 1)')
        for u in n['uses']:
            w = next((w for w in n['uses'] if w != u and u in anc(w)), None)
            if w:
                out.append(f'redundant: remove {u}, already reached via {w} (rule 2)')
        if args.proofs and not n['mathlib'] and n['decls']:
            used = {x for d in n['decls'] for c in (full.get(d) or []) for x in linkers.get(c, [])}
            for u in n['uses']:
                if u in nodes and not nodes[u]['mathlib'] and nodes[u]['decls'] and u not in used:
                    out.append(f'note: no Lean use of {u} (keep only if a deliberate conceptual dependency)')
        if out:
            print(f'{l} [{n["title"]}]')
            for o in out:
                print('   ' + o)
            problems += sum(not o.startswith('note:') for o in out)
    print(f'checked {len(check)} nodes: {problems} rule violations')
    return int(bool(problems))


if __name__ == '__main__':
    sys.exit(main())
