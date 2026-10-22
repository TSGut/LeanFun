#!/usr/bin/env python3
"""The LeanFun version a build comes from, derived from Git tags `vMAJOR.MINOR.PATCH`.

    v0.2.0                     the build is exactly at release tag v0.2.0
    v0.2.0+14 (a1b2c3d)        14 commits after v0.2.0
    unreleased (a1b2c3d)       no release tag yet
    ... with ", modified"      the working tree has uncommitted changes

Usage: version.py [--url REPOSITORY] [--tex]
  --url REPOSITORY  print the release page (tagged) or commit page (otherwise) instead
  --tex             print a TeX definition of \\leanfunversion
"""
import argparse
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    p = subprocess.run(['git', *args], cwd=ROOT, capture_output=True, text=True)
    return p.stdout.strip() if p.returncode == 0 else None


def describe():
    """(tag, distance, short sha, full sha, dirty) for HEAD; tag is None before the first release."""
    full = git('rev-parse', 'HEAD') or ''
    short = full[:7]
    dirty = bool(git('status', '--porcelain', '--untracked-files=no'))
    d = git('describe', '--tags', '--match', 'v[0-9]*', '--long')
    m = re.fullmatch(r'(v\d+\.\d+\.\d+.*)-(\d+)-g[0-9a-f]+', d or '')
    if not m:
        return None, 0, short, full, dirty
    return m[1], int(m[2]), short, full, dirty


def format_version(tag, distance, short, dirty):
    if tag and distance == 0 and not dirty:
        return tag
    base = f'{tag}+{distance}' if tag and distance else (tag or 'unreleased')
    detail = short + (', modified' if dirty else '')
    return f'{base} ({detail})' if detail else base


def version_url(repository, tag, distance, full, dirty):
    repository = repository.rstrip('/')
    if tag and distance == 0 and not dirty:
        return f'{repository}/releases/tag/{tag}'
    return f'{repository}/commit/{full}' if full else repository


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--url')
    ap.add_argument('--tex', action='store_true')
    args = ap.parse_args()
    tag, distance, short, full, dirty = describe()
    if args.url:
        print(version_url(args.url, tag, distance, full, dirty))
    elif args.tex:
        print('\\newcommand{\\leanfunversion}{' + format_version(tag, distance, short, dirty) + '}')
    else:
        print(format_version(tag, distance, short, dirty))


if __name__ == '__main__':
    main()
