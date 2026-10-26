"""Validate generated discovery links after leanblueprint web."""
from html.parser import HTMLParser
import json
import re
from pathlib import Path
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'blueprint/src'))
from revolver_data import load_catalog, source_notes, mathematical_source

class Anchors(HTMLParser):
    def __init__(self, text):
        super().__init__(); self.ids=set(); self.feed(text)
    def handle_starttag(self, tag, attrs):
        attrs=dict(attrs)
        for key in ('id', 'name'):
            if key in attrs: self.ids.add(attrs[key])

def main():
    directory=ROOT/'blueprint/web'
    entries=json.loads((directory/'search-index.json').read_text())
    nodes,catalog=load_catalog(ROOT/'blueprint/src')
    indexed={e['label']:e for e in entries if e.get('role') and e['kind'] != 'Section'}
    assert indexed.keys()==nodes.keys(), 'Incomplete index'
    cache={}
    def check(url):
        u=urlsplit(url); p=directory/unquote(u.path or 'index.html')
        assert p.is_file(), f'Missing page: {url}'
        if u.fragment:
            if p not in cache: cache[p]=Anchors(p.read_text()).ids
            assert unquote(u.fragment) in cache[p], f'Missing anchor: {url}'
    for e in entries: check(e['url'])
    for label,e in indexed.items():
        assert e['math'] and e['text'], label
        assert e['role']==catalog[label]['role'], label
    source = (ROOT/'blueprint/src/content.tex').read_text()
    for label, note in source_notes(source).items():
        assert mathematical_source(note) in indexed[label]['math'], f'Unsearchable commentary: {label}'
    roadmap = json.loads((ROOT/'blueprint/src/revolver_catalog.json').read_text()).get('roadmap', {})
    by_label = {e['label']: e for e in entries}
    # A part lists chapters; every chapter is a complete reading page.
    part_number = chapter_number = 0
    chapter_label = None
    for kind, label in re.findall(
            r'\\(part|chapter|section)\{[^}]*\}\s*\\label\{([^}]+)\}', source):
        if kind == 'part':
            part_number += 1
            chapter_number = 0
        elif kind == 'chapter':
            chapter_number += 1
            chapter_label = label
            assert by_label[label]['ref'] == f'{part_number}.{chapter_number}', label
        elif chapter_label:
            assert urlsplit(by_label[label]['url']).path == urlsplit(by_label[chapter_label]['url']).path, label
    for label, meta in catalog.items():
        assert urlsplit(indexed[label]['url']).path == urlsplit(by_label[meta['chapter']]['url']).path, label
    for page in ['index.html'] + [urlsplit(e['url']).path for e in entries if e['kind'] == 'Chapter']:
        sidebar = re.search(r'<nav class="toc">.*?</nav>', (directory/page).read_text(), re.S)[0]
        assert not re.search(r'class="sub-toc-[2-9]', sidebar), f'Internal headings leaked into sidebar: {page}'
    for label in roadmap:
        assert by_label[label]['kind'] == 'Section', f'Roadmap rendered as a statement: {label}'
        assert by_label[label]['status'] == 'planned', label
        assert by_label[label]['role'] == 'planned', label
    redirects=json.loads((directory/'legacy-urls.json').read_text())
    old=json.loads((ROOT/'blueprint/src/revolver_legacy_urls.json').read_text())
    current={e['label']:e['url'] for e in entries}
    for label,url in old.items():
        target=redirects.get(url,url)
        if label in current: assert target==current[label], f'Wrong legacy destination: {label}'
        check(target)
        assert target not in redirects, f'Redirect chain: {target}'
        assert (directory/url.split('#')[0]).is_file(), url
    for target in redirects.values(): check(target)
    print(f'{len(indexed)} nodes indexed; {len(entries)} current links and {len(old)} legacy links valid; {len(redirects)} redirects valid.')

if __name__=='__main__': main()
