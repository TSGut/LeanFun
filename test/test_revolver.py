"""Presentation contracts: canonical mathematics stays separate from discovery metadata."""
import json
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'blueprint/src'))
from revolver_data import source_nodes, source_notes, citation_terms, mathematical_source, load_catalog, legacy_redirects


class RevolverTests(unittest.TestCase):
    def test_catalog_has_exact_node_coverage(self):
        nodes, catalog = load_catalog(ROOT / 'blueprint/src')
        self.assertEqual(nodes.keys(), catalog.keys())
        self.assertTrue(all(v['reason'] and v['chapter'] for v in catalog.values()))
        for label, source in nodes.items():
            self.assertEqual(catalog[label]['role'] == 'planned', r'\notready' in source)

    def test_reference_table_targets_exist(self):
        nodes, _ = load_catalog(ROOT / 'blueprint/src')
        data = json.loads((ROOT / 'blueprint/src/revolver_reference.json').read_text())
        for row in data['rows']:
            self.assertEqual(len(row['nodes']), len(data['columns']))
            for cell in row['nodes']:
                for label in cell:
                    self.assertIn(label, nodes)

    def test_formula_search_does_not_drop_long_tail(self):
        source = r'\lean{Hidden.proof}\uses{hidden:node}' + 'x' * 900 + r'\frac{a}{b} \cite[18.9.15]{dlmf}'
        text = mathematical_source(source)
        self.assertIn(r'\frac{a}{b}', text)
        self.assertNotIn('Hidden.proof', text)
        self.assertNotIn('hidden:node', text)
        self.assertEqual(citation_terms(source), ['dlmf 18.9.15'])

    def test_multiple_citations_and_unlocated_citation(self):
        self.assertEqual(citation_terms(r'\cite[Chapter 7]{atap,szego} \cite{dlmf}'),
                         ['atap Chapter 7', 'szego Chapter 7', 'dlmf'])

    def test_editorial_notes_remain_searchable_but_outside_statements(self):
        source = (r'\begin{theorem}\label{thm:x}The assertion.\end{theorem}'
                  r'\rvnote{thm:x}{See \ref{thm:y}; $\{x\}$. \cite[18.3]{dlmf}}')
        self.assertNotIn('See', source_nodes(source)['thm:x'])
        self.assertEqual(source_notes(source)['thm:x'],
                         r'See \ref{thm:y}; $\{x\}$. \cite[18.3]{dlmf}')
        self.assertEqual(citation_terms(source_notes(source)['thm:x']), ['dlmf 18.3'])

    def test_legacy_map_preserves_fragments_without_loops(self):
        self.assertEqual(legacy_redirects({'def:x':'old.html#def:x', 'thm:y':'same.html#thm:y'},
                                         {'def:x':'new.html#def:x', 'thm:y':'same.html#thm:y'}),
                         {'old.html#def:x':'new.html#def:x'})

    def test_supporting_boundaries_and_planned_chapter(self):
        source = (ROOT / 'blueprint/src/content.tex').read_text()
        depth = 0
        for m in re.finditer(r'\\(begin|end)\{supporting\}|\\(?:chapter|part)\{', source):
            if m[1]:
                depth += 1 if m[1] == 'begin' else -1
                self.assertGreaterEqual(depth, 0)
            else:
                self.assertEqual(depth, 0, 'Disclosure crosses a chapter/part boundary')
        self.assertEqual(depth, 0)
        roadmap = source.split(r'\chapter{Roadmap and open targets}', 1)[1]
        self.assertFalse(source_nodes(roadmap), 'Roadmap prose must not be a theorem')
        targets = json.loads((ROOT / 'blueprint/src/revolver_catalog.json').read_text())['roadmap']
        self.assertEqual(set(re.findall(r'\\section\{[^}]+\}\\label\{([^}]+)\}', roadmap)), set(targets))

    def test_physical_chapters_match_catalog(self):
        source = (ROOT / 'blueprint/src/content.tex').read_text()
        _, catalog = load_catalog(ROOT / 'blueprint/src')
        chapters = list(re.finditer(r'\\chapter\{[^}]+\}\\label\{([^}]+)\}', source))
        for i,m in enumerate(chapters):
            chunk = source[m.end():chapters[i+1].start() if i+1<len(chapters) else len(source)]
            for label in source_nodes(chunk):
                self.assertEqual(catalog[label]['chapter'], m[1], label)


if __name__ == '__main__':
    unittest.main()
