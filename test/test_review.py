"""Integration tests: temporarily vary only test/ReviewTests/Fixture.lean, then restore it.

Real approvals are NEVER created. Fixture ledger lives in a temporary directory.
Run serially, with no concurrent edits to the fixture module.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import review

ROOT = review.ROOT
FIXTURE = ROOT / 'test/ReviewTests/Fixture.lean'
MODULE = 'ReviewTests.Fixture'


class ReviewTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = FIXTURE.read_text()
        cls.base = cls.compile(cls.original)

    @classmethod
    def tearDownClass(cls):
        FIXTURE.write_text(cls.original)
        subprocess.run(['lake', 'build', MODULE], cwd=ROOT, check=True, capture_output=True)

    @classmethod
    def compile(cls, text):
        FIXTURE.write_text(text)
        p = subprocess.run(['lake', 'build', MODULE, 'review_fingerprint'], cwd=ROOT,
                           text=True, capture_output=True)
        if p.returncode: raise RuntimeError(p.stdout + p.stderr)
        return review.extract(['ReviewFixture.' + n for n in
            ['region', 'witness', 'identity', 'constrained', 'polymorphic', 'argument', 'Box']], MODULE)

    def compare(self, before, after, decl, changed):
        result = self.compile(self.original.replace(before, after))
        a, b = self.base['ReviewFixture.' + decl], result['ReviewFixture.' + decl]
        self.assertEqual(a['fingerprint'] != b['fingerprint'], changed)
        return result

    def test_readable_definition_and_hypotheses(self):
        definition = self.base['ReviewFixture.region']['rendered']
        self.assertIn('definition ReviewFixture.region', definition)
        self.assertIn('Nat', definition)
        self.assertIn(':=', definition)
        self.assertIn('≤ 3', definition)
        self.assertNotIn('@', definition)
        self.assertNotIn('OfNat.ofNat', definition)
        self.assertLess(len(definition), 300)
        theorem = self.base['ReviewFixture.constrained']['rendered']
        self.assertIn('x = 0', theorem)
        self.assertNotIn(':=', theorem)
        self.assertIn('Type u', self.base['ReviewFixture.polymorphic']['rendered'])

    def test_proof_docstring_and_bound_names(self):
        self.compare(':= rfl', ':= by exact Eq.refl _', 'identity', False)
        self.compare('A fixture docstring.', 'An entirely different comment.', 'region', False)
        self.compare('(x : Nat) : x = x := rfl', '(y : Nat) : y = y := rfl', 'identity', False)

    def test_changes(self):
        self.compare('(x : Nat) : x = x', '(x : Nat) (h : x > 0) : x = x', 'identity', True)
        self.compare('(h : x = 0) : x = 0 := h', '(h : x ≤ 0) : x = 0 := Nat.eq_zero_of_le_zero h', 'constrained', True)
        self.compare('(x : Nat) : Nat := x', '(x : Int) : Int := x', 'argument', True)
        self.compare('x ≤ 3', 'x ≤ 4', 'witness', True)
        self.compare('Type u', 'Type (u + 1)', 'polymorphic', True)
        self.compare('(x : Nat) : Nat := x', '{x : Nat} : Nat := x', 'argument', True)
        self.compare('value : Nat', 'value : Int', 'Box', True)
        renamed = self.compile(self.original.replace('universe u', 'universe v').replace('Type u','Type v'))
        self.assertEqual(renamed['ReviewFixture.polymorphic']['fingerprint'],
                         self.base['ReviewFixture.polymorphic']['fingerprint'])

    def test_ledger_cli(self):
        self.compile(self.original)
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp) / 'statements.toml'
            review.write_ledger(ledger, {})
            bp = Path(tmp) / 'content.tex'
            book = (r'\begin{theorem}[Fixture]\label{thm:fixture}\lean{ReviewFixture.identity}\leanok'
                    '\nEvery natural number equals itself.\n\\end{theorem}')
            bp.write_text(book)
            base = [sys.executable, str(ROOT / 'scripts/review.py'), '--ledger', str(ledger),
                    '--blueprint', str(bp), '--module', MODULE]
            def run(*args):
                return subprocess.run(base + list(args), cwd=ROOT, capture_output=True, text=True)
            result = run('approve', 'ReviewFixture.identity', '--reviewer', 'fixture-owner', '--fixture')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(run('check').returncode, 0)
            # Bookkeeping macros and line breaks are not reviewed text.
            bp.write_text(book.replace(r'\leanok', r'\uses{thm:other}').replace(' equals', '\n  equals'))
            self.assertEqual(run('check').returncode, 0, run('check').stdout)
            # Changing the statement text voids the review and shows both versions.
            bp.write_text(book.replace('equals itself', 'is positive'))
            text_stale = run('check')
            self.assertNotEqual(text_stale.returncode, 0)
            self.assertIn('STALE: ReviewFixture.identity', text_stale.stdout)
            self.assertIn('--- reviewed book text', text_stale.stdout)
            self.assertIn('equals itself', text_stale.stdout)
            self.assertIn('is positive', text_stale.stdout)
            bp.write_text(book)
            self.assertEqual(run('check').returncode, 0)
            self.compile(self.original.replace('(x : Nat) : x = x', '(x : Nat) (h : x > 0) : x = x'))
            stale = run('check')
            self.assertNotEqual(stale.returncode, 0)
            self.assertIn('STALE: ReviewFixture.identity', stale.stdout)
            self.assertIn('--- reviewed', stale.stdout)
            self.assertIn('+++ current', stale.stdout)
            self.assertIn('Nat', stale.stdout)
            status = Path(tmp) / 'status.json'
            self.assertEqual(run('status', '--json', str(status)).returncode, 0)
            self.assertEqual(json.loads(status.read_text())['nodes']['thm:fixture'], 'stale')

    def test_node_states_and_style(self):
        spec = importlib.util.spec_from_file_location('leanfunreview', ROOT / 'blueprint/src/leanfunreview.py')
        plugin = importlib.util.module_from_spec(spec); spec.loader.exec_module(plugin)
        self.assertEqual(review.node_status([], {}), 'unreviewed')
        self.assertEqual(review.node_status(['a','b'], {'a':'reviewed-current','b':'unreviewed'}), 'unreviewed')
        self.assertEqual(review.node_status(['a'], {'a':'reviewed-current'}), 'reviewed-current')
        self.assertEqual(plugin.review_style('', 'reviewed-current', True), 'filled,bold')
        self.assertEqual(plugin.review_style('rounded,filled', 'stale', True), 'rounded,filled,dashed')
        self.assertEqual(plugin.review_style('', 'unreviewed', False), '')
        node = SimpleNamespace(userdata={'leandecls': ['a']})
        callbacks, resources = [], []
        graph = {'graphs': {'all': SimpleNamespace(nodes=[node])},
                 'fillcolorizer': lambda n: '#EEE4F7', 'legend': []}
        doc = SimpleNamespace(config={'general': {'renderer': 'HTML5'}},
                              userdata={'dep_graph': graph},
                              addPostParseCallbacks=lambda order, cb: callbacks.append(cb),
                              addPackageResource=resources.append)
        with patch.object(plugin.subprocess, 'run'), patch.object(plugin.Path, 'read_text',
                return_value=json.dumps({'declarations': {'a': 'reviewed-current'}})):
            plugin.ProcessOptions({}, doc)
        for cb in callbacks: cb()
        self.assertEqual(graph['stylerizer'](node), 'filled,bold')
        html = doc.userdata['thm_header_extras_tpl'][0].render(obj=node)
        self.assertIn('human-reviewed', html)
        self.assertIn(plugin.HUMAN, html)
        self.assertNotIn(plugin.ROBOT, html)
        stale = SimpleNamespace(userdata={'leandecls': ['b']})
        graph['graphs']['all'].nodes.append(stale)
        with patch.object(plugin.subprocess, 'run'), patch.object(plugin.Path, 'read_text',
                return_value=json.dumps({'declarations': {'a': 'reviewed-current', 'b': 'stale'}})):
            plugin.ProcessOptions({}, doc)
        for cb in callbacks: cb()
        html = doc.userdata['thm_header_extras_tpl'][-1].render(obj=stale)
        self.assertIn(plugin.STALE + ' human review stale', ' '.join(html.split()))
        self.assertEqual(graph['fillcolorizer'](node), '#EEE4F7')
        # Non-HTML processing is a no-op, without touching the ledger or tools.
        plugin.ProcessOptions({}, SimpleNamespace(config={'general': {'renderer': 'LaTeX'}}))

    def test_module_system(self):
        path = ROOT / 'test/ReviewTests/Public.lean'
        original = path.read_text()
        def sample():
            p = subprocess.run(['lake', 'build', 'ReviewTests.Public', 'review_fingerprint'],
                               cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            return review.extract(['ReviewPublic.witness'], 'ReviewTests.Public')['ReviewPublic.witness']
        try:
            before = sample()
            path.write_text(original.replace('Nat := 3', 'Nat := 4'))
            after = sample()
            self.assertNotEqual(before['fingerprint'], after['fingerprint'])
            self.assertEqual(before['rendered'], after['rendered'])
            self.assertIn('Root rendering unchanged', review.statement_diff(before, after))
        finally:
            path.write_text(original)
            subprocess.run(['lake', 'build', 'ReviewTests.Public'], cwd=ROOT,
                           check=True, capture_output=True)

    def test_revision_policy_and_missing(self):
        old = {'fingerprint': 'abc', 'toolchain': 'lean', 'external': ['X'], 'rendered': 'old'}
        new = {'fingerprint': 'abc', 'rendered': 'old', 'missing_external': []}
        self.assertEqual(review.state(old, new, {'toolchain': 'lean'}), 'reviewed-current')
        self.assertEqual(review.state(old, new, {'toolchain': 'other'}), 'stale')
        self.assertEqual(review.state(old, dict(new, missing_external=['X']), {'toolchain': 'lean'}), 'stale')
        self.assertEqual(review.state(old, {'missing': True}, {'toolchain': 'lean'}), 'stale')
        self.assertIn('declaration missing', review.statement_diff(old, {'missing': True}))

    def test_book_text(self):
        with tempfile.TemporaryDirectory() as tmp:
            bp = Path(tmp) / 'content.tex'
            bp.write_text('\\begin{definition}[Thing]\\label{def:a}\\uses{def:b}\n'
                          '\\lean{A.a, A.b}\\leanok\nFor $x$, define % a comment\n'
                          '\\begin{equation*}f(x)=x\\end{equation*}.\n\\end{definition}\n'
                          '\\begin{proof}\\leanok Not part of the statement.\\end{proof}\n')
            names, nodes, texts = review.blueprint(bp, with_text=True)
        self.assertEqual(nodes, {'def:a': ['A.a', 'A.b']})
        self.assertEqual(texts['def:a'],
                         '[Thing] For $x$, define \\begin{equation*}f(x)=x\\end{equation*}.')
        self.assertEqual(review.book_for('A.b', nodes, texts), (['def:a'], [texts['def:a']]))
        self.assertEqual(review.book_for('A.c', nodes, texts), ([], []))
        meta = {'toolchain': 'lean'}
        old = {'fingerprint': 'abc', 'toolchain': 'lean', 'external': [], 'rendered': 'r',
               'book_nodes': ['def:a'], 'book_texts': ['text']}
        new = {'fingerprint': 'abc', 'rendered': 'r', 'missing_external': []}
        self.assertEqual(review.state(old, new, meta, (['def:a'], ['text'])), 'reviewed-current')
        self.assertEqual(review.state(old, new, meta, (['def:a'], ['edited'])), 'stale')
        self.assertEqual(review.state(old, new, meta, (['def:a', 'thm:b'], ['text', 'x'])), 'stale')
        self.assertEqual(review.state(old, new, meta, ([], [])), 'stale')
        legacy = {k: v for k, v in old.items() if not k.startswith('book_')}
        self.assertEqual(review.state(legacy, new, meta, (['def:a'], ['text'])), 'stale')
        self.assertIn('not recorded', review.report(legacy, new, (['def:a'], ['text'])))
        self.assertEqual(review.book_diff(old, (['def:a'], ['text'])), '')

    def test_banner_counts(self):
        spec = importlib.util.spec_from_file_location('leanfunreview', ROOT / 'blueprint/src/leanfunreview.py')
        plugin = importlib.util.module_from_spec(spec); spec.loader.exec_module(plugin)
        def node(status, icon=True):
            return SimpleNamespace(userdata={'statement_review': status,
                                             'review_icon': plugin.ROBOT if icon else ''})
        nodes = [node('reviewed-current'), node('stale'), node('stale'), node('unreviewed'),
                 node('unreviewed', icon=False)]
        self.assertEqual(plugin.banner_counts(nodes), (1, 2, 1))
        svg = plugin.review_banner(1, 2, 1)
        self.assertIn('human-reviewed: 1 (25%)', svg)
        self.assertIn(plugin.STALE + ' review stale: 2 (50%)', svg)
        self.assertIn('LLM-only: 1 (25%)', svg)



class PathCaseTests(unittest.TestCase):
    def test_executable_root_matches_git_case(self):
        """Git's spelling is authoritative even on case-insensitive filesystems."""
        import tomllib
        config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
        executable = next(e for e in config['lean_exe'] if e['name'] == 'review_fingerprint')
        source = executable['root'].replace('.', '/') + '.lean'
        tracked = subprocess.check_output(
            ['git', 'ls-files', '-z'], cwd=ROOT, text=True).split('\0')
        self.assertIn(source, tracked, f'Lean module path must match Git case exactly: {source}')


if __name__ == '__main__': unittest.main()
