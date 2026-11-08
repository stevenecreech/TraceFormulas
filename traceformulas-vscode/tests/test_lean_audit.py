import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts/audit_lean.py'
spec = importlib.util.spec_from_file_location('audit_lean', SCRIPT)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)

class GuardTests(unittest.TestCase):
    def test_version_match(self):
        self.assertEqual(audit.verify_lean_version('leanprover/lean4:v4.21.0-rc3',
            'Lean (version 4.21.0-rc3, platform, commit abc, Release)'), '4.21.0-rc3')

    def test_version_failures(self):
        for pin, actual in [
            ('leanprover/lean4:v4.21.0-rc3', 'Lean (version 4.21.0, platform)'),
            ('leanprover/lean4:v4.21.0-rc3', 'Lean (version 4.21.0-rc2, platform)'),
            ('leanprover/lean4:nightly', 'Lean (version 4.21.0-rc3, platform)'),
            ('leanprover/lean4:v4.21.0-rc3', 'unexpected output'),
        ]:
            with self.subTest(pin=pin, actual=actual), self.assertRaises(RuntimeError):
                audit.verify_lean_version(pin, actual)

    def test_attributed_modifiers(self):
        for source, modifier in [
            ('@[inline] unsafe def bad := 1', 'unsafe'),
            ('@[irreducible]\nprivate /- comment -/ partial def bad := bad', 'partial'),
            ('noncomputable unsafe opaque bad : Nat', 'unsafe'),
        ]:
            with self.subTest(source=source):
                self.assertEqual(audit.forbidden_lean_modifier(source), modifier)

    def test_literal_and_comment_boundaries(self):
        source = r'''/- unsafe /- partial -/ unsafe -/
-- partial def comment := 0
 def literal := "unsafe \\"partial"
 def rawLiteral := r##"unsafe /- partial \""##
 def character := '"'
 def «unsafe» := 0
 def unsafeName := 0
 def partial' := 0
'''
        # Use an ordinary string with an escaped quote, not a source escape outside it.
        source = source.replace(r'"unsafe \\"partial"', '"unsafe \\\"partial"')
        self.assertIsNone(audit.forbidden_lean_modifier(source))

    def test_unterminated_regions_fail_closed(self):
        for source in ['/- nested /- x -/', '"unsafe', 'r##"partial"#', '«unsafe']:
            with self.subTest(source=source), self.assertRaises(RuntimeError):
                audit.forbidden_lean_modifier(source)

    def run_runner(self, *, version=None, mutation=None, source='def checked := 1'):
        with tempfile.TemporaryDirectory(prefix='traceformulas-audit-test-') as directory:
            root = Path(directory)
            lean = root / 'lean'
            lean.mkdir()
            (root / 'source.lean').write_text(source)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.21.0-rc3\n')
            manifest = {'packagesDir': '.lake/packages', 'packages': [
                {'name': 'mathlib', 'url': 'https://example.invalid/mathlib', 'rev': 'locked'}]}
            (root / 'lake-manifest.json').write_text(json.dumps(manifest))
            for n in (1, 2, 3):
                section = root / f'volumes/Volume01/A/chapters/Chapter00/sections/Section{n:02}'
                section.mkdir(parents=True)
                (section / 'section.json').write_text(json.dumps(
                    {'formal': {'declarations': ['TraceFormulas.checked']}}))
            runs = []
            dependency_checks = []
            def output(argv, cwd=None):
                if argv[-1] == '--version':
                    return version or 'Lean (version 4.21.0-rc3, platform)'
                if argv[1] == 'rev-parse':
                    dependency_checks.append(len(runs))
                    return 'changed' if mutation == ('head', len(runs)) else 'locked'
                return ' M tracked.lean' if mutation == ('dirty', len(runs)) else ''
            def run(argv, *, cwd, stdout, stderr):
                runs.append(argv)
                self.assertEqual(cwd, root)
                if argv[-1] == 'lean/Audit.lean':
                    stdout.write('AXIOM_AUDIT_JSON ' + json.dumps({
                        'declaration': 'TraceFormulas.checked', 'axioms': ['propext']}) + '\n')
                    stdout.write('AXIOM_AUDIT_CHECKED 1\n')
                return type('Result', (), {'returncode': 0})()
            dest = root / 'audit'
            with patch.object(audit, 'ROOT', root), patch.object(audit, 'LEAN', lean), \
                 patch.object(audit, 'source_hashes', return_value={'source.lean': 'stable'}), \
                 patch.object(audit, 'output', side_effect=output), \
                 patch.object(audit.subprocess, 'run', side_effect=run), \
                 patch('sys.argv', ['audit_lean.py', '--lake', 'lake', '--output', str(dest)]), \
                 contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                result = audit.main()
            return result, json.loads((dest / 'record.json').read_text()), len(runs), dependency_checks

    def test_runner_success_rechecks_after_each_stage(self):
        result, record, runs, checks = self.run_runner()
        self.assertEqual((result, record['status'], runs), (0, 'passed', 2))
        self.assertEqual(checks, [0, 1, 2])
        self.assertEqual(record['dependency_verification_stages'],
                         ['before-build', 'after-build', 'after-axioms'])

    def test_runner_wrong_version_stops_before_build(self):
        result, record, runs, checks = self.run_runner(version='Lean (version 4.22.0, platform)')
        self.assertEqual((result, record['status'], runs, checks), (1, 'failed', 0, []))
        self.assertIn('does not match', record['error'])

    def test_runner_rejects_dependency_drift(self):
        for mutation in [('dirty', 0), ('head', 0), ('dirty', 1), ('head', 2)]:
            with self.subTest(mutation=mutation):
                result, record, runs, _ = self.run_runner(mutation=mutation)
                self.assertEqual((result, record['status']), (1, 'failed'))
                self.assertIn('differs from its locked source', record['error'])
                self.assertEqual(runs, mutation[1])

    def test_runner_rejects_attributed_unsafe(self):
        result, record, runs, _ = self.run_runner(source='@[inline] private unsafe def bad := 1')
        self.assertEqual((result, record['status'], runs), (1, 'failed', 0))
        self.assertIn('Forbidden unsafe keyword', record['error'])

if __name__ == '__main__':
    unittest.main(verbosity=2)
