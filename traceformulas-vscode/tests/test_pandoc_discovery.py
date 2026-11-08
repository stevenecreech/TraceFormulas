"""Find an installed converter even without a checkout-local virtual environment."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from tex import pandoc_path


class PandocDiscoveryTests(unittest.TestCase):
    def test_installed_package_without_project_venv_or_path_entry(self):
        converter = Path(pandoc_path(ROOT)).resolve()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            package = root / 'site-packages/pypandoc'
            (package / 'files').mkdir(parents=True)
            (package / '__init__.py').write_text('')
            # Reuse the installed binary without copying its large payload.
            bundled = package / 'files/pandoc'
            bundled.symlink_to(converter)
            environment = {k: v for k, v in os.environ.items() if k != 'PANDOC'}
            environment.update(PATH='', PYTHONDONTWRITEBYTECODE='1')
            result = subprocess.run([
                sys.executable, '-c',
                'import sys; from pathlib import Path; '
                'sys.path[:0] = sys.argv[1:3]; '
                'from tex import pandoc_path, run; '
                'root = Path(sys.argv[3]); '
                'converter = pandoc_path(root); '
                'assert converter == sys.argv[4], converter; '
                'print(run([converter, "--version"], cwd=root))',
                str(package.parent), str(ROOT / 'scripts'), str(root), str(bundled),
            ], cwd=root, env=environment, text=True, capture_output=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('pandoc ', result.stdout)


if __name__ == '__main__':
    unittest.main()
