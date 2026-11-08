"""The viewer must retain a complete PDF during successful or failed builds."""
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from tex import build_pdf, TexError


class PdfRefreshTests(unittest.TestCase):
    def test_success_and_failure_keep_complete_pdf_available(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = r'\documentclass{article}\begin{document}First version.\end{document}'
            pdf = build_pdf(root, 'v1a', source)
            original = pdf.read_bytes()
            failures = []
            stop = threading.Event()

            def observe():
                while not stop.is_set():
                    try:
                        data = pdf.read_bytes()
                        if not data.startswith(b'%PDF-') or not data.rstrip().endswith(b'%%EOF'):
                            failures.append('Incomplete PDF observed')
                    except OSError as exc:
                        failures.append(str(exc))
                    time.sleep(0.002)

            observer = threading.Thread(target=observe)
            observer.start()
            try:
                self.assertEqual(build_pdf(root, 'v1a', source.replace('First', 'Second')), pdf)
                updated = pdf.read_bytes()
                self.assertNotEqual(original, updated)
                with self.assertRaises(TexError):
                    build_pdf(root, 'v1a', r'\documentclass{article}\begin{document}\undefinedcommand\end{document}')
                self.assertEqual(updated, pdf.read_bytes())
            finally:
                stop.set()
                observer.join()
            self.assertEqual(failures, [])
