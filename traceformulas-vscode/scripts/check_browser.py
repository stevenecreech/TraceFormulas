"""Optional browser smoke test. Uses Playwright and an existing Chrome installation."""
from pathlib import Path
import argparse
import functools
import http.server
import json
import threading
import tempfile
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--chrome', default='/Applications/Google Chrome.app/Contents/MacOS/Google Chrome')
    args = parser.parse_args()
    if not Path(args.chrome).is_file():
        parser.error('Supply --chrome with the path to an existing Chrome/Chromium executable.')
    with tempfile.TemporaryDirectory() as directory:
        # Exercise a real hosting subdirectory, not just the domain root.
        (Path(directory) / 'trace-formulas').symlink_to(ROOT / 'dist', target_is_directory=True)
        handler = functools.partial(QuietHandler, directory=directory)
        server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        base = f'http://127.0.0.1:{server.server_port}/trace-formulas/'
        errors = []
        try:
            with sync_playwright() as pw:
                browser = pw.chromium.launch(executable_path=args.chrome, headless=True)
                page = browser.new_page(viewport={'width': 1440, 'height': 1100})
                page.on('pageerror', lambda error: errors.append(str(error)))
                response = page.goto(base)
                assert response.status == 200
                page.locator('.series-part').first.wait_for()
                assert page.locator('.series-part').count() == 12
                (ROOT / '.build').mkdir(exist_ok=True)
                page.screenshot(path=str(ROOT / '.build/series-desktop.png'), full_page=True)
                series = json.loads((ROOT / 'dist/data/series.json').read_text())
                for volume in series['volumes']:
                    page.goto(base + '?volume=' + volume['id'] + '#/overview')
                    page.locator('main h1').wait_for()
                    assert page.locator('.error-page').count() == 0
                    if volume['status'] == 'planned':
                        assert 'This volume is planned' in page.locator('main').inner_text()
                page.goto(base + '?volume=v1a#/chapter/v1a-ch00/read')
                page.locator('#v1a-ch00-s1 .prose').wait_for()
                page.wait_for_function("window.MathJax?.startup?.promise !== undefined")
                page.evaluate('async () => { await MathJax.startup.promise; await MathJax.typesetPromise(); }')
                assert page.locator('mjx-container').count() > 0
                assert page.locator('[data-mjx-error], mjx-merror').count() == 0
                cyclic = page.locator('[id="linear-algebra.trace-cyclic"]')
                assert cyclic.evaluate('el => el.matches(".proposition.theorem-block")')
                assert 'Cyclicity for two factors' in cyclic.inner_text()
                assert page.locator('#v1a-ch00-s1 .proof').count() == 3
                assert page.locator('.section-content .prose h2, .section-content .prose h3').count() == 0
                assert page.locator('.section-content').count() == 3
                assert page.locator('#v1a-ch00-s3').count() == 0
                assert page.locator('#v1a-ch00-s1 .theorem-block').first.get_attribute('id') == 'linear-algebra.trace-eigenvalue-sum'
                page.goto(base + '?volume=v1a#/chapter/v1a-app-i/read')
                page.locator('.prose a[href$="/finite-kernel-model"]').first.click()
                page.wait_for_url('**?volume=v1a#/chapter/v1a-ch00/read/v1a-ch00-s2/finite-kernel-model')
                anchor = page.locator('#finite-kernel-model')
                anchor.wait_for(state='attached')
                assert anchor.evaluate('el => el.matches("span.prose-anchor")')
                page.evaluate('async () => { await MathJax.startup.promise; await MathJax.typesetPromise(); }')
                page.wait_for_function('(() => { const r = document.getElementById("finite-kernel-model").getBoundingClientRect(); const bar = document.querySelector(".topbar").getBoundingClientRect(); return r.top >= bar.bottom && r.top < innerHeight; })()')
                page.goto(base + '?volume=v1a#/chapter/v1a-app-i/read')
                page.locator('#v1a-notation-matrices').wait_for()
                page.locator('.prose a[href$="/definition-the-trace"]').first.click()
                page.locator('#definition-the-trace').wait_for()
                assert page.locator('#definition-the-trace').evaluate('el => el.matches(".definition.theorem-block")')
                page.go_back()
                page.locator('#v1a-notation-matrices').wait_for()
                page.locator('.prose a[href$="/relative-finite-pairing"]').first.click()
                page.wait_for_url('**?volume=v1a#/chapter/v1a-ch00/read/v1a-ch00-s5/relative-finite-pairing')
                page.locator('#relative-finite-pairing').wait_for()
                assert page.locator('#v1a-ch00-s5 .section-number').inner_text() == 'SECTION 0.3'
                page.go_back()
                page.locator('#v1a-notation-matrices').wait_for()
                page.go_forward()
                page.locator('#v1a-ch00-s1 .prose').wait_for()
                page.locator('a.tab[href$="/compare"]').click()
                page.locator('#v1a-ch00-s1 pre code').wait_for()
                chapter_data = json.loads((ROOT / 'dist/data/v1a/content.json').read_text())['chapters']['v1a-ch00']
                for source in chapter_data['formal']['sources']:
                    expected = (ROOT / source['source'].removeprefix('sources/')).read_text()
                    assert page.locator('#' + source['sectionId'] + ' pre code').inner_text() == expected
                assert page.locator('[id="linear-algebra.trace-cyclic"]').evaluate('el => el.matches(".proposition.theorem-block")')
                for path in page.locator('.comparison a[download]').evaluate_all('(nodes) => nodes.map(n => n.href)'):
                    assert page.request.get(path).status == 200
                page.screenshot(path=str(ROOT / '.build/compare-desktop.png'), full_page=True)
                page.locator('a.tab[href$="/formal"]').click()
                for source in chapter_data['formal']['sources']:
                    expected = (ROOT / source['source'].removeprefix('sources/')).read_text()
                    assert page.locator('#' + source['sectionId'] + ' .lean-source code').inner_text() == expected
                page.locator('a.tab[href$="/watch"]').click()
                page.locator('.media-card').first.wait_for()
                assert page.locator('.media-card').count() == 1
                page.locator('.transcript summary').click()
                transcript = page.locator('.transcript')
                assert 'Chapter 0: What does a trace measure?' in transcript.inner_text()
                assert 'Scene 15. One kernel, three questions.' in transcript.inner_text()
                assert 'No recording has been produced.' in transcript.inner_text()
                page.evaluate('async () => { await MathJax.startup.promise; await MathJax.typesetPromise(); }')
                assert transcript.locator('mjx-container').count() > 0
                assert page.locator('[data-mjx-error], mjx-merror').count() == 0
                page.screenshot(path=str(ROOT / '.build/chapter00-watch-desktop.png'))
                page.locator('a.tab[href$="/map"]').click()
                page.locator('#map-focus').select_option('v1a-ch00-s1')
                assert 'Finite matrices' in page.locator('.dep-node.current').inner_text()
                page.goto(base + '?volume=v1a#/overview')
                pdf = page.locator('a[href="pdf/v1a.pdf"]')
                pdf.wait_for()
                pdf_response = page.request.get(base + 'pdf/v1a.pdf')
                assert pdf_response.status == 200 and pdf_response.body().startswith(b'%PDF-')
                page.set_viewport_size({'width': 390, 'height': 844})
                page.goto(base + '?volume=v1a#/chapter/v1a-ch00/compare')
                page.locator('.comparison').first.wait_for()
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                page.goto(base + '?volume=v1a#/chapter/v1a-ch00/watch')
                page.locator('.transcript summary').click()
                page.evaluate('async () => { await MathJax.startup.promise; await MathJax.typesetPromise(); }')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                assert page.locator('[data-mjx-error], mjx-merror').count() == 0
                page.screenshot(path=str(ROOT / '.build/chapter00-watch-mobile.png'))
                page.locator('.menu-toggle').click()
                page.locator('#volume-select').select_option('v2b')
                page.wait_for_url('**/?volume=v2b#/overview')
                assert 'This volume is planned' in page.locator('main').inner_text()
                page.screenshot(path=str(ROOT / '.build/volume-mobile.png'), full_page=True)
                assert not errors, errors
                browser.close()
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
    print('Browser checks passed: 12 volume parts, all chapter tabs, cross-chapter hyperlink and back navigation, exact Lean source, MathJax, PDF/source downloads, mobile navigation, subdirectory hosting; no page errors.')


if __name__ == '__main__':
    main()
