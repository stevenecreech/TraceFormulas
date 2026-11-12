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
                    assert 'autoformalized · awaiting human review' in page.locator('#' + source['sectionId'] + ' .comparison-column').nth(1).inner_text().casefold()
                assert page.locator('[id="linear-algebra.trace-cyclic"]').evaluate('el => el.matches(".proposition.theorem-block")')
                for path in page.locator('.comparison a[download]').evaluate_all('(nodes) => nodes.map(n => n.href)'):
                    assert page.request.get(path).status == 200
                page.screenshot(path=str(ROOT / '.build/compare-desktop.png'), full_page=True)
                page.locator('a.tab[href$="/formal"]').click()
                page.locator('.formal-panel').first.wait_for()
                assert 'autoformalized · awaiting human review' in page.locator('.formal-panel').first.inner_text().casefold()
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
                page.goto(base + '?volume=v1a#/chapter/v1a-ch01/read')
                page.locator('#v1a-ch01-s1 .prose').wait_for()
                page.evaluate('async () => { await MathJax.startup.promise; await MathJax.typesetPromise(); }')
                assert page.locator('.section-number').all_text_contents() == [f'SECTION 1.{i}' for i in range(1, 9)]
                assert page.locator('#v1a-ch01-s6 .section-number').inner_text() == 'SECTION 1.2'
                assert page.locator('#v1a-ch01-s3 .section-number').inner_text() == 'SECTION 1.6'
                assert page.locator('#v1a-ch01-s5 .section-number').inner_text() == 'SECTION 1.8'
                page.locator('#v1a-ch01-s5 a[href$="/measure.haar-uniqueness"]').first.click()
                page.wait_for_url('**/chapter/v1a-app-a/read/v1a-app-a-s2/measure.haar-uniqueness')
                page.locator('[id="measure.haar-uniqueness"]').wait_for(state='visible')
                page.evaluate('async () => { await MathJax.typesetPromise(); }')
                assert page.locator('.section-number').all_text_contents() == ['SECTION A.1', 'SECTION A.2']
                assert page.locator('.aside-number').all_text_contents() == ['A.1', 'A.2']
                assert page.locator('.numbered-equation').count() == 3
                assert page.locator('[data-mjx-error], mjx-merror').count() == 0
                page.set_viewport_size({'width': 390, 'height': 844})
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                page.locator('[id="measure.haar-uniqueness"]').scroll_into_view_if_needed()
                page.screenshot(path=str(ROOT / '.build/haar-appendix-mobile.png'))
                page.set_viewport_size({'width': 1440, 'height': 1100})
                page.goto(base + '?volume=v1a#/chapter/v1a-app-a/compare')
                page.locator('.comparison').first.wait_for()
                assert page.locator('.comparison').count() == 2
                appendix = json.loads((ROOT / 'dist/data/v1a/content.json').read_text())['chapters']['v1a-app-a']
                for row in appendix['comparisons']:
                    comparison = page.locator('#' + row['sectionId'])
                    assert 'in progress' in comparison.locator('.comparison-column').nth(1).inner_text().casefold()
                    assert comparison.locator('pre code').inner_text() == (ROOT / row['leanSource'].removeprefix('sources/')).read_text()
                assert 'Autoformalized' not in page.locator('main').inner_text()
                page.goto(base + '?volume=v1a#/chapter/v1a-app-a/map')
                page.locator('#map-focus').wait_for()
                assert page.locator('#map-focus option').nth(1).inner_text().startswith('A.1 · ')
                assert page.locator('#map-focus option').nth(2).inner_text().startswith('A.2 · ')
                page.goto(base + '?volume=v1a#/chapter/v1a-ch01/read')
                page.locator('#v1a-ch01-s1 .prose').wait_for()
                page.evaluate('async () => { await MathJax.typesetPromise(); }')
                assert page.locator('[data-mjx-error], mjx-merror').count() == 0
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                assert page.locator('.numbered-equation mjx-container[display="true"]').count() == 44
                assert page.locator('[id="eq:hyperbolic-distance"] .equation-number').inner_text() == '(1.3.3)'
                horizontal_ref = page.locator('#v1a-ch01-s4 a.equation-reference[href$="/eq%3Ahorizontal-segment-length"]').first
                assert horizontal_ref.inner_text() == '(1.3.4)'
                horizontal_ref.click()
                page.wait_for_url('**/read/v1a-ch01-s2/eq%3Ahorizontal-segment-length')
                page.locator('[id="eq:horizontal-segment-length"]').wait_for(state='visible')
                page.goto(base + '?volume=v1a#/chapter/v1a-ch01/read')
                page.locator('#v1a-ch01-s4 .prose').wait_for()
                page.evaluate('async () => { await MathJax.typesetPromise(); }')
                distance_ref = page.locator('#v1a-ch01-s7 a.equation-reference[href$="/eq%3Ahyperbolic-distance"]')
                assert distance_ref.inner_text() == '(1.3.3)'
                distance_ref.click()
                page.wait_for_url('**/read/v1a-ch01-s2/eq%3Ahyperbolic-distance')
                equation = page.locator('[id="eq:hyperbolic-distance"]')
                equation.wait_for(state='visible')
                page.evaluate('async () => { await MathJax.typesetPromise(); }')
                equation.screenshot(path=str(ROOT / '.build/equation-desktop.png'))
                assert equation.evaluate('el => { const r = el.getBoundingClientRect(); return r.top >= 0 && r.top < innerHeight; }')
                page.go_back()
                page.wait_for_url('**/chapter/v1a-ch01/read')
                page.locator('#v1a-ch01-s5 .prose a[href$="/hyperbolic.invariant-density"]').click()
                page.wait_for_url('**/read/v1a-ch01-s2/hyperbolic.invariant-density')
                page.locator('#v1a-ch01-s2 .prose a[href$="/hyperbolic.geodesics-diagram"]').click()
                page.wait_for_url('**/read/v1a-ch01-s2/hyperbolic.geodesics-diagram')
                figure = page.locator('[id="hyperbolic.geodesics-diagram"]')
                figure.wait_for()
                graphic = figure.locator('img')
                assert graphic.get_attribute('src').endswith('/figures/geodesics.svg')
                graphic.evaluate('img => img.decode()')
                assert graphic.evaluate('img => img.naturalWidth > 0')
                assert 'perpendicular bisector' in figure.locator('figcaption').inner_text()
                response = page.request.get(graphic.get_attribute('src'))
                assert response.status == 200 and b'<svg' in response.body()
                assert page.request.get(graphic.get_attribute('src').replace('.svg', '.pdf')).body().startswith(b'%PDF-')
                figure.screenshot(path=str(ROOT / '.build/chapter01-geodesics-desktop.png'))
                for section_id, label, stem in (
                    ('v1a-ch01-s8', 'hyperbolic.elliptic-motion-diagram', 'elliptic-motion'),
                    ('v1a-ch01-s8', 'hyperbolic.parabolic-motion-diagram', 'parabolic-motion'),
                    ('v1a-ch01-s8', 'hyperbolic.translation-dilation-diagram', 'translation-dilation'),
                    ('v1a-ch01-s3', 'modular.domain-diagram', 'fundamental-domain'),
                    ('v1a-ch01-s3', 'modular.tiling-diagram', 'modular-tiling'),
                ):
                    page.locator(f'#{section_id} .prose a[href$="/{label}"]').click()
                    page.wait_for_url(f'**/read/{section_id}/{label}')
                    page.evaluate('async () => { await MathJax.typesetPromise(); }')
                    motion_figure = page.locator(f'[id="{label}"]')
                    graphic = motion_figure.locator('img')
                    assert graphic.get_attribute('src').endswith(f'/figures/{stem}.svg')
                    graphic.evaluate('img => img.decode()')
                    assert graphic.evaluate('img => img.naturalWidth > 0')
                    if stem == 'fundamental-domain':
                        assert graphic.evaluate('img => { const r=img.getBoundingClientRect(), f=img.closest("figure").getBoundingClientRect(); return Math.abs(r.width/f.width-.55)<.01 && Math.abs((r.left+r.right)-(f.left+f.right))<2; }')
                        app_source = (ROOT / 'dist/app.js').read_text()
                        sanitizer_source = app_source[app_source.index('function safeURL'):app_source.index('function prose')]
                        assert page.evaluate('''source => {
                            const sanitize = new Function(source + '; return renderedHTML;')();
                            for (const [width, expected] of [["55%", "55%"], ["150%", ""], ["-5%", ""], ["55px", ""]]) {
                                const box=document.createElement("div");
                                box.innerHTML=sanitize('<img src="sources/figure.svg" style="width:'+width+';position:fixed" onerror="alert(1)">');
                                const img=box.querySelector("img");
                                if (img.style.width!==expected || img.style.position || img.hasAttribute("onerror")) return false;
                            }
                            return true;
                        }''', sanitizer_source)
                    assert page.request.get(graphic.get_attribute('src')).status == 200
                    assert page.request.get(graphic.get_attribute('src').replace('.svg', '.pdf')).body().startswith(b'%PDF-')
                    motion_figure.screenshot(path=str(ROOT / f'.build/chapter01-{stem}-desktop.png'))
                page.goto(base + '?volume=v1a#/chapter/v1a-ch01/read')
                page.locator('[id="hyperbolic.invariant-geometry"]').wait_for()
                page.screenshot(path=str(ROOT / '.build/chapter01-read-desktop.png'))
                page.goto(base + '?volume=v1a#/chapter/v1a-app-i/read')
                page.locator('.prose a[href$="/modular.central-covolumes"]').first.click()
                page.wait_for_url('**?volume=v1a#/chapter/v1a-ch01/read/v1a-ch01-s5/modular.central-covolumes')
                page.locator('[id="modular.central-covolumes"]').wait_for()
                page.goto(base + '?volume=v1a#/chapter/v1a-ch01/compare')
                page.locator('.comparison').first.wait_for()
                assert page.locator('.comparison').count() == 8
                assert page.get_by_text('No Lean source has been written for this section.', exact=True).count() == 0
                for section_id in ('v1a-ch01-s1', 'v1a-ch01-s6', 'v1a-ch01-s2', 'v1a-ch01-s7', 'v1a-ch01-s8', 'v1a-ch01-s3', 'v1a-ch01-s4', 'v1a-ch01-s5'):
                    comparison = page.locator('#' + section_id)
                    assert 'in progress' in comparison.locator('.comparison-column').nth(1).inner_text().casefold()
                    row = next(r for r in json.loads((ROOT / 'dist/data/v1a/content.json').read_text())['chapters']['v1a-ch01']['comparisons'] if r['sectionId'] == section_id)
                    assert comparison.locator('pre code').inner_text() == (ROOT / row['leanSource'].removeprefix('sources/')).read_text()
                assert 'Autoformalized' not in page.locator('main').inner_text()
                assert page.locator('.numbered-equation').count() == 44
                assert page.locator('#v1a-ch01-s7 a.equation-reference[href$="/eq%3Apoint-pair-distance"]').inner_text() == '(1.4.7)'
                page.locator('#v1a-ch01-s7 a.equation-reference[href$="/eq%3Apoint-pair-distance"]').click()
                page.wait_for_url('**/read/v1a-ch01-s7/eq%3Apoint-pair-distance')
                page.set_viewport_size({'width': 390, 'height': 844})
                page.goto(base + '?volume=v1a#/chapter/v1a-ch01/read')
                page.locator('#v1a-ch01-s1 .prose').wait_for()
                page.evaluate('async () => { await MathJax.startup.promise; await MathJax.typesetPromise(); }')
                assert page.locator('[data-mjx-error], mjx-merror').count() == 0
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                equation = page.locator('[id="eq:point-pair-distance"]')
                assert equation.locator('.equation-number').inner_text() == '(1.4.7)'
                assert equation.locator('.equation-number').evaluate('el => { const r = el.getBoundingClientRect(); return r.left >= 0 && r.right <= innerWidth; }')
                equation.screenshot(path=str(ROOT / '.build/equation-mobile.png'))
                page.locator('#v1a-ch01-s7 a.equation-reference[href$="/eq%3Apoint-pair-distance"]').click()
                page.wait_for_url('**/read/v1a-ch01-s7/eq%3Apoint-pair-distance')
                assert equation.evaluate('el => { const r = el.getBoundingClientRect(); return r.top >= 0 && r.top < innerHeight; }')
                page.screenshot(path=str(ROOT / '.build/chapter01-read-mobile.png'))
                page.locator('#v1a-ch01-s2 .prose a[href$="/hyperbolic.geodesics-diagram"]').click()
                figure = page.locator('[id="hyperbolic.geodesics-diagram"]')
                figure.locator('img').evaluate('img => img.decode()')
                assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                figure.screenshot(path=str(ROOT / '.build/chapter01-geodesics-mobile.png'))
                for section_id, label, stem in (
                    ('v1a-ch01-s8', 'hyperbolic.elliptic-motion-diagram', 'elliptic-motion'),
                    ('v1a-ch01-s8', 'hyperbolic.parabolic-motion-diagram', 'parabolic-motion'),
                    ('v1a-ch01-s8', 'hyperbolic.translation-dilation-diagram', 'translation-dilation'),
                    ('v1a-ch01-s3', 'modular.domain-diagram', 'fundamental-domain'),
                    ('v1a-ch01-s3', 'modular.tiling-diagram', 'modular-tiling'),
                ):
                    page.locator(f'#{section_id} .prose a[href$="/{label}"]').click()
                    page.wait_for_url(f'**/read/{section_id}/{label}')
                    page.evaluate('async () => { await MathJax.typesetPromise(); }')
                    motion_figure = page.locator(f'[id="{label}"]')
                    motion_figure.locator('img').evaluate('img => img.decode()')
                    if stem == 'fundamental-domain':
                        assert motion_figure.locator('img').evaluate('img => Math.abs(img.getBoundingClientRect().width/img.closest("figure").getBoundingClientRect().width-1)<.01')
                    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
                    motion_figure.screenshot(path=str(ROOT / f'.build/chapter01-{stem}-mobile.png'))

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
