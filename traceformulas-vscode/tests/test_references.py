"""Check real PDF links between separately authored chapter fragments."""
from pathlib import Path
import json
import os
import re
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from build import BuildError, compile_book
from tex import build_pdf, pandoc_path, print_source, Renderer, TexError


class PdfReferenceTests(unittest.TestCase):
    def test_cross_chapter_numbers_and_pdf_destinations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / 'tex', root / 'tex')
            records, directories = [], {}
            for number in (8, 10):
                chapter_id = f'v1a-ch{number:02d}'
                records.append({
                    'id': chapter_id, 'number': number, 'division': 'test',
                    'title': f'Reference chapter {number}',
                    'sections': [{'id': chapter_id + '-s1', 'title': 'Reference section'}],
                })
                chapter = root / 'chapters' / f'Chapter{number:02d}'
                (chapter / 'sections/Section01').mkdir(parents=True)
                (chapter / 'intro.tex').write_text('')
                directories[chapter_id] = chapter
            (directories['v1a-ch08'] / 'sections/Section01/text.tex').write_text(r'''
\begin{theorem}\label{v1a-thm:sample-eight}
The identity $1=1$ holds.
\end{theorem}
\begin{equation}\label{v1a-eq:sample-eight}1=1.\end{equation}
A forward reference: Chapter~\ref{v1a-ch10}, Section~\ref{v1a-ch10-s1}.
''')
            (directories['v1a-ch10'] / 'sections/Section01/text.tex').write_text(r'''
By Theorem~\ref{v1a-thm:sample-eight} in Chapter~\ref{v1a-ch08},
Section~\ref{v1a-ch08-s1}, equation~\eqref{v1a-eq:sample-eight} holds.
''')
            outline = {
                'title': 'Reference test', 'volume': '1A', 'subtitle': 'Test',
                'author': 'Test', 'divisions': [{'id': 'test', 'title': 'Reference tests'}],
            }
            source = print_source(root, outline, records, directories)
            # Expose annotation dictionaries for inspection without a PDF library.
            source = '\\pdfcompresslevel=0\n\\pdfobjcompresslevel=0\n' + source
            pdf = build_pdf(root, 'v1a', source)
            aux = pdf.with_suffix('.aux').read_text()
            for label, number in {
                'v1a-ch08': '8', 'v1a-ch08-s1': '8.1',
                'v1a-ch10': '10', 'v1a-ch10-s1': '10.1',
                'v1a-thm:sample-eight': '8.1.1', 'v1a-eq:sample-eight': '8.1.1',
            }.items():
                self.assertIn('\\newlabel{' + label + '}{{' + number + '}', aux)
            data = pdf.read_bytes()
            for destination in (
                'chapter.8', 'section.8.1', 'chapter.10', 'section.10.1',
                'theorem.8.1.1', 'equation.8.1.1',
            ):
                name = destination.encode('ascii')
                self.assertIn(b'/A << /S /GoTo /D (' + name + b') >>', data)
                self.assertRegex(data, rb'\(' + re.escape(name) + rb'\) \d+ 0 R')

    def test_missing_reference_rejects_pdf(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = (r'\documentclass{article}\begin{document}'
                      r'See \ref{missing-label}.\end{document}')
            with self.assertRaisesRegex(TexError, 'unresolved references'):
                build_pdf(root, 'v1a', source)
            self.assertFalse((root / '.build/v1a/main.pdf').exists())


class NamedHyperlinkTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        shutil.copytree(ROOT / 'tex', self.root / 'tex')
        (self.root / 'scripts').mkdir()
        shutil.copyfile(ROOT / 'scripts/strict-tex.lua', self.root / 'scripts/strict-tex.lua')
        (self.root / 'site.json').write_text('{}')
        previous = os.environ.get('PANDOC')
        os.environ['PANDOC'] = pandoc_path(ROOT)
        self.addCleanup(lambda: os.environ.pop('PANDOC', None) if previous is None
                        else os.environ.__setitem__('PANDOC', previous))
        self.volume = {'id': 'v1a', 'label': '1a', 'path': 'volumes/Volume01/A'}
        self.book = self.root / self.volume['path']
        self.records, self.directories = [], {}
        for number in (8, 10):
            chapter_id = f'v1a-ch{number:02d}'
            self.records.append({
                'id': chapter_id, 'number': number, 'division': 'test',
                'title': f'Chapter {number}', 'description': 'Reference test',
                'sections': [{'id': chapter_id + '-s1', 'title': 'Reference section'}],
            })
            chapter = self.book / 'chapters' / f'Chapter{number:02d}'
            section = chapter / 'sections/Section01'
            section.mkdir(parents=True)
            self.directories[chapter_id] = chapter
            (chapter / 'chapter.json').write_text('{}')
            (chapter / 'intro.tex').write_text('')
            (chapter / 'formalization.tex').write_text('')
            (section / 'text.tex').write_text('A draft section.')
            (section / 'Formalization.lean').write_text('-- Keep <a href="#v1a-ch08"> verbatim.\n')
        outline = {
            'schemaVersion': 1, 'title': 'Reference test', 'volume': '1a',
            'subtitle': 'Test', 'author': 'Test', 'source': 'Test fixture',
            'divisions': [{'id': 'test', 'title': 'Reference tests'}],
            'chapters': self.records, 'appendices': [], 'routes': [],
        }
        (self.book / 'outline.json').write_text(json.dumps(outline))

    def compile(self):
        return compile_book(self.root, self.volume, Renderer(self.root))

    def section(self, number):
        return self.directories[f'v1a-ch{number:02d}'] / 'sections/Section01'

    def test_forward_and_backward_links_share_pdf_and_website_sources(self):
        (self.directories['v1a-ch08'] / 'intro.tex').write_text(
            r'\subsection{Introduction}\label{v1a-intro-eight}Introductory text.')
        (self.section(8) / 'text.tex').write_text(r'''
\subsection{An earlier fact}\label{v1a-fact-eight}
See \hyperref[v1a-ch10]{the later chapter} and
\hyperref[v1a-ch10-s1]{its first section}.
''')
        (self.section(10) / 'text.tex').write_text(r'''
See \hyperref[v1a-ch08]{Chapter 8}, \hyperref[v1a-ch08-s1]{its first section},
\hyperref[v1a-fact-eight]{the earlier fact}, and \hyperref[v1a-intro-eight]{its introduction}.
An external \href{https://example.org/page\#anchor}{link}; $x<y$.
''')
        outline, content, records = self.compile()
        earlier = content['chapters']['v1a-ch08']['sections']['v1a-ch08-s1']
        later = content['chapters']['v1a-ch10']['sections']['v1a-ch10-s1']
        for destination in ('#/chapter/v1a-ch10/read', '#/chapter/v1a-ch10/read/v1a-ch10-s1'):
            self.assertIn('href="' + destination + '"', earlier)
        for destination in (
            '#/chapter/v1a-ch08/read', '#/chapter/v1a-ch08/read/v1a-ch08-s1',
            '#/chapter/v1a-ch08/read/v1a-ch08-s1/v1a-fact-eight',
            '#/chapter/v1a-ch08/read//v1a-intro-eight',
        ):
            self.assertIn('href="' + destination + '"', later)
        self.assertIn('href="https://example.org/page#anchor"', later)
        self.assertIn(r'\(x&lt;y\)', later)
        chapter = content['chapters']['v1a-ch10']
        self.assertEqual(chapter['comparisons'][0]['book'], later)
        expected_lean = (self.section(10) / 'Formalization.lean').read_text()
        self.assertEqual(chapter['comparisons'][0]['lean'], expected_lean)
        self.assertEqual(chapter['formal']['sources'][0]['code'], expected_lean)
        pdf = build_pdf(self.root, 'v1a', print_source(self.root, outline, records, self.directories))
        self.assertTrue(pdf.read_bytes().startswith(b'%PDF-'))

    def test_all_media_prose_routes_links_without_changing_lean(self):
        chapter = self.directories['v1a-ch10']
        link = r'See \hyperref[v1a-ch08-s1]{the earlier section}.'
        (chapter / 'intro.tex').write_text(link)
        (chapter / 'formalization.tex').write_text(link)
        (chapter / 'link.tex').write_text(link)
        (chapter / 'chapter.json').write_text(json.dumps({
            'videos': [{'title': 'Test', 'transcriptFile': 'link.tex'}],
            'exercises': [{'title': 'Test', 'questionFile': 'link.tex',
                           'hintFile': 'link.tex', 'solutionFile': 'link.tex'}],
            'explorations': [{'title': 'Test', 'descriptionFile': 'link.tex'}],
        }))
        (self.section(10) / 'compare.tex').write_text(link)
        result = self.compile()[1]['chapters']['v1a-ch10']
        prose = [result['intro'], result['formal']['summary'], result['videos'][0]['transcript'],
                 result['explorations'][0]['description'], result['comparisons'][0]['notes']]
        prose.extend(result['exercises'][0][key] for key in ('question', 'hint', 'solution'))
        for value in prose:
            self.assertIn('href="#/chapter/v1a-ch08/read/v1a-ch08-s1"', value)
        self.assertEqual(result['formal']['sources'][0]['code'],
                         (self.section(10) / 'Formalization.lean').read_text())

    def test_prose_anchors_keep_links_without_headings_in_both_editions(self):
        (self.directories['v1a-ch08'] / 'intro.tex').write_text(
            r'\phantomsection\label{intro-anchor}Introductory text.')
        (self.section(8) / 'text.tex').write_text(r'''
\phantomsection\label{prose-anchor}

The first paragraph has no heading.
Another sentence.\phantomsection \label{inline-anchor} A target within prose.
''')
        (self.section(10) / 'text.tex').write_text(r'''
See \hyperref[intro-anchor]{the introduction},
\hyperref[prose-anchor]{the earlier paragraph}, and
\hyperref[inline-anchor]{the following sentence}.
''')
        outline, content, records = self.compile()
        chapter = content['chapters']['v1a-ch08']
        earlier = chapter['sections']['v1a-ch08-s1']
        later = content['chapters']['v1a-ch10']['sections']['v1a-ch10-s1']
        self.assertIn('<span id="intro-anchor" class="prose-anchor"></span>Introductory',
                      chapter['intro'])
        self.assertTrue(earlier.startswith('<span id="prose-anchor" class="prose-anchor"></span>'))
        self.assertIn('<span id="inline-anchor" class="prose-anchor"></span>', earlier)
        self.assertNotRegex(earlier, r'<h[1-6]\b')
        self.assertNotRegex(earlier, r'<p><span[^>]+></span></p>')
        self.assertEqual(chapter['comparisons'][0]['book'], earlier)
        for destination in (
            '#/chapter/v1a-ch08/read//intro-anchor',
            '#/chapter/v1a-ch08/read/v1a-ch08-s1/prose-anchor',
            '#/chapter/v1a-ch08/read/v1a-ch08-s1/inline-anchor',
        ):
            self.assertIn('href="' + destination + '"', later)

        source = print_source(self.root, outline, records, self.directories)
        source = '\\pdfcompresslevel=0\n\\pdfobjcompresslevel=0\n' + source
        pdf = build_pdf(self.root, 'v1a', source)
        aux, data = pdf.with_suffix('.aux').read_text(), pdf.read_bytes()
        destinations = []
        for label in ('intro-anchor', 'prose-anchor', 'inline-anchor'):
            match = re.search(r'\\newlabel\{' + label + r'\}\{\{[^\n]*?\}\{(section\*\.\d+)\}', aux)
            self.assertIsNotNone(match, aux)
            name = match.group(1).encode('ascii')
            destinations.append(name)
            self.assertIn(b'/A << /S /GoTo /D (' + name + b') >>', data)
            self.assertRegex(data, rb'\(' + re.escape(name) + rb'\) \d+ 0 R')
        self.assertEqual(len(set(destinations)), 3)

    def test_prose_anchors_do_not_accept_unpaired_or_theorem_labels(self):
        for source in (
            r'\label{unpaired}Prose.',
            r'\phantomsection Prose.',
            r'\phantomsection\unsupportedcommand{content}\label{target}Prose.',
            r'\begin{theorem}Statement.\phantomsection\label{late}More.\end{theorem}',
        ):
            with self.subTest(source=source):
                (self.section(8) / 'text.tex').write_text(source)
                with self.assertRaises(TexError):
                    self.compile()

    def test_unknown_target_fails_with_source_location(self):
        (self.section(10) / 'text.tex').write_text(r'See \hyperref[missing-label]{the missing result}.')
        with self.assertRaisesRegex(BuildError, 'v1a-ch10.*unknown manuscript hyperlink target.*missing-label'):
            self.compile()

    def test_duplicate_headings_only_fail_when_referenced(self):
        for number in (8, 10):
            (self.section(number) / 'text.tex').write_text(r'\subsection{Repeated heading}Some text.')
        self.compile()
        (self.section(10) / 'compare.tex').write_text(r'See \hyperref[repeated-heading]{the heading}.')
        with self.assertRaisesRegex(BuildError, 'ambiguous manuscript hyperlink target.*repeated-heading'):
            self.compile()


if __name__ == '__main__':
    unittest.main()
