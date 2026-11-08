"""Regression tests for the LaTeX/Lean source pipeline (requires Pandoc)."""
from pathlib import Path
import json
import os
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from build import BuildError, build, catalog, compile_book
from tex import Renderer, TexError, build_pdf, pandoc_path, print_source
from preview_tex import preview


class SourcePipelineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pandoc = pandoc_path(ROOT)

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.previous_pandoc = os.environ.get('PANDOC')
        os.environ['PANDOC'] = self.pandoc
        self.addCleanup(self.restore_pandoc)
        shutil.copytree(ROOT / 'tex', self.root / 'tex')
        (self.root / 'scripts').mkdir()
        shutil.copyfile(ROOT / 'scripts/strict-tex.lua', self.root / 'scripts/strict-tex.lua')
        (self.root / 'web').mkdir()
        (self.root / 'web/index.html').write_text('<!doctype html><title>Test</title>')
        # Keep the fixture independent of live chapter prose and its cross-chapter
        # links: this miniature book intentionally contains only Chapter 0.
        (self.root / 'site.json').write_text(json.dumps({
            'features': {'exercises': False, 'explore': False},
            'repositoryUrl': '',
        }))
        series = {
            'schemaVersion': 1,
            'title': 'Test Series',
            'defaultVolume': 'v1a',
            'volumes': [
                {
                    'id': 'v1' + part,
                    'number': 1,
                    'part': part,
                    'label': '1' + part,
                    'topic': 'Test topic',
                    'perspective': 'Test perspective',
                    'description': 'Test volume',
                    'path': 'volumes/Volume01/' + part.upper(),
                    'status': 'draft' if part == 'a' else 'planned',
                }
                for part in ('a', 'b')
            ],
        }
        (self.root / 'series.json').write_text(json.dumps(series))
        self.volume = series['volumes'][0]
        sections = [
            {'id': f'v1a-ch00-s{index}', 'title': f'Test section {index}'}
            for index in range(1, 6)
        ]
        for entry in series['volumes']:
            (self.root / entry['path']).mkdir(parents=True)
            outline = {
                'schemaVersion': 1,
                'title': 'Test Book',
                'subtitle': 'Source pipeline fixture',
                'volume': entry['label'],
                'author': 'Test Author',
                'source': 'Self-contained test fixture',
                'divisions': [],
                'chapters': [],
                'appendices': [],
                'routes': [],
            }
            if entry['id'] == 'v1a':
                outline['divisions'] = [{'id': 'A', 'title': 'Test Division'}]
                outline['chapters'] = [{
                    'id': 'v1a-ch00',
                    'number': 0,
                    'title': 'Test Chapter',
                    'description': 'A chapter with one populated section.',
                    'division': 'A',
                    'sections': sections,
                }]
            (self.root / entry['path'] / 'outline.json').write_text(json.dumps(outline))
        self.chapter = self.root / self.volume['path'] / 'chapters/Chapter00'
        self.chapter.mkdir(parents=True)
        (self.chapter / 'chapter.json').write_text('{}')
        (self.chapter / 'intro.tex').write_text('A self-contained test chapter.\n')
        (self.chapter / 'formalization.tex').write_text('')
        for index in range(1, len(sections) + 1):
            directory = self.chapter / 'sections' / f'Section{index:02d}'
            directory.mkdir(parents=True)
            (directory / 'text.tex').write_text('')
        self.section = self.chapter / 'sections/Section01'
        (self.section / 'text.tex').write_text('Fixture prose: $a=a$.\n')
        (self.section / 'Formalization.lean').write_text('-- A fixture, not a checked proof.\n')
        (self.section / 'compare.tex').write_text('Correspondence awaits review.\n')
        (self.section / 'lecture.tex').write_text('A fixture lecture transcript.\n')
        (self.section / 'section.json').write_text(json.dumps({
            'formal': {'status': 'not-started', 'declarations': []},
            'videos': [{
                'title': 'Fixture lecture',
                'kind': 'proof',
                'url': '',
                'transcriptFile': 'lecture.tex',
            }],
        }))

    def restore_pandoc(self):
        if self.previous_pandoc is None:
            os.environ.pop('PANDOC', None)
        else:
            os.environ['PANDOC'] = self.previous_pandoc

    def content(self):
        return compile_book(self.root, self.volume, Renderer(self.root))[1]['chapters']['v1a-ch00']

    def test_manuscript_preview_resolves_other_sections_and_preserves_numbering(self):
        (self.section / 'text.tex').write_text(
            r'\begin{theorem}\label{preview-result}The identity $1=1$ holds.\end{theorem}')
        selected = self.chapter / 'sections/Section02/text.tex'
        selected.write_text(r'See \hyperref[preview-result]{the earlier theorem}.')
        with patch('preview_tex.ROOT', self.root):
            pdf = preview(selected)
            self.assertEqual(pdf, self.root / '.build/v1a/main.pdf')
            self.assertIn(r'\newlabel{preview-result}{{0.1.1}', pdf.with_suffix('.aux').read_text())
            self.assertNotIn('There were undefined references', pdf.with_suffix('.log').read_text())
            self.assertEqual(pdf.read_bytes(), (self.root / 'dist/pdf/v1a.pdf').read_bytes())
            self.assertFalse((self.root / '.build/previews').exists())
            complete_pdf = pdf.read_bytes()
            selected.write_text(r'See \hyperref[missing-result]{a genuinely missing theorem}.')
            with self.assertRaises(BuildError):
                preview(selected)
            self.assertEqual(complete_pdf, pdf.read_bytes())

    def test_chapter_lecture_preview_is_separate_from_manuscript(self):
        lecture = self.chapter / 'lecture.tex'
        lecture.write_text(r'\phantomsection\label{lecture-only}A separate script: $1=1$.')
        # A manuscript error must not prevent a self-contained script preview.
        (self.section / 'text.tex').write_text(r'\undefinedManuscriptCommand')
        with patch('preview_tex.ROOT', self.root):
            pdf = preview(lecture)
        expected = self.root / '.build/previews/Volume01/A/chapters/Chapter00/lecture/preview.pdf'
        self.assertEqual(pdf, expected)
        self.assertTrue(pdf.read_bytes().startswith(b'%PDF-'))
        self.assertIn(r'\newlabel{lecture-only}', pdf.with_suffix('.aux').read_text())
        self.assertFalse((self.root / '.build/v1a/main.pdf').exists())

    def test_compare_reads_both_sources_and_tracks_edits(self):
        first = self.content()
        self.assertEqual(first['sections']['v1a-ch00-s1'], first['comparisons'][0]['book'])
        self.assertEqual(first['comparisons'][0]['lean'], (self.section / 'Formalization.lean').read_text())
        (self.section / 'text.tex').write_text(r'Changed prose: $a+b=b+a$.')
        lean = '-- a source edit, not a proof\n'
        (self.section / 'Formalization.lean').write_text(lean)
        second = self.content()
        self.assertIn('Changed prose', second['comparisons'][0]['book'])
        self.assertEqual(second['comparisons'][0]['lean'], lean)
        self.assertEqual(second['formal']['sources'][0]['status'], 'not-started')

    def test_missing_lean_is_explicit_and_not_a_completed_proof(self):
        (self.section / 'Formalization.lean').unlink()
        content = self.content()
        self.assertEqual(content['comparisons'][0]['lean'], '')
        self.assertEqual(content['comparisons'][0]['leanSource'], '')
        self.assertEqual(content['formal']['sources'], [])
        metadata = json.loads((self.section / 'section.json').read_text())
        metadata['formal']['status'] = 'in-progress'
        (self.section / 'section.json').write_text(json.dumps(metadata))
        with self.assertRaisesRegex(BuildError, 'requires Formalization.lean'):
            self.content()

    def test_path_escape_in_media_is_rejected(self):
        data = json.loads((self.section / 'section.json').read_text())
        data['videos'][0]['transcriptFile'] = '../../../../../../../../site.json'
        (self.section / 'section.json').write_text(json.dumps(data))
        with self.assertRaisesRegex(BuildError, 'stay inside'):
            self.content()

    def test_unsupported_tex_fails_instead_of_losing_content(self):
        (self.section / 'text.tex').write_text(r'Before \unsupportedcommand{essential mathematics} after.')
        with self.assertRaises(TexError):
            self.content()

    def test_supported_math_macros_and_proof_environment(self):
        (self.section / 'text.tex').write_text(r'''
\begin{proposition}[A test]
For $z\in\HH$, we have $z=z$.
\end{proposition}
\begin{proof}Reflexivity.\end{proof}
\begin{itemize}\item A finite example.\end{itemize}
''')
        html = self.content()['sections']['v1a-ch00-s1']
        self.assertIn('Proposition', html)
        self.assertIn('Reflexivity', html)
        self.assertIn('math inline', html)
        self.assertIn(r'\mathbb{H}', html)
        self.assertIn('<li>', html)

    def test_ams_environments_share_pdf_numbers_labels_and_styles(self):
        environments = [
            ('definition', 'Definition'), ('proposition', 'Proposition'),
            ('lemma', 'Lemma'), ('corollary', 'Corollary'), ('theorem', 'Theorem'),
            ('example', 'Example'), ('remark', 'Remark'), ('defn', 'Definition'),
            ('prop', 'Proposition'), ('lem', 'Lemma'), ('cor', 'Corollary'),
            ('thm', 'Theorem'), ('rem', 'Remark'),
        ]
        source = '\n'.join(
            r'\begin{' + name + '}[A named result]' + r'\label{result-' + name + '}'
            + 'Body of ' + name + '.' + r'\end{' + name + '}'
            for name, _ in environments
        )
        source += r'\begin{proof}A complete argument.\end{proof}'
        (self.section / 'text.tex').write_text(source)
        (self.chapter / 'intro.tex').write_text(
            r'\begin{remark}\label{intro-remark}An introductory comment.\end{remark}')
        second = self.chapter / 'sections/Section02/text.tex'
        second.write_text(r'''
\begin{proposition}\label{next-section}Another result.\end{proposition}
See \hyperref[result-proposition]{the earlier proposition}.
''')
        outline, content, records = compile_book(self.root, self.volume, Renderer(self.root))
        chapter = content['chapters']['v1a-ch00']
        html = chapter['sections']['v1a-ch00-s1']
        for index, (name, title) in enumerate(environments, 1):
            self.assertIn('id="result-' + name + '"', html)
            self.assertIn(f'{title} 0.1.{index}', html)
        self.assertIn('class="definition theorem-block"', html)
        self.assertIn('  Body of definition.', html)
        self.assertIn('<em>Body of proposition.</em>', html)
        self.assertIn('class="proof"', html)
        self.assertIn('A complete argument.', html)
        self.assertIn('◻', html)
        self.assertIn('Remark 0.0.1', chapter['intro'])
        self.assertIn('Proposition 0.2.1', chapter['sections']['v1a-ch00-s2'])
        self.assertIn('href="#/chapter/v1a-ch00/read/v1a-ch00-s1/result-proposition"',
                      chapter['sections']['v1a-ch00-s2'])
        self.assertEqual(chapter['comparisons'][0]['book'], html)

        pdf = build_pdf(self.root, 'v1a', print_source(
            self.root, outline, records, {'v1a-ch00': self.chapter}))
        aux = pdf.with_suffix('.aux').read_text()
        for index, (name, _) in enumerate(environments, 1):
            self.assertIn(r'\newlabel{result-' + name + '}{{0.1.' + str(index) + '}', aux)
        self.assertIn(r'\newlabel{intro-remark}{{0.0.1}', aux)
        self.assertIn(r'\newlabel{next-section}{{0.2.1}', aux)

    def test_renderer_counter_context_is_not_reused_from_cache(self):
        source = self.section / 'text.tex'
        source.write_text(r'\begin{theorem}\label{sample}A statement.\end{theorem}')
        renderer = Renderer(self.root)
        self.assertIn('Theorem 0.1.1', renderer.render(source, number_prefix='0.1'))
        self.assertIn('Theorem B.2.1', renderer.render(source, number_prefix='B.2'))
        self.assertIn('Theorem 1', renderer.render(source))

    def test_unhandled_labels_and_tex_still_fail_inside_theorem_documents(self):
        for source in (
            r'\label{unscoped}An unattached label.',
            r'\begin{theorem}\label{one}\label{two}A statement.\end{theorem}',
            r'\begin{theorem}\[1=1\]\label{late}A statement.\end{theorem}',
            r'\begin{theorem}\label{one}\unsupportedcommand{essential text}\end{theorem}',
            r'\begin{theorem}\label{one}A statement.\end{theorem} See \ref{one}.',
        ):
            with self.subTest(source=source):
                (self.section / 'text.tex').write_text(source)
                with self.assertRaises(TexError):
                    self.content()

    def test_all_volumes_and_downloads_are_built_under_a_subdirectory(self):
        output = self.root / 'preview/nested/site'
        result = build(self.root, output)
        self.assertEqual(result['volumes'], 2)
        data = json.loads((output / 'data/series.json').read_text())
        self.assertEqual(data['volumes'][1]['status'], 'planned')
        self.assertEqual(json.loads((output / 'data/v1b/content.json').read_text())['chapters'], {})
        content = json.loads((output / 'data/v1a/content.json').read_text())['chapters']['v1a-ch00']
        row = content['comparisons'][0]
        self.assertEqual((output / row['leanSource']).read_text(), row['lean'])
        self.assertEqual((output / row['texSource']).read_text(), (self.section / 'text.tex').read_text())

    def test_check_does_not_write_and_source_output_is_rejected(self):
        output = self.root / 'preview'
        build(self.root, output, check_only=True)
        self.assertFalse(output.exists())
        with self.assertRaisesRegex(BuildError, 'separate'):
            build(self.root, self.root / 'volumes')

    def test_duplicate_volume_and_unknown_selection_fail(self):
        data = json.loads((self.root / 'series.json').read_text())
        data['volumes'].append(data['volumes'][0])
        (self.root / 'series.json').write_text(json.dumps(data))
        with self.assertRaisesRegex(BuildError, 'duplicate'):
            catalog(self.root)

    def test_print_uses_manuscript_only(self):
        outline, _, records = compile_book(self.root, self.volume, Renderer(self.root))
        source = print_source(self.root, outline, records, {'v1a-ch00': self.chapter})
        self.assertIn('sections/Section01/text.tex', source)
        self.assertNotIn('Formalization.lean', source)
        self.assertNotIn('lecture.tex', source)
        self.assertNotIn('compare.tex', source)
        self.assertIn(r'\setcounter{chapter}{-1}', source)


if __name__ == '__main__':
    unittest.main()
