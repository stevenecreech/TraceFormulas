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
            self.assertNotIn('destination with the same identifier', pdf.with_suffix('.log').read_text())
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

    def figure_fixture(self):
        directory = self.section / 'figures'
        directory.mkdir()
        pdf, svg = directory / 'geometry.pdf', directory / 'geometry.svg'
        # Source-routing fixtures; the real book build checks the actual vector PDF.
        pdf.write_bytes(b'%PDF-figure-fixture')
        svg.write_text('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 10 10"><circle cx="5" cy="5" r="3"/></svg>')
        name = pdf.relative_to(self.root).as_posix()
        (self.section / 'text.tex').write_text(
            r'\begin{figure}[htbp]\includegraphics[width=\linewidth]{' + name +
            r'}\caption{A geometric diagram.}\label{geometry-picture}\end{figure}'
            r'See \hyperref[geometry-picture]{the diagram}.')
        return pdf, svg

    def test_vector_figure_routes_to_svg_preserves_caption_and_exports_both_assets(self):
        pdf, svg = self.figure_fixture()
        content = self.content()
        rendered = content['sections']['v1a-ch00-s1']
        expected = 'sources/' + svg.relative_to(self.root).as_posix()
        self.assertIn('src="' + expected + '"', rendered)
        self.assertIn('<figcaption', rendered)
        self.assertIn('A geometric diagram.', rendered)
        self.assertIn('id="geometry-picture"', rendered)
        self.assertIn('#/chapter/v1a-ch00/read/v1a-ch00-s1/geometry-picture', rendered)
        self.assertEqual(content['comparisons'][0]['book'], rendered)
        build(self.root, self.root / 'dist')
        for path in (pdf, svg):
            self.assertEqual(path.read_bytes(),
                (self.root / 'dist/sources' / path.relative_to(self.root)).read_bytes())

    def test_vector_figure_requires_web_counterpart(self):
        _, svg = self.figure_fixture()
        svg.unlink()
        with self.assertRaisesRegex(TexError, 'requires a paired SVG'):
            self.content()

    def test_vector_figure_rejects_outside_source_tree(self):
        _, svg = self.figure_fixture()
        outside = self.root / 'private.svg'
        outside.write_text('<svg/>')
        svg.unlink()
        svg.symlink_to(outside)
        with self.assertRaisesRegex(TexError, 'requires a paired SVG'):
            self.content()

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

    def test_autoformalized_status_preserves_pending_review_in_exports(self):
        status = 'autoformalized-awaiting-review'
        chapter = json.loads((self.chapter / 'chapter.json').read_text())
        chapter['formal'] = {'status': status, 'declarations': []}
        (self.chapter / 'chapter.json').write_text(json.dumps(chapter))
        section = json.loads((self.section / 'section.json').read_text())
        section['formal']['status'] = status
        (self.section / 'section.json').write_text(json.dumps(section))
        content = self.content()
        self.assertEqual(content['formal']['status'], status)
        self.assertEqual(content['formal']['sources'][0]['status'], status)
        self.assertEqual(content['comparisons'][0]['status'], status)
        # Metadata is a declaration of status, never proof evidence created by
        # the renderer. Even this status must not work without a source file.
        (self.section / 'Formalization.lean').unlink()
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

    def test_math_environment_groups_remain_scoped_without_tex_primitives(self):
        (self.section / 'text.tex').write_text(r'''
An inline column: $v=\begin{smallpmatrix}z\\1\end{smallpmatrix}$.
\begin{equation}\label{grouped-matrix}
\begin{smallpmatrix}a&b\\c&d\end{smallpmatrix}
\end{equation}
Nested groups: $\bgroup\bf a+\bgroup b\egroup\egroup+c$.
Control symbols: $\begin{smallmatrix}a\\bgroup\end{smallmatrix}+\{x\}$.
''')
        content = self.content()
        html = content['sections']['v1a-ch00-s1']
        self.assertIn(r'v={ \left(\begin{smallmatrix}z\\1\end{smallmatrix}\right)}', html)
        self.assertIn(r'{ \left(\begin{smallmatrix}a&amp;b\\c&amp;d\end{smallmatrix}\right)}', html)
        self.assertIn(r'{\bf a+{ b}}+c', html)
        self.assertIn(r'\begin{smallmatrix}a\\bgroup\end{smallmatrix}+\{x\}', html)
        self.assertNotIn(r'\egroup', html)
        self.assertNotIn(r'\bgroup ', html)
        self.assertIn('data-equation-number="0.1.1"', html)
        self.assertEqual(content['comparisons'][0]['book'], html)

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

    def test_equation_numbers_and_forward_links_match_pdf_across_chapters(self):
        (self.chapter / 'intro.tex').write_text(
            r'\begin{equation}\label{eq:intro}0=0\end{equation}')
        (self.section / 'text.tex').write_text(r'''
\begin{proposition}\label{statement}A statement.
\begin{equation}\label{eq:first}\begin{aligned}a&=b\\c&=d\end{aligned}\end{equation}
\end{proposition}
\[x=x\]
\begin{equation*}y=y\end{equation*}
\begin{equation}z=z\label{eq:second}\end{equation}
See \eqref{eq:first}, \eqref{eq:later}, and \eqref{eq:appendix}.
\begin{lemma}\label{after-equations}A later statement.\end{lemma}
''')
        (self.section / 'compare.tex').write_text(r'Compare with \eqref{eq:first}.')
        outline_path = self.root / self.volume['path'] / 'outline.json'
        outline = json.loads(outline_path.read_text())
        directories = {'v1a-ch00': self.chapter}
        for appendix, identifier, prefix, label in (
            (False, 'v1a-ch02', '2.1', 'eq:later'),
            (True, 'v1a-app-b', 'B.1', 'eq:appendix'),
        ):
            record = {'id': identifier, 'title': 'Later material', 'description': '',
                      'sections': [{'id': identifier + '-s1', 'title': 'Formulas'}]}
            record.update({'letter': 'B'} if appendix else {'number': 2, 'division': 'A'})
            outline['appendices' if appendix else 'chapters'].append(record)
            directory = self.root / self.volume['path'] / ('appendices/B' if appendix else 'chapters/Chapter02')
            directories[identifier] = directory
            (directory / 'sections/Section01').mkdir(parents=True)
            (directory / 'chapter.json').write_text('{}')
            (directory / 'intro.tex').write_text('')
            (directory / 'formalization.tex').write_text('')
            (directory / 'sections/Section01/text.tex').write_text(
                r'\begin{equation}\label{' + label + r'}1=1\end{equation}'
                r'See \eqref{eq:first} and \hyperref[eq:second]{the second equation}.')
        outline_path.write_text(json.dumps(outline))
        outline, content, records = compile_book(self.root, self.volume, Renderer(self.root))
        chapter = content['chapters']['v1a-ch00']
        source = chapter['sections']['v1a-ch00-s1']
        self.assertIn('Proposition 0.1.1', source)
        self.assertIn('Lemma 0.1.2', source)
        for label, number in [('eq:first', '0.1.1'), ('eq:second', '0.1.2')]:
            self.assertIn(f'id="{label}" class="numbered-equation" data-equation-number="{number}"', source)
            self.assertIn('class="equation-number">(' + number + ')</span>', source)
        self.assertNotIn(r'\label', source)
        self.assertIn('href="#/chapter/v1a-ch02/read/v1a-ch02-s1/eq%3Alater" class="equation-reference">(2.1.1)</a>', source)
        self.assertIn('>(B.1.1)</a>', source)
        self.assertIn('>(0.1.1)</a>', chapter['comparisons'][0]['notes'])
        self.assertEqual(source, chapter['comparisons'][0]['book'])
        pdf = build_pdf(self.root, 'v1a', print_source(self.root, outline, records, directories))
        aux = pdf.with_suffix('.aux').read_text()
        for label, number in [('eq:intro', '0.0.1'), ('eq:first', '0.1.1'), ('eq:second', '0.1.2'),
                              ('eq:later', '2.1.1'), ('eq:appendix', 'B.1.1'), ('after-equations', '0.1.2')]:
            self.assertIn(r'\newlabel{' + label + '}{{' + number + '}', aux)

    def test_equation_references_reject_missing_non_equation_and_duplicate_targets(self):
        for source in (
            r'See \eqref{absent}.',
            r'\begin{theorem}\label{result}Text.\end{theorem} See \eqref{result}.',
            r'\begin{equation}\label{duplicate}a=b\end{equation}'
            r'\begin{equation}\label{duplicate}c=d\end{equation}',
            r'\begin{equation}\label{duplicate}a=b\end{equation}'
            r'\phantomsection\label{duplicate}Text.',
        ):
            with self.subTest(source=source):
                (self.section / 'text.tex').write_text(source)
                with self.assertRaises(BuildError):
                    self.content()

    def test_unsupported_equation_numbering_fails_instead_of_misnumbering(self):
        for source in (
            r'\begin{equation}a=b\end{equation}',
            r'\begin{equation}\label{one}\label{two}a=b\end{equation}',
            r'\begin{equation}\label{one}a=b\tag{custom}\end{equation}',
            r'\begin{equation}\label{one}a=b\nonumber\end{equation}',
            r'\begin{align}a&=b\label{one}\\c&=d\end{align}',
            r'\[a=b\label{one}\]',
            r'$\eqref{one}$',
        ):
            with self.subTest(source=source):
                (self.section / 'text.tex').write_text(source)
                with self.assertRaises(TexError):
                    self.content()
        path = self.section / 'text.tex'
        path.write_text(r'\begin{equation}\label{one}a=b\end{equation}')
        renderer = Renderer(self.root)
        self.assertIn('class="equation-number">(1.3.1)</span>', renderer.render(path, number_prefix='1.3'))
        self.assertIn('class="equation-number">(B.2.1)</span>', renderer.render(path, number_prefix='B.2'))
        with self.assertRaises(TexError):
            renderer.render(path)

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
