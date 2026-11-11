from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from reasbook_deploy_sdk.release.artifacts import PagesSiteProjector

class ChapterAliasTests(unittest.TestCase):
    def test_flat_chapter_alias_keeps_query_fragment_and_distinct_content(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            canonical = root / 'versions/v4.30.0/books/demo/chapters/chap02/index.html'
            alias = root / 'versions/v4.30.0/demo/chap02/index.html'
            for path in (canonical, alias):
                path.parent.mkdir(parents=True)
            modern = '/ReasBook/versions/v4.30.0/books/demo/chapters/chap02/'
            old = '/ReasBook/versions/v4.30.0/demo/chap02/'
            page = '<script>window.__versoSiteRoot="/ReasBook/";</script><a href="' + modern + '#item">x</a>'
            canonical.write_text(page)
            alias.write_text(page.replace(modern, old))
            report = PagesSiteProjector()._deduplicate_chapter_aliases(SimpleNamespace(base_path='/ReasBook/'), root)
            self.assertEqual(report['aliases'], 1)
            self.assertIn('location.search+location.hash', alias.read_text())
            self.assertIn(modern, alias.read_text())
            self.assertEqual(canonical.read_text(), page)

    def test_only_complete_equivalent_native_pages_become_redirects(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            book=root/'versions/v4.26.0/books/demo'
            canonical=book/'chapters/chap01/index.html'
            alias=book/'chap01/index.html'
            canonical.parent.mkdir(parents=True)
            alias.parent.mkdir(parents=True)
            modern='/ReasBook/versions/v4.26.0/books/demo/chapters/chap01/'
            legacy='/ReasBook/versions/v4.26.0/books/demo/chap01/'
            page='<script>window.__versoSiteRoot="/ReasBook/";</script><main><a href="'+modern+'#item">Jump</a><code data-verso-hover="8">theorem t : True</code></main>'
            canonical.write_text(page)
            alias.write_text(page.replace(modern,legacy))
            PagesSiteProjector()._deduplicate_chapter_aliases(SimpleNamespace(base_path='/ReasBook/'),root)
            text=alias.read_text()
            self.assertIn(modern,text)
            self.assertIn('location.search+location.hash',text)
            self.assertEqual(canonical.read_text(),page)
            distinct=page.replace('theorem t : True','theorem other : False').replace(modern,legacy)
            alias.write_text(distinct)
            PagesSiteProjector()._deduplicate_chapter_aliases(SimpleNamespace(base_path='/ReasBook/'),root)
            self.assertEqual(alias.read_text(),distinct)
