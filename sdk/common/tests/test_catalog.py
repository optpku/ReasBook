from __future__ import annotations

import unittest

from reasbook_sdk_common.catalog import CatalogEntry, catalog_page


class CatalogTests(unittest.TestCase):
    def test_self_contained_styled_catalog_escapes_text_and_keeps_route_order(self):
        page = catalog_page('Books <&>', [('Second <book>', 'two/?x=1&y="2"'), ('First', '../one/')])
        self.assertIn('<style>', page)
        self.assertIn('color-scheme: light', page)
        self.assertIn('--reader-link: #514077', page)
        self.assertNotIn('border-radius:', page)
        self.assertIn('id="main-content"', page)
        self.assertIn('Books &lt;&amp;&gt;', page)
        self.assertIn('Second &lt;book&gt;', page)
        self.assertIn('href="two/?x=1&amp;y=&quot;2&quot;"', page)
        self.assertLess(page.index('two/?'), page.index('../one/'))
        self.assertNotIn('<script', page)
        self.assertNotIn('http-equiv="refresh"', page)

    def test_empty_catalog_is_explicit(self):
        self.assertIn('No project artifacts are published here yet.', catalog_page('Empty', []))

    def test_categories_and_explicit_credit_survive_custom_local_routes(self):
        page = catalog_page('Collection', [
            CatalogEntry('BFGS', '/native/', 'papers/BFGSMinimumQOrder_Liu_2026', 'Native reading pages'),
            CatalogEntry('Beck', '/read/', 'books/FirstOrderMethodsOptimization_Beck_2017'),
            ('Versions', './versions/'),
        ], notice='Local preview <not published>')
        self.assertIn('aria-label="Collection sections"', page)
        self.assertLess(page.index('id="books"'), page.index('id="papers"'))
        self.assertLess(page.index('id="papers"'), page.index('id="resources"'))
        self.assertIn('Shu Miao', page)
        self.assertIn('Imported DFP infrastructure: Zichen Wang', page)
        self.assertIn('Native reading pages', page)
        self.assertIn('Local preview &lt;not published&gt;', page)
        self.assertNotIn('<script', page)
