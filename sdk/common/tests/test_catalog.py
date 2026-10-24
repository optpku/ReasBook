from __future__ import annotations

import unittest

from reasbook_sdk_common.catalog import catalog_page


class CatalogTests(unittest.TestCase):
    def test_self_contained_styled_catalog_escapes_text_and_keeps_route_order(self):
        page = catalog_page('Books <&>', [('Second <book>', 'two/?x=1&y="2"'), ('First', '../one/')])
        self.assertIn('<style>', page)
        self.assertIn('prefers-color-scheme: dark', page)
        self.assertIn('id="main-content"', page)
        self.assertIn('Books &lt;&amp;&gt;', page)
        self.assertIn('Second &lt;book&gt;', page)
        self.assertIn('href="two/?x=1&amp;y=&quot;2&quot;"', page)
        self.assertLess(page.index('two/?'), page.index('../one/'))
        self.assertNotIn('<script', page)
        self.assertNotIn('http-equiv="refresh"', page)

    def test_empty_catalog_is_explicit(self):
        self.assertIn('No project artifacts are published here yet.', catalog_page('Empty', []))
