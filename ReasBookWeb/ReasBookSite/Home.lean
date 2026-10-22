/-
Authors: Wanli Ma
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoBlog
open Verso Genre Blog

#doc (Page) "ReasBook" =>

This site publishes literate pages generated from the `ReasBook` Lean project.

Use the top navigation to browse:

- `Home`: project overview (this page)
- `Documentation`: Lean API docs
- each book/paper `Home` page: overview and links into that specific source

When new books, papers, or sections are added, regenerate `ReasBookSite/Sections.lean`
and `ReasBookSite/RouteTable.lean` with:

`python3 scripts/gen_sections.py`
