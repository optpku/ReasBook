---
version: 1
slug: "reasbookweb"
primary_target: "ReasBookWeb"
related_targets: ["sdk/common/src/reasbook_sdk_common/catalog.py"]
---

# Static mathematical reader

Mode: Read. Scope: production catalog and Verso home/chapter/statement shell;
local preview only. Existing doc-gen mathematical content remains intact.
The user delegated selection to the agent based on ReasBook's description.

## Direction contract

THESIS: A mathematical reference book with directly addressable statements,
not a promotional title page or a grid of developer cards.

OWN-WORLD: White pages, pale ink-gray navigation, charcoal prose and restrained
violet-ink links. Serif reading titles and prose; clear sans navigation; genuine
monospace Lean. Spacing and numbered headings organize continuous text.

STORY: Identify the book, choose a chapter, read its numbered statements, then
inspect documentation or attributed source. No new intermediate screens.

FIRST VIEWPORT: An 18rem contents rail beside a left-aligned, bounded reading
column. The home has a moderate book title and compact chapter list; secondary
resource links are quiet. A chapter starts with its chapter title, a compact
book-home link and excerpt note, then mathematics, without repeating a giant
book title. Active anchors align text with the open sidebar item.

FORM: Grounded candidate 1, mathematical reference handbook / marginal locators;
chosen under user-delegated judgment because README prioritizes original
reference structure and machine-checkable statements. seed:633eaa88189d9421.

FINISH: unreviewed and undocumented is unfinished; this build ends with the finish review, the verdict, DESIGN.md, and every shipping raster carrying its provenance

## Implementation plan

Core colors: surface #ffffff, navigation #f5f5f8, ink #25232d,
muted #68636f, link #514077, rule #ddd9e3. No decorative imagery.
Georgia / Times / DejaVu Serif for reading; system sans for navigation and
controls; explicit DejaVu Sans Mono fallback for Lean identifiers.

```
Home:    [book + chapter rail]  [book title                    ]
                                [Documentation   Lean source ]
                                [Chapters                     ]
                                [Chapter 01      Chapter 02   ]
Chapter: [book + chapter rail]  [Chapter 01                    ]
         [  numbered items  ]  [book home / source / scope note]
                                [Definition 1.1   small links ]
                                [prose, then Lean excerpt     ]
```

Brief check: serif plus whitespace alone would repeat the previous title-page
design. The selected change instead unifies all page types, removes statement
card shells, makes mathematical headings navigable, and keeps the original
chapter/item numbering as the signature structure. No invented chapter titles,
author lists, dependencies or performance claims. Home does not list items.

Verification: 320–1440px, 200% text, long titles/structures, no-JS content,
skip link and keyboard focus, mobile contents, exact anchors/back-forward,
main/fallback navigation and direct documentation. Preserve honest availability
and attribution. No source/math extraction changes.
