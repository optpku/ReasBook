# Integer Programming (Conforti, Cornuejols, Zambelli, 2014)

**Lean 4.30.0 review candidate.** Book: Integer Programming, Michele Conforti,
Gérard Cornuéjols, Giacomo Zambelli, Springer, Graduate Texts in Mathematics 271,
2014; ISBN 978-3-319-11007-3. Edition unknown. Bibliography was checked against the supplied book PDF (title and
imprint pages 1, 4 and 5); bibliographic authors are distinct from Lean code authors.
The printed book bears © Springer International Publishing Switzerland 2014;
that textbook notice is not the copyright notice for the Lean implementation.

## Source and toolchain

- [Complete import root](Book.lean)
- [Chapter source](Integer/Chapters/)
- [Validation evidence and pending checks](VALIDATION.md)
- [Metadata](book.yml)
- Exact toolchain: leanprover/lean4:v4.30.0; mathlib v4.30.0
- Original mathlib commit: c5ea00351c28e24afc9f0f84379aa41082b1188f

Source is the terminal M2F Job 2907 snapshot, archive SHA256
f3012f19df9a9ec24b75703566016068893bfe542edc8d839b765c3a23b948ee.
Internal import paths are prefixed with IntegerProgramming_Conforti_2014 for the branch's Books layout.
Proof bodies, theorem names and mathematical statements are preserved; 14 pre-existing trailing-whitespace lines were trimmed.
Book.lean imports all 1064 chapter modules; the library uses srcDir := "Books".

## Contributors and attribution

### Confirmed formalization attribution

- **Ziyu Wang** — project formalization lead, explicitly confirmed by the submitter
  on 2026-11-04. The 1010 first-party chapter/support/integration modules use this
  confirmed project-level attribution; it identifies the formalization lead and is
  not a claim of individual authorship of every line. A GitHub account and personal
  copyright ownership were not supplied and have not been inferred.
- **Cameron Freer** ([@cameronfreer](https://github.com/cameronfreer)) — original author
  and copyright holder named in the 55 received DPRM/Hilbert10 modules. Their existing
  copyright, Apache 2.0 and Authors notices are preserved, with the notices moved
  before the module command. These files keep their upstream author; Ziyu Wang's
  project role does not replace the upstream attribution.
- **TropicalFatFish** — [submission/integration account](https://github.com/TropicalFatFish),
  kept separate from the named human formalization lead.

The project-level attribution above is the submitter-confirmed scope for this candidate.
It is documented here as evidence for the individual opening headers, following the
existing Analysis II and Nesterov project-attribution format on ReasBook v4.30.0.
Historical contributor records in the v4.26.0 source and main catalog remain intact;
they are not silently assigned to these candidate files.

All 1065 Lean files now have an opening Authors: and Apache 2.0 notice before module/imports.
The official current-main author-header checker passes: 1065 files checked, 0 invalid.
Run python3 scripts/sync_lean_headers.py --check from this project directory to check
that re-generated source retains the same headers; omit --check to restore them.
First-party legacy files use Authors plus license and the cited project-level attribution.
No new individual Copyright holder is invented where ownership was not supplied.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for the original DPRM notices,
their exact file scope and the original textbook's distinct bibliographic copyright.

## Coverage

All received source modules under Chap01 through Chap10 are included. No module
from that tree is intentionally omitted. An independent comparison with every
statement/exercise of the printed textbook has not been performed; coverage of
unrepresented textbook material is unknown. Documentation, Verso and theorem-map
publication for this candidate is not claimed.

## Statistics and proof status

- Source command declarations: 17,080; theorem/lemma/example: 13,030; other: 4,050.
- Lean source: 1065 files, 469,843 lines (1064 chapter modules plus Book.lean).
- Counts are commands beginning on a line after masking nested comments/strings,
  not expanded kernel declarations or generated structure fields/constructors.
- Source code tokens: sorry=0, admit=0, direct sorryAx=0, axiom=0, constant=0.
  Raw words in comments are excluded.
- Original unfinished targets: 5/5 have proof bodies; all 3 edited files passed
  remote Lean compilation and were published before import-path relocation.
- Explicit final axiom outputs cover **2/5 original targets**. Three outputs are
  missing, as listed in VALIDATION.md; this is not a claim that those targets failed.
- Full-book kernel proof completion is not established; metadata proof_completion
  is null. The relocated Book.lean root has not been compiled. Original default
  roots imported only Mathlib and covered no chapters.

## Validation

See VALIDATION.md for remote compile/axiom evidence and integration checks.
Metadata/schema, static import closure and placeholder checks are performed locally.
No new proof task or local proof-search pipeline is started by this contribution.
