# Code authorship and provenance

Code authorship is distinct from the paper's bibliographic authors.

The BFGS project contributor is Chenyi Li, as recorded in the project
[README](README.md). Its imported DFP development comes from
[`imathwy/DFP_wolfe_local` at `e308927f5b7930bdd002f0c0e42b9d112ad821cb`](https://github.com/imathwy/DFP_wolfe_local/tree/e308927f5b7930bdd002f0c0e42b9d112ad821cb).
The [upstream README](https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md)
explicitly credits Zichen Wang as its formalization author.

The 869 Lean files inside this project directory are classified by their paths
and complete bodies, after excluding only the opening ordinary file header:

| Source category | Files | Header attribution |
| --- | ---: | --- |
| Body identical to the pinned upstream file | 819 | Zichen Wang; pinned upstream README and file URL |
| Upstream file adapted locally | 4 | Zichen Wang plus Chenyi Li; upstream source and explicitly project-level local contributor credit |
| No corresponding file in the pinned upstream tree | 46 | Confirmed BFGS project contributor roster, cited to the project README |

The adapted paths are:

- `ReasLib/Analysis/Calculus/LocalInvariantGraph/ExplicitContraction/MetricScalarTopSectionAdapter.lean`
- `ReasLib/Analysis/Calculus/LocalInvariantGraph/ExplicitContraction/MetricTopSectionCertificateAdapter.lean`
- `ReasLib/Geometry/Euclidean/Plane/Rotation.lean`
- `ReasLib/Optimization/LineSearch.lean`

The local credit is a maintainer-confirmed project-level fallback, not an
assertion that a separate per-file modification-author record was available.
The 46 BFGS-only files include new infrastructure and wrapper modules as well
as the paper-facing development. Their absence from this particular upstream
snapshot does not establish that no other provenance exists.

This attribution repair changes only file-header comments. It does not change
any mathematical declaration or proof, or claim a new full Lean build. The
third-party license remains recorded in [the notices](THIRD_PARTY_NOTICES.md)
and `LICENSES/DFP_wolfe_local-APACHE-2.0.txt`.
