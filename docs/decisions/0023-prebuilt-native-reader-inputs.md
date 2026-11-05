# ADR-0023: Read validated native inputs without nested builds

## Status

Accepted.

## Context

The release pipeline validates the complete identity-bound literate cache before
setting `REASBOOK_LITERATE_PREBUILT=1`. The full-page loader still acquired an
exclusive lock on the project's Lake configuration and invoked both `lake build`
and `lake query` for every page. Independent renderer processes therefore queued
behind one lock and repeated dependency traversal despite having complete inputs.
Increasing their CPU allocation alone did not remove that serialization.

## Decision

When `REASBOOK_LITERATE_PREBUILT` is exactly `1` or `true`, the full-page loader
reads `.lake/build/literate/<logical-module>.json` directly. This is the SDK's
canonical artifact path, including projects whose source directories differ from
their logical module paths. The pipeline must complete SDK cache validation
before enabling this mode. Missing or malformed data fails the render; it must
never trigger an implicit extraction or rebuild.

Interactive loading without the flag retains the original lock/build/query
behavior. Both paths share the existing JSON decoder, highlighted code and native
term metadata. Source, toolchain, attribution and mathematical content are unchanged.

## Validation

A bounded service canary holds an isolated project's configuration lock while
loading real cache data. The unmodified loader reaches the load call and waits;
the corrected loader finishes with both supported flag values and never invokes
a forbidden `elan` stub. Missing and corrupt inputs fail without subprocesses;
interactive mode still invokes its builder.

A complete Rockafellar page using a checksum-pinned 350,116,417-byte native input
also compiled successfully without nested builds. Its canary elapsed time was
26 seconds; the prior full-build log for the same page recorded 2,133 seconds.
These are different execution contexts, not a controlled whole-site speedup
measurement. The complete canary's sampled peak memory was about 2.9 GiB.

Keep live build inputs immutable. Adopt the fix through a new frozen candidate,
retain completed branch sites with their SDK-validated producer provenance, and
resume remaining work only after the superseded writer has released its Pod.

## Pages projection capacity

The full native artifact is retained. The bounded Pages view shares repeated
classic head scripts and styles, including generated navigation exceeding one
MiB. Head scanning stops at its closing tag and has an eight-MiB bound; CSS
relative-resource guards remain separate from JavaScript URL construction.

Native code may drop exact, unstyled inter-text wrappers while preserving every
text character, token and hover/binding attribute. Diagnostic documents and
inert/raw-text content are retained. Existing API pages remain byte-identical.
Duplicate chapter aliases become query/fragment-preserving redirects only when
the complete native HTML is equal after normalizing its own page URL. No distinct
mathematical or proof page is removed. Projection audits record bytes saved per
stage, and the Pages hard limit plus the release planning budget still apply.
