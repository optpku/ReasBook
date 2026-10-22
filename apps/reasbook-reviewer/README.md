# ReasBook Reviewer

The reading and review application shipped with ReasBook. Readers switch between
books and papers, inspect Lean source, Docs, Verso and theorem dependencies, and
publish a review comment after signing in. Source and generated evidence come
from the existing ReasBook SDK cache; starting the web server never builds Lean.

[Public reading and review website](https://reasbook.reaslab.io/) ·
[Open the hosted Reviewer](https://reasbook.reaslab.io/review/) ·
[Browse static Docs and Verso](https://reasbook.reaslab.io/artifacts/)

To review a formalization online, choose a textbook or paper and select a
declaration. Switch between Source, Docs, Verso and Graph to inspect the Lean
code, available documentation and theorem dependencies. Reading does not require
sign-in; posting a comment on the selected declaration requires ReasLab sign-in.
Available resources vary by project and declaration, as shown by the evidence
status indicators.

### Selecting a completed single-book Verso

An operator may independently select a successful project-finalizer's Verso in
`<reviewer-data>/verso-selections.json`, without replacing Source, Docs or Graph:

```json
{"schemaVersion": 1, "books": {"<slug>": {
  "releaseId": "<explicit-producer-release-id>",
  "resultSha256": "<SHA-256 of the original project result.json>"
}}}
```

Before atomically installing this record, verify the producer's result identity,
site tree digest with the SiFlow finalizer's `site_tree_digest`, and real content,
anchors and browser navigation. Select only approved producers, never by mtime.
The reader checks the pinned result and matching project/branch/source commit;
invalid selections retain the baseline. The API reports the independent producer
under `resources.verso.releaseId`; the top-level release still identifies the
baseline Source/Docs/Graph. This does not publish a full release or GitHub Pages.
Restart the reader after selection changes because resolvers cache their result.
To roll back, remove the book entry and restart, keeping the original artifacts
and review database intact. See [ADR 0018](../../docs/decisions/0018-independent-verso-selection.md).

## Reading controls

- The Graph opens in a natural-layout, three-layer neighborhood. Layers count
  dependency edges upstream and downstream from the selected declaration; choosing
  Full graph explicitly lays out the whole matching graph and disables the layer limit.
  Stmt / Proof filters nodes and edges before counting depth or running layout.
  Stmt edges retains the union of statement and proof/body nodes within the chosen
  depth, but draws only statement edges between them, including nodes without any
  visible edge. It replaces All; old saved All selections migrate to Stmt edges.
  Proof and Stmt edges share a layout computed from their bounded statement/proof
  union, in both Natural and Layered modes. Switching between them keeps common
  nodes, zoom and pan fixed; only visibility changes. Proof still hides nodes
  outside its proof-only depth, while Stmt edges retains the union nodes.
  Full graph shows all relationships matching
  that filter, while the selected node remains visible even if it has no matching
  links. The current statement label is the leftmost scope-row heading; node captions
  remain visible. The title, scope, layers and zoom controls share one horizontally
  scrollable row on narrow panes. These are display filters, not new
  dependency data.
  A bottom Zoom slider scales the graph from 3.5% to 500% without changing layout
  or dependencies. Its percentage stays synchronized with + / −, Fit and wheel
  zoom; the focused slider also supports arrow keys and Home / End.
  Safely parsed curated maps use the same controls, retaining their curated
  provenance; their original presentation remains available at
  `/api/books/<slug>/evidence/graph/original/index.html` below the deployment prefix.
- Catalog filters distinguish resource type, index availability and mathematical
  subject. A resource may belong to more than one subject; the curated mapping
  lives beside the catalog UI and unknown resources remain discoverable.
- Evidence (Graph / Source / Docs / Verso) stays open; Catalog, Queue and Review
  can still collapse. Pane widths remain adjustable on desktop.
  Index, resource availability and review counts sit directly below the evidence
  tabs, outside the scrolling content. Status chips wrap to fit the pane and remain
  visible when the queue is collapsed.
- Natural-language comments retain their original text through View source / Copy
  source. Rendering joins soft source-line wraps, respects paragraph breaks, and
  converts backtick-delimited mathematical notation mechanically: grouped powers
  and subscripts, `infty`, Unicode number sets/scripts, comparisons and sums.
  Existing TeX grouping is preserved. Lean expressions containing constructs such
  as `fun`, `by`, or `:=`, and fenced blocks, remain escaped code. This is a display
  normalizer, not a Lean parser or a mathematical rewrite of the statement.

Frontend regression checks (Node.js, no packages required):

```bash
node apps/reasbook-reviewer/tests/statement_rendering.cjs
node apps/reasbook-reviewer/tests/evidence_status.cjs
node sdk/theorem_graph/tests/test_graph_view.js
```

## Run from a checkout

Python 3.11+ is required. From the ReasBook repository root:

```bash
python3.11 -m venv apps/reasbook-reviewer/.venv
apps/reasbook-reviewer/.venv/bin/python -m pip install -r apps/reasbook-reviewer/requirements.txt
export REASBOOK_CACHE_ROOT=/srv/reasbook-cache
apps/reasbook-reviewer/start_server.sh
```

Set `REASBOOK_CACHE_ROOT` to your **existing absolute cache directory** to reuse
its releases and indexes. Choose a writable directory explicitly rather than
relying on the SDK's environment-specific default. An empty cache starts
with the repository catalog and pending indexes; it does not invent evidence.

Open <http://127.0.0.1:8876/ReasBook/>. The launcher loads an optional app `.env`
using the SDK's non-executable defaults parser; process environment variables
take precedence. Copy [.env.example](.env.example) to `.env` for local settings.
It chooses `.venv/bin/python`, then the legacy `.python311/bin/python`, then
`python3`; `REASBOOK_REVIEWER_PYTHON` overrides that choice. One Uvicorn worker
owns the SQLite service.

Without an authentication package and OAuth configuration, reading is public and
writes are disabled. `/api/health` reports `auth.configured=false`.

Review state is not imported from the former Stacks reviewer automatically.
Keep that database read-only until an explicit, audited mapping is prepared;
see [ADR 0011](../../docs/decisions/0011-review-state-migration.md).

## Data and cache contract

| Location | Purpose |
| --- | --- |
| `$REASBOOK_CACHE_ROOT/releases/` | Existing release manifests and generated evidence |
| `$REASBOOK_CACHE_ROOT/reviewer/data/catalog.json` | Optional cached catalog |
| `$REASBOOK_CACHE_ROOT/reviewer/data/books/<slug>/` | Review indexes and compatible compiled graph caches |
| `$REASBOOK_CACHE_ROOT/reviewer/state/reviews.sqlite3` | Persistent users, review comments and audit history |

`REASBOOK_REVIEWER_DATA`, `REASBOOK_REVIEWER_DB`, and
`REASBOOK_REVIEWER_RELEASE_ROOT` override these locations independently.
`REASBOOK_ROOT` overrides the enclosing repository used for catalog discovery.
Keep generated evidence outside Git. The SQLite database is user data and must
be backed up independently of rebuildable artifacts; use SQLite's backup API or
stop the service before copying the database and its journal files.

Retain the source snapshots referenced by release manifests. Older manifests
contain absolute paths: mount the cache at the same absolute location when using
containers, and preserve any referenced external source mounts. Moving a
manifest alone does not relocate its source or documentation trees.

Missing indexes can be generated with the existing deploy SDK, from the
repository root:

```bash
./sdk/deploy/bin/reasbook-deploy --book Analysis2_Tao_2022 --no-build --no-stacks
```

This explicitly creates a lightweight source index. To refresh compiled evidence,
use the [Deploy SDK](../../sdk/deploy/README.md) and
[theorem-graph SDK](../../sdk/theorem_graph/README.md). HTTP handlers only read
their output. Compiled graph caches must match the selected project's kind,
branch and commit; `source-only` means missing compiled evidence, not zero
dependencies. Statement edges come from Lean types and proof edges from proof
or definition bodies. The graph can aggregate helper paths and is not a tactic
execution trace.

The Source/Docs/Verso/Graph status chips describe the **selected declaration**,
not whole-book build coverage. They reset while its context loads and on request
failure. Docs and Verso are ready only when the item resolver supplies an
available page URL in the selected release; a book-level site directory is not
enough. Source readiness requires the selected file. Graph distinguishes a
compiled selected node, a source-only node, and a declaration not in the graph;
ready does not mean that every module in the book compiled. Newly completed
finalizer candidates are not automatically substituted for published evidence.

## Container deployment

Use Docker Engine with Compose 2.24+ from the repository root. The reviewer has a
separate Compose file because the existing `docker-compose.yml` serves static
releases. The source image contains the app, SDK and catalog configuration;
generated evidence and secrets are excluded from its build context.

```bash
export REASBOOK_CACHE_ROOT=/srv/reasbook-cache
export REASBOOK_REVIEWER_STATE_DIR="$REASBOOK_CACHE_ROOT/reviewer/state"
export REASBOOK_REVIEWER_UID="$(id -u)" REASBOOK_REVIEWER_GID="$(id -g)"
mkdir -p "$REASBOOK_CACHE_ROOT" "$REASBOOK_REVIEWER_STATE_DIR"
docker compose -f docker-compose.reviewer.yml config --quiet
docker compose -f docker-compose.reviewer.yml up --build -d --wait
curl --fail http://127.0.0.1:8876/ReasBook/api/health
```

Artifacts are mounted read-only at their original absolute path. The state
directory is mounted writable at `/var/lib/reasbook`; set it to the directory
containing the existing `reviews.sqlite3` when migrating. UID/GID must be able to
read artifacts and write that directory. The gateway binds to localhost by
default. Configure HTTPS in your public ingress and forward the whole URL space,
including `/ReasBook/`, `/api/`, assets, and login callbacks. The ingress must
set `X-Forwarded-Proto` to its actual external scheme; do not expose the backend
container port directly. Public hosting with
comments needs this backend; GitHub Pages only hosts static generated pages.

For updates, keep the cache and state volumes and rebuild the source image.
For rollback, select a previously built `REASBOOK_REVIEWER_IMAGE` and run
`docker compose -f docker-compose.reviewer.yml up -d --no-build`. Do not restore
an older database without accounting for comments written since the backup.

## Enable sign-in and public comments

For SiFlow managed hosting, use a **general service**, not a workbench port
proxy or a finite build task. Keep one replica while using SQLite, reuse the
external evidence cache, and migrate state using SQLite's backup API rather
than sharing its WAL database across hosts. See
[ADR-0017](../../docs/decisions/0017-siflow-managed-reviewer-service.md).
A localhost OAuth callback is only for local development; register the actual
service HTTPS callback before enabling remote login and comments.

ReasLab authentication is an optional external dependency, not bundled or copied
into this application. Install a trusted checkout into the same Python environment:

```bash
apps/reasbook-reviewer/.venv/bin/python -m pip install /path/to/reaslab-auth/python
```

Alternatively, point `REASLAB_AUTH_ROOT` at its `python/src` directory **after
installing that package's dependencies**. Configure the four `REASLAB_OAUTH_*`
variables in the example file and register the exact externally reachable
callback URL with the provider. Set a stable `REASBOOK_SESSION_SECRET`; keep
secure cookies enabled for HTTPS. For local HTTP sign-in only, set
`REASBOOK_SECURE_COOKIES=false`.

For path-based shared-host gateways, set `REASBOOK_AUTH_COOKIE_PATH` to the
external reviewer path (including the trailing `/ReasBook/`), so transaction,
session and deletion cookies do not reach sibling services. Login links retain
the declaration query string. `REASBOOK_APP_BASE_URL` is the HTTPS origin in
this setup, not the path prefix: the frontend already includes the full path in
`return_to`. With a non-root cookie path, the login handler normalizes gateway
aliases to that canonical prefix, preserving book paths and declaration queries.
The registered callback, cookie scope and post-login page must share this prefix;
returning to another gateway alias would make a successful login appear lost.
Inject a stable session secret and OAuth credentials only at runtime.

For an authenticated container deployment, build a small derived image from the
reviewer image and install the pinned `reaslab-auth` wheel (and its dependencies)
in that image. Use a trusted auth checkout pinned to the commit you intend to
deploy. From the ReasBook root, with BuildKit named build contexts enabled:

```bash
REASLAB_AUTH_CHECKOUT=/path/to/pinned/reaslab-auth
REASBOOK_AUTH_WHEELS="$(mktemp -d)"
apps/reasbook-reviewer/.venv/bin/python -m pip wheel --no-deps \
  --wheel-dir "$REASBOOK_AUTH_WHEELS" "$REASLAB_AUTH_CHECKOUT/python"
docker build -f apps/reasbook-reviewer/Dockerfile -t reasbook-reviewer:base .
docker build -f apps/reasbook-reviewer/Dockerfile.auth \
  --build-arg REVIEWER_BASE_IMAGE=reasbook-reviewer:base \
  --build-context "auth_wheels=$REASBOOK_AUTH_WHEELS" \
  -t reasbook-reviewer:auth .
export REASBOOK_REVIEWER_IMAGE=reasbook-reviewer:auth
docker compose -f docker-compose.reviewer.yml up -d --no-build --wait
```

The named context contains only the generated wheel; `Dockerfile.auth` copies
only `*.whl` files and installs their dependencies with pip. The ordinary build
context is empty for this derived image, and the base build excludes local
environments, credentials, caches and SQLite state. Keep the cache/state variables
from the container setup above and configure OAuth before running `up`.
Use `--no-build` when selecting this derived image so Compose does not replace it
with the base Dockerfile's unauthenticated image. Compose reads
`apps/reasbook-reviewer/.env` if present, or the file selected by
`REASBOOK_REVIEWER_ENV_FILE`; a mounted auth source directory alone does not
install its Python dependencies.

Public evidence is enabled by default; set `REASBOOK_PUBLIC_ARTIFACTS=false` to
require login for source/docs/graph payloads. For Compose, put this setting in the
app `.env` or the file selected by `REASBOOK_REVIEWER_ENV_FILE`; Compose preserves
that value instead of overriding it with a public-reading default. Local roles default to reviewer;
`REASBOOK_ADMIN_SUBJECTS` seeds administrator roles for the listed ReasLab subject
IDs. Review writes require a valid session, CSRF token and a known index key.

## API and maintenance

The same routes are available at `/api/` and `/ReasBook/api/`:

- `GET /api/health`, `/api/catalog`, `/api/books`: readiness and catalog.
- `GET /api/books/<slug>/index`, `/resources`, `/graph`: review units and evidence.
- `GET /api/books/<slug>/context/<item-key>`: selected statement and Lean code.
- `GET /api/books/<slug>/reviews`, `/reviews/<item-key>/history`: public reviews.
- `POST /api/books/<slug>/reviews/<item-key>`: `status`, `comment`, `clientId`,
  `baseRevision`; requires `X-CSRF-Token` obtained from `/api/auth/csrf`.
- `GET /api/books/<slug>/reviews/export.jsonl`: administrator audit export.

The current comment model stores one review per person and item, with an
append-only change history and optimistic concurrency. It is not a threaded
discussion system. Existing review keys and revisions remain stable across this
application move; reviewing a changed release still requires human judgment.

`app.py` owns HTTP/authentication, `storage.py` owns SQLite, `catalog.py` adapts
repository discovery, and `artifacts.py` resolves and embeds evidence.
`settings.py` and `bootstrap.py` connect to shared SDK configuration. The frontend
is plain JavaScript/CSS in `docs/`; theorem maps reuse the canonical SDK renderer
instead of maintaining a second graph implementation. This is a source-deployed application, not a
separately installable Python wheel.

```bash
cd apps/reasbook-reviewer
.venv/bin/python -m pip install httpx ruff==0.6.3
.venv/bin/python -m unittest discover -s tests -v
.venv/bin/python -m ruff check .
node --check docs/app.js
node --check docs/mathjax-config.js
```

The [reviewer workflow](../../.github/workflows/reviewer.yml) runs these offline
checks, audits runtime dependencies and smoke-tests the container. It performs
no Lean compilation or production deployment. Require it in GitHub branch
protection when publishing changes. Contribution rules are in
[CONTRIBUTING.md](../../CONTRIBUTING.md); integration decisions are recorded in
[ADR-0012](../../docs/decisions/0012-integrated-reader-and-review-platform.md).
