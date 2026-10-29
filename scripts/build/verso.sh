#!/usr/bin/env bash

# Generate sections and build the Verso site through sdk/verso.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "$SCRIPT_DIR/common.sh"

VERSO_SDK="$REASBOOK_TOOLING_ROOT/sdk/verso/bin/verso-build"
if [[ ! -x "$VERSO_SDK" ]]; then
  reasbook_die "Verso SDK entrypoint is missing: $VERSO_SDK"
  exit 2
fi
LITERATE_SDK="$REASBOOK_TOOLING_ROOT/sdk/verso/bin/verso-literate"
if [[ ! -x "$LITERATE_SDK" ]]; then
  reasbook_die "Verso literate cache entrypoint is missing: $LITERATE_SDK"
  exit 2
fi

export VERSO_WEB_ROOT="$REASBOOK_WEB_ROOT"
export VERSO_TARGETS="exe reasbook-site"

# A project finalizer must write to a disjoint artifact root.  Requiring an
# exact singleton selector here prevents two workers from claiming the same
# output or accidentally producing a branch-wide catalog.
fragment_project=""
if [[ "${REASBOOK_PROJECT_FRAGMENT:-0}" =~ ^(1|true|yes|on)$ ]]; then
  fragment_project="${REASBOOK_INCLUDE_PROJECTS:-}"
  if [[ ! "$fragment_project" =~ ^(books|papers)/[A-Za-z0-9_.-]+$ ]]; then
    reasbook_die "project fragments require one canonical REASBOOK_INCLUDE_PROJECTS key"
    exit 2
  fi
  if [[ -n "${REASBOOK_EXCLUDE_PROJECTS:-}" ]]; then
    reasbook_die "project fragments do not accept REASBOOK_EXCLUDE_PROJECTS"
    exit 2
  fi
  if [[ -z "${REASBOOK_PROJECT_FRAGMENT_ROOT:-}" ]]; then
    reasbook_die "REASBOOK_PROJECT_FRAGMENT_ROOT is required for project fragments"
    exit 2
  fi
  fragment_root="$REASBOOK_PROJECT_FRAGMENT_ROOT/$fragment_project"
  mkdir -p "$fragment_root"
  export VERSO_OUTPUT_DIR="$fragment_root/site"
fi
if [[ -n "${REASBOOK_VERSO_GENERATOR:-}" ]]; then
  generator_args=(
    "$REASBOOK_TOOLING_ROOT/sdk/common/bin/python"
    "$REASBOOK_VERSO_GENERATOR"
    --repo-root
    "$REASBOOK_REPO_ROOT"
  )
else
  generator_args=(
    "$REASBOOK_TOOLING_ROOT/sdk/common/bin/python"
    "$REASBOOK_WEB_ROOT/scripts/gen_sections.py"
    --repo-root
    "$REASBOOK_REPO_ROOT"
  )
fi

reasbook_log "generating Verso sections and literate module manifest"
(
  cd "$REASBOOK_REPO_ROOT"
  "${generator_args[@]}"
)

LITERATE_MANIFEST="$REASBOOK_WEB_ROOT/.literate-modules.json"
if [[ ! -f "$LITERATE_MANIFEST" || -L "$LITERATE_MANIFEST" ]]; then
  reasbook_die "Literate module manifest is missing or unsafe: $LITERATE_MANIFEST"
  exit 2
fi
reasbook_log "completing identity-bound literate cache"
REASBOOK_RUNTIME_CACHE_PREFIX= \
  reasbook_run_runtime "$REASBOOK_LEAN_ROOT" "$LITERATE_SDK" \
  --lean-root "$REASBOOK_LEAN_ROOT" \
  --module-manifest "$LITERATE_MANIFEST"

# Branch-specific Lake files only skip their nested extraction loop after the
# SDK has validated every artifact and atomically committed its completion
# marker.  The generator already ran above, so the generic Verso SDK must not
# run it a second time.
export REASBOOK_LITERATE_PREBUILT=1
export VERSO_ENV_REASBOOK_LITERATE_PREBUILT=1
export VERSO_GENERATOR=""
export VERSO_GENERATOR_CWD="$REASBOOK_REPO_ROOT"
if [[ -z "$fragment_project" ]]; then
  export VERSO_OUTPUT_DIR="$REASBOOK_WEB_ROOT/_site"
fi
export VERSO_VERIFY_OUTPUT=1

if ulimit -s unlimited 2>/dev/null; then
  echo "[build_reasbook_web] stack limit set to unlimited"
fi
reasbook_log "running sdk/verso pipeline"
REASBOOK_RUNTIME_CACHE_PREFIX=web- \
  reasbook_run_runtime "$REASBOOK_WEB_ROOT" "$VERSO_SDK" "$REASBOOK_WEB_ROOT"

reasbook_log "adding Lean source attribution to full literate reading pages"
"$REASBOOK_TOOLING_ROOT/sdk/common/bin/python" \
  "$REASBOOK_TOOLING_ROOT/ReasBookWeb/scripts/reader_attributions.py" \
  --site "$VERSO_OUTPUT_DIR" --manifest "$REASBOOK_WEB_ROOT/.reader-attributions.json"

if [[ -n "$fragment_project" ]]; then
  # Root index is shared catalog ownership and is intentionally excluded.
  # Static assets remain beside the project routes so the fragment is locally
  # inspectable and the merge layer can content-hash/deduplicate them.
  rm -f -- "$VERSO_OUTPUT_DIR/index.html"
  "$REASBOOK_TOOLING_ROOT/sdk/common/bin/python" - \
    "$REASBOOK_WEB_ROOT/.project-fragment.json" \
    "$fragment_root/fragment.json" "$fragment_project" "$VERSO_OUTPUT_DIR" <<'PY'
import json
import os
from pathlib import Path
import sys

selection, manifest = Path(sys.argv[1]), Path(sys.argv[2])
project, site = sys.argv[3], Path(sys.argv[4])
try:
    payload = json.loads(selection.read_text(encoding="utf-8"))
except (OSError, json.JSONDecodeError) as exc:
    raise SystemExit(f"invalid project fragment selection manifest: {exc}")
if payload.get("project") != project or payload.get("shared_catalog") is not False:
    raise SystemExit("project fragment selection identity does not match the build")
routes = payload.get("routes")
modules = payload.get("modules")
if not isinstance(routes, list) or not routes or not all(isinstance(x, str) and x for x in routes):
    raise SystemExit("project fragment selection has no valid routes")
if not isinstance(modules, list) or not modules or not all(isinstance(x, str) and x for x in modules):
    raise SystemExit("project fragment has no valid module inventory")
missing = [route for route in routes if not (site / route / "index.html").is_file()]
if missing:
    raise SystemExit(f"project fragment is missing {len(missing)} selected route(s): {missing[0]}")
payload["site_dir"] = "site"
temporary = manifest.with_name(f".{manifest.name}.{os.getpid()}.tmp")
temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
os.replace(temporary, manifest)
PY
  reasbook_log "wrote isolated project fragment: $fragment_root"
fi
