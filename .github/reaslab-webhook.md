# ReasLab upstream source notification

Configure a **repository webhook**, using [`reaslab-webhook.yml`](reaslab-webhook.yml).
GitHub sends push payloads directly to the Axum endpoint on ReasLab:

**POST https://reasbook.reaslab.io/hooks/upstream-sync**

This does not run a GitHub Actions job. Source synchronization, Lean/static
artifact generation and publication remain separate operations on ReasLab.

## Administrator setup

In this repository's **Settings → Webhooks → Add webhook**:

| Setting | Value |
|---|---|
| Payload URL | `https://reasbook.reaslab.io/hooks/upstream-sync` |
| Content type | `application/json` |
| Secret | The shared service secret, supplied privately by the ReasLab operator |
| SSL verification | Enable |
| Events | Just the push event |
| Active | Checked |

The secret value is not in the YAML, source tree, PR or URL. GitHub uses it to
produce `X-Hub-Signature-256`; unsigned or invalid requests are rejected. Do not
substitute a GitHub access token for this webhook secret.

Alternatively, use an administrator's authenticated `gh` CLI. The helper uses
the existing PyYAML dependency in `scripts/config/requirements.txt`, previews
without changing anything by default, and updates only a webhook with the exact
configured URL. Other hooks are retained:

```sh
python3 .github/scripts/register_reaslab_webhook.py

# Save the operator-supplied secret outside this checkout, with private permissions.
python3 .github/scripts/register_reaslab_webhook.py \
  --secret-file /absolute/private/path/reaslab-webhook-secret --apply
```

The helper can instead read `REASLAB_UPSTREAM_WEBHOOK_SECRET` from its environment.
It sends the secret through the API request's stdin and prints only non-secret
hook metadata. Both repository Admin rights and suitable token access are
required; Maintain access alone cannot manage repository webhooks.

## Events and processing

The receiver accepts the configured upstream refs: `main`, `v4.26.0`, `v4.29.0`,
`v4.30.0`, `v4.32.0`, `v4.32.2`, and
`book/stacks-project-chap04-07-v4.30.0`. It filters changed paths according to
the ReasLab source registry. Unrelated refs/paths are ignored. A repository
webhook covers all of these branches; there is no need to copy a workflow into
each version branch.

Accepted deliveries enter a persistent queue. The worker fetches the configured
upstreams, applies ordinary three-way source merges in an isolated checkout,
pushes clean changes to the downstream synchronization branch and reports
conflicts while retaining the local file and its original baseline. Repeated
delivery IDs are deduplicated. Deleted/forced/truncated pushes request a check
rather than blindly changing sources.

An authorized push to a configured source/ref also requests the downstream
build and publication stages. Those stages run as separate fixed tasks on
ReasLab, not as commands supplied by the webhook payload. Clean source,
successful resource-limited builds and artifact acceptance are required before
promoting a candidate; conflicts or failures keep the previous site available.

The webhook response acknowledges receipt, not a successful Lean build or a
website release. Current reading/review services and published artifacts are
kept available independently. The ReasLab operator retains per-delivery reports
and a downstream source-conflict report for review.
