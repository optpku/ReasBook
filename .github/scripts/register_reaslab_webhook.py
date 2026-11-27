#!/usr/bin/env python3
"""Preview/register the ReasLab repository webhook with an administrator's gh login."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=Path(__file__).resolve().parents[1] / "reaslab-webhook.yml")
    parser.add_argument("--secret-file", type=Path, help="Private local file containing the shared service secret")
    parser.add_argument("--apply", action="store_true", help="Create/update the matching webhook; default is a redacted preview")
    args = parser.parse_args()
    try:
        import yaml
    except ImportError:
        parser.exit(1, "Install existing repository requirements: python3 -m pip install -r scripts/config/requirements.txt\n")
    document = yaml.safe_load(args.config.read_text())
    repository = document["repository"]
    if len(repository.split("/")) != 2 or any(c in repository for c in "\n\r ?#"):
        parser.error("Expected owner/repository")
    config = document["config"]
    if not config["url"].startswith("https://") or config.get("insecure_ssl") != "0":
        parser.error("Use HTTPS and keep SSL verification enabled")
    payload = {key: document[key] for key in ["name", "active", "events"]}
    payload["config"] = dict(config)
    if not args.apply:
        payload["config"]["secret"] = "<supplied privately from file or environment>"
        print(json.dumps({"repository": repository, "webhook": payload}, indent=2))
        return 0
    secret = args.secret_file.read_text().strip() if args.secret_file else os.environ.get(document["secret_env"], "").strip()
    if not secret:
        parser.error("Supply --secret-file or the configured secret environment variable; do not put the secret on the command line")
    payload["config"]["secret"] = secret
    try:
        hooks = json.loads(subprocess.check_output(["gh", "api", f"repos/{repository}/hooks"], text=True))
        matches = [h for h in hooks if h.get("config", {}).get("url") == config["url"]]
        if len(matches) > 1:
            parser.error("More than one matching webhook exists; administrator review is required")
        endpoint = f"repos/{repository}/hooks" + (f"/{matches[0]['id']}" if matches else "")
        result = json.loads(subprocess.check_output(
            ["gh", "api", "--method", "PATCH" if matches else "POST", endpoint, "--input", "-"],
            input=json.dumps(payload), text=True))
    except subprocess.CalledProcessError:
        print("Webhook administration failed. Use a repository Admin login with webhook access.", file=sys.stderr)
        return 1
    print(json.dumps({"repository": repository, "id": result["id"], "active": result["active"],
                      "events": result["events"], "url": result["config"]["url"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
