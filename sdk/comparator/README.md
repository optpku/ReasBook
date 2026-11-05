# Comparator SDK

The [upstream Comparator project is deprecated](https://github.com/leanprover/comparator#deprecation)
and archived. From Lean `v4.35.0`, its functionality is provided by `lake comparator`
and `lake check`. ReasBook's current `v4.26.0`–`v4.32.2` projects predate those
commands; this SDK retains their pinned legacy workflow. When upgrading a
project to Lean `v4.35.0` or newer, migrate its validation setup to the core Lake
commands rather than assuming this wrapper invokes them.

`comparator-sdk` is a local, transport-neutral wrapper around the Lean FRO
[`Comparator`](https://github.com/leanprover/comparator) executable. It validates
a Challenge/Solution project, optionally builds the Comparator checkout, runs
the comparison with argv-only subprocesses, and returns a structured result that
an application or another execution service can consume.

The package intentionally contains no deployment-platform client or platform
credentials.  A caller can inject its own `CommandRunner` implementation when
the commands should run in a worker, container, or job service.

## Layout

```text
src/comparator_sdk/
  config.py       runtime options and Comparator JSON validation
  commands.py     argv construction (build, cache, compare)
  models.py       request and result dataclasses
  project.py      Lake project discovery and output checks
  runner.py       prepare/compare orchestration
  cli.py          `python -m comparator_sdk` entry point
```

## Python API

```python
from pathlib import Path
from comparator_sdk import ComparatorConfig, ComparatorRunner

config = ComparatorConfig.from_paths(
    project_root=Path("/work/challenge"),
    config_path=Path("configuration.json"),
    comparator_root=Path("/work/comparator"),
)
result = ComparatorRunner(config).compare()
if result.accepted:
    print("proof accepted")
```

Install the shared primitives first when using editable installs:

```bash
python3.11 -m pip install -e sdk/common -e sdk/comparator
```

The `runner` argument is injectable:

```python
result = ComparatorRunner(config, runner=my_command_runner).compare()
```

`my_command_runner` only needs a `run(Command) -> CommandResult` method.  The
shared primitives live in `sdk/common`, so build, Verso, graph, and Comparator
stages can use the same process and file semantics.

## CLI

From the repository root, the bundled wrapper is:

```bash
./sdk/comparator/bin/comparator --help
```

```bash
./sdk/comparator/bin/comparator compare /work/challenge configuration.json \
  --comparator-root /work/comparator
./sdk/comparator/bin/comparator validate /work/challenge configuration.json \
  --comparator-root /work/comparator
```

Use `--dry-run` to print the planned argv without running Lean.  A successful
Comparator verdict exits `0`; a rejected proof exits `1`; invalid input or a
missing tool exits `2`.

The default comparator command is equivalent to:

```text
lake build lean4export comparator       # optional preparation
lake env .lake/build/bin/comparator configuration.json
```

`COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_NANODA` may be
provided as ordinary Comparator environment values when the corresponding
tools are not on `PATH`.  They are never copied into result files.
