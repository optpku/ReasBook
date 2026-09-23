#!/usr/bin/env python3
"""Build the full DFP API documentation with the ReasBook build SDK.

Run after checking Paper.lean and committing the source snapshot. Output stays
outside the repository. Uses the already installed doc-gen4 executable; this
adapter never invokes lake build or updates dependencies.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk-root', type=Path, required=True,
                        help='ReasBook/sdk (containing build/ and common/)')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    paper = Path(__file__).resolve().parents[1]
    lean_root = paper.parents[1]
    repo = lean_root.parent
    output = args.output.resolve()
    if repo == output or repo in output.parents:
        parser.error('Documentation output must be outside the source repository')
    for package in ('common', 'build'):
        sys.path.insert(0, str(args.sdk_root.resolve() / package / 'src'))
    from reasbook_build_sdk.docs import ProjectDocumentationBuilder
    from reasbook_build_sdk.executor import SubprocessRunner

    class BoundedRunner:
        def run(self, command):
            argv = list(command.argv)
            if Path(argv[0]).name == 'lake' and 'build' in argv:
                raise RuntimeError('Prebuilt tools are required; lake build is disabled')
            if 'lean' in argv:
                index = argv.index('lean') + 1
                argv[index:index] = ['-j1', '-M8192']
            argv = ['taskset', '-c', '0-1', *argv]
            return SubprocessRunner(stream=True).run(replace(command, argv=argv))

    class DFPDocumentationBuilder(ProjectDocumentationBuilder):
        @staticmethod
        def _module_lexical_sources(project_root, module):
            usual = ProjectDocumentationBuilder._module_lexical_sources(project_root, module)
            if module.split('.')[0] in ('DFPWolfe', 'ReasLib'):
                return (*usual, project_root / 'Papers/DFP_wolfe_local' /
                        Path(*module.split('.')).with_suffix('.lean'))
            return usual

        @classmethod
        def _project_module_candidates(cls, project_root, roots):
            candidates = super()._project_module_candidates(project_root, roots)
            for path in (project_root / 'Papers/DFP_wolfe_local').rglob('*.lean'):
                relative = path.relative_to(project_root / 'Papers/DFP_wolfe_local').with_suffix('')
                if relative.parts[0] in ('DFPWolfe', 'ReasLib'):
                    candidates['.'.join(relative.parts)] = (path,)
            return candidates

    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    dirty = subprocess.check_output(['git', 'diff', 'HEAD', '--',
        'ReasBook/Papers/DFP_wolfe_local/**/*.lean',
        'ReasBook/Papers/DFP_wolfe_local/*.lean'], cwd=repo, text=True)
    if dirty:
        raise RuntimeError('Commit the Lean source before generating immutable source links')
    executable = lean_root / '.lake/packages/doc-gen4/.lake/build/bin/doc-gen4'
    if not executable.is_file():
        raise RuntimeError('Install a compatible prebuilt doc-gen4 executable first')
    builder = DFPDocumentationBuilder(BoundedRunner())
    plan = builder.plan_reachable_modules(lean_root, ['DFP_wolfe_local.Paper'])
    print(f'Reachable DFP modules: {len(plan.entries)}; revision: {revision}', flush=True)
    result = builder.build(lean_root, ['DFP_wolfe_local.Paper'], output,
        repository='https://github.com/optpku/ReasBook', revision=revision)
    print({'output': str(output), 'revision': revision, 'pages': len(result.pages),
           'mode': result.mode, 'reused': result.reused}, flush=True)


if __name__ == '__main__':
    main()
