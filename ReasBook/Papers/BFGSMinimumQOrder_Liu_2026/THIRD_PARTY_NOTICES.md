# Third-party notices

## DFP_wolfe_local

This project contains the complete `ReasLib/` Lean library from
[`imathwy/DFP_wolfe_local`](https://github.com/imathwy/DFP_wolfe_local), pinned
to commit `e308927f5b7930bdd002f0c0e42b9d112ad821cb`.

The `DFPWolfe/` modules are included as a separate Lean library because one
upstream `ReasLib` adapter imports theorem-level DFP modules. Keeping that
dependency closure makes every imported upstream module resolvable, while the
BFGS and DFP paper developments retain separate public entry points.

The source repository's top-level `ReasLib.lean` is byte-identical to this
project’s file.  The only non-identical path collision was
`ReasLib/Optimization/LineSearch.lean`; its DFP weak-Wolfe API and this
project's pre-existing exact-line-search API were combined additively.  The
existing BFGS-specific modules and paper-facing `Book/` files remain in the
same Lean project.

Two upstream long-tail adapter fixes were required by a strict build of every
`ReasLib` glob: a duplicate adapter theorem was given a distinct name, and a
continuity proof was made explicit about function composition.  These do not
change the selected smooth-interpolation or DFP theorem APIs.

The imported files are licensed under Apache License 2.0.  A copy is stored at
`LICENSES/DFP_wolfe_local-APACHE-2.0.txt`.
