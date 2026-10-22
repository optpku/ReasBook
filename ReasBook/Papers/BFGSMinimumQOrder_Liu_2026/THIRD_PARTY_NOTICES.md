# Third-party notices

## DFP_wolfe_local

This project contains the complete `ReasLib/` Lean library from
[`imathwy/DFP_wolfe_local`](https://github.com/imathwy/DFP_wolfe_local), pinned
to commit `e308927f5b7930bdd002f0c0e42b9d112ad821cb`.

The [pinned upstream README](https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md)
identifies **Zichen Wang** as the formalization author. Importing this code into
the BFGS project does not transfer that author credit to the importing project's
contributor. Imported file headers name the upstream author and cite the pinned
source file; adapted files additionally identify the confirmed local project
credit and its limited scope. See [authorship provenance](AUTHORSHIP.md).

The `DFPWolfe/` modules are included as a separate Lean library because one
upstream `ReasLib` adapter imports theorem-level DFP modules. Keeping that
dependency closure makes every imported upstream module resolvable, while the
BFGS and DFP paper developments retain separate public entry points.

The body of the source repository's top-level `ReasLib.lean` is identical to
this project's file after excluding the opening ordinary file header. The only
non-identical path collision in the original import was
`ReasLib/Optimization/LineSearch.lean`; its DFP weak-Wolfe API and this
project's pre-existing exact-line-search API were combined additively.  The
existing BFGS-specific modules and paper-facing `Book/` files remain in the
same Lean project.

Two upstream long-tail adapter fixes were required by a strict build of every
`ReasLib` glob: a duplicate adapter theorem was given a distinct name, and a
continuity proof was made explicit about function composition.  These do not
change the selected smooth-interpolation or DFP theorem APIs.

`ReasLib/Geometry/Euclidean/Plane/Rotation.lean` also includes BFGS-specific
quarter-turn matrix declarations and exports the coordinate area-form theorem.
Together with the combined line-search API and the two adapter fixes, these
are the four upstream-path files whose bodies differ from the pinned source.

The imported files are licensed under Apache License 2.0.  A copy is stored at
`LICENSES/DFP_wolfe_local-APACHE-2.0.txt`.
