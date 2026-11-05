/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

public section

/- Definition 2.53 (Chromatic number): for an undirected graph `G`, the chromatic number is
formalized by the canonical mathlib owner `SimpleGraph.chromaticNumber`. The proper-coloring
condition behind the source wording is `SimpleGraph.Colorable`, and for finite graphs the ordinary
natural-valued chromatic number used later in Chapter 2 is `ENat.toNat G.chromaticNumber`. -/
#check SimpleGraph.chromaticNumber
#check SimpleGraph.Colorable

end
