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
