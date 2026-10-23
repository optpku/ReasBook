module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open TopologicalSpace
open scoped ContDiff

noncomputable section

section

open Manifold

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝒪∞" => smoothSheaf (𝓘(ℝ, E)) 𝓘(ℝ) E ℝ

/- Domain-style sampling for Example 6.11.4:
- primary domain: stalks of concrete presheaves on topological spaces, specialized here to the
  smooth real-valued sheaf on `ℝ^n`;
- sampled owner API:
  `TopCat.Presheaf.germ_exist`,
  `TopCat.Presheaf.germ_eq`,
  `TopCat.Presheaf.germ_ext`,
  `smoothSheaf.eval_germ`;
- best owner abstraction: the stalk API on `TopCat.Presheaf`, with `germ_eq` and `germ_ext`
  controlling equality of germs and `germ_exist` providing representatives;
- primitive data: opens `U, V : Opens E`, a point `x : E` with `x ∈ U` and `x ∈ V`, and sections
  `f` and `g` of the smooth sheaf on `U` and `V`;
- derived API: no new public wrapper is needed; Example 6.11.4 is a direct specialization of the
  owner theorems above.

Source/core/bridge triage:
- `source-facing`: two smooth functions defined near `x` determine the same stalk element exactly
  when they agree after restriction to some smaller neighbourhood of `x`;
- `core/canonical`: `TopCat.Presheaf.germ_eq` and `TopCat.Presheaf.germ_ext`;
- `bridge/view`: the specialization from an arbitrary concrete presheaf to the smooth-function
  sheaf on `ℝ^n`. -/

/-
Every element of the stalk of the smooth real-valued sheaf on `ℝ^n` is represented by a smooth
function defined on some open neighbourhood of the point. This is the specialization of the
canonical stalk-representative theorem `TopCat.Presheaf.germ_exist`.
-/
recall TopCat.Presheaf.germ_exist

/- Companion recall: equality of germs in any concrete presheaf is detected after restricting to a
smaller neighbourhood. -/
recall TopCat.Presheaf.germ_eq

/- Companion recall: agreement of restrictions on a smaller neighbourhood gives equality of germs.
-/
recall TopCat.Presheaf.germ_ext

/-- Example 6.11.4: two smooth functions defined near `x` determine the same stalk element if and
only if they agree after restriction to some smaller neighbourhood of `x`. This is the direct
smooth-sheaf specialization of `TopCat.Presheaf.germ_eq` and `TopCat.Presheaf.germ_ext`. -/
theorem smoothSheaf_germ_eq_iff
    {U V : Opens E} (x : E) (hxU : x ∈ U) (hxV : x ∈ V)
    (f : 𝒪∞.presheaf.obj (op U)) (g : 𝒪∞.presheaf.obj (op V)) :
    𝒪∞.presheaf.germ U x hxU f = 𝒪∞.presheaf.germ V x hxV g ↔
      ∃ (W : Opens E) (_ : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V),
        𝒪∞.presheaf.map iU.op f = 𝒪∞.presheaf.map iV.op g := by
  constructor
  · intro h
    exact 𝒪∞.presheaf.germ_eq x hxU hxV f g h
  · rintro ⟨W, hxW, iU, iV, h⟩
    exact 𝒪∞.presheaf.germ_ext W hxW iU iV h

end

#min_imports
