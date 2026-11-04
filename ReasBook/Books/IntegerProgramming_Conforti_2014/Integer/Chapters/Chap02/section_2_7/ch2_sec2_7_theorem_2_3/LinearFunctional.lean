/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18

noncomputable section

open scoped BigOperators Matrix

/-- The coefficient vector `c` defines the linear functional `x ↦ c ⬝ᵥ x` on a finite
coordinate space. -/
abbrev dotProductLinearMap {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] ℝ :=
  dotProductEquiv ℝ ι c

/-- `dotProductLinearMap c` evaluates as the coordinate dot product with `c`. -/
@[simp] theorem dotProductLinearMap_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (c x : ι → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  rfl

/-- Helper for Theorem 2.3: the strong-dual functional associated with `c` is the corresponding
coordinate dot product. -/
noncomputable def dotProductStrongDual {n : ℕ} (c : Fin n → ℝ) :
    StrongDual ℝ (Fin n → ℝ) :=
  ∑ i, c i • ContinuousLinearMap.proj i

/-- Helper for Theorem 2.3: `dotProductStrongDual c` evaluates as the coordinate dot product with
`c`. -/
lemma dotProductStrongDual_apply {n : ℕ} (c x : Fin n → ℝ) :
    dotProductStrongDual c x = c ⬝ᵥ x := by
  simp [dotProductStrongDual, dotProduct]

/-- Helper for Theorem 2.3: every strong-dual functional on `Fin n → ℝ` is the dot product with
some coefficient vector. -/
lemma strongDual_eq_dotProduct_fin {n : ℕ} (l : StrongDual ℝ (Fin n → ℝ)) :
    ∃ c : Fin n → ℝ, ∀ x : Fin n → ℝ, l x = c ⬝ᵥ x := by
  let c : Fin n → ℝ := fun i ↦ l (Pi.single i 1)
  refine ⟨c, ?_⟩
  intro x
  have hx : x = ∑ i, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  calc
    l x = l (∑ i, x i • Pi.single i 1) := congrArg l hx
    _ = ∑ i, l (x i • Pi.single i 1) := by rw [map_sum]
    _ = ∑ i, x i * l (Pi.single i 1) := by simp
    _ = ∑ i, l (Pi.single i 1) * x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [mul_comm]
    _ = c ⬝ᵥ x := by
          simp [c, dotProduct]

/-- A linear functional is determined by its kernel together with one transverse vector where it
takes the value `1`. -/
lemma linearMap_eq_smul_of_ker_eq_and_apply_eq_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {L M : E →ₗ[ℝ] ℝ} {w : E}
    (hker : LinearMap.ker L = LinearMap.ker M)
    (hw : L w = 1) :
    M = (M w) • L := by
  ext x
  let x₀ : E := x - (L x) • w
  have hx₀_mem_L : x₀ ∈ LinearMap.ker L := by
    refine LinearMap.mem_ker.2 ?_
    dsimp [x₀]
    rw [LinearMap.map_sub, LinearMap.map_smul, hw]
    ring
  have hx₀_mem_M : x₀ ∈ LinearMap.ker M := by
    rw [← hker]
    exact hx₀_mem_L
  have hx_split : x = x₀ + (L x) • w := by
    dsimp [x₀]
    abel
  have hx₀_eval_M : M x₀ = 0 := LinearMap.mem_ker.mp hx₀_mem_M
  calc
    M x = M (x₀ + (L x) • w) := by simpa using congrArg M hx_split
    _ = M x₀ + M ((L x) • w) := by rw [LinearMap.map_add]
    _ = 0 + (L x) * M w := by simp [hx₀_eval_M]
    _ = ((M w) • L) x := by simp [smul_eq_mul, mul_comm]

/-- If every point of `F` lies on the same level set of a linear functional, then every direction
vector of `affineSpan ℝ F` lies in the functional's kernel. -/
lemma affineSpan_direction_le_ker_of_forall_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : Set E} {L : E →ₗ[ℝ] ℝ} {x0 : E} {δ : ℝ}
    (hx0 : x0 ∈ F)
    (hlevel : ∀ ⦃x : E⦄, x ∈ F → L x = δ) :
    (affineSpan ℝ F).direction ≤ LinearMap.ker L := by
  have hspan_level :
      (affineSpan ℝ F : Set E) ⊆ {x | L x = δ} := by
    intro x hx
    refine affineSpan_induction hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro a u v w hu hv hw
      have hu' : L u = δ := hu
      have hv' : L v = δ := hv
      have hw' : L w = δ := hw
      simp [hu', hv', hw', sub_eq_add_neg, add_comm]
  have hx0_aff : x0 ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hx0
  intro v hv
  rw [LinearMap.mem_ker]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  have hx_eq : L x = δ := hspan_level hx_aff
  have hx0_eq : L x0 = δ := hlevel hx0
  simp [vsub_eq_sub, hx_eq, hx0_eq]

/-- Helper for Theorem 2.3: the hyperplane defined by `c ⬝ᵥ x = δ`. -/
def linear_hyperplane {n : ℕ} (c : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {x | c ⬝ᵥ x = δ}

/-- Helper for Theorem 2.3: membership in `linear_hyperplane c δ` is exactly the defining
dot-product equation. -/
theorem mem_linear_hyperplane_iff {n : ℕ} {c x : Fin n → ℝ} {δ : ℝ} :
    x ∈ linear_hyperplane c δ ↔ c ⬝ᵥ x = δ := by
  rfl

/-- Helper for Theorem 2.3: the equality section of the valid inequality `c ⬝ᵥ x ≤ δ` on `P`. -/
def face_set {n : ℕ} (P : Set (Fin n → ℝ)) (c : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  P ∩ linear_hyperplane c δ

/-- Helper for Theorem 2.3: membership in `face_set P c δ` means lying in `P` and satisfying
`c ⬝ᵥ x = δ`. -/
theorem mem_face_set_iff {n : ℕ} {P : Set (Fin n → ℝ)} {c x : Fin n → ℝ} {δ : ℝ} :
    x ∈ face_set P c δ ↔ x ∈ P ∧ c ⬝ᵥ x = δ := by
  simp [face_set, linear_hyperplane]

/-- Helper for Theorem 2.3: when a valid inequality is attained, its equality face is the exposed
set of the corresponding dot-product functional. -/
lemma face_set_eq_toExposed_of_mem {n : ℕ} {P : Set (Fin n → ℝ)} {c x₀ : Fin n → ℝ} {δ : ℝ}
    (h_valid : is_valid_inequality P c δ) (hx₀ : x₀ ∈ face_set P c δ) :
    face_set P c δ = (dotProductStrongDual c).toExposed P := by
  have hx₀P : x₀ ∈ P := (mem_face_set_iff.1 hx₀).1
  have hx₀_eq : dotProductStrongDual c x₀ = δ := by
    simpa [dotProductStrongDual_apply] using (mem_face_set_iff.1 hx₀).2
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    intro y hyP
    calc
      dotProductStrongDual c y = c ⬝ᵥ y := dotProductStrongDual_apply c y
      _ ≤ δ := h_valid hyP
      _ = dotProductStrongDual c x := by
            simpa [dotProductStrongDual_apply] using hxEq.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hx₀_le : dotProductStrongDual c x₀ ≤ dotProductStrongDual c x := hx.2 x₀ hx₀P
    have hx_le : dotProductStrongDual c x ≤ dotProductStrongDual c x₀ := by
      simpa [dotProductStrongDual_apply, hx₀_eq] using h_valid hx.1
    have hx_eq : dotProductStrongDual c x = dotProductStrongDual c x₀ :=
      le_antisymm hx_le hx₀_le
    simpa [dotProductStrongDual_apply, hx₀_eq] using hx_eq

/-- Helper for Theorem 2.3: if an exposing functional is represented by `c` and attains its
maximum at `x₀`, then its exposed set is the equality face `c ⬝ᵥ x = c ⬝ᵥ x₀`. -/
lemma toExposed_eq_face_set_of_mem {n : ℕ} {P : Set (Fin n → ℝ)} {l : StrongDual ℝ (Fin n → ℝ)}
    {c x₀ : Fin n → ℝ} (hrep : ∀ x : Fin n → ℝ, l x = c ⬝ᵥ x) (hx₀ : x₀ ∈ l.toExposed P) :
    l.toExposed P = face_set P c (c ⬝ᵥ x₀) := by
  have h_valid : is_valid_inequality P c (c ⬝ᵥ x₀) := by
    intro x hxP
    calc
      c ⬝ᵥ x = l x := by rw [← hrep x]
      _ ≤ l x₀ := hx₀.2 x hxP
      _ = c ⬝ᵥ x₀ := hrep x₀
  have hx₀_face : x₀ ∈ face_set P c (c ⬝ᵥ x₀) := by
    exact (mem_face_set_iff).2 ⟨hx₀.1, rfl⟩
  have hl : l = dotProductStrongDual c := by
    ext x
    rw [hrep x, dotProductStrongDual_apply]
  calc
    l.toExposed P = (dotProductStrongDual c).toExposed P := by rw [hl]
    _ = face_set P c (c ⬝ᵥ x₀) := by
          symm
          exact face_set_eq_toExposed_of_mem h_valid hx₀_face

namespace IsExposed

/-- Helper for Theorem 2.3: a nonempty exposed subset is the equality face of one valid
inequality. -/
lemma exists_eq_face_set_of_nonempty {n : ℕ} {P F : Set (Fin n → ℝ)}
    (hF_face : IsExposed ℝ P F) (hF_nonempty : F.Nonempty) :
    ∃ c : Fin n → ℝ, ∃ δ : ℝ, is_valid_inequality P c δ ∧ F = face_set P c δ := by
  obtain ⟨x₀, hx₀F⟩ := hF_nonempty
  obtain ⟨l, rfl⟩ := hF_face ⟨x₀, hx₀F⟩
  -- Rewrite the exposing functional once into coordinates, then stay in face-set normal form.
  obtain ⟨c, hc⟩ := strongDual_eq_dotProduct_fin l
  refine ⟨c, c ⬝ᵥ x₀, ?_, ?_⟩
  · intro x hxP
    calc
      c ⬝ᵥ x = l x := by rw [← hc x]
      _ ≤ l x₀ := hx₀F.2 x hxP
      _ = c ⬝ᵥ x₀ := hc x₀
  · exact toExposed_eq_face_set_of_mem hc hx₀F

end IsExposed

/-- Helper for Theorem 2.3: every equality face cut out by a valid inequality is exposed. -/
lemma isExposed_face_set_of_valid_inequality {n : ℕ} {P : Set (Fin n → ℝ)} {c : Fin n → ℝ}
    {δ : ℝ} (h_valid : is_valid_inequality P c δ) :
    IsExposed ℝ P (face_set P c δ) := by
  by_cases h_face_nonempty : (face_set P c δ).Nonempty
  · obtain ⟨x₀, hx₀_face⟩ := h_face_nonempty
    -- Once the equality slice is inhabited, it is the maximizer set of the defining functional.
    rw [face_set_eq_toExposed_of_mem h_valid hx₀_face]
    exact ContinuousLinearMap.toExposed.isExposed
  · rw [Set.not_nonempty_iff_eq_empty.mp h_face_nonempty]
    exact isExposed_empty

/-- Helper for Theorem 2.3: if `L` takes the value `1` on some vector of `D`, then
`D ⊓ ker L` has codimension one inside `D`. -/
theorem submodule_finrank_inf_ker_add_one_of_eval_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Submodule ℝ E) (L : E →ₗ[ℝ] ℝ) {w : E}
    (hwD : w ∈ D) (hw : L w = 1) :
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  have hne : L.domRestrict D ≠ 0 := by
    -- Evaluating the restricted map on the chosen witness prevents it from vanishing.
    intro hzero
    have hvalue := congrArg (fun f : D →ₗ[ℝ] ℝ ↦ f ⟨w, hwD⟩) hzero
    simpa [LinearMap.domRestrict_apply, hw] using hvalue
  have hdim :
      Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 =
        Module.finrank ℝ ↥D := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero (f := L.domRestrict D) hne
  have hmap :
      (LinearMap.ker (L.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hfin :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) =
        Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) := by
    -- The subtype embedding identifies the restricted kernel with the ambient kernel cut.
    rw [← hmap]
    simpa using
      (Submodule.finrank_map_subtype_eq (R := ℝ) (p := D)
        (q := LinearMap.ker (L.domRestrict D)))
  calc
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1
        = Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 := by
            rw [hfin]
    _ = Module.finrank ℝ ↥D := hdim

/-- Helper for Theorem 2.3: adding a vector with zero incident-edge sum at every vertex preserves
the traveling-salesman degree-constraint slice. -/
lemma add_mem_travelingSalesmanDegreeConstraintSet_of_incident_sum_zero
    {n : ℕ} {x w : complete_graph_edges n → ℝ}
    (hx : x ∈ travelingSalesmanDegreeConstraintSet n)
    (hw :
      ∀ i : Fin n,
        ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) i).map
            completeGraphEdgeEquiv.symm.toEmbedding).sum w = 0) :
    x + w ∈ travelingSalesmanDegreeConstraintSet n := by
  -- Rewrite the degree-slice membership into the shared incident-edge-sum owner.
  rw [mem_travelingSalesmanDegreeConstraintSet_iff] at hx ⊢
  intro i
  -- Each degree equation is preserved because the added vector contributes zero to that sum.
  calc
    ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) i).map
        completeGraphEdgeEquiv.symm.toEmbedding).sum (x + w)
        =
          ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) i).map
              completeGraphEdgeEquiv.symm.toEmbedding).sum x +
            ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) i).map
                completeGraphEdgeEquiv.symm.toEmbedding).sum w := by
              simp only [Pi.add_apply, Finset.sum_add_distrib]
    _ = 2 + 0 := by rw [hx i, hw i]
    _ = 2 := by ring
