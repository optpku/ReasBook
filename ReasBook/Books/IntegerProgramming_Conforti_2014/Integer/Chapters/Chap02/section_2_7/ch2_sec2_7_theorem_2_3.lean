import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_2_definition_1_17.PolynomialBound
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_21
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38.FacetTransport
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

noncomputable section

open Filter Asymptotics
open scoped BigOperators Matrix

/-- Helper for Theorem 2.3: swapping the endpoints does not change their cut-incidence value. -/
theorem cut_incidence_value_symm {n : ℕ} (W : Finset (Fin n)) (u v : Fin n) :
    (if (u ∈ W) = (v ∈ W) then (0 : ℝ) else 1) =
      (if (v ∈ W) = (u ∈ W) then (0 : ℝ) else 1) := by
  -- Both expressions test the same equality with its sides reversed.
  by_cases huv : (u ∈ W) = (v ∈ W) <;> simp [huv, eq_comm]

/-- Helper for Theorem 2.3: the incidence vector of the complete-graph cut determined by `W`. -/
def cutIncidenceVector {n : ℕ} (W : Finset (Fin n)) : complete_graph_edges n → ℝ :=
  fun e ↦
    Sym2.lift
      ⟨fun u v : Fin n ↦ if (u ∈ W) = (v ∈ W) then (0 : ℝ) else 1,
        cut_incidence_value_symm W⟩
      e.1

/-- Helper for Theorem 2.3: a cut coordinate is one exactly when its endpoints are on opposite
sides of the cut. -/
theorem cutIncidenceVector_apply_pair {n : ℕ} (W : Finset (Fin n)) (u v : Fin n)
    (h : ¬ (s(u, v) : Sym2 (Fin n)).IsDiag) :
    cutIncidenceVector W ⟨s(u, v), h⟩ = if (u ∈ W) = (v ∈ W) then 0 else 1 := by
  -- Evaluate the symmetric lift on the represented unordered pair.
  simp [cutIncidenceVector]

/-- Helper for Theorem 2.3: every cut coordinate is either zero or one. -/
lemma cutIncidenceVector_eq_zero_or_one {n : ℕ}
    (W : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector W e = 0 ∨ cutIncidenceVector W e = 1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      -- Concrete pair evaluation leaves only the endpoint-membership dichotomy.
      rw [cutIncidenceVector_apply_pair W u v he]
      by_cases huv : (u ∈ W) = (v ∈ W) <;> simp [huv]

/-- Helper for Theorem 2.3: cut vectors form the source-facing family used by the later rooted-cut
arguments. -/
def cutVertices (n : ℕ) : Set (complete_graph_edges n → ℝ) :=
  Set.range fun W : Finset (Fin n) ↦ cutIncidenceVector W

/-- Helper for Theorem 2.3: every member of the cut-vector family is pointwise zero or one. -/
lemma cutVertices_subset_zero_one_box {n : ℕ} :
    cutVertices n ⊆ {x : complete_graph_edges n → ℝ | ∀ e, x e = 0 ∨ x e = 1} := by
  intro x hx e
  obtain ⟨W, rfl⟩ := hx
  -- Apply the pointwise cut-coordinate dichotomy.
  exact cutIncidenceVector_eq_zero_or_one W e

/-- Helper for Theorem 2.3: an edge value is the xor of its two root-edge values. -/
lemma cutIncidenceVector_apply_pair_eq_of_root_values {n : ℕ} (W : Finset (Fin n))
    {r u v : Fin n} (hru : r ≠ u) (hrv : r ≠ v) (huv : u ≠ v) :
    cutIncidenceVector W ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using huv⟩ =
      if cutIncidenceVector W
            ⟨s(r, u), by simpa [Sym2.mk_isDiag_iff] using hru⟩ =
          cutIncidenceVector W
            ⟨s(r, v), by simpa [Sym2.mk_isDiag_iff] using hrv⟩ then
        0
      else
        1 := by
  -- Evaluate the three cut coordinates and split on the three endpoint memberships.
  rw [cutIncidenceVector_apply_pair W u v]
  rw [cutIncidenceVector_apply_pair W r u]
  rw [cutIncidenceVector_apply_pair W r v]
  by_cases hr : r ∈ W <;> by_cases hu : u ∈ W <;> by_cases hv : v ∈ W <;>
    simp [hr, hu, hv]

/-- Helper for Theorem 2.3: the edge from the distinguished root to a successor is non-diagonal. -/
lemma rootEdge_not_diag {n : ℕ} (u : Fin n) :
    ¬ (s((0 : Fin (n + 1)), u.succ) : Sym2 (Fin (n + 1))).IsDiag := by
  -- A successor is never the root.
  simp [Sym2.mk_isDiag_iff, eq_comm, Fin.succ_ne_zero]

/-- Helper for Theorem 2.3: the edge from the distinguished root to `u.succ`. -/
def rootEdge {n : ℕ} (u : Fin n) : complete_graph_edges (n + 1) :=
  ⟨s((0 : Fin (n + 1)), u.succ), rootEdge_not_diag u⟩

/-- Helper for Theorem 2.3: distinct successors determine a non-diagonal edge. -/
lemma succPairEdge_not_diag {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    ¬ (s(u.succ, v.succ) : Sym2 (Fin (n + 1))).IsDiag := by
  -- Injectivity of `Fin.succ` transports endpoint distinctness.
  rw [Sym2.mk_isDiag_iff]
  exact fun h ↦ huv (Fin.succ_injective _ h)

/-- Helper for Theorem 2.3: the edge between two distinct successor vertices. -/
def succPairEdge {n : ℕ} (u v : Fin n) (huv : u ≠ v) : complete_graph_edges (n + 1) :=
  ⟨s(u.succ, v.succ), succPairEdge_not_diag huv⟩

/-- Helper for Theorem 2.3: a successor-pair coordinate is the xor of the corresponding root-edge
coordinates. -/
lemma cutIncidenceVector_apply_succPair_eq_of_root_values {n : ℕ}
    (W : Finset (Fin (n + 1))) {u v : Fin n} (huv : u ≠ v) :
    cutIncidenceVector W (succPairEdge u v huv) =
      if cutIncidenceVector W (rootEdge u) = cutIncidenceVector W (rootEdge v) then 0 else 1 := by
  -- Specialize the root-xor formula at the distinguished vertex `0`.
  simpa [succPairEdge, rootEdge] using
    (cutIncidenceVector_apply_pair_eq_of_root_values W
      (r := (0 : Fin (n + 1))) (u := u.succ) (v := v.succ)
      (Ne.symm (Fin.succ_ne_zero u))
      (Ne.symm (Fin.succ_ne_zero v))
      (fun h ↦ huv (Fin.succ_injective _ h)))

/-- Helper for Theorem 2.3: the coefficient vector `c` defines the linear functional
`x ↦ c ⬝ᵥ x` on a finite coordinate space. -/
abbrev dotProductLinearMap {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] ℝ :=
  dotProductEquiv ℝ ι c

/-- Helper for Theorem 2.3: `dotProductLinearMap c` evaluates as the coordinate dot product
with `c`. -/
@[simp] theorem dotProductLinearMap_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c x : ι → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  rfl

/-- Helper for Theorem 2.3: the strong-dual functional associated with `c` is the corresponding
coordinate dot product. -/
noncomputable def dotProductStrongDual
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    StrongDual ℝ (ι → ℝ) :=
  ∑ i, c i • ContinuousLinearMap.proj i

/-- Helper for Theorem 2.3: `dotProductStrongDual c` evaluates as the coordinate dot product with
`c`. -/
lemma dotProductStrongDual_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c x : ι → ℝ) :
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

/-- Helper for Theorem 2.3: a linear functional is determined by its kernel together with one
transverse vector where it takes the value `1`. -/
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

/-- Helper for Theorem 2.3: if every point of `F` lies on the same level set of a linear
functional, then every direction vector of `affineSpan ℝ F` lies in the functional's kernel. -/
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
def linear_hyperplane
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (δ : ℝ) : Set (ι → ℝ) :=
  {x | c ⬝ᵥ x = δ}

/-- Helper for Theorem 2.3: membership in `linear_hyperplane c δ` is exactly the defining
dot-product equation. -/
theorem mem_linear_hyperplane_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι] {c x : ι → ℝ} {δ : ℝ} :
    x ∈ linear_hyperplane c δ ↔ c ⬝ᵥ x = δ := by
  rfl

/-- Helper for Theorem 2.3: the equality section of the valid inequality `c ⬝ᵥ x ≤ δ` on `P`. -/
def face_set
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Set (ι → ℝ)) (c : ι → ℝ) (δ : ℝ) : Set (ι → ℝ) :=
  P ∩ linear_hyperplane c δ

/-- Helper for Theorem 2.3: membership in `face_set P c δ` means lying in `P` and satisfying
`c ⬝ᵥ x = δ`. -/
theorem mem_face_set_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Set (ι → ℝ)} {c x : ι → ℝ} {δ : ℝ} :
    x ∈ face_set P c δ ↔ x ∈ P ∧ c ⬝ᵥ x = δ := by
  simp [face_set, linear_hyperplane]

/-- Helper for Theorem 2.3: when a valid inequality is attained, its equality face is the exposed
set of the corresponding dot-product functional. -/
lemma face_set_eq_toExposed_of_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Set (ι → ℝ)} {c x₀ : ι → ℝ} {δ : ℝ}
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
lemma isExposed_face_set_of_valid_inequality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Set (ι → ℝ)} {c : ι → ℝ}
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
    simp [LinearMap.domRestrict_apply, hw] at hvalue
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
    simp
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

/-- The canonical `Fin`-coordinate view of `travelingSalesmanPolytope n`, obtained by reindexing
the native edge-coordinate space along `Fintype.equivFin (complete_graph_edges n)`. -/
noncomputable def travelingSalesmanPolytopeReindexed (n : ℕ) :
    Set (Fin (Fintype.card (complete_graph_edges n)) → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges n))).symm ''
    travelingSalesmanPolytope n

/-- Membership in `travelingSalesmanPolytopeReindexed n` means that the corresponding native
edge-coordinate vector lies in `travelingSalesmanPolytope n`. -/
theorem mem_travelingSalesmanPolytopeReindexed_iff
    {n : ℕ} {y : Fin (Fintype.card (complete_graph_edges n)) → ℝ} :
    y ∈ travelingSalesmanPolytopeReindexed n ↔
      (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges n))) y ∈
        travelingSalesmanPolytope n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · intro hy
    refine
      ⟨(LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges n))) y, hy, ?_⟩
    exact LinearEquiv.symm_apply_apply _ y

/-- Helper for Theorem 2.3: every reindexed traveling salesman polytope contains the incidence
vector of the identity Hamiltonian tour. -/
lemma travelingSalesmanPolytopeReindexed_nonempty (n : ℕ) :
    (travelingSalesmanPolytopeReindexed n).Nonempty := by
  let e := LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges n))
  let x : complete_graph_edges n → ℝ := hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  have hx_native : x ∈ travelingSalesmanPolytope n := by
    -- Every Hamiltonian-tour incidence vector is a vertex of the defining convex hull.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self _)
  refine ⟨e.symm x, ?_⟩
  -- Reindex the native Hamiltonian-tour vertex into the canonical `Fin` coordinates.
  have hx_reindexed : e (e.symm x) ∈ travelingSalesmanPolytope n := by
    rw [LinearEquiv.apply_symm_apply]
    exact hx_native
  exact (mem_travelingSalesmanPolytopeReindexed_iff).2 hx_reindexed

/-- Helper for Theorem 2.3: reindexing preserves the fact that the traveling salesman polytope is
a polytope. -/
lemma travelingSalesmanPolytopeReindexed_isPolytope (n : ℕ) :
    (travelingSalesmanPolytopeReindexed n).IsPolytope ℝ := by
  let e :
      (complete_graph_edges n → ℝ) ≃L[ℝ] (Fin (Fintype.card (complete_graph_edges n)) → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ
      (Fintype.equivFin (complete_graph_edges n))).symm.toContinuousLinearEquiv
  have hnative : (travelingSalesmanPolytope n).IsPolytope ℝ := by
    -- The native TSP polytope is the convex hull of finitely many Hamiltonian-tour vertices.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact ⟨Set.range (fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_tour_incidence_vector σ),
      Set.finite_range _, rfl⟩
  -- Transport the finite-vertex presentation through the coordinate equivalence.
  simpa [travelingSalesmanPolytopeReindexed, e] using
    isPolytope_image_continuousLinearEquiv e hnative

/-- Helper for Theorem 2.3: the subtour-elimination left-hand side is the cut-incidence dot
product. Keeping this owner local avoids the broken Chapter 7 import chain while preserving the
proof surface used later in the file. -/
def subtour_elimination_value
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) : ℝ :=
  cutIncidenceVector S ⬝ᵥ x

/-- Helper for Theorem 2.3: `subtour_elimination_value` unfolds to the corresponding cut-incidence
dot product. -/
theorem subtour_elimination_value_eq_dotProduct
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = cutIncidenceVector S ⬝ᵥ x :=
  rfl

/-- Helper for Theorem 2.3: the subtour face is the traveling-salesman equality face cut out by
the canonical cut functional. -/
def subtour_elimination_face (n : ℕ) (S : Finset (Fin n)) :
    Set (complete_graph_edges n → ℝ) :=
  {x | x ∈ travelingSalesmanPolytope n ∧ subtour_elimination_value S x = 2}

/-- Helper for Theorem 2.3: membership in the subtour face means TSP membership together with
equality in the cut-incidence equation. -/
theorem mem_subtour_elimination_face_iff
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧ subtour_elimination_value S x = 2 :=
  Iff.rfl

/-- Helper for Theorem 2.3: the subtour face can also be read as the equality set of the negated
cut-incidence inequality. -/
theorem mem_subtour_elimination_face_iff_neg_cutIncidence
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧ (-cutIncidenceVector S) ⬝ᵥ x = -2 := by
  -- Rewriting the local owner back to the dot-product normal form reduces the claim to negating
  -- both sides of the equality.
  rw [mem_subtour_elimination_face_iff, subtour_elimination_value_eq_dotProduct]
  constructor
  · rintro ⟨hx, hxeq⟩
    exact ⟨hx, by rw [neg_dotProduct, hxeq]⟩
  · rintro ⟨hx, hxeq⟩
    have hxeq' : cutIncidenceVector S ⬝ᵥ x = 2 := by
      simpa [neg_dotProduct] using congrArg Neg.neg hxeq
    exact ⟨hx, hxeq'⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the subtour face is the
canonical equality face for the negated cut inequality. -/
private lemma subtourEliminationFace_eq_faceSet
    {n : ℕ} (S : Finset (Fin n)) :
    subtour_elimination_face n S =
      face_set (travelingSalesmanPolytope n) (-cutIncidenceVector S) (-2) := by
  -- Put both descriptions into their common membership normal form.
  ext x
  rw [mem_subtour_elimination_face_iff_neg_cutIncidence, mem_face_set_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: every direction of an
inhabited subtour face is an ambient TSP direction annihilated by its cut functional. -/
private lemma subtourFaceDirection_le_ambientInfCutKernel
    {n : ℕ} (S : Finset (Fin n))
    (hface : (subtour_elimination_face n S).Nonempty) :
    (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
      (affineSpan ℝ (travelingSalesmanPolytope n)).direction ⊓
        LinearMap.ker (dotProductLinearMap (cutIncidenceVector S)) := by
  obtain ⟨x₀, hx₀⟩ := hface
  have hface_subset :
      subtour_elimination_face n S ⊆ travelingSalesmanPolytope n := by
    intro x hx
    exact (mem_subtour_elimination_face_iff S x).1 hx |>.1
  have hambient :
      (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
        (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
    -- Affine-span monotonicity supplies the ambient-direction component.
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hface_subset)
  have hlevel :
      ∀ ⦃x : complete_graph_edges n → ℝ⦄,
        x ∈ subtour_elimination_face n S →
          dotProductLinearMap (cutIncidenceVector S) x = 2 := by
    intro x hx
    simpa [dotProductLinearMap_apply, subtour_elimination_value_eq_dotProduct] using
      (mem_subtour_elimination_face_iff S x).1 hx |>.2
  have hkernel :
      (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
        LinearMap.ker (dotProductLinearMap (cutIncidenceVector S)) := by
    -- Differences of points on one cut level have zero cut evaluation.
    exact affineSpan_direction_le_ker_of_forall_eq hx₀ hlevel
  intro v hv
  exact ⟨hambient hv, hkernel hv⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: nonemptiness, validity, and
the codimension-one direction equation assemble the subtour equality slice into a facet. -/
private lemma subtourEliminationFace_isFacetOf_of_finrank
    {n : ℕ} (S : Finset (Fin n))
    (hface : (subtour_elimination_face n S).Nonempty)
    (hvalid :
      is_valid_inequality (travelingSalesmanPolytope n) (-cutIncidenceVector S) (-2))
    (hfinrank :
      Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope n)).direction) :
    IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n S) := by
  rw [isFacetOf_iff]
  refine ⟨hface, ?_, hfinrank⟩
  -- The valid inequality exposes precisely its equality slice.
  rw [subtourEliminationFace_eq_faceSet S]
  exact isExposed_face_set_of_valid_inequality hvalid

/-- Helper for Theorem 2.3: summing a single-edge basis vector over the incident complete-graph
edge coordinates at `i` just tests whether the chosen edge is incident to `i`. -/
lemma incidentEdgeSum_single_eq_indicator
    {n : ℕ} (i : Fin n) (e : complete_graph_edges n) (a : ℝ) :
    ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) i).map
        completeGraphEdgeEquiv.symm.toEmbedding).sum (Pi.single e a) =
      if i ∈ (e : Sym2 (Fin n)) then a else 0 := by
  have hfilter :
      ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) i).map
          completeGraphEdgeEquiv.symm.toEmbedding) =
        Finset.univ.filter fun e' : complete_graph_edges n ↦ i ∈ (e' : Sym2 (Fin n)) := by
    -- Normalize the graph-level incident-edge owner to the coordinate filter.
    ext e'
    constructor
    · intro he
      have hmem : i ∈ (e' : Sym2 (Fin n)) :=
        mem_completeGraph_incidentEdgeFinset_iff.1 he
      simpa [Finset.mem_filter] using hmem
    · intro he
      exact mem_completeGraph_incidentEdgeFinset_iff.2
        (by simpa [Finset.mem_filter] using he)
  rw [hfilter, Finset.sum_filter]
  by_cases hi : i ∈ (e : Sym2 (Fin n))
  · -- The chosen coordinate is the unique nonzero term of the filtered basis vector.
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
    · simp [hi]
    · intro e' _ he'
      by_cases hie' : i ∈ (e' : Sym2 (Fin n))
      · simp [he', hie']
      · simp [hie']
  · -- Off the chosen endpoint pair every filtered basis contribution vanishes.
    rw [if_neg hi]
    refine Finset.sum_eq_zero ?_
    intro e' he'
    by_cases hie' : i ∈ (e' : Sym2 (Fin n))
    · have he'ne : e' ≠ e := by
        intro heq
        apply hi
        simpa [heq] using hie'
      simp [hie', he'ne]
    · simp [hie']

/-- Helper for Theorem 2.3: two distinct vertices determine a complete-graph edge coordinate. -/
private lemma subtourEdge_notDiag {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    ¬ (s(u, v) : Sym2 (Fin n)).IsDiag := by
  -- Diagonality of an unordered pair is exactly equality of its endpoints.
  simpa [Sym2.mk_isDiag_iff] using huv

/-- Helper for Theorem 2.3: the complete-graph edge joining two distinct vertices. -/
private def subtourEdge {n : ℕ} (u v : Fin n) (huv : u ≠ v) : complete_graph_edges n :=
  ⟨s(u, v), subtourEdge_notDiag huv⟩

/-- Helper for Theorem 2.3: membership in a concrete edge is endpoint membership. -/
private lemma mem_subtourEdge_iff {n : ℕ} (u v z : Fin n) (huv : u ≠ v) :
    z ∈ ((subtourEdge u v huv : complete_graph_edges n) : Sym2 (Fin n)) ↔ z = u ∨ z = v := by
  -- Unfold the unordered pair and use the standard membership computation.
  simp [subtourEdge, Sym2.mem_iff]

/-- Helper for Theorem 2.3: the size hypotheses provide two distinct vertices on each side of
the cut. -/
private lemma exists_two_vertices_on_each_shore
    {n : ℕ} (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card) (hS_upper : S.card ≤ n - 2) :
    ∃ a b i j : Fin n,
      a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ i ∉ S ∧ j ∉ S ∧ i ≠ j := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨b, hbErase⟩ : (S.erase a).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  have hb : b ∈ S := (Finset.mem_erase.mp hbErase).2
  have hab : a ≠ b := (Finset.mem_erase.mp hbErase).1.symm
  let Sc : Finset (Fin n) := Sᶜ
  have hScCard : Sc.card = n - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hScLower : 2 ≤ Sc.card := by
    rw [hScCard]
    omega
  obtain ⟨i, hiSc⟩ := Finset.card_pos.mp (by omega : 0 < Sc.card)
  obtain ⟨j, hjErase⟩ : (Sc.erase i).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hiSc]; omega)
  have hjSc : j ∈ Sc := (Finset.mem_erase.mp hjErase).2
  have hi : i ∉ S := by simpa [Sc] using hiSc
  have hj : j ∉ S := by simpa [Sc] using hjSc
  have hij : i ≠ j := (Finset.mem_erase.mp hjErase).1.symm
  exact ⟨a, b, i, j, ha, hb, hab, hi, hj, hij⟩

/-- Helper for Theorem 2.3: extending permutations on two consecutive `Fin` blocks gives a
permutation of the concatenated block. -/
def splitBlockPerm {m n : ℕ}
    (ρ₁ : Equiv.Perm (Fin m))
    (ρ₂ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr ρ₁ ρ₂)).trans finSumFinEquiv

/-- Helper for Theorem 2.3: `splitBlockPerm` acts by `ρ₁` on the left block. -/
theorem splitBlockPerm_apply_castAdd
    {m n : ℕ}
    (ρ₁ : Equiv.Perm (Fin m))
    (ρ₂ : Equiv.Perm (Fin n))
    (i : Fin m) :
    splitBlockPerm ρ₁ ρ₂ (Fin.castAdd n i) = Fin.castAdd n (ρ₁ i) := by
  -- The sum equivalence preserves the left summand.
  simp [splitBlockPerm]

/-- Helper for Theorem 2.3: `splitBlockPerm` acts by `ρ₂` on the right block. -/
theorem splitBlockPerm_apply_natAdd
    {m n : ℕ}
    (ρ₁ : Equiv.Perm (Fin m))
    (ρ₂ : Equiv.Perm (Fin n))
    (i : Fin n) :
    splitBlockPerm ρ₁ ρ₂ (Fin.natAdd m i) = Fin.natAdd m (ρ₂ i) := by
  -- The sum equivalence preserves the right summand.
  simp [splitBlockPerm]

/-- Helper for Theorem 2.3: every shore can be enumerated first by a permutation of the ambient
vertex set. -/
private lemma exists_subtour_block_order {n : ℕ} (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, i ∈ S ↔ (σ i : ℕ) < S.card := by
  classical
  let splitIndex : Fin n ≃ ↥S ⊕ {i // i ∉ S} :=
    (Equiv.sumCompl fun i : Fin n ↦ i ∈ S).symm
  let shoreIndex : ↥S ≃ Fin S.card := Finset.equivFin S
  let complSubtype : {i : Fin n // i ∉ S} ≃ ↥(Sᶜ) :=
    { toFun := fun i ↦
        match i with
        | ⟨j, hj⟩ => ⟨j, by simpa [Finset.mem_compl] using hj⟩
      invFun := fun i ↦
        match i with
        | ⟨j, hj⟩ => ⟨j, by simpa [Finset.mem_compl] using hj⟩
      left_inv := by
        intro i
        cases i
        rfl
      right_inv := by
        intro i
        cases i
        rfl }
  let complIndexKc : ↥(Sᶜ) ≃ Fin (n - S.card) :=
    Finset.equivFinOfCardEq (by simp [Finset.card_compl, Fintype.card_fin])
  let complIndex : {i : Fin n // i ∉ S} ≃ Fin (n - S.card) :=
    complSubtype.trans complIndexKc
  have hcard : S.card + (n - S.card) = n := by
    simpa [Fintype.card_fin] using Nat.add_sub_of_le (Finset.card_le_univ S)
  let σ : Equiv.Perm (Fin n) :=
    ((splitIndex.trans (Equiv.sumCongr shoreIndex complIndex)).trans finSumFinEquiv).trans
      (Fin.castOrderIso hcard).toEquiv
  refine ⟨σ, ?_⟩
  intro i
  constructor
  · intro hi
    -- A shore vertex lands in the initial summand of the concatenated index.
    simp [σ, splitIndex, shoreIndex, complSubtype, complIndexKc, complIndex, hi]
  · intro hiσ
    by_contra hiS
    have hσi :
        (σ i : ℕ) = S.card + ((complIndex ⟨i, hiS⟩ : Fin (n - S.card)) : ℕ) := by
      simp [σ, splitIndex, shoreIndex, complSubtype, complIndexKc, complIndex, hiS]
    omega

/-- Helper for Theorem 2.3: on a tour whose position-membership predicate is an initial segment,
a path edge crosses the shore exactly at the segment boundary. -/
private lemma cutIncidenceVector_pathEdgeOfIndex_of_initialSegment
    {n : ℕ} (S : Finset (Fin n)) (p : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (k : Fin (n - 1)) :
    cutIncidenceVector S (path_edge_of_index σ k) =
      if ((k : ℕ) < p) = ((k : ℕ) + 1 < p) then 0 else 1 := by
  -- Unfolding one path edge exposes its consecutive positions; the block-order hypothesis then
  -- rewrites both endpoint memberships.
  unfold path_edge_of_index
  rw [cutIncidenceVector_apply_pair]
  simp only [hσ]
  rfl

/-- Helper for Theorem 2.3: the internal path of a block-ordered tour crosses the shore once. -/
private lemma blockOrderedPath_cutSum_eq_one
    {n : ℕ} (S : Finset (Fin n)) (p : ℕ) (σ : Equiv.Perm (Fin n))
    (hpLower : 1 ≤ p) (hpUpper : p ≤ n - 1)
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    (hamiltonian_path_edge_finset σ).sum (cutIncidenceVector S) = 1 := by
  let boundary : Fin (n - 1) := ⟨p - 1, by omega⟩
  rw [hamiltonian_path_edge_finset, Finset.sum_image]
  · rw [Finset.sum_eq_single boundary]
    · rw [cutIncidenceVector_pathEdgeOfIndex_of_initialSegment S p σ hσ]
      simp [boundary]
      omega
    · intro k hk hkNe
      rw [cutIncidenceVector_pathEdgeOfIndex_of_initialSegment S p σ hσ]
      have hkValNe : k.1 ≠ p - 1 := by
        intro hkVal
        apply hkNe
        exact Fin.ext hkVal
      by_cases hkp : k.1 < p
      · have hkSucc : k.1 + 1 < p := by omega
        simp [hkp, hkSucc]
      · have hkSucc : ¬ k.1 + 1 < p := by omega
        simp [hkp, hkSucc]
    · simp
  · intro a ha b hb hab
    exact path_edge_of_index_injective σ hab

/-- Helper for Theorem 2.3: dotting a cut vector with a tour incidence vector is the sum of the
cut coordinates over the tour-edge finset. -/
private lemma cutIncidenceVector_dot_tourIncidence
    {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    cutIncidenceVector S ⬝ᵥ hamiltonian_tour_incidence_vector σ =
      (hamiltonian_tour_edge_finset σ).sum (cutIncidenceVector S) := by
  -- The tour vector is the indicator of its edge finset.
  calc
    cutIncidenceVector S ⬝ᵥ hamiltonian_tour_incidence_vector σ =
        ∑ e : complete_graph_edges n,
          if e ∈ hamiltonian_tour_edge_finset σ then cutIncidenceVector S e else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge]
    _ = (hamiltonian_tour_edge_finset σ).sum (cutIncidenceVector S) := by
      rw [← Finset.sum_filter]
      simp

/-- Helper for Theorem 2.3: the internal edges of the shore `S`, in complete-graph
coordinates. -/
private def subtourInternalEdges {n : ℕ} (S : Finset (Fin n)) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S

/-- Helper for Theorem 2.3: the canonical endpoints of a complete-graph edge are distinct. -/
private lemma completeGraphEdge_out_ne {n : ℕ} (e : complete_graph_edges n) :
    e.1.out.1 ≠ e.1.out.2 := by
  -- Equality of the canonical endpoints would make the underlying unordered pair diagonal.
  intro h
  apply e.2
  rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
  exact h

/-- Helper for Theorem 2.3: the cut coordinate at an edge is read from its canonical
endpoints. -/
private lemma cutIncidenceVector_apply_out {n : ℕ} (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    cutIncidenceVector S e =
      if (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) then 0 else 1 := by
  -- Replace the unordered edge by its canonical representative before applying the pair formula.
  have hdiag : ¬ (s(e.1.out.1, e.1.out.2) : Sym2 (Fin n)).IsDiag := by
    simpa [Sym2.mk_isDiag_iff] using completeGraphEdge_out_ne e
  have hpair := cutIncidenceVector_apply_pair S e.1.out.1 e.1.out.2 hdiag
  simpa [e.1.out_eq] using hpair

/-- Helper for Theorem 2.3: filtering two distinct endpoints by a shore has the expected
zero-one-two cardinality. -/
private lemma pairFilterCard_of_ne
    {n : ℕ} (a b : Fin n) (hab : a ≠ b) (S : Finset (Fin n)) :
    (((({a, b} : Finset (Fin n)).filter fun v ↦ v ∈ S).card : ℕ) : ℝ) =
      if a ∈ S ∧ b ∈ S then 2 else if a ∈ S ∨ b ∈ S then 1 else 0 := by
  -- Compute the filtered pair in each endpoint-membership case.
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · have hfilter : ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ S) = {a, b} := by
        ext v
        constructor
        · intro hv
          exact (Finset.mem_filter.mp hv).1
        · intro hv
          refine Finset.mem_filter.mpr ⟨hv, ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · simp [ha]
          · rw [Finset.mem_singleton.mp hv']
            simp [hb]
      rw [hfilter]
      simp [ha, hb, hab]
    · have hfilter : ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ S) = {a} := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · simp
          · exfalso
            rw [Finset.mem_singleton.mp hv'] at hvS
            exact hb hvS
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp
          · simpa using ha
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ S
    · have hfilter : ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ S) = {b} := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with hv' | hvb
          · exfalso
            exact ha (hv' ▸ hvS)
          · simpa using hvb
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp
          · simpa using hb
      rw [hfilter]
      simp [ha, hb]
    · have hfilter : ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ S) = ∅ := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact (ha hvS).elim
          · exact (hb (by rw [Finset.mem_singleton.mp hv'] at hvS; exact hvS)).elim
        · intro hv
          simp at hv
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Theorem 2.3: summing over shore endpoints counts an internal edge twice and a
cut edge once. -/
private lemma endpointContribution_eq_internal_add_cut
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n)
    (x : complete_graph_edges n → ℝ) :
    S.sum (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) =
      (if e ∈ subtourInternalEdges S then 2 * x e else 0) +
        cutIncidenceVector S e * x e := by
  -- Rewrite the endpoint sum as a filtered-cardinality multiple and classify the two endpoints.
  have hfilter :
      S.filter (fun v ↦ v ∈ (e : Sym2 (Fin n))) =
        ((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ S) := by
    ext v
    simp [Sym2.mem_toFinset, and_comm]
  have hout : ((e : Sym2 (Fin n)).toFinset) = {e.1.out.1, e.1.out.2} := by
    calc
      _ = (s(e.1.out.1, e.1.out.2)).toFinset := by simp [e.1.out_eq]
      _ = _ := Sym2.toFinset_mk_eq
  calc
    S.sum (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) =
        (S.filter fun v ↦ v ∈ (e : Sym2 (Fin n))).sum (fun _ ↦ x e) := by
          rw [Finset.sum_filter]
    _ = (((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ S).sum (fun _ ↦ x e)) := by
          rw [hfilter]
    _ = (((((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ S).card : ℕ) : ℝ) * x e) := by
          simp [Finset.sum_const, mul_comm]
    _ = (if e ∈ subtourInternalEdges S then 2 * x e else 0) +
          cutIncidenceVector S e * x e := by
          rw [hout, pairFilterCard_of_ne e.1.out.1 e.1.out.2
            (completeGraphEdge_out_ne e) S, cutIncidenceVector_apply_out]
          by_cases ha : e.1.out.1 ∈ S <;> by_cases hb : e.1.out.2 ∈ S <;>
            simp [subtourInternalEdges, ha, hb]

/-- Helper for Theorem 2.3: summing the degree equations over `S` gives the usual internal-edge
and cut double-count identity. -/
private lemma sumIncidentEdges_eq_twiceInternal_add_cut
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    ∑ v ∈ S,
        ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).map
          completeGraphEdgeEquiv.symm.toEmbedding).sum x =
      2 * (subtourInternalEdges S).sum x + dotProduct (cutIncidenceVector S) x := by
  -- Swap the vertex and edge sums, then use the endpoint contribution formula coordinatewise.
  calc
    ∑ v ∈ S,
          ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).map
            completeGraphEdgeEquiv.symm.toEmbedding).sum x =
        ∑ v ∈ S, ∑ e : complete_graph_edges n,
          if v ∈ (e : Sym2 (Fin n)) then x e else 0 := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            have hincident :
                (incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).map
                    completeGraphEdgeEquiv.symm.toEmbedding =
                  Finset.univ.filter fun e : complete_graph_edges n ↦
                    v ∈ (e : Sym2 (Fin n)) := by
              ext e
              constructor
              · intro he
                have hmem : v ∈ (e : Sym2 (Fin n)) :=
                  mem_completeGraph_incidentEdgeFinset_iff.1 he
                simpa using hmem
              · intro he
                exact mem_completeGraph_incidentEdgeFinset_iff.2 (by simpa using he)
            rw [hincident, Finset.sum_filter]
    _ = ∑ e : complete_graph_edges n,
          ∑ v ∈ S, (if v ∈ (e : Sym2 (Fin n)) then x e else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ e : complete_graph_edges n,
          ((if e ∈ subtourInternalEdges S then 2 * x e else 0) +
            cutIncidenceVector S e * x e) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            exact endpointContribution_eq_internal_add_cut S e x
    _ = (subtourInternalEdges S).sum (fun e ↦ 2 * x e) +
          dotProduct (cutIncidenceVector S) x := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.sum_filter]
              have hfilter :
                  (Finset.univ : Finset (complete_graph_edges n)).filter
                      (fun e ↦ e ∈ subtourInternalEdges S) = subtourInternalEdges S := by
                ext e
                simp
              rw [hfilter]
    _ = 2 * (subtourInternalEdges S).sum x + dotProduct (cutIncidenceVector S) x := by
            rw [← Finset.mul_sum]

/-- Helper for Theorem 2.3: the cut sum of a Hamiltonian-tour indicator is the cardinality of
the tour edges with cut coordinate one. -/
private lemma cutTourSum_eq_card
    {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    (hamiltonian_tour_edge_finset σ).sum (cutIncidenceVector S) =
      (((hamiltonian_tour_edge_finset σ).filter
        (fun e ↦ cutIncidenceVector S e = 1)).card : ℕ) := by
  -- Replace each zero-one cut coordinate by the indicator of its being one.
  calc
    (hamiltonian_tour_edge_finset σ).sum (cutIncidenceVector S) =
        ∑ e ∈ hamiltonian_tour_edge_finset σ,
          if cutIncidenceVector S e = 1 then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            rcases cutIncidenceVector_eq_zero_or_one S e with hzero | hone
            · simp [hzero]
            · simp [hone]
    _ = (((hamiltonian_tour_edge_finset σ).filter
          (fun e ↦ cutIncidenceVector S e = 1)).card : ℕ) := by
            simp

/-- Helper for Theorem 2.3: summing a tour indicator on any edge set counts its tour edges. -/
private lemma tourIndicatorSum_eq_card_inter
    {n : ℕ} (T : Finset (complete_graph_edges n)) (σ : Equiv.Perm (Fin n)) :
    T.sum (hamiltonian_tour_incidence_vector σ) =
      (((T ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- Rewrite the zero-one tour vector as a filtered constant sum.
  calc
    T.sum (hamiltonian_tour_incidence_vector σ) =
        T.sum (fun e ↦ if e ∈ hamiltonian_tour_edge_finset σ then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge]
    _ = (T.filter fun e ↦ e ∈ hamiltonian_tour_edge_finset σ).sum
          (fun _ ↦ (1 : ℝ)) := by
          rw [Finset.sum_filter]
    _ = (((T ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
          have hfilter : T.filter (fun e ↦ e ∈ hamiltonian_tour_edge_finset σ) =
              T ∩ hamiltonian_tour_edge_finset σ := by
            ext e
            simp [Finset.mem_inter]
          rw [hfilter]
          simp

/-- Helper for Theorem 2.3: the cut value of a path edge compares membership of its two explicit
consecutive positions. -/
private lemma cutIncidenceVector_pathEdgeOfIndex
    {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    cutIncidenceVector S (path_edge_of_index σ k) =
      if (σ ⟨k.1, by omega⟩ ∈ S) = (σ ⟨k.1 + 1, by omega⟩ ∈ S) then 0 else 1 := by
  -- Expose exactly one path edge, then apply the pair evaluation lemma.
  change cutIncidenceVector S
      ⟨s(σ ⟨k.1, by omega⟩, σ ⟨k.1 + 1, by omega⟩), _⟩ = _
  rw [cutIncidenceVector_apply_pair]

/-- Helper for Theorem 2.3: if every consecutive edge has cut value zero, all positions of the
permutation lie on the same side of the cut. -/
private lemma all_positions_same_side_of_path_cut_zero
    {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hzero : ∀ k : Fin (n - 1), cutIncidenceVector S (path_edge_of_index σ k) = 0) :
    ∀ m : ℕ, ∀ hm : m < n, σ ⟨m, hm⟩ ∈ S ↔ σ ⟨0, by omega⟩ ∈ S := by
  intro m
  induction m with
  | zero =>
      intro hm
      rfl
  | succ m ih =>
      intro hm
      have hm' : m < n := by omega
      let k : Fin (n - 1) := ⟨m, by omega⟩
      have hedge := hzero k
      have hedge' :
          (if (σ ⟨m, hm'⟩ ∈ S) = (σ ⟨m + 1, hm⟩ ∈ S) then (0 : ℝ) else 1) = 0 := by
        -- The explicit endpoint view avoids the private position names in `path_edge_of_index`.
        simpa [k] using (cutIncidenceVector_pathEdgeOfIndex S σ k).symm.trans hedge
      have hstep : σ ⟨m, hm'⟩ ∈ S ↔ σ ⟨m + 1, hm⟩ ∈ S := by
        by_cases hl : σ ⟨m, hm'⟩ ∈ S <;>
          by_cases hr : σ ⟨m + 1, hm⟩ ∈ S <;> simp_all
      exact hstep.symm.trans (ih hm')

/-- Helper for Theorem 2.3: a Hamiltonian tour crossing a nonempty proper shore has a positive
number of cut edges. -/
private lemma cutTourCard_pos
    {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hSnonempty : S.Nonempty) (hSproper : S.card < n) :
    0 < ((hamiltonian_tour_edge_finset σ).filter
      (fun e ↦ cutIncidenceVector S e = 1)).card := by
  by_contra hnot
  have hempty : (hamiltonian_tour_edge_finset σ).filter
      (fun e ↦ cutIncidenceVector S e = 1) = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hnot)
  have hpathZero : ∀ k : Fin (n - 1),
      cutIncidenceVector S (path_edge_of_index σ k) = 0 := by
    intro k
    rcases cutIncidenceVector_eq_zero_or_one S (path_edge_of_index σ k) with hzero | hone
    · exact hzero
    · have hpath : path_edge_of_index σ k ∈ hamiltonian_path_edge_finset σ := by
        simp [hamiltonian_path_edge_finset]
      have htour : path_edge_of_index σ k ∈ hamiltonian_tour_edge_finset σ := by
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hn
        rw [Nat.add_comm] at hr
        subst n
        simp [hamiltonian_tour_edge_finset, hpath]
      have : path_edge_of_index σ k ∈
          (hamiltonian_tour_edge_finset σ).filter
            (fun e ↦ cutIncidenceVector S e = 1) := by simp [htour, hone]
      simp [hempty] at this
  have hsame := all_positions_same_side_of_path_cut_zero hn S σ hpathZero
  obtain ⟨u, hu⟩ := hSnonempty
  have houtside : ∃ v : Fin n, v ∉ S := by
    by_contra h
    push Not at h
    have hSuniv : S = Finset.univ := by ext v; simp [h v]
    have : S.card = n := by simp [hSuniv]
    omega
  obtain ⟨v, hv⟩ := houtside
  have hzeroMem : σ ⟨0, by omega⟩ ∈ S := by
    have hu' : σ ⟨(σ.symm u).1, (σ.symm u).2⟩ ∈ S := by simpa using hu
    exact (hsame (σ.symm u).1 (σ.symm u).2).mp hu'
  have hv' : σ ⟨(σ.symm v).1, (σ.symm v).2⟩ ∈ S :=
    (hsame (σ.symm v).1 (σ.symm v).2).mpr hzeroMem
  exact hv (by simpa using hv')

/-- Helper for Theorem 2.3: every tour generator crosses a proper nontrivial shore at least
twice. -/
private lemma hamiltonianTour_cutValue_ge_two
    {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card) (hS_upper : S.card ≤ n - 2)
    (σ : Equiv.Perm (Fin n)) :
    2 ≤ dotProduct (cutIncidenceVector S) (hamiltonian_tour_incidence_vector σ) := by
  have hxpoly : hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanPolytope n := by
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self σ)
  have hxdegree : hamiltonian_tour_incidence_vector σ ∈
      travelingSalesmanDegreeConstraintSet n := by
    have hspan := affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n (by omega)
    rw [← hspan]
    exact subset_affineSpan ℝ _ hxpoly
  have hdegree := mem_travelingSalesmanDegreeConstraintSet_iff.mp hxdegree
  have hdegreeSum :
      ∑ v ∈ S,
          ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).map
            completeGraphEdgeEquiv.symm.toEmbedding).sum
              (hamiltonian_tour_incidence_vector σ) = 2 * (S.card : ℝ) := by
    calc
      _ = ∑ v ∈ S, (2 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        exact hdegree v
      _ = 2 * (S.card : ℝ) := by simp [mul_comm]
  have hcount := sumIncidentEdges_eq_twiceInternal_add_cut S
    (hamiltonian_tour_incidence_vector σ)
  have hinternal : (subtourInternalEdges S).sum (hamiltonian_tour_incidence_vector σ) =
      ((((subtourInternalEdges S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
    -- A tour incidence vector is the indicator of its edge finset.
    exact tourIndicatorSum_eq_card_inter (subtourInternalEdges S) σ
  have hcut : dotProduct (cutIncidenceVector S) (hamiltonian_tour_incidence_vector σ) =
      ((((hamiltonian_tour_edge_finset σ).filter
        (fun e ↦ cutIncidenceVector S e = 1)).card : ℕ) : ℝ) := by
    rw [cutIncidenceVector_dot_tourIncidence]
    exact cutTourSum_eq_card S σ
  have hcountReal :
      2 * ((((subtourInternalEdges S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) +
          ((((hamiltonian_tour_edge_finset σ).filter
            (fun e ↦ cutIncidenceVector S e = 1)).card : ℕ) : ℝ) =
        2 * (S.card : ℝ) := by
    linarith
  have hcountNat :
      2 * ((subtourInternalEdges S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) +
          ((hamiltonian_tour_edge_finset σ).filter
            (fun e ↦ cutIncidenceVector S e = 1)).card = 2 * S.card := by
    exact_mod_cast hcountReal
  have hpositive := cutTourCard_pos (by omega) S σ
    (Finset.card_pos.mp (by omega)) (by omega)
  have htwo : 2 ≤ ((hamiltonian_tour_edge_finset σ).filter
      (fun e ↦ cutIncidenceVector S e = 1)).card := by omega
  rw [hcut]
  exact_mod_cast htwo

/-- Helper for Theorem 2.3: the endpoints of the `k`-th path edge are the vertices in positions
`k` and `k + 1`. -/
private lemma mem_pathEdgeOfIndex_iff
    {n : ℕ} (p : Fin n) (σ : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    p ∈ ((path_edge_of_index σ k : complete_graph_edges n) : Sym2 (Fin n)) ↔
      p = σ ⟨k.1, by omega⟩ ∨ p = σ ⟨k.1 + 1, by omega⟩ := by
  -- Expose the two consecutive positions once, so later arguments do not depend on the private
  -- implementation names used by the path-edge constructor.
  change
    p ∈ (s(σ ⟨k.1, by omega⟩, σ ⟨k.1 + 1, by omega⟩) : Sym2 (Fin n)) ↔
      p = σ ⟨k.1, by omega⟩ ∨ p = σ ⟨k.1 + 1, by omega⟩
  simp [Sym2.mem_iff]

/-- Helper for Theorem 2.3: an initial nontrivial block has exactly two boundary edges in its
block-ordered Hamiltonian tour. -/
private lemma blockOrderedTour_cutValue_eq_two
    {n : ℕ} (S : Finset (Fin n)) (p : ℕ) (σ : Equiv.Perm (Fin n))
    (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    cutIncidenceVector S ⬝ᵥ hamiltonian_tour_incidence_vector σ = 2 := by
  have hnTwo : 2 ≤ n := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hnTwo
  rw [Nat.add_comm] at hm
  subst n
  have hpathSum :
      (hamiltonian_path_edge_finset σ).sum (cutIncidenceVector S) = 1 :=
    blockOrderedPath_cutSum_eq_one S p σ (by omega) (by omega) hσ
  have hfirst : σ 0 ∈ S := by
    apply (hσ 0).2
    simpa using (show 0 < p by omega)
  have hlast : σ (hamiltonian_tour_last_position m) ∉ S := by
    intro hlastMem
    have hlastLt := (hσ (hamiltonian_tour_last_position m)).1 hlastMem
    simp [hamiltonian_tour_last_position] at hlastLt
    omega
  have hcloseValue :
      cutIncidenceVector S (hamiltonian_tour_closing_edge σ) = 1 := by
    rw [hamiltonian_tour_closing_edge, cutIncidenceVector_apply_pair]
    simp [hfirst, hlast]
  have hcloseNotPath :
      hamiltonian_tour_closing_edge σ ∉ hamiltonian_path_edge_finset σ := by
    intro hmem
    rw [hamiltonian_path_edge_finset, Finset.mem_image] at hmem
    rcases hmem with ⟨k, hk, hedge⟩
    have hcutEq := congrArg (cutIncidenceVector S) hedge
    rw [hcloseValue,
      cutIncidenceVector_pathEdgeOfIndex_of_initialSegment S p σ hσ] at hcutEq
    have hkBoundary : k.1 = p - 1 := by
      by_cases hkp : k.1 < p
      · by_cases hkSucc : k.1 + 1 < p
        · simp [hkp, hkSucc] at hcutEq
        · omega
      · simp [hkp] at hcutEq
        omega
    have hzeroMem :
        σ 0 ∈ ((path_edge_of_index σ k : complete_graph_edges (m + 2)) :
          Sym2 (Fin (m + 2))) := by
      rw [hedge]
      simp [hamiltonian_tour_closing_edge, Sym2.mem_iff]
    rcases (mem_pathEdgeOfIndex_iff  (σ 0) σ k).1 hzeroMem with hzeroMem | hzeroMem
    · have hzero := congrArg Fin.val (σ.injective hzeroMem)
      change 0 = k.1 at hzero
      omega
    · have hzero := congrArg Fin.val (σ.injective hzeroMem)
      change 0 = k.1 + 1 at hzero
      omega
  rw [cutIncidenceVector_dot_tourIncidence]
  rw [hamiltonian_tour_edge_finset, Finset.sum_insert hcloseNotPath, hcloseValue, hpathSum]
  norm_num

/-- Helper for Theorem 2.3: split the ambient position set into its initial `p` positions and
the remaining positions. -/
private def subtourBlockIndexEquiv {n p : ℕ} (hp : p ≤ n) :
    Fin n ≃ Fin p ⊕ Fin (n - p) :=
  (Fin.castOrderIso (Nat.add_sub_of_le hp)).symm.toEquiv.trans finSumFinEquiv.symm

/-- Helper for Theorem 2.3: the position occupied by a vertex of the first block. -/
private def subtourLeftPosition {n p : ℕ} (hp : p ≤ n) (i : Fin p) : Fin n :=
  (subtourBlockIndexEquiv hp).symm (Sum.inl i)

/-- Helper for Theorem 2.3: the position occupied by a vertex of the second block. -/
private def subtourRightPosition {n p : ℕ} (hp : p ≤ n) (i : Fin (n - p)) : Fin n :=
  (subtourBlockIndexEquiv hp).symm (Sum.inr i)

/-- Helper for Theorem 2.3: first-block positions keep their natural indices. -/
@[simp] private lemma subtourLeftPosition_val {n p : ℕ} (hp : p ≤ n) (i : Fin p) :
    (subtourLeftPosition hp i : ℕ) = i := by
  -- The sum-to-`Fin` equivalence places the left summand before the right one.
  simp [subtourLeftPosition, subtourBlockIndexEquiv]

/-- Helper for Theorem 2.3: second-block positions are offset by the first block size. -/
@[simp] private lemma subtourRightPosition_val {n p : ℕ} (hp : p ≤ n)
    (i : Fin (n - p)) :
    (subtourRightPosition hp i : ℕ) = p + i := by
  -- The sum-to-`Fin` equivalence offsets the right summand by `p`.
  simp [subtourRightPosition, subtourBlockIndexEquiv]

/-- Helper for Theorem 2.3: independently permute the two consecutive position blocks. -/
private def subtourBlockPositionPerm {n p : ℕ} (hp : p ≤ n)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) : Equiv.Perm (Fin n) :=
  (subtourBlockIndexEquiv hp).trans
    ((Equiv.sumCongr ρ₁ ρ₂).trans (subtourBlockIndexEquiv hp).symm)

/-- Helper for Theorem 2.3: a block tour first permutes within each shore and then applies the
chosen shore enumeration. -/
private def subtourBlockTourPerm {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) : Equiv.Perm (Fin n) :=
  (subtourBlockPositionPerm hp ρ₁ ρ₂).trans σ

/-- Helper for Theorem 2.3: the block tour acts by `ρ₁` on first-block positions. -/
@[simp] private lemma subtourBlockTourPerm_apply_left
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (i : Fin p) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ (subtourLeftPosition hp i) =
      σ (subtourLeftPosition hp (ρ₁ i)) := by
  -- Conjugating the sum permutation by the block chart gives the claimed action.
  simp [subtourBlockTourPerm, subtourBlockPositionPerm, subtourLeftPosition]

/-- Helper for Theorem 2.3: the block tour acts by `ρ₂` on second-block positions. -/
@[simp] private lemma subtourBlockTourPerm_apply_right
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (i : Fin (n - p)) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ (subtourRightPosition hp i) =
      σ (subtourRightPosition hp (ρ₂ i)) := by
  -- This is the right-summand companion of the preceding computation.
  simp [subtourBlockTourPerm, subtourBlockPositionPerm, subtourRightPosition]

/-- Helper for Theorem 2.3: a block permutation preserves the initial-segment shore
description. -/
private lemma subtourBlockTourPerm_mem_iff
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (t : Fin n) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ t ∈ S ↔ (t : ℕ) < p := by
  -- Split the position through the two-block chart and compute on its summand.
  generalize ht : subtourBlockIndexEquiv hp t = z
  rcases z with i | j
  · have ht' : t = subtourLeftPosition hp i := by
      apply (subtourBlockIndexEquiv hp).injective
      simp [ht, subtourLeftPosition]
    subst t
    rw [subtourBlockTourPerm_apply_left, hσ]
    simp
  · have ht' : t = subtourRightPosition hp j := by
      apply (subtourBlockIndexEquiv hp).injective
      simp [ht, subtourRightPosition]
    subst t
    rw [subtourBlockTourPerm_apply_right, hσ]
    simp

/-- Helper for Theorem 2.3: every block tour belongs to the tight subtour face. -/
private lemma subtourBlockTour_mem_face
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) ∈
      subtour_elimination_face n S := by
  -- The tour is a polytope generator, and the preserved block order makes its cut value two.
  refine ⟨?_, ?_⟩
  · rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self _)
  · rw [subtour_elimination_value_eq_dotProduct]
    exact blockOrderedTour_cutValue_eq_two S p _ hn hpLower hpUpper
      (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂)

/-- Helper for Theorem 2.3: inject the first shore's complete-graph coordinates into the ambient
edge space. -/
private def subtourLeftEdge {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges p) : complete_graph_edges n :=
  ⟨e.1.map (fun i ↦ σ (subtourLeftPosition hp i)), by
    have hinj : Function.Injective (fun i : Fin p ↦ σ (subtourLeftPosition hp i)) := by
      intro i j hij
      have hpos := σ.injective hij
      have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
      simpa [subtourLeftPosition] using hsum
    intro hdiag
    apply e.2
    exact (Sym2.isDiag_map hinj).1 hdiag⟩

/-- Helper for Theorem 2.3: inject the second shore's complete-graph coordinates into the ambient
edge space. -/
private def subtourRightEdge {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges (n - p)) : complete_graph_edges n :=
  ⟨e.1.map (fun i ↦ σ (subtourRightPosition hp i)), by
    have hinj : Function.Injective
        (fun i : Fin (n - p) ↦ σ (subtourRightPosition hp i)) := by
      intro i j hij
      have hpos := σ.injective hij
      have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
      simpa [subtourRightPosition] using hsum
    intro hdiag
    apply e.2
    exact (Sym2.isDiag_map hinj).1 hdiag⟩

/-- Helper for Theorem 2.3: the first-shore edge injection is injective. -/
private lemma subtourLeftEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (subtourLeftEdge hp σ) := by
  intro e f hef
  apply Subtype.ext
  have hinj : Function.Injective (fun i : Fin p ↦ σ (subtourLeftPosition hp i)) := by
    intro i j hij
    have hpos := σ.injective hij
    have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
    simpa [subtourLeftPosition] using hsum
  exact (Sym2.map.injective hinj) (congrArg Subtype.val hef)

/-- Helper for Theorem 2.3: the second-shore edge injection is injective. -/
private lemma subtourRightEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (subtourRightEdge hp σ) := by
  intro e f hef
  apply Subtype.ext
  have hinj : Function.Injective
      (fun i : Fin (n - p) ↦ σ (subtourRightPosition hp i)) := by
    intro i j hij
    have hpos := σ.injective hij
    have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
    simpa [subtourRightPosition] using hsum
  exact (Sym2.map.injective hinj) (congrArg Subtype.val hef)

/-- Helper for Theorem 2.3: restrict an ambient edge vector to the two internal shore graphs. -/
private def subtourInternalRestriction {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    (complete_graph_edges n → ℝ) →ₗ[ℝ]
      (complete_graph_edges p → ℝ) × (complete_graph_edges (n - p) → ℝ) where
  toFun x := (fun e ↦ x (subtourLeftEdge hp σ e), fun e ↦ x (subtourRightEdge hp σ e))
  map_add' x y := by ext e <;> rfl
  map_smul' a x := by ext e <;> rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the two projections of an
element of a product submodule lie in their respective factors. -/
private lemma submoduleProd_fst_mem
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (x : ↥(P.prod Q)) : x.1.1 ∈ P := by
  -- Product-submodule membership records membership of each coordinate.
  exact (Submodule.mem_prod.mp x.2).1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the second projection of a
product-submodule element lies in the second factor. -/
private lemma submoduleProd_snd_mem
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (x : ↥(P.prod Q)) : x.1.2 ∈ Q := by
  -- Product-submodule membership records membership of each coordinate.
  exact (Submodule.mem_prod.mp x.2).2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: pairing elements of two
submodules gives an element of their product submodule. -/
private lemma submoduleProd_pair_mem
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (x : P × Q) :
    ((x.1 : M), (x.2 : N)) ∈ P.prod Q := by
  -- Both coordinates carry precisely the membership certificates required by `Submodule.prod`.
  exact Submodule.mem_prod.mpr ⟨x.1.2, x.2.2⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the subtype of a product
submodule maps linearly to the product of the two subtypes. -/
private def submoduleProdToProd
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) : ↥(P.prod Q) →ₗ[𝕜] P × Q :=
  (LinearMap.codRestrict P
      ((LinearMap.fst 𝕜 M N).comp (P.prod Q).subtype)
      (submoduleProd_fst_mem P Q)).prod
    (LinearMap.codRestrict Q
      ((LinearMap.snd 𝕜 M N).comp (P.prod Q).subtype)
      (submoduleProd_snd_mem P Q))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the canonical linear map from
a product submodule to the product of its factors is bijective. -/
private lemma submoduleProdToProd_bijective
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    Function.Bijective (submoduleProdToProd P Q) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : P × Q ↦ ((z.1 : M), (z.2 : N))) hxy
  · intro y
    let x : ↥(P.prod Q) :=
      ⟨((y.1 : M), (y.2 : N)), submoduleProd_pair_mem P Q y⟩
    refine ⟨x, ?_⟩
    -- The two coordinate projections recover the original subtype elements.
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the finrank of a product
submodule is the sum of the finranks of its factors. -/
private lemma finrank_submoduleProd
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N] [Module.Finite 𝕜 M] [Module.Finite 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    Module.finrank 𝕜 ↥(P.prod Q) = Module.finrank 𝕜 P + Module.finrank 𝕜 Q := by
  let e := LinearEquiv.ofBijective (submoduleProdToProd P Q)
    (submoduleProdToProd_bijective P Q)
  -- Transport finrank across the canonical equivalence, then use the ambient product formula.
  calc
    Module.finrank 𝕜 ↥(P.prod Q) = Module.finrank 𝕜 (P × Q) := e.finrank_eq
    _ = Module.finrank 𝕜 P + Module.finrank 𝕜 Q := Module.finrank_prod

/-- Helper for Theorem 2.3: positions from opposite blocks determine a non-diagonal ambient
edge. -/
private lemma subtourCrossEdge_notDiag
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (i : Fin p) (j : Fin (n - p)) :
    ¬ (s(σ (subtourLeftPosition hp i), σ (subtourRightPosition hp j)) :
        Sym2 (Fin n)).IsDiag := by
  -- Equality of the endpoints would identify the two distinct summands of the block chart.
  rw [Sym2.mk_isDiag_iff]
  intro hij
  have hpos := σ.injective hij
  have hchart := congrArg (subtourBlockIndexEquiv hp) hpos
  simp [subtourLeftPosition, subtourRightPosition] at hchart

/-- Helper for Theorem 2.3: the ambient edge joining one position from each shore block. -/
private def subtourCrossEdge
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (i : Fin p) (j : Fin (n - p)) : complete_graph_edges n :=
  ⟨s(σ (subtourLeftPosition hp i), σ (subtourRightPosition hp j)),
    subtourCrossEdge_notDiag hp σ i j⟩

/-- Helper for Theorem 2.3: the two local endpoints uniquely determine an ambient cross edge. -/
private lemma subtourCrossEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective
      (fun z : Fin p × Fin (n - p) ↦ subtourCrossEdge hp σ z.1 z.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hedge
  have hsym := congrArg Subtype.val hedge
  simp only [subtourCrossEdge] at hsym
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hdirect | hswap
  · apply Prod.ext
    · apply Fin.ext
      have hpos := σ.injective hdirect.1
      simpa using congrArg Fin.val hpos
    · apply Fin.ext
      have hpos := σ.injective hdirect.2
      have hval := congrArg Fin.val hpos
      simp at hval
      omega
  · have hpos := σ.injective hswap.1
    have hval := congrArg Fin.val hpos
    simp at hval
    omega

/-- Helper for Theorem 2.3: every cross edge has cut-incidence value one for the block shore. -/
private lemma subtourCrossEdge_cutValue
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (i : Fin p) (j : Fin (n - p)) :
    cutIncidenceVector S (subtourCrossEdge hp σ i j) = 1 := by
  -- The block chart puts the left endpoint in `S` and the right endpoint outside it.
  unfold subtourCrossEdge
  rw [cutIncidenceVector_apply_pair]
  have hi : σ (subtourLeftPosition hp i) ∈ S := (hσ _).2 (by simp)
  have hj : σ (subtourRightPosition hp j) ∉ S := by
    rw [hσ]
    simp
  simp [hi, hj]

/-- Helper for Theorem 2.3: a block of size at least two has a first position. -/
private lemma subtourFirstPosition_lt {m : ℕ} (hm : 2 ≤ m) : 0 < m := by
  omega

/-- Helper for Theorem 2.3: a block of size at least two has a final position. -/
private lemma subtourLastPosition_lt {m : ℕ} (hm : 2 ≤ m) : m - 1 < m := by
  omega

/-- Helper for Theorem 2.3: successor indices in `Fin (m - 1)` give positions in `Fin m`. -/
private lemma subtourNonzeroPosition_lt
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : i.1 + 1 < m := by
  omega

/-- Helper for Theorem 2.3: the first position of a nontrivial block. -/
private def subtourFirstPosition {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨0, subtourFirstPosition_lt hm⟩

/-- Helper for Theorem 2.3: the final position of a nontrivial block. -/
private def subtourLastPosition {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨m - 1, subtourLastPosition_lt hm⟩

/-- Helper for Theorem 2.3: the nonzero block position indexed by `i : Fin (m - 1)`. -/
private def subtourNonzeroPosition
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : Fin m :=
  ⟨i.1 + 1, subtourNonzeroPosition_lt hm i⟩

/-- Helper for Theorem 2.3: the first block position has value zero. -/
@[simp] private lemma subtourFirstPosition_val
    {m : ℕ} (hm : 2 ≤ m) : (subtourFirstPosition hm : ℕ) = 0 := by
  -- This is the defining value of the first position.
  rfl

/-- Helper for Theorem 2.3: the last block position has value `m - 1`. -/
@[simp] private lemma subtourLastPosition_val
    {m : ℕ} (hm : 2 ≤ m) : (subtourLastPosition hm : ℕ) = m - 1 := by
  -- This is the defining value of the last position.
  rfl

/-- Helper for Theorem 2.3: the nonzero block position indexed by `i` has value `i + 1`. -/
@[simp] private lemma subtourNonzeroPosition_val
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    (subtourNonzeroPosition hm i : ℕ) = i.1 + 1 := by
  -- This is the defining value of the successor position.
  rfl

/-- Helper for Theorem 2.3: the first block position is distinct from every nonzero position. -/
@[simp] private lemma subtourFirstPosition_ne_nonzero
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourFirstPosition hm ≠ subtourNonzeroPosition hm i := by
  -- Their natural-number values are respectively zero and a successor.
  intro h
  have hval := congrArg Fin.val h
  simp at hval

/-- Helper for Theorem 2.3: every nonzero block position is distinct from the first position. -/
@[simp] private lemma subtourNonzeroPosition_ne_first
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourNonzeroPosition hm i ≠ subtourFirstPosition hm :=
  (subtourFirstPosition_ne_nonzero hm i).symm

/-- Helper for Theorem 2.3: the nonzero-position chart is injective. -/
private lemma subtourNonzeroPosition_injective
    {m : ℕ} (hm : 2 ≤ m) : Function.Injective (subtourNonzeroPosition hm) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp at hval
  omega

/-- Helper for Theorem 2.3: equality of nonzero block positions is equality of their indices. -/
@[simp] private lemma subtourNonzeroPosition_eq_iff
    {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m - 1)) :
    subtourNonzeroPosition hm i = subtourNonzeroPosition hm j ↔ i = j :=
  (subtourNonzeroPosition_injective hm).eq_iff

/-- Helper for Theorem 2.3: reversal exchanges the first and last positions of a nontrivial
block. -/
@[simp] private lemma subtourFirstPosition_rev
    {m : ℕ} (hm : 2 ≤ m) :
    (subtourFirstPosition hm).rev = subtourLastPosition hm := by
  -- Compare the explicit values of the two positions.
  apply Fin.ext
  simp [Fin.val_rev]

/-- Helper for Theorem 2.3: reversal exchanges the last and first positions of a nontrivial
block. -/
@[simp] private lemma subtourLastPosition_rev
    {m : ℕ} (hm : 2 ≤ m) :
    (subtourLastPosition hm).rev = subtourFirstPosition hm := by
  -- Compare the explicit values of the two positions.
  apply Fin.ext
  simp [Fin.val_rev]
  omega

/-- Helper for Theorem 2.3: the upper shore-size bound leaves at least two vertices in the
complement block. -/
private lemma subtourRightBlock_two_le
    {n p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2) : 2 ≤ n - p := by
  omega

/-- Helper for Theorem 2.3: swap the last position of a block with a prescribed nonzero
position, while fixing the first position. -/
private def subtourEndpointPerm
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : Equiv.Perm (Fin m) :=
  Equiv.swap (subtourLastPosition hm) (subtourNonzeroPosition hm i)

/-- Helper for Theorem 2.3: `subtourEndpointPerm` fixes the first block position. -/
@[simp] private lemma subtourEndpointPerm_apply_zero
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourEndpointPerm hm i (subtourFirstPosition hm) = subtourFirstPosition hm := by
  -- Both positions swapped by the permutation are nonzero.
  have hlast : subtourFirstPosition hm ≠ subtourLastPosition hm := by
    intro h
    have hval := congrArg Fin.val h
    simp [subtourFirstPosition, subtourLastPosition] at hval
    omega
  have hnonzero : subtourFirstPosition hm ≠ subtourNonzeroPosition hm i := by
    intro h
    have hval := congrArg Fin.val h
    simp [subtourFirstPosition, subtourNonzeroPosition] at hval
  exact Equiv.swap_apply_of_ne_of_ne hlast hnonzero

/-- Helper for Theorem 2.3: `subtourEndpointPerm` sends the last block position to the prescribed
nonzero position. -/
@[simp] private lemma subtourEndpointPerm_apply_last
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourEndpointPerm hm i (subtourLastPosition hm) = subtourNonzeroPosition hm i := by
  -- This is the defining left endpoint of the transposition.
  exact Equiv.swap_apply_left _ _

/-- Helper for Theorem 2.3: every endpoint of a left internal edge lies in the shore. -/
private lemma mem_shore_of_mem_subtourLeftEdge
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges p) {v : Fin n}
    (hv : v ∈ ((subtourLeftEdge hp σ e : complete_graph_edges n) : Sym2 (Fin n))) :
    v ∈ S := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      simp only [subtourLeftEdge, Sym2.map_mk, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (hσ _).2 (by simp)
      · exact (hσ _).2 (by simp)

/-- Helper for Theorem 2.3: every endpoint of a right internal edge lies outside the shore. -/
private lemma not_mem_shore_of_mem_subtourRightEdge
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges (n - p)) {v : Fin n}
    (hv : v ∈ ((subtourRightEdge hp σ e : complete_graph_edges n) : Sym2 (Fin n))) :
    v ∉ S := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      simp only [subtourRightEdge, Sym2.map_mk, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · rw [hσ]
        simp
      · rw [hσ]
        simp

/-- Helper for Theorem 2.3: a local left path edge becomes the corresponding global path edge
of the block tour. -/
private lemma subtourLeftEdge_pathEdge
    {n p : ℕ} (hpUpper : p ≤ n - 2) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (k : Fin (p - 1)) :
    subtourLeftEdge (by omega) σ (path_edge_of_index ρ₁ k) =
      path_edge_of_index (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        ⟨k.1, by omega⟩ := by
  -- Both sides are the unordered pair at local consecutive positions `k,k+1`.
  have hkSucc : k.1 + 1 < p := by
    have hk := k.2
    omega
  apply Subtype.ext
  change
    Sym2.map (fun i ↦ σ (subtourLeftPosition (by omega) i))
        (s(ρ₁ (⟨k.1, by omega⟩ : Fin p), ρ₁ ⟨k.1 + 1, hkSucc⟩)) =
      s(subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1, by omega⟩,
        subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1 + 1, by omega⟩)
  have hleft : (⟨k.1, by omega⟩ : Fin n) =
      subtourLeftPosition (by omega) (⟨k.1, by omega⟩ : Fin p) := by
    ext
    simp
  have hright : (⟨k.1 + 1, by omega⟩ : Fin n) =
      subtourLeftPosition (by omega) ⟨k.1 + 1, hkSucc⟩ := by
    ext
    simp
  rw [Sym2.map_mk, Sym2.eq_iff]
  left
  constructor
  · calc
      σ (subtourLeftPosition (by omega) (ρ₁ ⟨k.1, by omega⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourLeftPosition (by omega) ⟨k.1, by omega⟩) :=
        (subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1, by omega⟩ := by rw [hleft]
  · calc
      σ (subtourLeftPosition (by omega) (ρ₁ ⟨k.1 + 1, hkSucc⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourLeftPosition (by omega) ⟨k.1 + 1, hkSucc⟩) :=
        (subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1 + 1, by omega⟩ := by rw [hright]

/-- Helper for Theorem 2.3: a local right path edge becomes the offset global path edge of the
block tour. -/
private lemma subtourRightEdge_pathEdge
    {n p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (k : Fin ((n - p) - 1)) :
    subtourRightEdge (by omega) σ (path_edge_of_index ρ₂ k) =
      path_edge_of_index (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        ⟨p + k.1, by omega⟩ := by
  -- Offset by `p`; the two consecutive right-block positions remain consecutive globally.
  have hq : 2 ≤ n - p := by omega
  have hkSucc : k.1 + 1 < n - p := by
    have hk := k.2
    omega
  apply Subtype.ext
  change
    Sym2.map (fun i ↦ σ (subtourRightPosition (by omega) i))
        (s(ρ₂ (⟨k.1, by omega⟩ : Fin (n - p)), ρ₂ ⟨k.1 + 1, hkSucc⟩)) =
      s(subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1, by omega⟩,
        subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1 + 1, by omega⟩)
  have hleft : (⟨p + k.1, by omega⟩ : Fin n) =
      subtourRightPosition (by omega) (⟨k.1, by omega⟩ : Fin (n - p)) := by
    ext
    simp
  have hright : (⟨p + k.1 + 1, by omega⟩ : Fin n) =
      subtourRightPosition (by omega) ⟨k.1 + 1, hkSucc⟩ := by
    ext
    simp [Nat.add_assoc]
  rw [Sym2.map_mk, Sym2.eq_iff]
  left
  constructor
  · calc
      σ (subtourRightPosition (by omega) (ρ₂ ⟨k.1, by omega⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourRightPosition (by omega) ⟨k.1, by omega⟩) :=
        (subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1, by omega⟩ := by rw [hleft]
  · calc
      σ (subtourRightPosition (by omega) (ρ₂ ⟨k.1 + 1, hkSucc⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourRightPosition (by omega) ⟨k.1 + 1, hkSucc⟩) :=
        (subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1 + 1, by omega⟩ := by rw [hright]

/-- Helper for Theorem 2.3: the unique path edge between the two blocks is the edge joining the
last left endpoint to the first right endpoint. -/
private lemma subtourBlockTour_boundaryEdge
    {n p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) :
    path_edge_of_index (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        ⟨p - 1, by omega⟩ =
      subtourCrossEdge (by omega) σ (ρ₁ (subtourLastPosition hpLower))
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
  -- Identify the two path endpoints through the block chart, then use endpoint extensionality.
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  apply Subtype.ext
  apply Sym2.ext
  intro v
  have hleft : (⟨p - 1, by omega⟩ : Fin n) =
      subtourLeftPosition (by omega) (subtourLastPosition hpLower) := by
    ext
    simp
  have hright : (⟨p, by omega⟩ : Fin n) =
      subtourRightPosition (by omega)
        (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)) := by
    ext
    simp
  have hleftEval : τ ⟨p - 1, by omega⟩ =
      σ (subtourLeftPosition (by omega) (ρ₁ (subtourLastPosition hpLower))) := by
    rw [hleft]
    exact subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _
  have hrightEval : τ ⟨p, by omega⟩ =
      σ (subtourRightPosition (by omega)
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    rw [hright]
    exact subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _
  have hrightEval' : τ ⟨p - 1 + 1, by omega⟩ =
      σ (subtourRightPosition (by omega)
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    have hpos : (⟨p - 1 + 1, by omega⟩ : Fin n) = ⟨p, by omega⟩ := by
      apply Fin.ext
      exact Nat.sub_add_cancel (by omega)
    rw [hpos, hrightEval]
  rw [mem_pathEdgeOfIndex_iff]
  unfold subtourCrossEdge
  simp only [Sym2.mem_iff]
  rw [hleftEval, hrightEval']

/-- Helper for Theorem 2.3: the closing edge of a block tour joins the first left endpoint to the
last right endpoint. -/
private lemma subtourBlockTour_closingEdge
    {m p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ m + 2 - 2)
    (σ : Equiv.Perm (Fin (m + 2)))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (m + 2 - p))) :
    hamiltonian_tour_closing_edge (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) =
      subtourCrossEdge (by omega) σ (ρ₁ (subtourFirstPosition hpLower))
        (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
  -- The first and last global positions are the first left and last right block positions.
  apply Subtype.ext
  change
      s(subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ 0,
        subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ (hamiltonian_tour_last_position m)) =
      s(σ (subtourLeftPosition (by omega) (ρ₁ (subtourFirstPosition hpLower))),
        σ (subtourRightPosition (by omega)
          (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))))
  have hfirst : (0 : Fin (m + 2)) =
      subtourLeftPosition (by omega) (subtourFirstPosition hpLower) := by
    ext
    simp
  have hlast : hamiltonian_tour_last_position m =
      subtourRightPosition (by omega)
        (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)) := by
    ext
    simp [hamiltonian_tour_last_position]
    omega
  rw [Sym2.eq_iff]
  left
  constructor
  · rw [hfirst, subtourBlockTourPerm_apply_left]
  · rw [hlast, subtourBlockTourPerm_apply_right]

/-- Helper for Theorem 2.3: a cross edge belongs to a block tour exactly when it is one of the
two connector edges. -/
private lemma subtourCrossEdge_mem_blockTour_iff
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (i : Fin p) (j : Fin (n - p)) :
    subtourCrossEdge (by omega) σ i j ∈
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) ↔
      subtourCrossEdge (by omega) σ i j =
          subtourCrossEdge (by omega) σ (ρ₁ (subtourLastPosition hpLower))
            (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
        subtourCrossEdge (by omega) σ i j =
          subtourCrossEdge (by omega) σ (ρ₁ (subtourFirstPosition hpLower))
            (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  rw [Nat.add_comm] at hm
  subst n
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  have hτ : ∀ t : Fin (m + 2), τ t ∈ S ↔ (t : ℕ) < p :=
    subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂
  rw [hamiltonian_tour_edge_finset, Finset.mem_insert]
  constructor
  · rintro (hclosing | hpath)
    · right
      exact hclosing.trans
        (subtourBlockTour_closingEdge hpLower hpUpper σ ρ₁ ρ₂)
    · rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
      rcases hpath with ⟨k, hkU, hk⟩
      have hkCut : cutIncidenceVector S (path_edge_of_index τ k) = 1 := by
        rw [hk]
        exact subtourCrossEdge_cutValue (by omega) S σ hσ i j
      rw [cutIncidenceVector_pathEdgeOfIndex_of_initialSegment S p τ hτ] at hkCut
      have hkBoundary : k.1 = p - 1 := by
        by_cases hkp : k.1 < p
        · by_cases hkSucc : k.1 + 1 < p
          · simp [hkp, hkSucc] at hkCut
          · omega
        · simp [hkp] at hkCut
          omega
      have hkEq : k = (⟨p - 1, by omega⟩ : Fin (m + 2 - 1)) := Fin.ext hkBoundary
      rw [hkEq] at hk
      left
      exact hk.symm.trans (subtourBlockTour_boundaryEdge hpLower hpUpper σ ρ₁ ρ₂)
  · rintro (hboundary | hclosing)
    · right
      rw [hamiltonian_path_edge_finset, Finset.mem_image]
      refine ⟨(⟨p - 1, by omega⟩ : Fin (m + 2 - 1)), Finset.mem_univ _, ?_⟩
      exact (subtourBlockTour_boundaryEdge hpLower hpUpper σ ρ₁ ρ₂).trans hboundary.symm
    · left
      exact hclosing.trans
        (subtourBlockTour_closingEdge hpLower hpUpper σ ρ₁ ρ₂).symm

/-- Helper for Theorem 2.3: the cross coordinate of a block-tour incidence vector is the
indicator of its two connector pairs. -/
private lemma subtourBlockTour_crossCoordinate
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (i : Fin p) (j : Fin (n - p)) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        (subtourCrossEdge (by omega) σ i j) =
      if (i, j) = (ρ₁ (subtourLastPosition hpLower),
            ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
          (i, j) = (ρ₁ (subtourFirstPosition hpLower),
            ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper))) then 1 else 0 := by
  -- Reduce tour membership to the two connector edges, then use injectivity of the cross chart.
  rw [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
    subtourCrossEdge_mem_blockTour_iff hn hpLower hpUpper S σ hσ]
  let f : Fin p × Fin (n - p) → complete_graph_edges n :=
    fun z ↦ subtourCrossEdge (by omega) σ z.1 z.2
  have hinj : Function.Injective f := subtourCrossEdge_injective (by omega) σ
  have hconditions :
      (subtourCrossEdge (by omega) σ i j =
            subtourCrossEdge (by omega) σ (ρ₁ (subtourLastPosition hpLower))
              (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
          subtourCrossEdge (by omega) σ i j =
            subtourCrossEdge (by omega) σ (ρ₁ (subtourFirstPosition hpLower))
              (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))) ↔
        ((i, j) = (ρ₁ (subtourLastPosition hpLower),
              ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
          (i, j) = (ρ₁ (subtourFirstPosition hpLower),
              ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    constructor
    · rintro (h | h)
      · left
        apply hinj
        simpa [f] using h
      · right
        apply hinj
        simpa [f] using h
    · rintro (h | h)
      · left
        simpa [f] using congrArg f h
      · right
        simpa [f] using congrArg f h
  rw [hconditions]
  by_cases h :
      (i, j) = (ρ₁ (subtourLastPosition hpLower),
            ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
        (i, j) = (ρ₁ (subtourFirstPosition hpLower),
            ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))
  · simp
  · simp

/-- Helper for Theorem 2.3: every path edge belongs to the tour obtained by adding the closing
edge. -/
private lemma hamiltonianPathEdge_mem_tour
    {n : ℕ} (hn : 2 ≤ n) (τ : Equiv.Perm (Fin n)) {e : complete_graph_edges n}
    (he : e ∈ hamiltonian_path_edge_finset τ) :
    e ∈ hamiltonian_tour_edge_finset τ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  simp [hamiltonian_tour_edge_finset, he]

/-- Helper for Theorem 2.3: reversing the position order of a Hamiltonian path preserves its
edge-incidence vector. -/
private lemma hamiltonianPathIncidence_reverse
    {n : ℕ} (hn : 2 ≤ n) (ρ : Equiv.Perm (Fin n)) :
    hamiltonian_path_incidence_vector (Fin.revPerm.trans ρ) =
      hamiltonian_path_incidence_vector ρ := by
  have hedge (k : Fin (n - 1)) :
      path_edge_of_index (Fin.revPerm.trans ρ) k.rev = path_edge_of_index ρ k := by
    -- Compare endpoint membership, using the public path-edge interface to avoid unfolding its
    -- private position wrappers.
    apply Subtype.ext
    apply Sym2.ext
    intro v
    rw [mem_pathEdgeOfIndex_iff, mem_pathEdgeOfIndex_iff]
    have hleft :
        (Fin.revPerm.trans ρ) ⟨k.rev.1, by omega⟩ = ρ ⟨k.1 + 1, by omega⟩ := by
      apply congrArg ρ
      apply Fin.ext
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    have hright :
        (Fin.revPerm.trans ρ) ⟨k.rev.1 + 1, by omega⟩ = ρ ⟨k.1, by omega⟩ := by
      apply congrArg ρ
      apply Fin.ext
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    rw [hleft, hright]
    tauto
  funext e
  simp only [hamiltonian_path_incidence_vector]
  congr 1
  apply propext
  simp only [hamiltonian_path_edge_finset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k.rev, ?_⟩
    -- Normalize the double reversal before composing with the membership witness.
    calc
      path_edge_of_index ρ k.rev =
          path_edge_of_index (Fin.revPerm.trans ρ) k := by
            simpa using (hedge k.rev).symm
      _ = e := hk
  · rintro ⟨k, hk⟩
    refine ⟨k.rev, ?_⟩
    calc
      path_edge_of_index (Fin.revPerm.trans ρ) k.rev =
          path_edge_of_index ρ k := hedge k
      _ = e := hk

/-- Helper for Theorem 2.3: restricting a block tour to its first shore recovers the first
Hamiltonian-path incidence vector. -/
private lemma subtourBlockTour_leftCoordinate
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (e : complete_graph_edges p) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        (subtourLeftEdge (by omega) σ e) =
      hamiltonian_path_incidence_vector ρ₁ e := by
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  have hiff : subtourLeftEdge (by omega) σ e ∈ hamiltonian_tour_edge_finset τ ↔
      e ∈ hamiltonian_path_edge_finset ρ₁ := by
    constructor
    · intro htour
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
      rw [Nat.add_comm] at hm
      subst n
      simp only [hamiltonian_tour_edge_finset, Finset.mem_insert] at htour
      rcases htour with hclose | hpath
      · have hlastEdge :
            τ (hamiltonian_tour_last_position m) ∈
              ((subtourLeftEdge (by omega) σ e : complete_graph_edges (m + 2)) :
                Sym2 (Fin (m + 2))) := by
          rw [hclose]
          simp [hamiltonian_tour_closing_edge, Sym2.mem_iff]
        have hlastS := mem_shore_of_mem_subtourLeftEdge (by omega) S σ hσ e hlastEdge
        have hlt := (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ _).1 hlastS
        simp [hamiltonian_tour_last_position] at hlt
        omega
      · rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
        rcases hpath with ⟨k, hkU, hk⟩
        have hrightEdge :
            τ ⟨k.1 + 1, by omega⟩ ∈
              ((subtourLeftEdge (by omega) σ e : complete_graph_edges (m + 2)) :
                Sym2 (Fin (m + 2))) := by
          rw [← hk]
          exact (mem_pathEdgeOfIndex_iff _ τ k).2 (Or.inr rfl)
        have hrightS := mem_shore_of_mem_subtourLeftEdge (by omega) S σ hσ e hrightEdge
        have hklt :=
          (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ _).1 hrightS
        have hkSuccLt : k.1 + 1 < p := by
          simpa using hklt
        let k' : Fin (p - 1) := ⟨k.1, by omega⟩
        have hedge : e = path_edge_of_index ρ₁ k' := by
          apply subtourLeftEdge_injective (by omega) σ
          calc
            subtourLeftEdge (by omega) σ e = path_edge_of_index τ k := hk.symm
            _ = subtourLeftEdge (by omega) σ (path_edge_of_index ρ₁ k') := by
              symm
              simpa [τ, k'] using subtourLeftEdge_pathEdge hpUpper σ ρ₁ ρ₂ k'
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        exact ⟨k', Finset.mem_univ _, hedge.symm⟩
    · intro hpath
      rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
      rcases hpath with ⟨k, hkU, hk⟩
      have hglobal : subtourLeftEdge (by omega) σ e ∈
          hamiltonian_path_edge_finset τ := by
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        refine ⟨(⟨k.1, by omega⟩ : Fin (n - 1)), Finset.mem_univ _, ?_⟩
        rw [← hk]
        exact (subtourLeftEdge_pathEdge hpUpper σ ρ₁ ρ₂ k).symm
      exact hamiltonianPathEdge_mem_tour (by omega) τ hglobal
  -- Compare the two indicator functions propositionally, avoiding decidable-instance transport.
  by_cases hpath : e ∈ hamiltonian_path_edge_finset ρ₁
  · have htour := hiff.2 hpath
    have htour' : subtourLeftEdge (by omega) σ e ∈
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]
  · have htour : subtourLeftEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset τ := fun h ↦ hpath (hiff.1 h)
    have htour' : subtourLeftEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]

/-- Helper for Theorem 2.3: restricting a block tour to its second shore recovers the second
Hamiltonian-path incidence vector. -/
private lemma subtourBlockTour_rightCoordinate
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (e : complete_graph_edges (n - p)) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        (subtourRightEdge (by omega) σ e) =
      hamiltonian_path_incidence_vector ρ₂ e := by
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  have hiff : subtourRightEdge (by omega) σ e ∈ hamiltonian_tour_edge_finset τ ↔
      e ∈ hamiltonian_path_edge_finset ρ₂ := by
    constructor
    · intro htour
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
      rw [Nat.add_comm] at hm
      subst n
      simp only [hamiltonian_tour_edge_finset, Finset.mem_insert] at htour
      rcases htour with hclose | hpath
      · have hfirstEdge : τ 0 ∈
            ((subtourRightEdge (by omega) σ e : complete_graph_edges (m + 2)) :
              Sym2 (Fin (m + 2))) := by
          rw [hclose]
          simp [hamiltonian_tour_closing_edge, Sym2.mem_iff]
        have hfirstNot := not_mem_shore_of_mem_subtourRightEdge
          (by omega) S σ hσ e hfirstEdge
        have hzeroLt : (0 : ℕ) < p := by omega
        have hfirstMem : τ 0 ∈ S :=
          (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ 0).2 hzeroLt
        exact (hfirstNot hfirstMem).elim
      · rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
        rcases hpath with ⟨k, hkU, hk⟩
        have hleftEdge : τ ⟨k.1, by omega⟩ ∈
            ((subtourRightEdge (by omega) σ e : complete_graph_edges (m + 2)) :
              Sym2 (Fin (m + 2))) := by
          rw [← hk]
          exact (mem_pathEdgeOfIndex_iff _ τ k).2 (Or.inl rfl)
        have hleftNot := not_mem_shore_of_mem_subtourRightEdge
          (by omega) S σ hσ e hleftEdge
        have hkge : p ≤ k.1 := by
          by_contra h
          have hkltP : k.1 < p := by omega
          exact hleftNot
            ((subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ _).2 hkltP)
        let k' : Fin ((m + 2 - p) - 1) := ⟨k.1 - p, by omega⟩
        have hedge : e = path_edge_of_index ρ₂ k' := by
          apply subtourRightEdge_injective (by omega) σ
          calc
            subtourRightEdge (by omega) σ e = path_edge_of_index τ k := hk.symm
            _ = subtourRightEdge (by omega) σ (path_edge_of_index ρ₂ k') := by
              symm
              simpa [τ, k', Nat.add_sub_of_le hkge] using
                subtourRightEdge_pathEdge hpLower hpUpper σ ρ₁ ρ₂ k'
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        exact ⟨k', Finset.mem_univ _, hedge.symm⟩
    · intro hpath
      rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
      rcases hpath with ⟨k, hkU, hk⟩
      have hglobal : subtourRightEdge (by omega) σ e ∈
          hamiltonian_path_edge_finset τ := by
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        refine ⟨(⟨p + k.1, by omega⟩ : Fin (n - 1)), Finset.mem_univ _, ?_⟩
        rw [← hk]
        exact (subtourRightEdge_pathEdge hpLower hpUpper σ ρ₁ ρ₂ k).symm
      exact hamiltonianPathEdge_mem_tour (by omega) τ hglobal
  -- Compare the two indicator functions propositionally, avoiding decidable-instance transport.
  by_cases hpath : e ∈ hamiltonian_path_edge_finset ρ₂
  · have htour := hiff.2 hpath
    have htour' : subtourRightEdge (by omega) σ e ∈
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]
  · have htour : subtourRightEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset τ := fun h ↦ hpath (hiff.1 h)
    have htour' : subtourRightEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]

/-- Helper for Theorem 2.3: every left-shore coordinate-sum basis difference occurs in the
range of internal restriction on the tight-face direction. -/
private lemma subtourLeftBasisDifference_mem_internalRange
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges p) :
    (Pi.basisFun ℝ (complete_graph_edges p) e -
          Pi.basisFun ℝ (complete_graph_edges p) (reference_edge p hpLower), 0) ∈
      LinearMap.range
        ((subtourInternalRestriction (by omega) σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  obtain ⟨ρ, τ, hdiff⟩ := reference_edge_difference_vertex_witness p hpLower e
  let xρ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ ρ (Equiv.refl (Fin (n - p))))
  let xτ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ τ (Equiv.refl (Fin (n - p))))
  have hxρ : xρ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ ρ (Equiv.refl _))
  have hxτ : xτ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ τ (Equiv.refl _))
  have hv : xρ - xτ ∈ (affineSpan ℝ (subtour_elimination_face n S)).direction := by
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxρ hxτ
  refine ⟨⟨xρ - xτ, hv⟩, ?_⟩
  -- The coordinate specification sends the face-direction witness to the desired left basis
  -- difference, while its unchanged right path cancels.
  apply Prod.ext
  · funext d
    change (xρ - xτ) (subtourLeftEdge (by omega) σ d) =
      (Pi.basisFun ℝ (complete_graph_edges p) e -
        Pi.basisFun ℝ (complete_graph_edges p) (reference_edge p hpLower)) d
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ]
    exact congrFun hdiff d
  · funext d
    change (xρ - xτ) (subtourRightEdge (by omega) σ d) = 0
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ]
    simp

/-- Helper for Theorem 2.3: every right-shore coordinate-sum basis difference occurs in the
range of internal restriction on the tight-face direction. -/
private lemma subtourRightBasisDifference_mem_internalRange
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges (n - p)) :
    (0, Pi.basisFun ℝ (complete_graph_edges (n - p)) e -
          Pi.basisFun ℝ (complete_graph_edges (n - p))
            (reference_edge (n - p) (by omega))) ∈
      LinearMap.range
        ((subtourInternalRestriction (by omega) σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  have hq : 2 ≤ n - p := by omega
  obtain ⟨ρ, τ, hdiff⟩ := reference_edge_difference_vertex_witness (n - p) hq e
  let xρ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ (Equiv.refl (Fin p)) ρ)
  let xτ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ (Equiv.refl (Fin p)) τ)
  have hxρ : xρ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ (Equiv.refl _) ρ)
  have hxτ : xτ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ (Equiv.refl _) τ)
  have hv : xρ - xτ ∈ (affineSpan ℝ (subtour_elimination_face n S)).direction := by
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxρ hxτ
  refine ⟨⟨xρ - xτ, hv⟩, ?_⟩
  -- This time the left path is fixed and the right coordinate records the path witness.
  apply Prod.ext
  · funext d
    change (xρ - xτ) (subtourLeftEdge (by omega) σ d) = 0
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ]
    simp
  · funext d
    change (xρ - xτ) (subtourRightEdge (by omega) σ d) =
      (Pi.basisFun ℝ (complete_graph_edges (n - p)) e -
        Pi.basisFun ℝ (complete_graph_edges (n - p)) (reference_edge (n - p) hq)) d
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ]
    exact congrFun hdiff d

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the product of the two
internal zero-sum coordinate spaces lies in the range of restriction from the tight face. -/
private lemma subtourInternalDirections_le_range
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    (LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges p)).sumCoords).prod
        (LinearMap.ker
          (Pi.basisFun ℝ (complete_graph_edges (n - p))).sumCoords) ≤
      LinearMap.range
        ((subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  have hqLower : 2 ≤ n - p := by omega
  let Rng := LinearMap.range
    ((subtourInternalRestriction hp σ).domRestrict
      (affineSpan ℝ (subtour_elimination_face n S)).direction)
  intro x hx
  have hxLeft : x.1 ∈
      LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges p)).sumCoords :=
    (Submodule.mem_prod.mp hx).1
  have hxRight : x.2 ∈
      LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges (n - p))).sumCoords :=
    (Submodule.mem_prod.mp hx).2
  rw [sum_zero_submodule_eq_span_reference_differences
    (complete_graph_edges p) (reference_edge p hpLower)] at hxLeft
  rw [sum_zero_submodule_eq_span_reference_differences
    (complete_graph_edges (n - p)) (reference_edge (n - p) hqLower)] at hxRight
  have hleftSpan :
      ∀ y ∈ Submodule.span ℝ (Set.range fun e : complete_graph_edges p ↦
          Pi.basisFun ℝ (complete_graph_edges p) e -
            Pi.basisFun ℝ (complete_graph_edges p) (reference_edge p hpLower)),
        (y, 0) ∈ Rng := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨e, rfl⟩
      exact subtourLeftBasisDifference_mem_internalRange hn hpLower hpUpper S σ hσ e
    · exact Rng.zero_mem
    · intro u v _ _ hu hv
      simpa using Rng.add_mem hu hv
    · intro a u _ hu
      simpa using Rng.smul_mem a hu
  have hrightSpan :
      ∀ y ∈ Submodule.span ℝ (Set.range fun e : complete_graph_edges (n - p) ↦
          Pi.basisFun ℝ (complete_graph_edges (n - p)) e -
            Pi.basisFun ℝ (complete_graph_edges (n - p)) (reference_edge (n - p) hqLower)),
        (0, y) ∈ Rng := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨e, rfl⟩
      exact subtourRightBasisDifference_mem_internalRange hn hpLower hpUpper S σ hσ e
    · exact Rng.zero_mem
    · intro u v _ _ hu hv
      simpa using Rng.add_mem hu hv
    · intro a u _ hu
      simpa using Rng.smul_mem a hu
  have hleft := hleftSpan x.1 hxLeft
  have hright := hrightSpan x.2 hxRight
  -- Adding the two coordinate-axis witnesses gives the required pair.
  change x ∈ Rng
  simpa using Rng.add_mem hleft hright

/-- Helper for Theorem 2.3: reversing the left block of an endpoint-controlled block tour gives
an anchored cross-rectangle direction. -/
private def subtourCrossRectangleDirection
    {n p : ℕ} (hp : p ≤ n) (hpLower : 2 ≤ p) (hqLower : 2 ≤ n - p)
    (σ : Equiv.Perm (Fin n))
    (z : Fin (p - 1) × Fin (n - p - 1)) : complete_graph_edges n → ℝ :=
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm hqLower z.2
  hamiltonian_tour_incidence_vector (subtourBlockTourPerm hp σ ρ₁ ρ₂) -
    hamiltonian_tour_incidence_vector
      (subtourBlockTourPerm hp σ (Fin.revPerm.trans ρ₁) ρ₂)

/-- Helper for Theorem 2.3: every anchored cross rectangle is a direction of the tight subtour
face. -/
private lemma subtourCrossRectangleDirection_mem_faceDirection
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    subtourCrossRectangleDirection (by omega) hpLower
        (subtourRightBlock_two_le hpLower hpUpper) σ z ∈
      (affineSpan ℝ (subtour_elimination_face n S)).direction := by
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm (subtourRightBlock_two_le hpLower hpUpper) z.2
  let x := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
  let y := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ (Fin.revPerm.trans ρ₁) ρ₂)
  have hx : x ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ ρ₁ ρ₂)
  have hy : y ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ
        (Fin.revPerm.trans ρ₁) ρ₂)
  -- The difference of the two tight tour vertices lies in the face direction.
  simpa [subtourCrossRectangleDirection, ρ₁, ρ₂, x, y, vsub_eq_sub] using
    AffineSubspace.vsub_mem_direction hx hy

/-- Helper for Theorem 2.3: cross rectangles vanish after restricting to the two internal shore
graphs. -/
private lemma subtourInternalRestriction_crossRectangle_eq_zero
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    subtourInternalRestriction (p := p) (by omega) σ
        (subtourCrossRectangleDirection (by omega) hpLower
          (subtourRightBlock_two_le hpLower hpUpper) σ z) = 0 := by
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm (subtourRightBlock_two_le hpLower hpUpper) z.2
  apply Prod.ext
  · funext e
    change
      (hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) -
          hamiltonian_tour_incidence_vector
            (subtourBlockTourPerm (by omega) σ (Fin.revPerm.trans ρ₁) ρ₂))
          (subtourLeftEdge (p := p) (by omega) σ e) = 0
    rw [Pi.sub_apply,
      subtourBlockTour_leftCoordinate (p := p) hn hpLower hpUpper S σ hσ,
      subtourBlockTour_leftCoordinate (p := p) hn hpLower hpUpper S σ hσ,
      hamiltonianPathIncidence_reverse hpLower ρ₁]
    simp
  · funext e
    change
      (hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) -
          hamiltonian_tour_incidence_vector
            (subtourBlockTourPerm (by omega) σ (Fin.revPerm.trans ρ₁) ρ₂))
          (subtourRightEdge (p := p) (by omega) σ e) = 0
    rw [Pi.sub_apply,
      subtourBlockTour_rightCoordinate (p := p) hn hpLower hpUpper S σ hσ,
      subtourBlockTour_rightCoordinate (p := p) hn hpLower hpUpper S σ hσ]
    simp

/-- Helper for Theorem 2.3: evaluating an anchored cross rectangle at a variable-variable cross
edge recovers its index coefficient. -/
private lemma subtourCrossRectangleDirection_apply
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z k : Fin (p - 1) × Fin (n - p - 1)) :
    subtourCrossRectangleDirection (by omega) hpLower
        (subtourRightBlock_two_le hpLower hpUpper) σ z
        (subtourCrossEdge (by omega) σ
          (subtourNonzeroPosition hpLower k.1)
          (subtourNonzeroPosition (subtourRightBlock_two_le hpLower hpUpper) k.2)) =
      if k = z then -1 else 0 := by
  let hqLower := subtourRightBlock_two_le hpLower hpUpper
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm hqLower z.2
  simp only [subtourCrossRectangleDirection, Pi.sub_apply]
  rw [subtourBlockTour_crossCoordinate hn hpLower hpUpper S σ hσ,
    subtourBlockTour_crossCoordinate hn hpLower hpUpper S σ hσ]
  -- The unreversed tour avoids variable-variable cross edges; the reversed tour contains exactly
  -- the coordinate indexed by `z`.
  simp [Equiv.trans_apply, Fin.revPerm_apply, Prod.ext_iff]
  split_ifs <;> norm_num

/-- Helper for Theorem 2.3: the anchored cross-rectangle directions are linearly independent. -/
private lemma subtourCrossRectangleDirection_linearIndependent
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    LinearIndependent ℝ
      (fun z : Fin (p - 1) × Fin (n - p - 1) ↦
        subtourCrossRectangleDirection (by omega) hpLower
          (subtourRightBlock_two_le hpLower hpUpper) σ z) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum z
  have hcoord := congrArg
    (fun x : complete_graph_edges n → ℝ ↦
      x (subtourCrossEdge (by omega) σ
        (subtourNonzeroPosition hpLower z.1)
        (subtourNonzeroPosition (subtourRightBlock_two_le hpLower hpUpper) z.2))) hsum
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hcoord
  simp_rw [subtourCrossRectangleDirection_apply hn hpLower hpUpper S σ hσ] at hcoord
  simpa using neg_eq_zero.mp (by simpa using hcoord)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: an anchored cross rectangle,
regarded as a vector in the tight-face direction. -/
private def subtourCrossRectangleFaceDirection
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    (affineSpan ℝ (subtour_elimination_face n S)).direction :=
  ⟨subtourCrossRectangleDirection hp hpLower
      (subtourRightBlock_two_le hpLower hpUpper) σ z,
    subtourCrossRectangleDirection_mem_faceDirection hn hpLower hpUpper S σ hσ z⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: a cross-rectangle face
direction belongs to the kernel of internal-coordinate restriction. -/
private lemma subtourCrossRectangleFaceDirection_mem_internalKernel
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    subtourCrossRectangleFaceDirection hn hpLower hpUpper hp S σ hσ z ∈
      LinearMap.ker
        ((subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  -- The kernel equation is exactly the previously established internal-coordinate vanishing.
  exact subtourInternalRestriction_crossRectangle_eq_zero
    hn hpLower hpUpper S σ hσ z

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: an anchored cross rectangle as
an element of the internal-restriction kernel. -/
private def subtourCrossRectangleKernelDirection
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    LinearMap.ker
      ((subtourInternalRestriction hp σ).domRestrict
        (affineSpan ℝ (subtour_elimination_face n S)).direction) :=
  ⟨subtourCrossRectangleFaceDirection hn hpLower hpUpper hp S σ hσ z,
    subtourCrossRectangleFaceDirection_mem_internalKernel
      hn hpLower hpUpper hp S σ hσ z⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the anchored cross rectangles
remain linearly independent inside the internal-restriction kernel. -/
private lemma subtourCrossRectangleKernelDirection_linearIndependent
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    LinearIndependent ℝ
      (subtourCrossRectangleKernelDirection hn hpLower hpUpper hp S σ hσ) := by
  let inclusion :
      LinearMap.ker
          ((subtourInternalRestriction hp σ).domRestrict
            (affineSpan ℝ (subtour_elimination_face n S)).direction) →ₗ[ℝ]
        (complete_graph_edges n → ℝ) :=
    (affineSpan ℝ (subtour_elimination_face n S)).direction.subtype.comp
      (LinearMap.ker
        ((subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction)).subtype
  apply LinearIndependent.of_comp inclusion
  -- Forgetting the two subtypes recovers the already independent ambient rectangle family.
  simpa [inclusion, Function.comp_def, subtourCrossRectangleKernelDirection,
    subtourCrossRectangleFaceDirection] using
      subtourCrossRectangleDirection_linearIndependent hn hpLower hpUpper S σ hσ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean`: the two internal path
dimensions and the cross-rectangle dimension add to the TSP facet dimension. -/
private lemma subtourDimensionArithmetic
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (Nat.choose p 2 - 1 + (Nat.choose q 2 - 1)) +
        (p - 1) * (q - 1) + 1 =
      Nat.choose (p + q) 2 - (p + q) := by
  have hpChoosePos : 0 < Nat.choose p 2 := Nat.choose_pos hp
  have hqChoosePos : 0 < Nat.choose q 2 := Nat.choose_pos hq
  have hpChooseSplit : Nat.choose p 2 - 1 + 1 = Nat.choose p 2 := by omega
  have hqChooseSplit : Nat.choose q 2 - 1 + 1 = Nat.choose q 2 := by omega
  have hpSplit : p - 1 + 1 = p := by omega
  have hqSplit : q - 1 + 1 = q := by omega
  have hprod :
      p * q = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by
    calc
      p * q = ((p - 1) + 1) * ((q - 1) + 1) := by rw [hpSplit, hqSplit]
      _ = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by ring
  have hchoose :
      Nat.choose (p + q) 2 = Nat.choose p 2 + p * q + Nat.choose q 2 := by
    -- Vandermonde leaves the three rank-two terms in antidiagonal order.
    rw [Nat.add_choose_eq]
    norm_num [Finset.antidiagonal]
    ring
  -- Expand the three positive predecessors and use Vandermonde's identity at rank two.
  omega

/-- Helper for Theorem 2.3: the scaled four-edge exchange is an ambient TSP direction on which
the subtour cut functional evaluates to one. -/
private lemma subtourCut_existsNormalizingDirection
    {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card) (hS_upper : S.card ≤ n - 2) :
    ∃ w : complete_graph_edges n → ℝ,
      w ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction ∧
        dotProductLinearMap (cutIncidenceVector S) w = 1 := by
  classical
  obtain ⟨a, b, i, j, ha, hb, hab, hi, hj, hij⟩ :=
    exists_two_vertices_on_each_shore S hS_lower hS_upper
  have hai : a ≠ i := fun h ↦ hi (h ▸ ha)
  have haj : a ≠ j := fun h ↦ hj (h ▸ ha)
  have hbi : b ≠ i := fun h ↦ hi (h ▸ hb)
  have hbj : b ≠ j := fun h ↦ hj (h ▸ hb)
  let eab : complete_graph_edges n := subtourEdge a b hab
  let eij : complete_graph_edges n := subtourEdge i j hij
  let eai : complete_graph_edges n := subtourEdge a i hai
  let ebj : complete_graph_edges n := subtourEdge b j hbj
  let w : complete_graph_edges n → ℝ :=
    Pi.single eai (1 / 2 : ℝ) + Pi.single ebj (1 / 2 : ℝ) -
      Pi.single eab (1 / 2 : ℝ) - Pi.single eij (1 / 2 : ℝ)
  have hwIncident :
      ∀ z : Fin n,
        ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) z).map
            completeGraphEdgeEquiv.symm.toEmbedding).sum w = 0 := by
    intro z
    let I :=
      (incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) z).map
        completeGraphEdgeEquiv.symm.toEmbedding
    have heaiSum : I.sum (Pi.single eai (1 / 2 : ℝ)) =
        if z ∈ (eai : Sym2 (Fin n)) then (1 / 2 : ℝ) else 0 := by
      exact incidentEdgeSum_single_eq_indicator z eai (1 / 2)
    have hebjSum : I.sum (Pi.single ebj (1 / 2 : ℝ)) =
        if z ∈ (ebj : Sym2 (Fin n)) then (1 / 2 : ℝ) else 0 := by
      exact incidentEdgeSum_single_eq_indicator z ebj (1 / 2)
    have heabSum : I.sum (Pi.single eab (1 / 2 : ℝ)) =
        if z ∈ (eab : Sym2 (Fin n)) then (1 / 2 : ℝ) else 0 := by
      exact incidentEdgeSum_single_eq_indicator z eab (1 / 2)
    have heijSum : I.sum (Pi.single eij (1 / 2 : ℝ)) =
        if z ∈ (eij : Sym2 (Fin n)) then (1 / 2 : ℝ) else 0 := by
      exact incidentEdgeSum_single_eq_indicator z eij (1 / 2)
    -- Each of the four anchor vertices sees one positive and one negative half-edge.
    change I.sum w = 0
    rw [show I.sum w =
        I.sum (Pi.single eai (1 / 2 : ℝ)) + I.sum (Pi.single ebj (1 / 2 : ℝ)) -
          I.sum (Pi.single eab (1 / 2 : ℝ)) - I.sum (Pi.single eij (1 / 2 : ℝ)) by
      simp [w, Finset.sum_add_distrib, Finset.sum_sub_distrib]]
    rw [heaiSum, hebjSum, heabSum, heijSum]
    by_cases hza : z = a
    · subst z
      simp [eab, eij, eai, ebj, mem_subtourEdge_iff, hab, hai, haj]
    by_cases hzb : z = b
    · subst z
      simp [eab, eij, eai, ebj, mem_subtourEdge_iff, hbi, hbj, hza]
    by_cases hzi : z = i
    · subst z
      simp [eab, eij, eai, ebj, mem_subtourEdge_iff, hij, hza, hzb]
    by_cases hzj : z = j
    · subst z
      simp [eab, eij, eai, ebj, mem_subtourEdge_iff, hza, hzb, hzi]
    · simp [eab, eij, eai, ebj, mem_subtourEdge_iff, hza, hzb, hzi, hzj]
  let x₀ : complete_graph_edges n → ℝ :=
    hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  have hx₀Poly : x₀ ∈ travelingSalesmanPolytope n := by
    -- The identity tour is one of the convex-hull generators.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx₀Aff : x₀ ∈ affineSpan ℝ (travelingSalesmanPolytope n) :=
    subset_affineSpan ℝ _ hx₀Poly
  have hspan :
      (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
        travelingSalesmanDegreeConstraintSet n := by
    simpa using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n (by omega)
  have hx₀Degree : x₀ ∈ travelingSalesmanDegreeConstraintSet n := by
    rw [← hspan]
    exact hx₀Aff
  have hx₀wDegree : x₀ + w ∈ travelingSalesmanDegreeConstraintSet n :=
    add_mem_travelingSalesmanDegreeConstraintSet_of_incident_sum_zero hx₀Degree hwIncident
  have hx₀wAff : x₀ + w ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    have hx₀wSet : x₀ + w ∈
        (affineSpan ℝ (travelingSalesmanPolytope n) :
          Set (complete_graph_edges n → ℝ)) := by
      rw [hspan]
      exact hx₀wDegree
    exact hx₀wSet
  have hwDirection : w ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
    have hvsub := AffineSubspace.vsub_mem_direction hx₀wAff hx₀Aff
    simpa [vsub_eq_sub] using hvsub
  have heab : cutIncidenceVector S eab = 0 := by
    simp [eab, subtourEdge, cutIncidenceVector_apply_pair, ha, hb]
  have heij : cutIncidenceVector S eij = 0 := by
    simp [eij, subtourEdge, cutIncidenceVector_apply_pair, hi, hj]
  have heai : cutIncidenceVector S eai = 1 := by
    simp [eai, subtourEdge, cutIncidenceVector_apply_pair, ha, hi]
  have hebj : cutIncidenceVector S ebj = 1 := by
    simp [ebj, subtourEdge, cutIncidenceVector_apply_pair, hb, hj]
  have hwEval : dotProductLinearMap (cutIncidenceVector S) w = 1 := by
    -- Only the two crossing coordinates contribute to the cut dot product.
    rw [dotProductLinearMap_apply]
    calc
      cutIncidenceVector S ⬝ᵥ w =
          cutIncidenceVector S ⬝ᵥ Pi.single eai (1 / 2 : ℝ) +
            cutIncidenceVector S ⬝ᵥ Pi.single ebj (1 / 2 : ℝ) -
              cutIncidenceVector S ⬝ᵥ Pi.single eab (1 / 2 : ℝ) -
                cutIncidenceVector S ⬝ᵥ Pi.single eij (1 / 2 : ℝ) := by
            simp [w, dotProduct_add, dotProduct_sub]
      _ = cutIncidenceVector S eai * (1 / 2 : ℝ) +
            cutIncidenceVector S ebj * (1 / 2 : ℝ) -
              cutIncidenceVector S eab * (1 / 2 : ℝ) -
                cutIncidenceVector S eij * (1 / 2 : ℝ) := by
            rw [dotProduct_single, dotProduct_single, dotProduct_single, dotProduct_single]
      _ = 1 := by rw [heab, heij, heai, hebj]; norm_num
  exact ⟨w, hwDirection, hwEval⟩

/-- Helper for Theorem 2.3: the subtour equality face is a facet whenever the corresponding
subtour inequality is facet-defining. This local owner replaces the broken transitive import edge
from Chapter 7. -/
theorem subtour_elimination_face_isFacetOf
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n S) := by
  -- Route correction: the old proof depended on `ch7_sec7_4_theorem_7_19`, whose import chain
  -- contains an unresolved reverse-inclusion proof.  We instead keep the proved exposed-face
  -- shell local and isolate the three combinatorial inputs needed by the independent-family route.
  have hface : (subtour_elimination_face n S).Nonempty := by
    obtain ⟨π, hπ⟩ := exists_subtour_block_order S
    let σ : Equiv.Perm (Fin n) := π.symm
    have hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < S.card := by
      intro t
      simpa [σ] using hπ (σ t)
    have hpoly : hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanPolytope n := by
      -- The block-ordered tour is one of the convex-hull generators.
      rw [travelingSalesmanPolytope_eq_convexHull]
      exact subset_convexHull ℝ _ (Set.mem_range_self σ)
    have hcut : subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) = 2 := by
      rw [subtour_elimination_value_eq_dotProduct]
      exact blockOrderedTour_cutValue_eq_two S S.card σ hn hS_lower hS_upper hσ
    exact ⟨hamiltonian_tour_incidence_vector σ, hpoly, hcut⟩
  have hvalid :
      is_valid_inequality (travelingSalesmanPolytope n) (-cutIncidenceVector S) (-2) := by
    rw [is_valid_inequality_iff]
    intro x hx
    let H : Set (complete_graph_edges n → ℝ) :=
      {y | 2 ≤ dotProduct (cutIncidenceVector S) y}
    have hHconvex : Convex ℝ H := by
      let L : (complete_graph_edges n → ℝ) →ₗ[ℝ] ℝ :=
        dotProductLinearMap (cutIncidenceVector S)
      have hH : H = L ⁻¹' Set.Ici (2 : ℝ) := by
        ext y
        simp [H, L]
      rw [hH]
      exact (convex_Ici (2 : ℝ)).linear_preimage L
    have hpoly : travelingSalesmanPolytope n ⊆ H := by
      rw [travelingSalesmanPolytope_eq_convexHull]
      refine convexHull_min ?_ hHconvex
      rintro y ⟨σ, rfl⟩
      -- Every generating tour has at least the two boundary edges proved above.
      exact hamiltonianTour_cutValue_ge_two hn S hS_lower hS_upper σ
    have hge : 2 ≤ dotProduct (cutIncidenceVector S) x := hpoly hx
    simpa [dotProduct_neg] using neg_le_neg hge
  have hfinrank :
      Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
    let D : Submodule ℝ (complete_graph_edges n → ℝ) :=
      (affineSpan ℝ (travelingSalesmanPolytope n)).direction
    let L : (complete_graph_edges n → ℝ) →ₗ[ℝ] ℝ :=
      dotProductLinearMap (cutIncidenceVector S)
    have hdir_le :
        (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
          D ⊓ LinearMap.ker L := by
      -- The already-normalized face equation supplies the ambient and kernel inclusions.
      simpa [D, L] using subtourFaceDirection_le_ambientInfCutKernel S hface
    have hnormalizing :
        ∃ w : complete_graph_edges n → ℝ, w ∈ D ∧ L w = 1 := by
      -- The sparse four-edge exchange supplies the required transverse direction.
      simpa [D, L] using
        subtourCut_existsNormalizingDirection hn S hS_lower hS_upper
    obtain ⟨w, hwD, hwL⟩ := hnormalizing
    have hkernel_codim :
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
      -- A transverse ambient direction makes the restricted cut kernel codimension one.
      exact submodule_finrank_inf_ker_add_one_of_eval_one D L hwD hwL
    have hupper :
        Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 ≤
          Module.finrank ℝ ↥D := by
      have hmono :
          Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
            Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) :=
        Submodule.finrank_mono hdir_le
      omega
    have hlower :
        Module.finrank ℝ ↥D ≤
          Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 := by
      obtain ⟨π, hπ⟩ := exists_subtour_block_order S
      let σ : Equiv.Perm (Fin n) := π.symm
      have hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < S.card := by
        intro t
        simpa [σ] using hπ (σ t)
      have hp : S.card ≤ n := by omega
      have hqLower : 2 ≤ n - S.card := by omega
      let Kleft : Submodule ℝ (complete_graph_edges S.card → ℝ) :=
        LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges S.card)).sumCoords
      let Kright : Submodule ℝ (complete_graph_edges (n - S.card) → ℝ) :=
        LinearMap.ker
          (Pi.basisFun ℝ (complete_graph_edges (n - S.card))).sumCoords
      let R :=
        (subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction
      have hinternal : Kleft.prod Kright ≤ LinearMap.range R := by
        -- The two independent path-direction blocks are realized by tight block-tour differences.
        simpa [Kleft, Kright, R] using
          subtourInternalDirections_le_range hn hS_lower hS_upper hp S σ hσ
      have hKleftEq :
          Kleft = (affineSpan ℝ (hamiltonian_path_polytope S.card)).direction := by
        apply le_antisymm
        · simpa [Kleft] using
            sumCoords_ker_le_hamiltonian_path_direction S.card hS_lower
        · simpa [Kleft] using
            hamiltonian_path_polytope_direction_le_sumCoords_ker S.card
      have hKrightEq :
          Kright =
            (affineSpan ℝ (hamiltonian_path_polytope (n - S.card))).direction := by
        apply le_antisymm
        · simpa [Kright] using
            sumCoords_ker_le_hamiltonian_path_direction (n - S.card) hqLower
        · simpa [Kright] using
            hamiltonian_path_polytope_direction_le_sumCoords_ker (n - S.card)
      have hKleftFinrank :
          Module.finrank ℝ Kleft = Nat.choose S.card 2 - 1 := by
        rw [hKleftEq]
        exact hamiltonian_path_polytope_finrank_direction_affineSpan S.card
      have hKrightFinrank :
          Module.finrank ℝ Kright = Nat.choose (n - S.card) 2 - 1 := by
        rw [hKrightEq]
        exact hamiltonian_path_polytope_finrank_direction_affineSpan (n - S.card)
      have hinternalFinrank :
          Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1) ≤
            Module.finrank ℝ (LinearMap.range R) := by
        calc
          Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1) =
              Module.finrank ℝ ↥(Kleft.prod Kright) := by
                rw [finrank_submoduleProd, hKleftFinrank, hKrightFinrank]
          _ ≤ Module.finrank ℝ (LinearMap.range R) :=
            Submodule.finrank_mono hinternal
      have hcrossIndependent :
          LinearIndependent ℝ
            (subtourCrossRectangleKernelDirection
              hn hS_lower hS_upper hp S σ hσ) := by
        exact subtourCrossRectangleKernelDirection_linearIndependent
          hn hS_lower hS_upper hp S σ hσ
      have hkernelFinrank :
          (S.card - 1) * (n - S.card - 1) ≤
            Module.finrank ℝ (LinearMap.ker R) := by
        have hcard := hcrossIndependent.fintype_card_le_finrank
        simpa [R] using hcard
      have hrankNullity :
          Module.finrank ℝ (LinearMap.range R) +
              Module.finrank ℝ (LinearMap.ker R) =
            Module.finrank ℝ
              (affineSpan ℝ (subtour_elimination_face n S)).direction := by
        simpa [R] using LinearMap.finrank_range_add_finrank_ker R
      have hfaceLower :
          (Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1)) +
              (S.card - 1) * (n - S.card - 1) ≤
            Module.finrank ℝ
              (affineSpan ℝ (subtour_elimination_face n S)).direction := by
        calc
          (Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1)) +
                (S.card - 1) * (n - S.card - 1) ≤
              Module.finrank ℝ (LinearMap.range R) +
                Module.finrank ℝ (LinearMap.ker R) :=
            Nat.add_le_add hinternalFinrank hkernelFinrank
          _ = Module.finrank ℝ
                (affineSpan ℝ (subtour_elimination_face n S)).direction := hrankNullity
      have hDfinrank : Module.finrank ℝ ↥D = Nat.choose n 2 - n := by
        simpa [D] using
          finrank_direction_affineSpan_travelingSalesmanPolytope n (by omega)
      have hsum : S.card + (n - S.card) = n := Nat.add_sub_of_le hp
      have harithmetic := subtourDimensionArithmetic
        S.card (n - S.card) hS_lower hqLower
      rw [hsum] at harithmetic
      -- Rank-nullity combines the internal path directions with all cross rectangles.
      rw [hDfinrank]
      calc
        Nat.choose n 2 - n =
            (Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1)) +
              (S.card - 1) * (n - S.card - 1) + 1 := harithmetic.symm
        _ ≤ Module.finrank ℝ
              (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 :=
          Nat.add_le_add_right hfaceLower 1
    -- The independent-family lower bound meets the cut-kernel upper bound.
    simpa [D] using Nat.le_antisymm hupper hlower
  -- The remaining assembly is now independent of the concrete tour constructions.
  exact subtourEliminationFace_isFacetOf_of_finrank S hface hvalid hfinrank

/-- Helper for Theorem 2.3: a valid inequality for a nonempty matrix polyhedron is equivalent to a
nonnegative row multiplier certificate. -/
theorem valid_inequality_iff_exists_nonneg_row_multiplier
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty) :
    is_valid_inequality (polyhedron_le_set A b) c δ ↔
      ∃ u : Fin m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
  constructor
  · intro hvalid
    have hP_nonempty_raw : Set.Nonempty {x : Fin n → ℝ | A *ᵥ x ≤ b} := by
      simpa [polyhedron_le_set] using hP_nonempty
    have hvalid_raw : ∀ ⦃x : Fin n → ℝ⦄, x ∈ {x : Fin n → ℝ | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ := by
      simpa [is_valid_inequality, polyhedron_le_set] using hvalid
    exact exists_nonneg_row_multiplier_of_valid_inequality A b c δ hP_nonempty_raw hvalid_raw
  · rintro ⟨u, hu_nonneg, hu_row, hub⟩
    rw [is_valid_inequality_iff]
    intro x hx
    -- Convert the exact matrix description into the primal and dual feasible regions.
    have hx_primal : x ∈ primal_feasible_region A b := by
      simpa [polyhedron_le_set, primal_feasible_region] using hx
    have hu_dual : u ∈ dual_feasible_region A c := by
      exact (mem_dual_feasible_region_iff A c u).2 ⟨hu_row, hu_nonneg⟩
    -- Weak duality bounds `c ⬝ᵥ x` by `u ⬝ᵥ b`, and the certificate finishes the estimate.
    calc
      c ⬝ᵥ x ≤ u ⬝ᵥ b := weak_duality_feasible_pair A b c hx_primal hu_dual
      _ ≤ δ := hub

-- Helper for Theorem 2.3: the row-count facet bound starts with the single-row tight-face owner.
/-- Helper for Theorem 2.3: the singleton row face of `polyhedron_le_set A b` is the feasible set
where row `j` is tight. -/
def singleRowFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m) :
    Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | x ∈ polyhedron_le_set A b ∧ (A *ᵥ x) j = b j}

/-- Helper for Theorem 2.3: membership in `singleRowFace A b j` means feasibility together with
equality in row `j`. -/
theorem mem_singleRowFace_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {j : Fin m}
    {x : Fin n → ℝ} :
    x ∈ singleRowFace A b j ↔ x ∈ polyhedron_le_set A b ∧ (A *ᵥ x) j = b j :=
  Iff.rfl

/-- Helper for Theorem 2.3: the single-row active face is the canonical equality face cut out by
the `j`th row inequality. -/
lemma singleRowFace_eq_face_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m) :
    singleRowFace A b j = face_set (polyhedron_le_set A b) (A j) (b j) := by
  ext x
  rw [mem_singleRowFace_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxj⟩
    refine ⟨hxP, ?_⟩
    simpa [Matrix.mulVec, dotProduct] using hxj
  · rintro ⟨hxP, hxj⟩
    refine ⟨hxP, ?_⟩
    simpa [Matrix.mulVec, dotProduct] using hxj

/-- Helper for Theorem 2.3: the row-evaluation face `singleRowFace A b j` is exposed by the
`j`th row functional. -/
lemma singleRowFace_isExposed
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m) :
    IsExposed ℝ (polyhedron_le_set A b) (singleRowFace A b j) := by
  -- Route correction: rewrite the row face to the canonical equality-face owner and apply the
  -- generic exposed-face API there, rather than manipulating a raw exposing functional.
  rw [singleRowFace_eq_face_set]
  apply isExposed_face_set_of_valid_inequality
  intro x hx
  simpa [Matrix.mulVec, dotProduct] using hx j

/-- Helper for Theorem 2.3: every codimension-one exposed face of `polyhedron_le_set A b` is cut
out by one remaining row. -/
lemma exists_eq_singleRowFace_of_isFacetOf
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (F : Set (Fin n → ℝ))
    (hF : IsFacetOf (polyhedron_le_set A b) F) :
    ∃ j : {j // j ∈ remaining_inequality_indices A b},
      F = singleRowFace A b j.1 := by
  classical
  rcases isFacetOf_iff.mp hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  obtain ⟨x0, hx0F⟩ := hF_nonempty
  have hF_nonempty' : F.Nonempty := ⟨x0, hx0F⟩
  have hx0P : x0 ∈ polyhedron_le_set A b := hF_exposed.subset hx0F
  obtain ⟨c, δ, hvalid, hF_eq_face⟩ :=
    IsExposed.exists_eq_face_set_of_nonempty hF_exposed hF_nonempty'
  have hx0eq : c ⬝ᵥ x0 = δ := by
    have hx0Face : x0 ∈ face_set (polyhedron_le_set A b) c δ := by
      simpa [hF_eq_face] using hx0F
    exact (mem_face_set_iff.mp hx0Face).2
  obtain ⟨u, hu_nonneg, hu_row, hub_le⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier A b c δ h_nonempty).mp hvalid
  have hub_eq : u ⬝ᵥ b = δ := by
    have hdelta_le : δ ≤ u ⬝ᵥ b := by
      calc
        δ = c ⬝ᵥ x0 := hx0eq.symm
        _ = (u ᵥ* A) ⬝ᵥ x0 := by rw [← hu_row]
        _ = u ⬝ᵥ (A *ᵥ x0) := by rw [← Matrix.dotProduct_mulVec]
        _ ≤ u ⬝ᵥ b := by
              exact dotProduct_le_dotProduct_of_nonneg_left hx0P hu_nonneg
    exact le_antisymm hub_le hdelta_le
  have hpos_row :
      ∃ j : Fin m, 0 < u j ∧ j ∈ remaining_inequality_indices A b := by
    by_contra hno
    have hall_implicit :
        ∀ j : Fin m, 0 < u j → is_implicit_equality A b j := by
      intro j hj
      by_contra hj_not
      exact hno ⟨j, hj, (mem_remaining_inequality_indices_iff A b j).2 hj_not⟩
    have hall_eq :
        ∀ y ∈ polyhedron_le_set A b, c ⬝ᵥ y = δ := by
      intro y hy
      calc
        c ⬝ᵥ y = (u ᵥ* A) ⬝ᵥ y := by rw [hu_row]
        _ = u ⬝ᵥ (A *ᵥ y) := by rw [← Matrix.dotProduct_mulVec]
        _ = u ⬝ᵥ b := by
              rw [dotProduct]
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hi_pos : 0 < u i
              · have hi_eq : (A *ᵥ y) i = b i := hall_implicit i hi_pos hy
                rw [hi_eq]
              · have hi_zero : u i = 0 := by
                  exact le_antisymm (le_of_not_gt hi_pos) (hu_nonneg i)
                simp [hi_zero]
        _ = δ := hub_eq
    have hF_eq_poly : F = polyhedron_le_set A b := by
      apply Set.Subset.antisymm hF_exposed.subset
      intro y hy
      rw [hF_eq_face, mem_face_set_iff]
      exact ⟨hy, hall_eq y hy⟩
    have hcollapse :
        Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
      have hcollapse' := hF_codim
      rw [hF_eq_poly] at hcollapse'
      exact hcollapse'
    omega
  rcases hpos_row with ⟨j, hj_pos, hj_remaining⟩
  have hF_subset_row :
      F ⊆ singleRowFace A b j := by
    intro x hxF
    have hxFace : x ∈ face_set (polyhedron_le_set A b) c δ := by
      simpa [hF_eq_face] using hxF
    have hxP : x ∈ polyhedron_le_set A b := (mem_face_set_iff.mp hxFace).1
    have hx_eqδ : c ⬝ᵥ x = δ := (mem_face_set_iff.mp hxFace).2
    have hsum_zero : ∑ i : Fin m, u i * (b i - (A *ᵥ x) i) = 0 := by
      calc
        ∑ i : Fin m, u i * (b i - (A *ᵥ x) i)
            = u ⬝ᵥ b - u ⬝ᵥ (A *ᵥ x) := by
                simp [dotProduct, mul_sub, Finset.sum_sub_distrib]
        _ = δ - c ⬝ᵥ x := by
              rw [hub_eq, ← hu_row, ← Matrix.dotProduct_mulVec]
        _ = 0 := by rw [hx_eqδ, sub_self]
    have hterm_zero :
        ∀ i : Fin m, u i * (b i - (A *ᵥ x) i) = 0 := by
      have hzero_on_univ :
          ∀ i ∈ (Finset.univ : Finset (Fin m)), u i * (b i - (A *ᵥ x) i) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ ↦ mul_nonneg (hu_nonneg i) (sub_nonneg.mpr (hxP i)))).1 hsum_zero
      intro i
      exact hzero_on_univ i (Finset.mem_univ i)
    have hj_eq : (A *ᵥ x) j = b j := by
      have hprod_zero : u j * (b j - (A *ᵥ x) j) = 0 := hterm_zero j
      have hgap_zero : b j - (A *ᵥ x) j = 0 := by
        exact (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt hj_pos)
      linarith
    exact ⟨hxP, hj_eq⟩
  have hx0Row : x0 ∈ singleRowFace A b j := hF_subset_row hx0F
  obtain ⟨xP, hxP, hxP_lt⟩ :=
    exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b j hj_remaining
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ (polyhedron_le_set A b)).direction
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductLinearMap (A j)
  let Lc : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductLinearMap c
  have hrow_subset_poly : singleRowFace A b j ⊆ polyhedron_le_set A b := by
    intro x hx
    exact (mem_singleRowFace_iff.mp hx).1
  have hrow_aff_le :
      affineSpan ℝ (singleRowFace A b j) ≤ affineSpan ℝ (polyhedron_le_set A b) :=
    affineSpan_mono ℝ hrow_subset_poly
  have hrow_dir_le :
      (affineSpan ℝ (singleRowFace A b j)).direction ≤ D ⊓ LinearMap.ker L := by
    have hlevel_row :
        ∀ ⦃x : Fin n → ℝ⦄, x ∈ singleRowFace A b j → L x = b j := by
      intro x hx
      simpa [L, dotProductLinearMap_apply] using hx.2
    intro v hv
    refine ⟨?_, ?_⟩
    · exact (AffineSubspace.direction_le hrow_aff_le) hv
    · exact (affineSpan_direction_le_ker_of_forall_eq hx0Row hlevel_row) hv
  have hx0_affP : x0 ∈ affineSpan ℝ (polyhedron_le_set A b) := subset_affineSpan ℝ _ hx0P
  have hxP_affP : xP ∈ affineSpan ℝ (polyhedron_le_set A b) := subset_affineSpan ℝ _ hxP
  let gap : ℝ := b j - (A *ᵥ xP) j
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  let w : Fin n → ℝ := gap⁻¹ • (x0 - xP)
  have hwD : w ∈ D := by
    dsimp [D, w]
    exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hx0_affP hxP_affP)
  have hw_eval : L w = 1 := by
    have hx0_eval : L x0 = b j := by
      simpa [L, dotProductLinearMap_apply] using hx0Row.2
    have hxP_eval : L xP = (A *ᵥ xP) j := by
      simp [L, Matrix.mulVec, dotProduct]
    calc
      L w = gap⁻¹ * L (x0 - xP) := by
            simp [L, w]
      _ = gap⁻¹ * (L x0 - L xP) := by
            rw [LinearMap.map_sub]
      _ = gap⁻¹ * gap := by
            rw [hx0_eval, hxP_eval]
      _ = 1 := by
            field_simp [hgap_pos.ne']
  have hcodim_ker :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
    exact submodule_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
  have hF_aff_le :
      affineSpan ℝ F ≤ affineSpan ℝ (singleRowFace A b j) :=
    affineSpan_mono ℝ hF_subset_row
  have hF_dir_le :
      (affineSpan ℝ F).direction ≤ (affineSpan ℝ (singleRowFace A b j)).direction := by
    exact AffineSubspace.direction_le hF_aff_le
  have hF_codim' :
      Module.finrank ℝ ↥((affineSpan ℝ F).direction) + 1 =
        Module.finrank ℝ ↥D := by
    simpa [D] using hF_codim
  have hdir_finrank_eq :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (affineSpan ℝ (singleRowFace A b j)).direction := by
    have hF_le :
        Module.finrank ℝ ↥((affineSpan ℝ F).direction) ≤
          Module.finrank ℝ ↥((affineSpan ℝ (singleRowFace A b j)).direction) :=
      Submodule.finrank_mono hF_dir_le
    have hrow_le :
        Module.finrank ℝ ↥((affineSpan ℝ (singleRowFace A b j)).direction) ≤
          Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) :=
      Submodule.finrank_mono hrow_dir_le
    omega
  have hdir_eq :
      (affineSpan ℝ F).direction =
        (affineSpan ℝ (singleRowFace A b j)).direction := by
    exact Submodule.eq_of_le_of_finrank_eq hF_dir_le hdir_finrank_eq
  have hlevel_F :
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → Lc x = δ := by
    intro x hx
    have hxFace : x ∈ face_set (polyhedron_le_set A b) c δ := by
      simpa [hF_eq_face] using hx
    simpa [Lc, dotProductLinearMap_apply] using (mem_face_set_iff.mp hxFace).2
  have hF_dir_ker :
      (affineSpan ℝ F).direction ≤ LinearMap.ker Lc := by
    exact affineSpan_direction_le_ker_of_forall_eq hx0F hlevel_F
  have hrow_subset_F :
      singleRowFace A b j ⊆ F := by
    intro x hxRow
    have hxRow_aff : x ∈ affineSpan ℝ (singleRowFace A b j) := subset_affineSpan ℝ _ hxRow
    have hx0Row_aff : x0 ∈ affineSpan ℝ (singleRowFace A b j) := subset_affineSpan ℝ _ hx0Row
    have hx_vsub_row :
        x -ᵥ x0 ∈ (affineSpan ℝ (singleRowFace A b j)).direction :=
      AffineSubspace.vsub_mem_direction hxRow_aff hx0Row_aff
    have hx_vsub_F :
        x -ᵥ x0 ∈ (affineSpan ℝ F).direction := by
      simpa [hdir_eq] using hx_vsub_row
    have hx_zero : Lc (x - x0) = 0 := hF_dir_ker hx_vsub_F
    have hx0_level : Lc x0 = δ := by
      simpa [Lc, dotProductLinearMap_apply] using hx0eq
    have hlx : Lc x = δ := by
      have hsub_zero : Lc x - Lc x0 = 0 := by
        simpa [LinearMap.map_sub] using hx_zero
      linarith
    rw [hF_eq_face, mem_face_set_iff]
    refine ⟨hxRow.1, ?_⟩
    simpa [Lc, dotProductLinearMap_apply] using hlx
  refine ⟨⟨j, hj_remaining⟩, ?_⟩
  exact Set.Subset.antisymm hF_subset_row hrow_subset_F

lemma facetCount_le_rowCount_ofExactDescription
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty) :
    {F : Set (Fin n → ℝ) | IsFacetOf (polyhedron_le_set A b) F}.ncard ≤ m := by
  classical
  let rowFacet : {j // j ∈ remaining_inequality_indices A b} → Set (Fin n → ℝ) :=
    fun j ↦ singleRowFace A b j.1
  have hsubset :
      {F : Set (Fin n → ℝ) | IsFacetOf (polyhedron_le_set A b) F} ⊆ Set.range rowFacet := by
    intro F hF
    rcases exists_eq_singleRowFace_of_isFacetOf A b h_nonempty F hF with
      ⟨j, hj⟩
    -- Each facet coincides with the face where one remaining row becomes tight.
    exact ⟨j, hj.symm⟩
  have hrowFacet_finite : (Set.range rowFacet).Finite := Set.finite_range rowFacet
  have hrange_le :
      (Set.range rowFacet).ncard ≤ Fintype.card {j // j ∈ remaining_inequality_indices A b} := by
    calc
      (Set.range rowFacet).ncard
          = (rowFacet '' (Set.univ : Set {j // j ∈ remaining_inequality_indices A b})).ncard := by
            rw [Set.image_univ]
      _ ≤ (Set.univ : Set {j // j ∈ remaining_inequality_indices A b}).ncard := by
            exact Set.ncard_image_le
      _ = Fintype.card {j // j ∈ remaining_inequality_indices A b} := by
            simp
  -- Bound the finite set of facets by the finite family of remaining inequality rows.
  calc
    {F : Set (Fin n → ℝ) | IsFacetOf (polyhedron_le_set A b) F}.ncard
        ≤ (Set.range rowFacet).ncard := by
          exact Set.ncard_le_ncard hsubset hrowFacet_finite
    _ ≤ Fintype.card {j // j ∈ remaining_inequality_indices A b} := hrange_le
    _ ≤ m := by
          simpa using
            (Fintype.card_subtype_le fun j : Fin m ↦ j ∈ remaining_inequality_indices A b)

/-- Helper for Theorem 2.3: the Chapter 7 subtour facets remain facets after reindexing the edge
coordinates to the canonical `Fin` chart. -/
lemma subtourFaceReindexed_isFacet
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    IsFacetOf (travelingSalesmanPolytopeReindexed n)
      ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges n))).symm ''
        subtour_elimination_face n S) := by
  let e :
      (complete_graph_edges n → ℝ) ≃L[ℝ] (Fin (Fintype.card (complete_graph_edges n)) → ℝ) :=
    (LinearEquiv.funCongrLeft ℝ ℝ
      (Fintype.equivFin (complete_graph_edges n))).symm.toContinuousLinearEquiv
  have hfacet_native : IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n S) :=
    subtour_elimination_face_isFacetOf hn S hS_lower hS_upper
  -- Transport the native Chapter 7 facet through the coordinate equivalence.
  simpa [travelingSalesmanPolytopeReindexed, e] using
    (isFacetOf_image_continuousLinearEquiv e).1 hfacet_native

/-- Helper for Theorem 2.3: any polynomial bound on the row count is eventually dominated by
`4 ^ k` along odd input sizes `2 * k + 1`. -/
lemma natPolynomial_mulEvalOdd_lt_fourPow (p : Polynomial ℕ) :
    ∃ k : ℕ, 4 ≤ k ∧ k * p.eval (2 * k + 1) < 4 ^ k := by
  let P : Polynomial ℝ := p.map (Nat.castRingHom ℝ)
  have hdeg :
      P.degree ≤ (((Polynomial.X : Polynomial ℝ) ^ (P.natDegree + 1)).degree) := by
    -- Compare the lifted polynomial against one higher monomial degree so the later factor `k`
    -- is absorbed into the same asymptotic bound.
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_le_of_natDegree_le (Nat.le_succ _)
  have hpolyBigO :
      P.eval =O[atTop] fun x : ℝ ↦ x ^ (P.natDegree + 1) := by
    simpa using
      (Polynomial.isBigO_atTop_of_degree_le P
        (((Polynomial.X : Polynomial ℝ) ^ (P.natDegree + 1))) hdeg)
  obtain ⟨C, hCpos, hCbound⟩ := hpolyBigO.exists_pos
  have htNat : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop := by
    -- The odd-size specialization still tends to infinity.
    refine tendsto_atTop.2 ?_
    intro n
    exact Filter.eventually_atTop.2 ⟨n, fun k hk ↦ by omega⟩
  have htOdd : Tendsto (fun k : ℕ ↦ ((2 * k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htNat
  have hboundOdd :
      Asymptotics.IsBigOWith C atTop
        (fun k : ℕ ↦ P.eval ((2 * k + 1 : ℕ) : ℝ))
        (fun k : ℕ ↦ (((2 * k + 1 : ℕ) : ℝ) ^ (P.natDegree + 1))) :=
    hCbound.comp_tendsto htOdd
  have hpowLittle :
      (fun k : ℕ ↦ (((2 * k + 1 : ℕ) : ℝ) ^ (P.natDegree + 2))) =o[atTop]
        (fun k : ℕ ↦ Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) ) := by
    -- Exponential growth beats any fixed power, so the extra factor `k` can be absorbed.
    let hpowBase :=
      isLittleO_pow_exp_pos_mul_atTop (P.natDegree + 2) (by positivity : 0 < Real.log 2)
    simpa using hpowBase.comp_tendsto htOdd
  have hpowSmall :
      Asymptotics.IsBigOWith ((4 * C)⁻¹) atTop
        (fun k : ℕ ↦ (((2 * k + 1 : ℕ) : ℝ) ^ (P.natDegree + 2)))
        (fun k : ℕ ↦ Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) ) :=
    hpowLittle.def' (by positivity)
  have hEventually :
      ∀ᶠ k : ℕ in atTop,
        4 ≤ k ∧ ((k * p.eval (2 * k + 1) : ℕ) : ℝ) < (4 : ℝ) ^ k := by
    filter_upwards
      [eventually_ge_atTop 4, hboundOdd.bound, hpowSmall.bound] with k hk4 hkBig hkSmall
    let x : ℝ := ((2 * k + 1 : ℕ) : ℝ)
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      positivity
    have hx_ge_k : (k : ℝ) ≤ x := by
      have hnat : k ≤ 2 * k + 1 := by omega
      dsimp [x]
      exact_mod_cast hnat
    have hEvalCast : P.eval x = (p.eval (2 * k + 1) : ℕ) := by
      change
        Polynomial.eval ((Nat.castRingHom ℝ) (2 * k + 1))
            (Polynomial.map (Nat.castRingHom ℝ) p) =
          (Nat.castRingHom ℝ) (Polynomial.eval (2 * k + 1) p)
      simpa using Polynomial.eval_map_apply (Nat.castRingHom ℝ) (2 * k + 1)
    have hEvalNonneg : 0 ≤ P.eval x := by
      rw [hEvalCast]
      positivity
    have hpolyLe : P.eval x ≤ C * x ^ (P.natDegree + 1) := by
      have hnorm :
          ‖P.eval x‖ ≤ C * ‖x ^ (P.natDegree + 1)‖ := by
        simpa [x] using hkBig
      have habs :
          |P.eval x| ≤ C * x ^ (P.natDegree + 1) := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg, hCpos.le] using hnorm
      rwa [abs_of_nonneg hEvalNonneg] at habs
    have hleftLe : ((k * p.eval (2 * k + 1) : ℕ) : ℝ) ≤ C * x ^ (P.natDegree + 2) := by
      calc
        ((k * p.eval (2 * k + 1) : ℕ) : ℝ) = (k : ℝ) * P.eval x := by
          rw [Nat.cast_mul, hEvalCast]
        _ ≤ x * (C * x ^ (P.natDegree + 1)) := by
          gcongr
        _ = C * x ^ (P.natDegree + 2) := by
          rw [pow_succ']
          ring
    have hsmallLe :
        C * x ^ (P.natDegree + 2) ≤ (1 / 4 : ℝ) *
          Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) := by
      have hxpow :
          x ^ (P.natDegree + 2) ≤ (4 * C)⁻¹ *
            Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) := by
        simpa
          [x, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * k + 1)]
          using hkSmall
      have hCnonneg : 0 ≤ C := le_of_lt hCpos
      calc
        C * x ^ (P.natDegree + 2)
            ≤ C * ((4 * C)⁻¹ * Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ)))) := by
              gcongr
        _ = (1 / 4 : ℝ) * Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) := by
              field_simp [hCpos.ne']
    have hExpEq :
        Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) = (2 : ℝ) ^ (2 * k + 1) := by
      rw [Real.exp_mul, Real.exp_log (by norm_num : 0 < (2 : ℝ)), Real.rpow_natCast]
    have hpowEq : (1 / 4 : ℝ) * (2 : ℝ) ^ (2 * k + 1) = (1 / 2 : ℝ) * (4 : ℝ) ^ k := by
      rw [pow_succ', pow_mul]
      ring
    have hstrict : C * x ^ (P.natDegree + 2) < (4 : ℝ) ^ k := by
      have hpowPos : (0 : ℝ) < (4 : ℝ) ^ k := by
        positivity
      calc
        C * x ^ (P.natDegree + 2)
            ≤ (1 / 4 : ℝ) * Real.exp (Real.log 2 * (((2 * k + 1 : ℕ) : ℝ))) := hsmallLe
        _ = (1 / 2 : ℝ) * (4 : ℝ) ^ k := by rw [hExpEq, hpowEq]
        _ < (4 : ℝ) ^ k := by
              nlinarith
    exact ⟨hk4, lt_of_le_of_lt hleftLe hstrict⟩
  rw [eventually_atTop] at hEventually
  rcases hEventually with ⟨k, hkAll⟩
  have hkPair := hkAll k le_rfl
  refine ⟨k, hkPair.1, ?_⟩
  have hkCast : ((k * p.eval (2 * k + 1) : ℕ) : ℝ) < (4 : ℝ) ^ k := hkPair.2
  norm_num at hkCast
  exact_mod_cast hkCast

/-- Helper for Theorem 2.3: inserting the root `0` and shifting the remaining vertices by
`Fin.succEmb` identifies `k`-subsets of `Fin (2 * k)` with rooted `(k + 1)`-subsets of
`Fin (2 * k + 1)`. -/
def rootedOddSubsetEmbedding (k : ℕ) :
    Finset (Fin (2 * k)) ↪ Finset (Fin (2 * k + 1)) where
  toFun := fun U ↦ insert 0 (U.map (Fin.succEmb (2 * k)))
  inj' := by
    intro U V hUV
    have hzeroU : (0 : Fin (2 * k + 1)) ∉ U.map (Fin.succEmb (2 * k)) := by
      intro h
      rcases Finset.mem_map.mp h with ⟨u, -, hu⟩
      exact Fin.succ_ne_zero u hu
    have hzeroV : (0 : Fin (2 * k + 1)) ∉ V.map (Fin.succEmb (2 * k)) := by
      intro h
      rcases Finset.mem_map.mp h with ⟨v, -, hv⟩
      exact Fin.succ_ne_zero v hv
    have hErase :
        (insert 0 (U.map (Fin.succEmb (2 * k)))).erase 0 =
          (insert 0 (V.map (Fin.succEmb (2 * k)))).erase 0 := by
      exact congrArg (fun W : Finset (Fin (2 * k + 1)) ↦ W.erase 0) hUV
    rw [Finset.erase_insert hzeroU, Finset.erase_insert hzeroV] at hErase
    exact (Finset.map_injective (Fin.succEmb (2 * k))) hErase

/-- Helper for Theorem 2.3: the rooted odd subset family has cardinality `Nat.centralBinom k`. -/
lemma rootedOddSubsetFamily_card (k : ℕ) :
    Nat.centralBinom k =
      ((Finset.univ.powersetCard k).image (rootedOddSubsetEmbedding k)).card := by
  calc
    Nat.centralBinom k = ((Finset.univ : Finset (Fin (2 * k))).powersetCard k).card := by
      simp [Nat.centralBinom]
    _ = ((Finset.univ.powersetCard k).image (rootedOddSubsetEmbedding k)).card := by
      symm
      exact Finset.card_image_of_injective _ (rootedOddSubsetEmbedding k).injective

/-- Helper for Theorem 2.3: the rooted embedding always inserts the root and raises the cardinality
by exactly one. -/
lemma rootedOddSubsetEmbedding_card
    (k : ℕ) (U : Finset (Fin (2 * k))) :
    (rootedOddSubsetEmbedding k U).card = U.card + 1 := by
  -- The shifted image misses `0`, so inserting the root contributes exactly one new element.
  have hzero :
      (0 : Fin (2 * k + 1)) ∉ U.map (Fin.succEmb (2 * k)) := by
    intro h
    rcases Finset.mem_map.mp h with ⟨u, -, hu⟩
    exact Fin.succ_ne_zero u hu
  calc
    (rootedOddSubsetEmbedding k U).card
        = (insert 0 (U.map (Fin.succEmb (2 * k)))).card := by
            rfl
    _ = (U.map (Fin.succEmb (2 * k))).card + 1 := by simp [hzero]
    _ = U.card + 1 := by simp

/-- Helper for Theorem 2.3: away from the root `0`, membership in the rooted embedding is exactly
source membership after applying `Fin.succ`. -/
lemma succ_mem_rootedOddSubsetEmbedding_iff
    (k : ℕ) (U : Finset (Fin (2 * k))) (u : Fin (2 * k)) :
    u.succ ∈ rootedOddSubsetEmbedding k U ↔ u ∈ U := by
  constructor
  · intro hu
    rw [rootedOddSubsetEmbedding] at hu
    rcases Finset.mem_insert.mp hu with hzero | hmap
    · exact False.elim (Fin.succ_ne_zero u hzero)
    · rcases Finset.mem_map.mp hmap with ⟨v, hv, hvu⟩
      have hvu' : v = u := by
        simpa using hvu
      exact hvu' ▸ hv
  · intro hu
    rw [rootedOddSubsetEmbedding]
    exact Finset.mem_insert.mpr <|
      Or.inr (Finset.mem_map.mpr ⟨u, hu, rfl⟩)

/-- Helper for Theorem 2.3: on rooted embeddings, the root-edge cut values recover source
membership. -/
lemma cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge
    (k : ℕ) (U : Finset (Fin (2 * k))) (u : Fin (2 * k)) :
    cutIncidenceVector (rootedOddSubsetEmbedding k U) (rootEdge u) =
      if u ∈ U then 0 else 1 := by
  -- Evaluate the cut indicator on the edge from the distinguished root to `u.succ`.
  rw [rootEdge,
    cutIncidenceVector_apply_pair (rootedOddSubsetEmbedding k U) 0 u.succ (rootEdge_not_diag u)]
  have hroot : (0 : Fin (2 * k + 1)) ∈ rootedOddSubsetEmbedding k U := by
    simp [rootedOddSubsetEmbedding]
  by_cases hu : u ∈ U
  · -- If `u` belongs to the source subset, the root edge stays inside the rooted side of the cut.
    have hsucc : u.succ ∈ rootedOddSubsetEmbedding k U :=
      (succ_mem_rootedOddSubsetEmbedding_iff k U u).2 hu
    simp [hroot, hsucc, hu]
  · -- Otherwise the root edge crosses the cut exactly once.
    have hsucc : u.succ ∉ rootedOddSubsetEmbedding k U := by
      simpa [succ_mem_rootedOddSubsetEmbedding_iff k U u] using hu
    simp [hroot, hsucc, hu]

/-- Helper for Theorem 2.3: the cut-incidence vector of a rooted embedding determines the source
subset. -/
lemma rootedOddSubsetEmbedding_eq_of_cutIncidenceVector_eq
    (k : ℕ) {U V : Finset (Fin (2 * k))}
    (hcut :
      cutIncidenceVector (rootedOddSubsetEmbedding k U) =
        cutIncidenceVector (rootedOddSubsetEmbedding k V)) :
    U = V := by
  ext u
  -- Compare the two cut vectors on the root edge adjacent to `u`.
  have hroot :
      cutIncidenceVector (rootedOddSubsetEmbedding k U) (rootEdge u) =
        cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge u) := by
    simpa using
      congrArg (fun x : complete_graph_edges (2 * k + 1) → ℝ ↦ x (rootEdge u)) hcut
  rw [cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge,
    cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge] at hroot
  by_cases hu : u ∈ U <;> by_cases hv : u ∈ V <;> simp [hu, hv] at hroot ⊢

/-- Helper for Theorem 2.3: the complete-graph incident-edge finset at a vertex has cardinality
`n - 1`. -/
lemma completeGraphIncidentEdgeFinset_card
    (n : ℕ) (v : Fin n) :
    ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).map
      completeGraphEdgeEquiv.symm.toEmbedding).card = n - 1 := by
  let incidentFinsetEquiv :
      {e : (SimpleGraph.completeGraph (Fin n)).edgeSet //
        e ∈ incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v} ≃
      {e : (SimpleGraph.completeGraph (Fin n)).edgeSet // v ∈ (e : Sym2 (Fin n))} :=
    { toFun := fun e ↦ ⟨e.1, mem_incidentEdgeFinset_iff.mp e.2⟩
      invFun := fun e ↦ ⟨e.1, mem_incidentEdgeFinset_iff.mpr e.2⟩
      left_inv := by
        intro e
        cases e
        rfl
      right_inv := by
        intro e
        cases e
        rfl }
  let incidentEquiv :
      {e : (SimpleGraph.completeGraph (Fin n)).edgeSet // v ∈ (e : Sym2 (Fin n))} ≃
        (SimpleGraph.completeGraph (Fin n)).incidenceSet v :=
    { toFun := fun e ↦ ⟨e.1, e.1.2, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := by
        intro e
        cases e
        rfl
      right_inv := by
        intro e
        cases e
        rfl }
  -- Count incident edges by transporting the finset filter to the graph's incidence-set owner.
  calc
    ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).map
        completeGraphEdgeEquiv.symm.toEmbedding).card
        = (incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v).card := by
            simp
    _ = Fintype.card
          {e : (SimpleGraph.completeGraph (Fin n)).edgeSet //
            e ∈ incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v} := by
          symm
          exact Fintype.card_ofFinset
            (incidentEdgeFinset (SimpleGraph.completeGraph (Fin n)) v) (by intro e; rfl)
    _ =
        Fintype.card
          {e : (SimpleGraph.completeGraph (Fin n)).edgeSet // v ∈ (e : Sym2 (Fin n))} := by
          exact Fintype.card_congr incidentFinsetEquiv
    _ = (SimpleGraph.completeGraph (Fin n)).degree v := by
          calc
            Fintype.card {e : (SimpleGraph.completeGraph (Fin n)).edgeSet // v ∈ (e : Sym2 (Fin n))}
                = Fintype.card ((SimpleGraph.completeGraph (Fin n)).incidenceSet v) := by
                    exact Fintype.card_congr incidentEquiv
            _ = (SimpleGraph.completeGraph (Fin n)).degree v := by
                  exact (SimpleGraph.completeGraph (Fin n)).card_incidenceSet_eq_degree v
    _ = n - 1 := by
          simp

/-- Helper for Theorem 2.3: the four-edge probe isolates one root-edge coordinate while
preserving every degree equation. -/
def rootEdgeProbe
    {k : ℕ} (u p q : Fin (2 * k)) (huq : u ≠ q) (hpq : p ≠ q) :
    complete_graph_edges (2 * k + 1) → ℝ :=
  Pi.single (rootEdge u) 1 - Pi.single (rootEdge p) 1
    - Pi.single (succPairEdge u q huq) 1 + Pi.single (succPairEdge p q hpq) 1

/-- Helper for Theorem 2.3: the root edge `rootEdge u` is always incident to the distinguished
root vertex `0`. -/
lemma rootEdge_mem_zero
    {k : ℕ} (u : Fin (2 * k)) :
    (0 : Fin (2 * k + 1)) ∈
      ((rootEdge u : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) := by
  simp [rootEdge, Sym2.mem_iff]

/-- Helper for Theorem 2.3: among successor vertices, `rootEdge u` is incident exactly to
`u.succ`. -/
lemma succ_mem_rootEdge_iff
    {k : ℕ} (j u : Fin (2 * k)) :
    j.succ ∈ ((rootEdge u : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) ↔
      j = u := by
  simp [rootEdge, Sym2.mem_iff]

/-- Helper for Theorem 2.3: no successor-pair edge is incident to the distinguished root vertex
`0`. -/
lemma zero_not_mem_succPairEdge
    {k : ℕ} (u q : Fin (2 * k)) (huq : u ≠ q) :
    (0 : Fin (2 * k + 1)) ∉
      ((succPairEdge u q huq : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) := by
  intro h
  rw [succPairEdge, Sym2.mem_iff] at h
  rcases h with h0 | h0
  · exact Fin.succ_ne_zero u h0.symm
  · exact Fin.succ_ne_zero q h0.symm

/-- Helper for Theorem 2.3: among successor vertices, `succPairEdge u q huq` is incident exactly
to `u.succ` and `q.succ`. -/
lemma succ_mem_succPairEdge_iff
    {k : ℕ} (j u q : Fin (2 * k)) (huq : u ≠ q) :
    j.succ ∈
      ((succPairEdge u q huq : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) ↔
        j = u ∨ j = q := by
  simp [succPairEdge, Sym2.mem_iff]

/-- Helper for Theorem 2.3: every vertex sees zero total probe contribution, so the probe preserves
the degree equations of the odd traveling salesman affine slice. -/
lemma incidentEdgeSum_rootEdgeProbe_eq_zero
    {k : ℕ} (u p q : Fin (2 * k)) (huq : u ≠ q) (hpq : p ≠ q)
    (i : Fin (2 * k + 1)) :
    ((incidentEdgeFinset (SimpleGraph.completeGraph (Fin (2 * k + 1))) i).map
        completeGraphEdgeEquiv.symm.toEmbedding).sum (rootEdgeProbe u p q huq hpq) = 0 := by
  let I :
      Finset (complete_graph_edges (2 * k + 1)) :=
    (incidentEdgeFinset (SimpleGraph.completeGraph (Fin (2 * k + 1))) i).map
      completeGraphEdgeEquiv.symm.toEmbedding
  change I.sum (rootEdgeProbe u p q huq hpq) = 0
  have hrootu :
      I.sum (Pi.single (rootEdge u) 1) =
        if i ∈ ((rootEdge u : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) then
          (1 : ℝ)
        else 0 :=
    by
      simpa [I] using
        (incidentEdgeSum_single_eq_indicator i (rootEdge u) 1)
  have hrootp :
      I.sum (Pi.single (rootEdge p) 1) =
        if i ∈ ((rootEdge p : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) then
          (1 : ℝ)
        else 0 :=
    by
      simpa [I] using
        (incidentEdgeSum_single_eq_indicator i (rootEdge p) 1)
  have hpairu :
      I.sum (Pi.single (succPairEdge u q huq) 1) =
        if i ∈
            ((succPairEdge u q huq : complete_graph_edges (2 * k + 1)) :
              Sym2 (Fin (2 * k + 1))) then
          (1 : ℝ)
        else 0 :=
    by
      simpa [I] using
        (incidentEdgeSum_single_eq_indicator i (succPairEdge u q huq) 1)
  have hpairp :
      I.sum (Pi.single (succPairEdge p q hpq) 1) =
        if i ∈
            ((succPairEdge p q hpq : complete_graph_edges (2 * k + 1)) :
              Sym2 (Fin (2 * k + 1))) then
          (1 : ℝ)
        else 0 :=
    by
      simpa [I] using
        (incidentEdgeSum_single_eq_indicator i (succPairEdge p q hpq) 1)
  have hneg_rootp :
      I.sum (-Pi.single (rootEdge p) 1) =
        - (if i ∈ ((rootEdge p : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) then
            (1 : ℝ)
          else 0) := by
    simpa [Finset.sum_neg_distrib, Pi.neg_apply] using congrArg Neg.neg hrootp
  have hneg_pairu :
      I.sum (-Pi.single (succPairEdge u q huq) 1) =
        - (if i ∈
              ((succPairEdge u q huq : complete_graph_edges (2 * k + 1)) :
                Sym2 (Fin (2 * k + 1))) then
            (1 : ℝ)
          else 0) := by
    simpa [Finset.sum_neg_distrib, Pi.neg_apply] using congrArg Neg.neg hpairu
  -- Expand the four-edge probe into an additive sum of isolated basis contributions.
  calc
    I.sum (rootEdgeProbe u p q huq hpq)
        =
          I.sum (fun x ↦
            Pi.single (rootEdge u) 1 x + -Pi.single (rootEdge p) 1 x +
              (-Pi.single (succPairEdge u q huq) 1 x) +
                Pi.single (succPairEdge p q hpq) 1 x) := by
              simp [rootEdgeProbe, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply]
    _ = I.sum (Pi.single (rootEdge u) 1) +
          (I.sum (-Pi.single (rootEdge p) 1) +
            (I.sum (-Pi.single (succPairEdge u q huq) 1) +
              I.sum (Pi.single (succPairEdge p q hpq) 1))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp [add_assoc]
    _ =
        (if i ∈ ((rootEdge u : complete_graph_edges (2 * k + 1)) : Sym2 (Fin (2 * k + 1))) then
            (1 : ℝ)
          else 0) +
          (- (if
                  i ∈ ((rootEdge p : complete_graph_edges (2 * k + 1)) :
                    Sym2 (Fin (2 * k + 1))) then
                (1 : ℝ)
              else 0) +
            (- (if
                    i ∈
                        ((succPairEdge u q huq : complete_graph_edges (2 * k + 1)) :
                          Sym2 (Fin (2 * k + 1))) then
                  (1 : ℝ)
                else 0) +
              (if
                  i ∈
                      ((succPairEdge p q hpq : complete_graph_edges (2 * k + 1)) :
                        Sym2 (Fin (2 * k + 1))) then
                (1 : ℝ)
              else 0))) := by
              rw [hrootu, hneg_rootp, hneg_pairu, hpairp]
  -- Split the vertex into the distinguished root or a successor vertex and use the endpoint API.
    _ = 0 := by
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp [rootEdge_mem_zero, zero_not_mem_succPairEdge]
      · simp only [succ_mem_rootEdge_iff, succ_mem_succPairEdge_iff]
        by_cases hju : j = u
        · subst j
          by_cases hup : u = p
          · simp [hup]
          · simp [hup, huq]
        · by_cases hjp : j = p
          · subst j
            simp [hju, hpq]
          · by_cases hjq : j = q
            · subst j
              have hqu : q ≠ u := fun hqu' ↦ huq hqu'.symm
              have hqp : q ≠ p := fun hqp' ↦ hpq hqp'.symm
              simp [hqu, hqp]
            · simp [hju, hjp, hjq]

/-- Helper for Theorem 2.3: the four-edge probe lies in the affine-hull direction of the odd TSP
polytope because it preserves all degree equations. -/
lemma rootEdgeProbe_mem_affineHullDirection
    {k : ℕ} (u p q : Fin (2 * k)) (huq : u ≠ q) (hpq : p ≠ q) :
    rootEdgeProbe u p q huq hpq ∈
      (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction := by
  let n := 2 * k + 1
  let x0 : complete_graph_edges n → ℝ := hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  have hcard : 2 ≤ 2 * k := by
    -- Distinct vertices `u` and `q` force the even block to contain at least two elements.
    have hu_lt : u.1 < 2 * k := u.2
    have hq_lt : q.1 < 2 * k := q.2
    have hval_ne : u.1 ≠ q.1 := by
      intro hval
      apply huq
      exact Fin.ext hval
    omega
  have hn : 3 ≤ n := by
    dsimp [n]
    omega
  have hx0_poly : x0 ∈ travelingSalesmanPolytope n := by
    -- The identity Hamiltonian tour is one of the convex-hull generators.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx0_aff : x0 ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    -- Any tour vertex lies in the affine hull of the polytope.
    exact subset_affineSpan ℝ _ hx0_poly
  have hAffineEq :
      (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
        travelingSalesmanDegreeConstraintSet n := by
    simpa [n] using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n hn
  have hx0_degree : x0 ∈ travelingSalesmanDegreeConstraintSet n := by
    -- Transport the base tour vertex from the affine hull to the degree slice.
    rw [← hAffineEq]
    exact hx0_aff
  have htranslate_degree :
      x0 + rootEdgeProbe u p q huq hpq ∈ travelingSalesmanDegreeConstraintSet n := by
    -- Route correction: use the reusable degree-slice translation lemma instead of re-expanding
    -- the incident-edge sums inside this affine-direction proof.
    refine add_mem_travelingSalesmanDegreeConstraintSet_of_incident_sum_zero hx0_degree ?_
    intro i
    simpa [n] using incidentEdgeSum_rootEdgeProbe_eq_zero u p q huq hpq i
  have htranslate_aff :
      x0 + rootEdgeProbe u p q huq hpq ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    -- Move the translated point back from the degree slice to the affine hull.
    change x0 + rootEdgeProbe u p q huq hpq ∈
      ((affineSpan ℝ (travelingSalesmanPolytope n) :
          AffineSubspace ℝ (complete_graph_edges n → ℝ)) : Set (complete_graph_edges n → ℝ))
    rw [hAffineEq]
    exact htranslate_degree
  -- Express the probe as the difference of two points in the affine hull.
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
  refine ⟨x0 + rootEdgeProbe u p q huq hpq, htranslate_aff, ?_⟩
  ext e
  simp [vsub_eq_sub]

/-- Helper for Theorem 2.3: the cut vector evaluates on the probe by the corresponding four edge
coordinates, and the pair edges reduce to root-edge comparisons. -/
lemma cutIncidenceVector_dot_rootEdgeProbe
    {k : ℕ} (W : Finset (Fin (2 * k + 1))) (u p q : Fin (2 * k))
    (huq : u ≠ q) (hpq : p ≠ q) :
    cutIncidenceVector W ⬝ᵥ rootEdgeProbe u p q huq hpq =
      cutIncidenceVector W (rootEdge u) - cutIncidenceVector W (rootEdge p)
        - (if cutIncidenceVector W (rootEdge u) = cutIncidenceVector W (rootEdge q) then 0 else 1)
        +
          (if cutIncidenceVector W (rootEdge p) = cutIncidenceVector W (rootEdge q) then 0
            else 1) := by
  -- Expand the sparse probe and rewrite the pair-edge coordinates through root-edge values.
  have hrootu :
      ∑ x, (if x = rootEdge u then cutIncidenceVector W x else 0) =
        cutIncidenceVector W (rootEdge u) := by
    simp
  have hrootp :
      ∑ x, (if x = rootEdge p then cutIncidenceVector W x else 0) =
        cutIncidenceVector W (rootEdge p) := by
    simp
  have hpairu :
      ∑ x, (if x = succPairEdge u q huq then cutIncidenceVector W x else 0) =
        cutIncidenceVector W (succPairEdge u q huq) := by
    simp
  have hpairp :
      ∑ x, (if x = succPairEdge p q hpq then cutIncidenceVector W x else 0) =
        cutIncidenceVector W (succPairEdge p q hpq) := by
    simp
  have hneg_rootp :
      ∑ x, (-(if x = rootEdge p then cutIncidenceVector W x else 0 : ℝ)) =
        -cutIncidenceVector W (rootEdge p) := by
    rw [Finset.sum_neg_distrib]
    exact congrArg Neg.neg hrootp
  have hneg_pairu :
      ∑ x, (-(if x = succPairEdge u q huq then cutIncidenceVector W x else 0 : ℝ)) =
        -cutIncidenceVector W (succPairEdge u q huq) := by
    rw [Finset.sum_neg_distrib]
    exact congrArg Neg.neg hpairu
  rw [rootEdgeProbe, dotProduct]
  simp only
    [Pi.add_apply, Pi.neg_apply, Pi.single_apply, sub_eq_add_neg, mul_add, mul_neg, mul_ite,
      mul_one, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hrootu, hpairp, hneg_rootp, hneg_pairu]
  rw [cutIncidenceVector_apply_succPair_eq_of_root_values W huq,
    cutIncidenceVector_apply_succPair_eq_of_root_values W hpq]

/-- Helper for Theorem 2.3: once one anchor root edge is inside and one is outside, the probe
value is exactly `2` times the isolated root-edge coordinate. -/
lemma cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
    {k : ℕ} (W : Finset (Fin (2 * k + 1))) (u p q : Fin (2 * k))
    (huq : u ≠ q) (hpq : p ≠ q)
    (hp : cutIncidenceVector W (rootEdge p) = 0)
    (hq : cutIncidenceVector W (rootEdge q) = 1) :
    cutIncidenceVector W ⬝ᵥ rootEdgeProbe u p q huq hpq =
      2 * cutIncidenceVector W (rootEdge u) := by
  -- The two pair edges collapse to the XOR-pattern determined by the root values at `u,p,q`.
  rw [cutIncidenceVector_dot_rootEdgeProbe, hp, hq]
  by_cases hu : cutIncidenceVector W (rootEdge u) = 1
  · simp [hu]
    norm_num
  · have hu' : cutIncidenceVector W (rootEdge u) = 0 := by
      rcases cutVertices_subset_zero_one_box ⟨W, rfl⟩ (rootEdge u) with hzero | hone
      · exact hzero
      · exact False.elim (hu hone)
    simp [hu']

/-- Helper for Theorem 2.3: if the anchor root edge at `q` stays on the rooted side of the cut,
then the four-edge probe evaluates to `0`. -/
lemma cutIncidenceVector_dot_rootEdgeProbe_eq_zero_of_anchor_zero
    {k : ℕ} (W : Finset (Fin (2 * k + 1))) (u p q : Fin (2 * k))
    (huq : u ≠ q) (hpq : p ≠ q)
    (hq : cutIncidenceVector W (rootEdge q) = 0) :
    cutIncidenceVector W ⬝ᵥ rootEdgeProbe u p q huq hpq = 0 := by
  have hu01 :
      cutIncidenceVector W (rootEdge u) = 0 ∨ cutIncidenceVector W (rootEdge u) = 1 := by
    simpa using cutVertices_subset_zero_one_box ⟨W, rfl⟩ (rootEdge u)
  have hp01 :
      cutIncidenceVector W (rootEdge p) = 0 ∨ cutIncidenceVector W (rootEdge p) = 1 := by
    simpa using cutVertices_subset_zero_one_box ⟨W, rfl⟩ (rootEdge p)
  -- Route correction: once the anchor value at `q` is `0`, the pair-edge terms cancel in every
  -- remaining `0/1` case.
  rw [cutIncidenceVector_dot_rootEdgeProbe, hq]
  rcases hu01 with hu | hu <;> rcases hp01 with hp | hp <;> simp [hu, hp]

/-- Helper for Theorem 2.3: if the anchor root edge at `q` crosses the cut, the four-edge probe
records twice the difference of the two root-edge values at `u` and `p`. -/
lemma cutIncidenceVector_dot_rootEdgeProbe_eq_two_mul_sub_of_anchor_one
    {k : ℕ} (W : Finset (Fin (2 * k + 1))) (u p q : Fin (2 * k))
    (huq : u ≠ q) (hpq : p ≠ q)
    (hq : cutIncidenceVector W (rootEdge q) = 1) :
    cutIncidenceVector W ⬝ᵥ rootEdgeProbe u p q huq hpq =
      2 * (cutIncidenceVector W (rootEdge u) - cutIncidenceVector W (rootEdge p)) := by
  have hu01 :
      cutIncidenceVector W (rootEdge u) = 0 ∨ cutIncidenceVector W (rootEdge u) = 1 := by
    simpa using cutVertices_subset_zero_one_box ⟨W, rfl⟩ (rootEdge u)
  have hp01 :
      cutIncidenceVector W (rootEdge p) = 0 ∨ cutIncidenceVector W (rootEdge p) = 1 := by
    simpa using cutVertices_subset_zero_one_box ⟨W, rfl⟩ (rootEdge p)
  -- Once the anchor value at `q` is `1`, the pair-edge terms become the expected `0/1`
  -- difference across the two root edges.
  rw [cutIncidenceVector_dot_rootEdgeProbe, hq]
  rcases hu01 with hu | hu <;> rcases hp01 with hp | hp <;> simp [hu, hp] <;> norm_num

/-- Helper for Theorem 2.3: a `k`-subset of `Fin (2 * k)` with `k ≥ 2` contains two distinct
inside anchors and has two distinct outside anchors. -/
lemma powersetCard_exists_two_inside_two_outside
    (k : ℕ) (hk : 2 ≤ k)
    {U : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k) :
    ∃ p s q r : Fin (2 * k),
      p ∈ U ∧ s ∈ U ∧ s ≠ p ∧ q ∉ U ∧ r ∉ U ∧ r ≠ q := by
  have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
  have hUp : 0 < U.card := by
    rw [hUcard]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hUp
  have hUerase_pos : 0 < (U.erase p).card := by
    rw [Finset.card_erase_of_mem hp, hUcard]
    omega
  obtain ⟨s, hsErase⟩ := Finset.card_pos.mp hUerase_pos
  have hs_ne : s ≠ p := (Finset.mem_erase.mp hsErase).1
  have hs : s ∈ U := (Finset.mem_erase.mp hsErase).2
  have huniv_card : (Finset.univ : Finset (Fin (2 * k))).card = 2 * k := by
    simp
  have hcompl_card : (Finset.univ \ U).card = k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), huniv_card, hUcard]
    omega
  have hcompl_pos : 0 < (Finset.univ \ U).card := by
    rw [hcompl_card]
    omega
  obtain ⟨q, hqCompl⟩ := Finset.card_pos.mp hcompl_pos
  have hq : q ∉ U := (Finset.mem_sdiff.mp hqCompl).2
  have hcomplErase_pos : 0 < ((Finset.univ \ U).erase q).card := by
    rw [Finset.card_erase_of_mem hqCompl, hcompl_card]
    omega
  obtain ⟨r, hrErase⟩ := Finset.card_pos.mp hcomplErase_pos
  have hr_ne : r ≠ q := (Finset.mem_erase.mp hrErase).1
  have hrCompl : r ∈ Finset.univ \ U := (Finset.mem_erase.mp hrErase).2
  have hr : r ∉ U := (Finset.mem_sdiff.mp hrCompl).2
  exact ⟨p, s, q, r, hp, hs, hs_ne, hq, hr, hr_ne⟩

/-- Helper for Theorem 2.3: reversing the endpoints of a root edge does not change the
cut-incidence coordinate. -/
lemma cutIncidenceVector_rootEdge_symm_apply
    {n : ℕ} (W : Finset (Fin (n + 1))) (u : Fin n)
    (h : ¬ (s(u.succ, (0 : Fin (n + 1))) : Sym2 (Fin (n + 1))).IsDiag) :
    cutIncidenceVector W ⟨s(u.succ, 0), h⟩ = cutIncidenceVector W (rootEdge u) := by
  -- Normalize the reversed spelling back to the canonical `rootEdge u`.
  rw [cutIncidenceVector_apply_pair W u.succ 0 h]
  rw [rootEdge, cutIncidenceVector_apply_pair W 0 u.succ (rootEdge_not_diag u)]
  by_cases hu : u.succ ∈ W <;> by_cases h0 : (0 : Fin (n + 1)) ∈ W <;> simp [hu, h0, eq_comm]

/-- Helper for Theorem 2.3: on a complete graph with distinguished root `0`, a cut-incidence
vector is determined by its values on the root edges. -/
lemma cutIncidenceVector_eq_of_rootEdgeValues_eq
    {n : ℕ} (W U : Finset (Fin (n + 1)))
    (hroot :
      ∀ u : Fin n, cutIncidenceVector W (rootEdge u) = cutIncidenceVector U (rootEdge u)) :
    cutIncidenceVector W = cutIncidenceVector U := by
  -- Route correction: reduce every non-diagonal edge either to a canonical root edge or to a
  -- successor-pair edge whose value is determined by the two root-edge endpoints.
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨u, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨v, rfl⟩
        · exact False.elim <| he <| by simp [Sym2.mk_isDiag_iff]
        · simpa [rootEdge] using hroot v
      · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨v, rfl⟩
        · rw [cutIncidenceVector_rootEdge_symm_apply W u he,
            cutIncidenceVector_rootEdge_symm_apply U u he]
          exact hroot u
        · by_cases huv : u = v
          · subst huv
            exact False.elim <| he <| by simp [Sym2.mk_isDiag_iff]
          · simpa [succPairEdge, hroot u, hroot v] using
              (show cutIncidenceVector W (succPairEdge u v huv) =
                  cutIncidenceVector U (succPairEdge u v huv) by
                rw [cutIncidenceVector_apply_succPair_eq_of_root_values W huv]
                rw [cutIncidenceVector_apply_succPair_eq_of_root_values U huv]
                simp [hroot u, hroot v])

/-- Helper for Theorem 2.3: every rooted subtour cut has a probe in the ambient TSP direction
where its cut functional takes the normalized value `1`. -/
lemma rootedSubtour_cut_normalizingProbe
    (k : ℕ) (hk : 2 ≤ k)
    {U : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k) :
    ∃ w : complete_graph_edges (2 * k + 1) → ℝ,
      w ∈ (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ∧
      dotProductLinearMap
          (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
            complete_graph_edges (2 * k + 1) → ℝ) w = 1 := by
  let W := rootedOddSubsetEmbedding k U
  obtain ⟨p, _, q, r, hp, -, -, hq, hr, hr_ne⟩ :=
    powersetCard_exists_two_inside_two_outside k hk hU
  have hpq : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hp)
  let w : complete_graph_edges (2 * k + 1) → ℝ := (1 / 2 : ℝ) • rootEdgeProbe r p q hr_ne hpq
  have hw_mem :
      w ∈ (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction := by
    -- Scale the canonical probe that already lies in the ambient direction.
    exact Submodule.smul_mem _ _ (rootEdgeProbe_mem_affineHullDirection r p q hr_ne hpq)
  have hp0 : cutIncidenceVector W (rootEdge p) = 0 := by
    simpa [W, hp] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U p
  have hq1 : cutIncidenceVector W (rootEdge q) = 1 := by
    simpa [W, hq] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U q
  have hr1 : cutIncidenceVector W (rootEdge r) = 1 := by
    simpa [W, hr] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U r
  have hprobe_eval :
      dotProductLinearMap (cutIncidenceVector W : complete_graph_edges (2 * k + 1) → ℝ)
        (rootEdgeProbe r p q hr_ne hpq) = 2 := by
    -- The chosen anchors force the raw probe to isolate the outside root edge at `r`.
    rw [dotProductLinearMap_apply]
    calc
      cutIncidenceVector W ⬝ᵥ rootEdgeProbe r p q hr_ne hpq
          = 2 * cutIncidenceVector W (rootEdge r) := by
              exact cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values W r p q hr_ne hpq hp0 hq1
      _ = 2 := by rw [hr1]; norm_num
  refine ⟨w, hw_mem, ?_⟩
  -- Rescaling by `1 / 2` normalizes the evaluation from `2` to `1`.
  calc
    dotProductLinearMap (cutIncidenceVector W : complete_graph_edges (2 * k + 1) → ℝ) w
        = (1 / 2 : ℝ) *
            dotProductLinearMap (cutIncidenceVector W : complete_graph_edges (2 * k + 1) → ℝ)
              (rootEdgeProbe r p q hr_ne hpq) := by
              simp [w]
    _ = (1 / 2 : ℝ) * 2 := by rw [hprobe_eval]
    _ = 1 := by norm_num

/-- Helper for Theorem 2.3: the rooted subtour-face direction sits inside the ambient TSP
direction and the kernel of the corresponding cut functional. -/
lemma rootedSubtourFace_direction_le_ambientCutKer
    (k : ℕ) (hk : 2 ≤ k)
    {U : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k) :
    (affineSpan ℝ (subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U))).direction ≤
      (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
        LinearMap.ker
          (dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
              complete_graph_edges (2 * k + 1) → ℝ)) := by
  let n := 2 * k + 1
  let W := rootedOddSubsetEmbedding k U
  let D := (affineSpan ℝ (travelingSalesmanPolytope n)).direction
  let L : (complete_graph_edges n → ℝ) →ₗ[ℝ] ℝ :=
    dotProductLinearMap (cutIncidenceVector W : complete_graph_edges n → ℝ)
  have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
  have hWcard : W.card = k + 1 := by
    simpa [W, hUcard] using rootedOddSubsetEmbedding_card k U
  have hn : 4 ≤ n := by
    omega
  have hWlower : 2 ≤ W.card := by
    omega
  have hWupper : W.card ≤ n - 2 := by
    omega
  have hfacet :
      IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n W) := by
    -- The rooted subset lies in the Chapter 7 facet range `2 ≤ |W| ≤ n - 2`.
    exact subtour_elimination_face_isFacetOf hn W hWlower hWupper
  rcases isFacetOf_iff.mp hfacet with ⟨hface_nonempty, _, _⟩
  obtain ⟨x0, hx0⟩ := hface_nonempty
  have hface_subset :
      subtour_elimination_face n W ⊆ travelingSalesmanPolytope n := by
    intro x hx
    exact (mem_subtour_elimination_face_iff W x).1 hx |>.1
  have hdir_le_ambient :
      (affineSpan ℝ (subtour_elimination_face n W)).direction ≤ D := by
    -- Every face direction is in particular an ambient TSP direction.
    change
      (affineSpan ℝ (subtour_elimination_face n W)).direction ≤
        (affineSpan ℝ (travelingSalesmanPolytope n)).direction
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hface_subset)
  have hlevel :
      ∀ ⦃x : complete_graph_edges n → ℝ⦄, x ∈ subtour_elimination_face n W → L x = 2 := by
    intro x hx
    -- Membership in the face means that the cut-incidence functional is tight at value `2`.
    simpa [L, dotProductLinearMap_apply, subtour_elimination_value_eq_dotProduct] using
      (mem_subtour_elimination_face_iff W x).1 hx |>.2
  have hdir_le_ker :
      (affineSpan ℝ (subtour_elimination_face n W)).direction ≤ LinearMap.ker L := by
    exact affineSpan_direction_le_ker_of_forall_eq hx0 hlevel
  -- Combine the ambient-direction and kernel inclusions into the desired intersection inclusion.
  intro v hv
  exact ⟨hdir_le_ambient hv, hdir_le_ker hv⟩

/-- Helper for Theorem 2.3: the direction of a rooted subtour face is exactly the ambient TSP
direction cut by the kernel of its cut-incidence functional. -/
lemma rootedSubtourFace_direction_eq_ambientCutKer
    (k : ℕ) (hk : 2 ≤ k)
    {U : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k) :
    (affineSpan ℝ (subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U))).direction =
      (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
        LinearMap.ker
          (dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
              complete_graph_edges (2 * k + 1) → ℝ)) := by
  let n := 2 * k + 1
  let W := rootedOddSubsetEmbedding k U
  let D := (affineSpan ℝ (travelingSalesmanPolytope n)).direction
  let L : (complete_graph_edges n → ℝ) →ₗ[ℝ] ℝ :=
    dotProductLinearMap (cutIncidenceVector W : complete_graph_edges n → ℝ)
  have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
  have hWcard : W.card = k + 1 := by
    simpa [W, hUcard] using rootedOddSubsetEmbedding_card k U
  have hfacet :
      IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n W) := by
    -- The rooted subset lies in the Chapter 7 facet range `2 ≤ |W| ≤ n - 2`.
    exact subtour_elimination_face_isFacetOf (by omega) W (by omega) (by omega)
  rcases isFacetOf_iff.mp hfacet with ⟨_, _, hface_codim⟩
  have hdir_le :
      (affineSpan ℝ (subtour_elimination_face n W)).direction ≤ D ⊓ LinearMap.ker L := by
    -- Reuse the inclusion lemma so this theorem only closes the codimension argument.
    simpa [n, D, L] using rootedSubtourFace_direction_le_ambientCutKer k hk hU
  obtain ⟨w, hwD, hw_eval⟩ := rootedSubtour_cut_normalizingProbe k hk hU
  have hcodim_ker :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
    exact submodule_finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
  have hface_codim_aux :
      Module.finrank ℝ ↥((affineSpan ℝ (subtour_elimination_face n W)).direction) + 1 =
        Module.finrank ℝ ↥D := by
    simpa [D] using hface_codim
  have hfin :
      Module.finrank ℝ ↥((affineSpan ℝ (subtour_elimination_face n W)).direction) =
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) := by
    omega
  -- Equal codimension-one dimensions upgrade the kernel inclusion to equality.
  exact Submodule.eq_of_le_of_finrank_eq hdir_le hfin

/-- Helper for Theorem 2.3: equality of the ambient kernel cuts `D ⊓ ker L` pulls back to
equality of the subtype kernels of the restricted maps. -/
lemma kerDomRestrict_eq_of_infKer_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : Submodule ℝ E)
    (L₁ L₂ : E →ₗ[ℝ] ℝ)
    (hinf : D ⊓ LinearMap.ker L₁ = D ⊓ LinearMap.ker L₂) :
    LinearMap.ker (L₁.domRestrict D) = LinearMap.ker (L₂.domRestrict D) := by
  have hmap₁ :
      (LinearMap.ker (L₁.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L₁ := by
    -- Rewrite the restricted kernel in the ambient module where the comparison is stable.
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hmap₂ :
      (LinearMap.ker (L₂.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L₂ := by
    -- The same normalization applies to the second restricted functional.
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  -- Pull the ambient equality back through the injective subtype embedding.
  apply Submodule.map_injective_of_injective D.subtype_injective
  calc
    (LinearMap.ker (L₁.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L₁ := hmap₁
    _ = D ⊓ LinearMap.ker L₂ := hinf
    _ = (LinearMap.ker (L₂.domRestrict D)).map D.subtype := hmap₂.symm

/-- Helper for Theorem 2.3: equal rooted subtour faces force the two restricted cut functionals
to differ only by a nonzero scalar on the ambient TSP direction. -/
lemma equalRootedSubtourFaces_infKer_eq
    (k : ℕ) (hk : 2 ≤ k)
    {U V : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hV : V ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hface :
      subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U) =
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V)) :
    (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
        LinearMap.ker
          (dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
              complete_graph_edges (2 * k + 1) → ℝ)) =
      (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
        LinearMap.ker
          (dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)) := by
  -- Compare the two ambient cut kernels through the common rooted subtour face direction.
  calc
    (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
        LinearMap.ker
          (dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
              complete_graph_edges (2 * k + 1) → ℝ))
        =
          (affineSpan ℝ
            (subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U))).direction := by
            simpa using (rootedSubtourFace_direction_eq_ambientCutKer k hk hU).symm
    _ =
        (affineSpan ℝ
          (subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V))).direction := by
          simpa using congrArg (fun s ↦ (affineSpan ℝ s).direction) hface
    _ =
        (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
          LinearMap.ker
            (dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                complete_graph_edges (2 * k + 1) → ℝ)) := by
                  simpa using rootedSubtourFace_direction_eq_ambientCutKer k hk hV

/-- Helper for Theorem 2.3: equal rooted subtour faces force the restricted cut maps to have the
same kernel on the ambient TSP direction. -/
lemma equalRootedSubtourFaces_restrictedCut_kernel_eq
    (k : ℕ) (hk : 2 ≤ k)
    {U V : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hV : V ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hface :
      subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U) =
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V)) :
    LinearMap.ker
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
      LinearMap.ker
        ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) := by
  exact kerDomRestrict_eq_of_infKer_eq
    ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)
    (dotProductLinearMap
      (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
        complete_graph_edges (2 * k + 1) → ℝ))
    (dotProductLinearMap
      (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
        complete_graph_edges (2 * k + 1) → ℝ))
    (equalRootedSubtourFaces_infKer_eq k hk hU hV hface)

/-- Helper for Theorem 2.3: equal rooted subtour faces force the two restricted cut functionals
to differ only by a nonzero scalar on the ambient TSP direction. -/
lemma equalRootedSubtourFaces_restrictedCut_smul
    (k : ℕ) (hk : 2 ≤ k)
    {U V : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hV : V ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hface :
      subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U) =
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V)) :
    ∃ t : ℝ, t ≠ 0 ∧
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) := by
  have hinf :
      (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
          LinearMap.ker
            (dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)) =
        (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction ⊓
          LinearMap.ker
            (dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                complete_graph_edges (2 * k + 1) → ℝ)) :=
    equalRootedSubtourFaces_infKer_eq k hk hU hV hface
  have hker :
      LinearMap.ker
        ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        LinearMap.ker
          ((dotProductLinearMap
                (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                  complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
              ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) :=
    equalRootedSubtourFaces_restrictedCut_kernel_eq k hk hU hV hface
  obtain ⟨wU, hwUD, hwU_eval⟩ := rootedSubtour_cut_normalizingProbe k hk hU
  obtain ⟨wV, hwVD, hwV_eval⟩ := rootedSubtour_cut_normalizingProbe k hk hV
  have hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        (((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) ⟨wU, hwUD⟩) •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) := by
    -- Once the restricted kernels agree, the `U`-normalizing probe fixes the scalar.
    refine linearMap_eq_smul_of_ker_eq_and_apply_eq_one hker ?_
    simpa [LinearMap.domRestrict_apply] using hwU_eval
  have ht_ne :
      (((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) ⟨wU, hwUD⟩) ≠ 0 := by
    intro ht_zero
    have hzeroMap :
        ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) = 0 := by
      rw [hsmul, ht_zero, zero_smul]
    have hvalue0 :
        dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ) wV = 0 := by
      simpa [LinearMap.domRestrict_apply] using
        congrArg
          (fun f :
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction →ₗ[ℝ] ℝ) ↦
              f ⟨wV, hwVD⟩)
          hzeroMap
    have hvalue : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) =
            dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
                complete_graph_edges (2 * k + 1) → ℝ) wV := by
                  simpa using hwV_eval.symm
        _ = 0 := hvalue0
    exact one_ne_zero hvalue
  refine
    ⟨(((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) ⟨wU, hwUD⟩),
      ht_ne, ?_⟩
  simpa using hsmul

/-- Helper for Theorem 2.3: once the two rooted cut functionals agree up to a nonzero scalar on
the ambient TSP direction, the target rooted cut matches the source anchor values and the scalar
is forced to be `1`. -/
lemma rootedSubtour_restrictedCut_smul_apply
    (k : ℕ)
    {U V : Finset (Fin (2 * k))}
    {t : ℝ}
    (hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)))
    {w : complete_graph_edges (2 * k + 1) → ℝ}
    (hw : w ∈ (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction) :
    dotProductLinearMap
        (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
          complete_graph_edges (2 * k + 1) → ℝ) w =
      t *
        dotProductLinearMap
          (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
            complete_graph_edges (2 * k + 1) → ℝ) w := by
  -- Evaluate the restricted scalar identity on the ambient direction vector `w`.
  simpa [LinearMap.domRestrict_apply, smul_eq_mul] using
    congrArg
      (fun f :
        ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction →ₗ[ℝ] ℝ) ↦
          f ⟨w, hw⟩)
      hsmul

/-- Helper for Theorem 2.3: the target rooted cut must cross the root edge at each source
outside anchor. -/
lemma rootedSubtour_target_qValue_eq_one_of_restrictedCut_smul
    (k : ℕ)
    {U V : Finset (Fin (2 * k))}
    {t : ℝ}
    (ht_ne : t ≠ 0)
    (hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)))
    {p q r : Fin (2 * k)}
    (hp : p ∈ U)
    (hq : q ∉ U)
    (hr : r ∉ U)
    (hr_ne : r ≠ q) :
    cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge q) = 1 := by
  let WU := rootedOddSubsetEmbedding k U
  let WV := rootedOddSubsetEmbedding k V
  have hpq : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hp)
  have hp0U :
      cutIncidenceVector WU (rootEdge p) = 0 := by
    simpa [WU, hp] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U p
  have hq1U :
      cutIncidenceVector WU (rootEdge q) = 1 := by
    simpa [WU, hq] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U q
  have hr1U :
      cutIncidenceVector WU (rootEdge r) = 1 := by
    simpa [WU, hr] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U r
  have hprobe_mem :
      rootEdgeProbe r p q hr_ne hpq ∈
        (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction :=
    rootEdgeProbe_mem_affineHullDirection r p q hr_ne hpq
  have hprobe_rel :
      dotProductLinearMap
          (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
          (rootEdgeProbe r p q hr_ne hpq) =
        t *
          dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) :=
    rootedSubtour_restrictedCut_smul_apply k hsmul hprobe_mem
  rcases cutVertices_subset_zero_one_box ⟨WV, rfl⟩ (rootEdge q) with hq0V | hq1V
  · have hUeval :
        dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) = 2 := by
      rw [dotProductLinearMap_apply]
      calc
        cutIncidenceVector WU ⬝ᵥ rootEdgeProbe r p q hr_ne hpq
            = 2 * cutIncidenceVector WU (rootEdge r) := by
                exact
                  cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
                    WU r p q hr_ne hpq hp0U hq1U
        _ = 2 := by rw [hr1U]; norm_num
    have hVeval :
        dotProductLinearMap
            (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) = 0 := by
      rw [dotProductLinearMap_apply]
      exact cutIncidenceVector_dot_rootEdgeProbe_eq_zero_of_anchor_zero
        WV r p q hr_ne hpq hq0V
    rw [hUeval, hVeval] at hprobe_rel
    have : t = 0 := by linarith
    exact False.elim (ht_ne this)
  · exact hq1V

/-- Helper for Theorem 2.3: the target rooted cut must also cross any second source outside
anchor. -/
lemma rootedSubtour_target_rValue_eq_one_of_restrictedCut_smul
    (k : ℕ)
    {U V : Finset (Fin (2 * k))}
    {t : ℝ}
    (ht_ne : t ≠ 0)
    (hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)))
    {p q r : Fin (2 * k)}
    (hp : p ∈ U)
    (hq : q ∉ U)
    (hr : r ∉ U)
    (hr_ne : r ≠ q) :
    cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge r) = 1 := by
  let WU := rootedOddSubsetEmbedding k U
  let WV := rootedOddSubsetEmbedding k V
  have hpr : p ≠ r := by
    intro hpr
    exact hr (hpr ▸ hp)
  have hp0U :
      cutIncidenceVector WU (rootEdge p) = 0 := by
    simpa [WU, hp] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U p
  have hq1U :
      cutIncidenceVector WU (rootEdge q) = 1 := by
    simpa [WU, hq] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U q
  have hr1U :
      cutIncidenceVector WU (rootEdge r) = 1 := by
    simpa [WU, hr] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U r
  have hprobe_mem :
      rootEdgeProbe q p r hr_ne.symm hpr ∈
        (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction :=
    rootEdgeProbe_mem_affineHullDirection q p r hr_ne.symm hpr
  have hprobe_rel :
      dotProductLinearMap
          (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
          (rootEdgeProbe q p r hr_ne.symm hpr) =
        t *
          dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe q p r hr_ne.symm hpr) :=
    rootedSubtour_restrictedCut_smul_apply k hsmul hprobe_mem
  rcases cutVertices_subset_zero_one_box ⟨WV, rfl⟩ (rootEdge r) with hr0V | hr1V
  · have hUeval :
        dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe q p r hr_ne.symm hpr) = 2 := by
      rw [dotProductLinearMap_apply]
      calc
        cutIncidenceVector WU ⬝ᵥ rootEdgeProbe q p r hr_ne.symm hpr
            = 2 * cutIncidenceVector WU (rootEdge q) := by
                exact
                  cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
                    WU q p r hr_ne.symm hpr hp0U hr1U
        _ = 2 := by rw [hq1U]; norm_num
    have hVeval :
        dotProductLinearMap
            (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe q p r hr_ne.symm hpr) = 0 := by
      rw [dotProductLinearMap_apply]
      exact cutIncidenceVector_dot_rootEdgeProbe_eq_zero_of_anchor_zero
        WV q p r hr_ne.symm hpr hr0V
    rw [hUeval, hVeval] at hprobe_rel
    have : t = 0 := by linarith
    exact False.elim (ht_ne this)
  · exact hr1V

/-- Helper for Theorem 2.3: the target rooted cut keeps the source inside anchor on the rooted
side once both outside anchors have been identified. -/
lemma rootedSubtour_target_pValue_eq_zero_of_restrictedCut_smul
    (k : ℕ)
    {U V : Finset (Fin (2 * k))}
    {t : ℝ}
    (ht_ne : t ≠ 0)
    (hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)))
    {p q r : Fin (2 * k)}
    (hp : p ∈ U)
    (hq : q ∉ U)
    (hr : r ∉ U)
    (hr_ne : r ≠ q)
    (hq1V : cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge q) = 1)
    (hr1V : cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge r) = 1) :
    cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge p) = 0 := by
  let WU := rootedOddSubsetEmbedding k U
  let WV := rootedOddSubsetEmbedding k V
  have hpq : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hp)
  have hp0U :
      cutIncidenceVector WU (rootEdge p) = 0 := by
    simpa [WU, hp] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U p
  have hq1U :
      cutIncidenceVector WU (rootEdge q) = 1 := by
    simpa [WU, hq] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U q
  have hr1U :
      cutIncidenceVector WU (rootEdge r) = 1 := by
    simpa [WU, hr] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U r
  have hprobe_mem :
      rootEdgeProbe r p q hr_ne hpq ∈
        (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction :=
    rootEdgeProbe_mem_affineHullDirection r p q hr_ne hpq
  have hprobe_rel :
      dotProductLinearMap
          (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
          (rootEdgeProbe r p q hr_ne hpq) =
        t *
          dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) :=
    rootedSubtour_restrictedCut_smul_apply k hsmul hprobe_mem
  rcases cutVertices_subset_zero_one_box ⟨WV, rfl⟩ (rootEdge p) with hp0V | hp1V
  · exact hp0V
  · have hUeval :
        dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) = 2 := by
      rw [dotProductLinearMap_apply]
      calc
        cutIncidenceVector WU ⬝ᵥ rootEdgeProbe r p q hr_ne hpq
            = 2 * cutIncidenceVector WU (rootEdge r) := by
                exact
                  cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
                    WU r p q hr_ne hpq hp0U hq1U
        _ = 2 := by rw [hr1U]; norm_num
    have hVeval :
        dotProductLinearMap
            (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) = 0 := by
      rw [dotProductLinearMap_apply]
      calc
        cutIncidenceVector WV ⬝ᵥ rootEdgeProbe r p q hr_ne hpq
            = 2 *
                (cutIncidenceVector WV (rootEdge r) -
                  cutIncidenceVector WV (rootEdge p)) := by
                    exact
                      cutIncidenceVector_dot_rootEdgeProbe_eq_two_mul_sub_of_anchor_one
                        WV r p q hr_ne hpq hq1V
        _ = 0 := by linarith [hr1V, hp1V]
    rw [hUeval, hVeval] at hprobe_rel
    have : t = 0 := by linarith
    exact False.elim (ht_ne this)

/-- Helper for Theorem 2.3: once the target rooted cut matches the source anchor values, the
restricted-cut scalar is forced to be `1`. -/
lemma rootedSubtour_scalar_eq_one_of_restrictedCut_smul
    (k : ℕ)
    {U V : Finset (Fin (2 * k))}
    {t : ℝ}
    (hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)))
    {p q r : Fin (2 * k)}
    (hp : p ∈ U)
    (hq : q ∉ U)
    (hr : r ∉ U)
    (hr_ne : r ≠ q)
    (hq1V : cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge q) = 1)
    (hr1V : cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge r) = 1)
    (hp0V : cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge p) = 0) :
    t = 1 := by
  let WU := rootedOddSubsetEmbedding k U
  let WV := rootedOddSubsetEmbedding k V
  have hpq : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hp)
  have hp0U :
      cutIncidenceVector WU (rootEdge p) = 0 := by
    simpa [WU, hp] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U p
  have hq1U :
      cutIncidenceVector WU (rootEdge q) = 1 := by
    simpa [WU, hq] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U q
  have hr1U :
      cutIncidenceVector WU (rootEdge r) = 1 := by
    simpa [WU, hr] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U r
  have hprobe_mem :
      rootEdgeProbe r p q hr_ne hpq ∈
        (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction :=
    rootEdgeProbe_mem_affineHullDirection r p q hr_ne hpq
  have hprobe_rel :
      dotProductLinearMap
          (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
          (rootEdgeProbe r p q hr_ne hpq) =
        t *
          dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe r p q hr_ne hpq) :=
    rootedSubtour_restrictedCut_smul_apply k hsmul hprobe_mem
  have hUeval :
      dotProductLinearMap
          (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
          (rootEdgeProbe r p q hr_ne hpq) = 2 := by
    rw [dotProductLinearMap_apply]
    calc
      cutIncidenceVector WU ⬝ᵥ rootEdgeProbe r p q hr_ne hpq
          = 2 * cutIncidenceVector WU (rootEdge r) := by
              exact
                cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
                  WU r p q hr_ne hpq hp0U hq1U
      _ = 2 := by rw [hr1U]; norm_num
  have hVeval :
      dotProductLinearMap
          (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
          (rootEdgeProbe r p q hr_ne hpq) = 2 := by
    rw [dotProductLinearMap_apply]
    calc
      cutIncidenceVector WV ⬝ᵥ rootEdgeProbe r p q hr_ne hpq
          = 2 * cutIncidenceVector WV (rootEdge r) := by
              exact
                cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
                  WV r p q hr_ne hpq hp0V hq1V
      _ = 2 := by rw [hr1V]; norm_num
  rw [hUeval, hVeval] at hprobe_rel
  linarith

/-- Helper for Theorem 2.3: once the two rooted cut functionals agree up to a nonzero scalar on
the ambient TSP direction, the target rooted cut matches the source anchor values and the scalar
is forced to be `1`. -/
lemma rootedSubtour_targetAnchorValues_of_restrictedCut_smul
    (k : ℕ)
    {U V : Finset (Fin (2 * k))}
    {t : ℝ}
    (ht_ne : t ≠ 0)
    (hsmul :
      ((dotProductLinearMap
            (cutIncidenceVector (rootedOddSubsetEmbedding k V) :
              complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
          ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)) =
        t •
          ((dotProductLinearMap
              (cutIncidenceVector (rootedOddSubsetEmbedding k U) :
                complete_graph_edges (2 * k + 1) → ℝ)).domRestrict
            ((affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction)))
    {p q r : Fin (2 * k)}
    (hp : p ∈ U)
    (hq : q ∉ U)
    (hr : r ∉ U)
    (hr_ne : r ≠ q) :
    let WV := rootedOddSubsetEmbedding k V
    cutIncidenceVector WV (rootEdge q) = 1 ∧
      cutIncidenceVector WV (rootEdge r) = 1 ∧
        cutIncidenceVector WV (rootEdge p) = 0 ∧
          t = 1 := by
  let WV := rootedOddSubsetEmbedding k V
  have hq1V :
      cutIncidenceVector WV (rootEdge q) = 1 := by
    simpa [WV] using
      rootedSubtour_target_qValue_eq_one_of_restrictedCut_smul k ht_ne hsmul hp hq hr hr_ne
  have hr1V :
      cutIncidenceVector WV (rootEdge r) = 1 := by
    simpa [WV] using
      rootedSubtour_target_rValue_eq_one_of_restrictedCut_smul k ht_ne hsmul hp hq hr hr_ne
  have hp0V :
      cutIncidenceVector WV (rootEdge p) = 0 := by
    simpa [WV] using
      rootedSubtour_target_pValue_eq_zero_of_restrictedCut_smul
        k ht_ne hsmul hp hq hr hr_ne
          (by simpa [WV] using hq1V)
          (by simpa [WV] using hr1V)
  have ht_one : t = 1 :=
    rootedSubtour_scalar_eq_one_of_restrictedCut_smul
      k hsmul hp hq hr hr_ne
        (by simpa [WV] using hq1V)
        (by simpa [WV] using hr1V)
        (by simpa [WV] using hp0V)
  exact ⟨hq1V, hr1V, hp0V, ht_one⟩

/-- Helper for Theorem 2.3: every rooted embedded `k`-subset yields a transported subtour facet of
`travelingSalesmanPolytopeReindexed (2 * k + 1)`. -/
lemma rootedSubtourFacet_mapsToFacet
    (k : ℕ) (hk : 2 ≤ k) :
    Set.MapsTo
      (fun U : Finset (Fin (2 * k)) ↦
        ((LinearEquiv.funCongrLeft ℝ ℝ
            (Fintype.equivFin (complete_graph_edges (2 * k + 1)))).symm ''
          subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U)))
      ((Finset.univ : Finset (Fin (2 * k))).powersetCard k)
      {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
          IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F} := by
  intro U hU
  have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
  have hrooted_card : (rootedOddSubsetEmbedding k U).card = k + 1 := by
    -- Rewrite the rooted cardinality through the source family cardinality `|U| = k`.
    simpa [hUcard] using rootedOddSubsetEmbedding_card k U
  -- The rooted family lands in the odd-cardinality facet range handled by Chapter 7.
  refine subtourFaceReindexed_isFacet (by omega) (rootedOddSubsetEmbedding k U) ?_ ?_
  · omega
  · omega

/-- Helper for Theorem 2.3: the remaining combinatorial separator step is exactly the injectivity
of the rooted subtour-face map on the source `k`-subset family. -/
lemma rootedSubtour_rootEdgeValues_eq_of_face_eq
    (k : ℕ) (hk : 2 ≤ k)
    {U V : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hV : V ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hface :
      subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U) =
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V)) :
    ∀ u : Fin (2 * k),
      cutIncidenceVector (rootedOddSubsetEmbedding k U) (rootEdge u) =
        cutIncidenceVector (rootedOddSubsetEmbedding k V) (rootEdge u) := by
  let WU := rootedOddSubsetEmbedding k U
  let WV := rootedOddSubsetEmbedding k V
  obtain ⟨t, ht_ne, hsmul⟩ := equalRootedSubtourFaces_restrictedCut_smul k hk hU hV hface
  obtain ⟨p, _, q, r, hp, -, -, hq, hr, hr_ne⟩ :=
    powersetCard_exists_two_inside_two_outside k hk hU
  have hpq : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hp)
  have hp0U :
      cutIncidenceVector WU (rootEdge p) = 0 := by
    -- The inside anchor `p` stays on the rooted side of the source cut.
    simpa [WU, hp] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U p
  have hq1U :
      cutIncidenceVector WU (rootEdge q) = 1 := by
    -- The outside anchor `q` crosses the source cut at the root edge.
    simpa [WU, hq] using cutIncidenceVector_rootedOddSubsetEmbedding_rootEdge k U q
  obtain ⟨hq1V, hr1V, hp0V, ht_one⟩ := by
    -- Recover the target anchor values and normalize the scalar in one reusable step.
    simpa [WU, WV] using
      rootedSubtour_targetAnchorValues_of_restrictedCut_smul k ht_ne hsmul hp hq hr hr_ne
  intro u
  by_cases huq : u = q
  · subst u
    calc
      cutIncidenceVector WU (rootEdge q) = 1 := hq1U
      _ = cutIncidenceVector WV (rootEdge q) := hq1V.symm
  · have hprobe_mem :
        rootEdgeProbe u p q huq hpq ∈
          (affineSpan ℝ (travelingSalesmanPolytope (2 * k + 1))).direction :=
      rootEdgeProbe_mem_affineHullDirection u p q huq hpq
    have hprobe_rel :
        dotProductLinearMap
            (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe u p q huq hpq) =
          t *
            dotProductLinearMap
              (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
              (rootEdgeProbe u p q huq hpq) :=
      rootedSubtour_restrictedCut_smul_apply k hsmul hprobe_mem
    have hUeval :
        dotProductLinearMap
            (cutIncidenceVector WU : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe u p q huq hpq) =
          2 * cutIncidenceVector WU (rootEdge u) := by
      rw [dotProductLinearMap_apply]
      exact
        cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
          WU u p q huq hpq hp0U hq1U
    have hVeval :
        dotProductLinearMap
            (cutIncidenceVector WV : complete_graph_edges (2 * k + 1) → ℝ)
            (rootEdgeProbe u p q huq hpq) =
          2 * cutIncidenceVector WV (rootEdge u) := by
      rw [dotProductLinearMap_apply]
      exact
        cutIncidenceVector_dot_rootEdgeProbe_of_anchor_values
          WV u p q huq hpq hp0V hq1V
    rw [hUeval, hVeval, ht_one] at hprobe_rel
    linarith

/-- Helper for Theorem 2.3: the remaining combinatorial separator step is exactly the injectivity
of the rooted subtour-face map on the source `k`-subset family. -/
lemma rootedSubtourFace_eq_implies_cutIncidence_eq
    (k : ℕ) (hk : 2 ≤ k)
    {U V : Finset (Fin (2 * k))}
    (hU : U ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hV : V ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard k)
    (hface :
      subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U) =
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V)) :
    cutIncidenceVector (rootedOddSubsetEmbedding k U) =
      cutIncidenceVector (rootedOddSubsetEmbedding k V) := by
  -- Route correction: first recover all root-edge coordinates from the probe comparison, and
  -- only then reconstruct the full cut vector from those canonical coordinates.
  exact cutIncidenceVector_eq_of_rootEdgeValues_eq _ _
    (rootedSubtour_rootEdgeValues_eq_of_face_eq k hk hU hV hface)

/-- Helper for Theorem 2.3: the remaining combinatorial separator step is exactly the injectivity
of the rooted subtour-face map on the source `k`-subset family. -/
lemma rootedSubtourFacet_injOnPowersetCard
    (k : ℕ) (hk : 2 ≤ k) :
    Set.InjOn
      (fun U : Finset (Fin (2 * k)) ↦
        ((LinearEquiv.funCongrLeft ℝ ℝ
            (Fintype.equivFin (complete_graph_edges (2 * k + 1)))).symm ''
          subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U)))
      ((Finset.univ : Finset (Fin (2 * k))).powersetCard k) := by
  intro U hU V hV hface
  let e := LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges (2 * k + 1)))
  have hnative :
      subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U) =
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V) := by
    -- Pull the transported face equality back through the coordinate equivalence in one step.
    exact
      (Equiv.image_eq_iff_eq e.symm.toEquiv
        (subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U))
        (subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k V))).mp hface
  -- The cut vector already determines the rooted source subset.
  exact rootedOddSubsetEmbedding_eq_of_cutIncidenceVector_eq k
    (rootedSubtourFace_eq_implies_cutIncidence_eq k hk hU hV hnative)

/-- Helper for Theorem 2.3: the rooted odd-cardinality subtour family contributes at least
`Nat.centralBinom k` distinct facets to the reindexed traveling salesman polytope. -/
lemma rootedOddSubtourFacetCountLowerBound
    (k : ℕ) (hk : 2 ≤ k) :
    Nat.centralBinom k ≤
      {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
          IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F}.ncard := by
  let source :
      Set (Finset (Fin (2 * k))) :=
    (Finset.univ : Finset (Fin (2 * k))).powersetCard k
  let facetMap :
      Finset (Fin (2 * k)) →
        Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) :=
    fun U ↦
      ((LinearEquiv.funCongrLeft ℝ ℝ
          (Fintype.equivFin (complete_graph_edges (2 * k + 1)))).symm ''
        subtour_elimination_face (2 * k + 1) (rootedOddSubsetEmbedding k U))
  have hsource :
      source.ncard = Nat.centralBinom k := by
    -- The source family is exactly the `k`-subsets of `Fin (2 * k)`.
    simp [source, Nat.centralBinom]
  have hfacet_le :
      source.ncard ≤
        {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
            IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F}.ncard := by
    -- Compare the counted source family with the facet owner through the rooted subtour-face map.
    exact Set.ncard_le_ncard_of_injOn facetMap
      (rootedSubtourFacet_mapsToFacet k hk)
      (rootedSubtourFacet_injOnPowersetCard k hk)
      (polytope_finite_facets (travelingSalesmanPolytopeReindexed_isPolytope (2 * k + 1)))
  -- Substitute the source cardinality to recover the advertised central-binomial lower bound.
  simpa [hsource] using hfacet_le

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_7/ch2_sec2_7_theorem_2_3.lean.
Theorem 2.3. [Kaibel--Weltge] There is no polynomially bounded family of linear inequality systems
whose feasible regions are the canonical `Fin`-coordinate reindexings of
`travelingSalesmanPolytope n` for every `n ≥ 3`. -/
theorem travelingSalesmanPolytope_no_polynomial_size_linear_system :
    ¬ ∃ (m : ℕ → ℕ)
        (A : ∀ n, Matrix (Fin (m n)) (Fin (Fintype.card (complete_graph_edges n))) ℝ)
        (b : ∀ n, Fin (m n) → ℝ),
          m.PolynomiallyBoundedByNat id ∧
            ∀ n, 3 ≤ n →
              travelingSalesmanPolytopeReindexed n = polyhedron_le_set (A n) (b n) := by
  intro hsystem
  rcases hsystem with ⟨m, A, b, hm_poly, hdesc⟩
  -- Route correction: the source only cites Kaibel--Weltge abstractly, so the Lean route first
  -- turns any exact description into a row bound on the facet count of each reindexed TSP polytope.
  have hrowBound :
      ∀ n, 3 ≤ n →
        {F : Set (Fin (Fintype.card (complete_graph_edges n)) → ℝ) |
            IsFacetOf (travelingSalesmanPolytopeReindexed n) F}.ncard ≤ m n := by
    intro n hn
    have h_nonempty : (travelingSalesmanPolytopeReindexed n).Nonempty :=
      travelingSalesmanPolytopeReindexed_nonempty n
    have hpoly_nonempty : (polyhedron_le_set (A n) (b n)).Nonempty := by
      -- Rewrite the exact description to inherit nonemptiness from the reindexed TSP polytope.
      simpa [hdesc n hn] using h_nonempty
    -- Apply the generic facet-count bound to the exact matrix presentation at size `n`.
    simpa [hdesc n hn] using
      facetCount_le_rowCount_ofExactDescription (A n) (b n) hpoly_nonempty
  rcases (Function.polynomiallyBoundedByNat_iff).1 hm_poly with ⟨p, hp⟩
  rcases natPolynomial_mulEvalOdd_lt_fourPow p with ⟨k, hk4, hkGrow⟩
  have hk2 : 2 ≤ k := by omega
  have hfacetLower :
      Nat.centralBinom k ≤
        {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
            IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F}.ncard :=
    rootedOddSubtourFacetCountLowerBound k hk2
  have hfacetUpper :
      {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
          IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F}.ncard ≤
        m (2 * k + 1) :=
    hrowBound (2 * k + 1) (by omega)
  have hmEval : m (2 * k + 1) ≤ p.eval (2 * k + 1) :=
    hp (2 * k + 1)
  have hlower :
      4 ^ k <
        k *
          {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
              IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F}.ncard := by
    -- The central-binomial family already gives exponentially many facet candidates at odd sizes.
    exact lt_of_lt_of_le
      (Nat.four_pow_lt_mul_centralBinom k hk4)
      (Nat.mul_le_mul_left k hfacetLower)
  have hupper :
      k *
          {F : Set (Fin (Fintype.card (complete_graph_edges (2 * k + 1))) → ℝ) |
              IsFacetOf (travelingSalesmanPolytopeReindexed (2 * k + 1)) F}.ncard ≤
        k * p.eval (2 * k + 1) := by
    -- The row-count upper bound transports directly through the polynomial witness for `m`.
    exact le_trans (Nat.mul_le_mul_left k hfacetUpper) (Nat.mul_le_mul_left k hmEval)
  have hcontr : 4 ^ k < 4 ^ k := by
    exact lt_of_lt_of_le hlower (le_trans hupper (le_of_lt hkGrow))
  exact Nat.lt_irrefl _ hcontr

#print axioms travelingSalesmanPolytope_no_polynomial_size_linear_system
