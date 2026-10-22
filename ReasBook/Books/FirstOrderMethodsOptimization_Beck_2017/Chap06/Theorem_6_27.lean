/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_10
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp

section

variable {E : Type*} [NormedAddCommGroup E]

private lemma projection_mapping_eq_of_pairwise_norm_comparison
    (D : Set E) (x x' : E)
    (hcmp : ∀ {y z : E}, y ∈ D → z ∈ D →
      (‖y - x‖ ≤ ‖z - x‖ ↔ ‖y - x'‖ ≤ ‖z - x'‖)) :
    P[D] x = P[D] x' := by
  ext y
  rw [mem_projection_mapping_iff, mem_projection_mapping_iff]
  constructor
  · rintro ⟨hyD, hyMin⟩
    refine ⟨hyD, ?_⟩
    rw [isMinOn_iff] at hyMin ⊢
    intro z hz
    exact (hcmp hyD hz).mp (hyMin z hz)
  · rintro ⟨hyD, hyMin⟩
    refine ⟨hyD, ?_⟩
    rw [isMinOn_iff] at hyMin ⊢
    intro z hz
    exact (hcmp hyD hz).mpr (hyMin z hz)

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma norm_le_norm_sub_smul_iff_of_mem_hyperplane
    {a : E} {b μ : ℝ} {x y z : E}
    (hy : y ∈ (hyperplane a b : Set E))
    (hz : z ∈ (hyperplane a b : Set E)) :
    ‖y - x‖ ≤ ‖z - x‖ ↔ ‖y - (x - μ • a)‖ ≤ ‖z - (x - μ • a)‖ := by
  have hy_inner : inner ℝ y a = b := by
    simpa [real_inner_comm] using (mem_hyperplane_iff a b y).mp hy
  have hz_inner : inner ℝ z a = b := by
    simpa [real_inner_comm] using (mem_hyperplane_iff a b z).mp hz
  have hy_shift :
      ‖y - (x - μ • a)‖ * ‖y - (x - μ • a)‖ =
        ‖y - x‖ * ‖y - x‖ +
          (2 * μ * b + (‖x - μ • a‖ * ‖x - μ • a‖ - ‖x‖ * ‖x‖)) := by
    have hyx := norm_sub_mul_self_real y x
    rw [norm_sub_mul_self_real]
    simp [hy_inner, inner_sub_right, real_inner_smul_right]
    nlinarith [hyx]
  have hz_shift :
      ‖z - (x - μ • a)‖ * ‖z - (x - μ • a)‖ =
        ‖z - x‖ * ‖z - x‖ +
          (2 * μ * b + (‖x - μ • a‖ * ‖x - μ • a‖ - ‖x‖ * ‖x‖)) := by
    have hzx := norm_sub_mul_self_real z x
    rw [norm_sub_mul_self_real]
    simp [hz_inner, inner_sub_right, real_inner_smul_right]
    nlinarith [hzx]
  constructor <;> intro h
  · have hsq : ‖y - x‖ * ‖y - x‖ ≤ ‖z - x‖ * ‖z - x‖ := by
      nlinarith [h, norm_nonneg (y - x), norm_nonneg (z - x)]
    have hsq_shift :
        ‖y - (x - μ • a)‖ * ‖y - (x - μ • a)‖ ≤
          ‖z - (x - μ • a)‖ * ‖z - (x - μ • a)‖ := by
      nlinarith [hsq, hy_shift, hz_shift]
    nlinarith [hsq_shift, norm_nonneg (y - (x - μ • a)), norm_nonneg (z - (x - μ • a))]
  · have hsq :
        ‖y - (x - μ • a)‖ * ‖y - (x - μ • a)‖ ≤
          ‖z - (x - μ • a)‖ * ‖z - (x - μ • a)‖ := by
      nlinarith [h, norm_nonneg (y - (x - μ • a)), norm_nonneg (z - (x - μ • a))]
    have hsq_unshift : ‖y - x‖ * ‖y - x‖ ≤ ‖z - x‖ * ‖z - x‖ := by
      nlinarith [hsq, hy_shift, hz_shift]
    nlinarith [hsq_unshift, norm_nonneg (y - x), norm_nonneg (z - x)]

lemma projection_mapping_eq_shifted_projection_mapping_of_subset_hyperplane
    (a : E) (b : ℝ) (D : Set E) (x : E) (μ : ℝ)
    (hD : D ⊆ (hyperplane a b : Set E)) :
    P[D] x = P[D] (x - μ • a) := by
  exact
    projection_mapping_eq_of_pairwise_norm_comparison D x (x - μ • a)
      fun hy hz ↦ norm_le_norm_sub_smul_iff_of_mem_hyperplane (hD hy) (hD hz)

/- Theorem 6.27 lives in the Chapter 6 projection domain. Domain sampling for the target
declarations is:
1. `P[C]` from Theorem 6.24, the chapter's set-valued projection owner.
2. `hyperplane a b` from Definition 1.10, the intrinsic affine-constraint owner on real
   inner-product spaces.
3. `coordinateHyperplane a b` from Definition 1.10, the coordinate `bridge/view` obtained by
   transporting `hyperplane` through `toLp 2`.
4. `projection_mapping_inter_eq_of_projection_mapping_subset` from Theorem 6.24, the canonical
   restriction theorem used once the hyperplane constraint is known to contain the shifted
   projection set.

The primitive data are only a constraint set `C`, a hyperplane normal `a`, an offset `b`, and a
shift scalar `μ`. The `core/canonical` statement therefore belongs first at the intrinsic
`hyperplane` level, while the coordinate theorem below is kept only as the bridge needed to expose
the textbook finite-coordinate box specialization. -/

-- Proof sketch: the hypothesis says that every minimizer of the shifted projection problem onto
-- `C` already lies on the affine boundary `hyperplane a b`. Hence those same minimizers are
-- feasible for the smaller problem on `(hyperplane a b : Set E) ∩ C`, and no other point in the
-- intersection can improve the distance beyond the shifted minimum.
/-- Core/canonical hyperplane-shift identity: if the shifted projection set onto `C` already lies
in the intrinsic hyperplane `hyperplane a b`, then projecting `x` onto the intersection with that
hyperplane agrees with projecting `x - μ • a` onto `C`. -/
theorem projection_mapping_hyperplane_inter_eq_shifted_projection_mapping
    (a : E) (b : ℝ) (C : Set E) (x : E) (μ : ℝ)
    (hproj_nonempty : (P[C] (x - μ • a)).Nonempty)
    (hμ : P[C] (x - μ • a) ⊆ (hyperplane a b : Set E)) :
    P[((hyperplane a b : Set E) ∩ C)] x =
      P[C] (x - μ • a) := by
  calc
    P[((hyperplane a b : Set E) ∩ C)] x =
        P[((hyperplane a b : Set E) ∩ C)] (x - μ • a) := by
      exact
        projection_mapping_eq_shifted_projection_mapping_of_subset_hyperplane
          a b (((hyperplane a b : Set E) ∩ C)) x μ fun _ hy ↦ hy.1
    _ = P[C] (x - μ • a) := by
      simpa [Set.inter_comm] using
        projection_mapping_inter_eq_of_projection_mapping_subset
          C (hyperplane a b : Set E) (x - μ • a) hproj_nonempty hμ

end

section

variable {ι : Type*} [Fintype ι]

local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι

/-- Helper for Theorem 6.27: pulling the coordinate hyperplane back along `ofLp` recovers the
intrinsic Euclidean hyperplane. -/
lemma preimage_coordinateHyperplane_eq_hyperplane (a : X) (b : ℝ) :
    ((fun y : E ↦ y.ofLp) ⁻¹' coordinateHyperplane a b) =
      (hyperplane (toLp 2 a) b : Set E) := by
  -- Unfold the coordinate view and cancel the `ofLp`/`toLp` transport on the Euclidean owner.
  ext y
  simp [coordinateHyperplane]

/-- Bridge/view theorem in the Euclidean coordinate model: if the shifted projection set onto `C`
already lies in the coordinate hyperplane, then projecting `x` onto the intersection with that
coordinate hyperplane agrees with projecting `x - μ • a` onto `C`. The coordinate predicates are
pulled back along `ofLp`, so the owner `P[...]` is the Euclidean `L²` projection matching the
textbook statement. -/
theorem projection_mapping_coordinateHyperplane_inter_eq_shifted_projection_mapping
    (a : X) (b : ℝ) (C : Set X) (x : E) (μ : ℝ)
    (hproj_nonempty : (P[((fun y : E ↦ y.ofLp) ⁻¹' C)] (x - μ • toLp 2 a)).Nonempty)
    (hμ : P[((fun y : E ↦ y.ofLp) ⁻¹' C)] (x - μ • toLp 2 a) ⊆
      ((fun y : E ↦ y.ofLp) ⁻¹' coordinateHyperplane a b)) :
    P[((fun y : E ↦ y.ofLp) ⁻¹' (coordinateHyperplane a b ∩ C))] x =
      P[((fun y : E ↦ y.ofLp) ⁻¹' C)] (x - μ • toLp 2 a) := by
  -- Route correction: the old raw `ι → ℝ` owner used the wrong ambient norm, so the proof now
  -- stays on `EuclideanSpace ℝ ι` and only transports the constraint sets through `ofLp`.
  have hμ' :
      P[((fun y : E ↦ y.ofLp) ⁻¹' C)] (x - μ • toLp 2 a) ⊆
        (hyperplane (toLp 2 a) b : Set E) := by
    -- Rewrite the coordinate hyperplane pullback into the intrinsic hyperplane owner.
    simpa [preimage_coordinateHyperplane_eq_hyperplane] using hμ
  -- After the transport rewrite, the result is exactly the intrinsic hyperplane theorem.
  simpa [Set.preimage_inter, preimage_coordinateHyperplane_eq_hyperplane] using
    projection_mapping_hyperplane_inter_eq_shifted_projection_mapping
      (toLp 2 a) b ((fun y : E ↦ y.ofLp) ⁻¹' C) x μ hproj_nonempty hμ'

omit [Fintype ι] in
/-- Helper for Theorem 6.27: a nonempty coordinate box stays nonempty after pulling it back to the
Euclidean owner along `ofLp`. -/
lemma preimage_box_nonempty_of_box_nonempty (l u : ι → EReal)
    (hbox : (Box[l,u] : Set X).Nonempty) :
    (((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u]) : Set E).Nonempty := by
  rcases hbox with ⟨z, hz⟩
  -- The witness `toLp 2 z` maps back to the original feasible box point `z`.
  refine ⟨toLp 2 z, ?_⟩
  simpa [WithLp.ofLp_toLp] using hz

/-- Theorem 6.27: Euclidean coordinate form of the projection formula for
`H_(a,b) ∩ Box[ℓ,u]`. If the shifted box projection set already satisfies the hyperplane equation,
then the projection of `x` onto the pulled-back hyperplane-box intersection equals the projection
of `x - μ a` onto the pulled-back box. -/
theorem projection_mapping_hyperplane_inter_box_eq_shifted_box_projection_mapping
    (a : X) (b : ℝ) (l u : ι → EReal) (x : E) (μ : ℝ)
    (hμ : P[((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u])] (x - μ • toLp 2 a) ⊆
      ((fun y : E ↦ y.ofLp) ⁻¹' coordinateHyperplane a b)) :
    P[((fun y : E ↦ y.ofLp) ⁻¹' (coordinateHyperplane a b ∩ Box[l,u]))] x =
      P[((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u])] (x - μ • toLp 2 a) := by
  -- Route correction: the theorem is the Euclidean `L²` specialization, so we split on whether
  -- the box owner is empty and then reuse the transported hyperplane theorem from above.
  by_cases hbox : (Box[l,u] : Set X).Nonempty
  · letI : ProperSpace E := FiniteDimensional.proper ℝ E
    have hpreimage_nonempty :
        (((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u]) : Set E).Nonempty :=
      preimage_box_nonempty_of_box_nonempty l u hbox
    have hpreimage_closed :
        IsClosed (((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u]) : Set E) := by
      -- Closedness is preserved under the continuous coordinate-view map `ofLp`.
      exact
        (isClosed_box l u).preimage
          (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : ι ↦ ℝ))
    have hproj_nonempty :
        (P[((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u])] (x - μ • toLp 2 a)).Nonempty :=
      projection_mapping_nonempty_of_nonempty_isClosed
        (((fun y : E ↦ y.ofLp) ⁻¹' Box[l,u]))
        hpreimage_nonempty hpreimage_closed (x - μ • toLp 2 a)
    -- The shifted box projection is nonempty, so the coordinate hyperplane transport theorem
    -- applies directly.
    exact
      projection_mapping_coordinateHyperplane_inter_eq_shifted_projection_mapping
        a b (Box[l,u]) x μ hproj_nonempty hμ
  · have hbox_empty : (Box[l,u] : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp hbox
    -- If the box is empty, both the box and the hyperplane-box intersection have empty
    -- projection owners after pullback.
    ext y
    simp [projection_mapping, hbox_empty]

end
