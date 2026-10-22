/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Finset
open scoped BigOperators WithTopConvexAnalysis

universe uX uU

variable {N : ℕ}

/-
Lemma 3.23 lies in the chapter's primal-dual residual / lower-value domain.

Sampled owner-style declarations:
- `IsLeast`, the canonical order owner for attained lower values;
- mathlib `Finset.centerMass`, the canonical owner for the sampled dual average;
- `gapFunctionCertificate` in `Chap03/Lemma_3_24`, the chapter owner for the sampled certificate;
- `sampledAffineMinorant` in `Chap03/Proposition_3_26`, the chapter owner for one sampled affine
  lower model;
- the affine-map sum `∑ k, α k • ℓ k : X →ᵃ[ℝ] ℝ` in `Chap03/Proposition_3_27`, the canonical
  owner for weighted sums of sampled affine minorants;
- `primal_dual_decomposition_mem_Icc_of_gap_le` in `Chap03/Lemma_3_1_23`, the project's generic
  interval owner for the source-facing chain
  `0 ≤ (f(x_N) - f^*) + (φ^* - φ(\hat u_N)) ≤ f(x_N) - φ(\hat u_N) ≤ r_N`;
- `compact_convex_concave_minimax` in `Chap03/Theorem_3_37`, whose lower slice-value side uses the
  same canonical lower-value construction `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`;
- `∂[P] f(x)` together with the bridge `subdifferentialWithin` in `Chap03/Theorem_3_44`, the
  source-facing owner surface for the relative subgradients used to build the affine lower model.

Best owner abstraction:
- source-facing: the textbook affine model `l_N` built from the sampled selections `u(y_k)` and
  `g(y_k)`, together with the resulting raw gap and interval estimate at the averaged dual point
- core/canonical: the lower slice-value owner
  `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`
- bridge/view: the auxiliary sampled-family specialization of the canonical affine-map sum owner

Primitive data:
- the feasible primal and dual sets `P`, `S`
- the kernel `Ψ`
- the weights `α`, sample points `y`, the sampled-selection maps `u`, `g`
- the iterate `xN`, the attained affine-model minimum `modelMin`, and the residual bound `rN`

Derived API:
- the averaged sampled dual point `(Finset.univ).centerMass α (u ∘ y)`
- the textbook affine model
  `l_N = ∑ k, α k • sampledAffineMinorant (y k) (g (y k)) (Ψ (y k) (u (y k)))`
- the canonical lower slice value `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`
- the auxiliary sampled-family bridge theorem obtained by replacing `u(y_k)` and `g(y_k)` by
  arbitrary sampled families
- the affine-model minimum witness `h_modelMin`

The previous version stated the public residual bound only for a normalized auxiliary sampled model
with arbitrary sampled dual and subgradient families, and it exposed a stronger global attainment
bridge `φ`. This refinement keeps the auxiliary sampled-family bridge, but restores the main
theorem to the textbook source-facing affine model `l_N` built from the sampled selections
`u(y_k)` and `g(y_k)` while placing the chapter's canonical lower-value owner
`u ↦ sInf ((fun x ↦ Ψ x u) '' P)` directly on the public theorem surface.
-/

section AveragedAffineLowerModel

variable {X : Type uX} [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {U : Type uU} [AddCommGroup U] [Module ℝ U]

variable {P : Set X} {S : Set U}
variable {f : X → ℝ}
variable {Ψ : X → U → ℝ}
variable {α : Fin (N + 1) → ℝ} {y : Fin (N + 1) → X}
variable {xN : X}
variable {modelMin rN fStar φStar : ℝ}

local notation "lowerValue" => fun u' : U ↦ sInf ((fun x ↦ Ψ x u') '' P)

section SampledAffineLowerModel

variable {g : Fin (N + 1) → X} {u : Fin (N + 1) → U}

local notation "uHat" => Finset.univ.centerMass α u
local notation "samplePoint[" k "]" => y k
local notation "sampledSlice[" k "]" => (((fun x ↦ Ψ x (u k)) : X → ℝ))
local notation "sampledModel" =>
  (∑ k, α k • sampledAffineMinorant (y k) (g k) (Ψ (y k) (u k)) : X →ᵃ[ℝ] ℝ)

/-- Helper for Lemma 3.23: evaluating the sampled affine model recovers the textbook weighted sum
of sampled affine minorants. -/
theorem sampled_model_apply (x : X) :
    sampledModel x =
      ∑ k, α k * (Ψ (y k) (u k) + inner ℝ (g k) (x - y k)) := by
  classical
  -- Expand the affine-map sum into the scalar textbook model.
  let s : Finset (Fin (N + 1)) := Finset.univ
  change (s.sum fun k ↦ α k • sampledAffineMinorant (y k) (g k) (Ψ (y k) (u k))) x =
      s.sum fun k ↦ α k * (Ψ (y k) (u k) + inner ℝ (g k) (x - y k))
  clear_value s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      simp [his, ih, sampledAffineMinorant_apply]

/-- Helper for Lemma 3.23: each sampled affine lower model lies below its corresponding sampled
slice on the feasible set `P`, and summing preserves that lower bound. -/
theorem sampled_model_le_sampled_slice_sum
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (h_subgrad : ∀ k : Fin (N + 1), g k ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    {x : X} (hx : x ∈ P) :
    sampledModel x ≤ ∑ k, α k * Ψ x (u k) := by
  have hsupport :
      ∀ k : Fin (N + 1),
        Ψ (y k) (u k) + inner ℝ (g k) (x - y k) ≤ Ψ x (u k) := by
    intro k
    rcases mem_subdifferentialWithin_iff.mp (h_subgrad k) with ⟨_, hminorant⟩
    exact hminorant hx
  -- Compare termwise after rewriting the affine-map sum in textbook scalar form.
  calc
    sampledModel x = ∑ k, α k * (Ψ (y k) (u k) + inner ℝ (g k) (x - y k)) := by
      rw [sampled_model_apply]
    _ ≤ ∑ k, α k * Ψ x (u k) := by
      refine Finset.sum_le_sum fun k _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hsupport k) (hα_nonneg k)

/-- Helper for Lemma 3.23: concavity in the dual variable turns the weighted sampled slice values
into the slice value at the averaged sampled dual point. -/
theorem sampled_slice_sum_le_center_mass_slice
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u k ∈ S)
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    {x : X} (hx : x ∈ P) :
    ∑ k, α k * Ψ x (u k) ≤ Ψ x uHat := by
  have h_center_mass :
      Finset.univ.centerMass α (((fun v ↦ Ψ x v) : U → ℝ) ∘ u) ≤ Ψ x uHat := by
    -- Apply Jensen's inequality to the concave slice `v ↦ Ψ x v`.
    exact (h_concave_u x hx).le_map_centerMass
      (t := Finset.univ)
      (fun k _ ↦ hα_nonneg k)
      (by simp [hα_sum_one])
      (fun k _ ↦ hu_mem k)
  -- Rewrite the center of mass of real slice values as the normalized weighted sum.
  rw [Finset.centerMass_eq_of_sum_1 (t := Finset.univ)
      (w := α) (((fun v ↦ Ψ x v) : U → ℝ) ∘ u) hα_sum_one] at h_center_mass
  simpa [Function.comp] using h_center_mass

/-- Helper for Lemma 3.23: the attained minimum of the sampled affine model is a lower bound for
the canonical lower slice value at the averaged sampled dual point. -/
theorem modelMin_le_lowerValue_uHat
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u k ∈ S)
    (h_subgrad : ∀ k : Fin (N + 1), g k ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (sampledModel '' P) modelMin) :
    modelMin ≤ lowerValue uHat := by
  rcases h_modelMin.1 with ⟨x0, hx0, _⟩
  refine le_csInf ?_ ?_
  · exact ⟨Ψ x0 uHat, ⟨x0, hx0, rfl⟩⟩
  · rintro b ⟨x, hx, rfl⟩
    have h_lower_model : modelMin ≤ sampledModel x := by
      exact h_modelMin.2 ⟨x, hx, rfl⟩
    -- Chain the affine-model lower bound with Jensen's inequality at the averaged dual point.
    exact h_lower_model.trans <|
      (sampled_model_le_sampled_slice_sum hα_nonneg h_subgrad hx).trans <|
        sampled_slice_sum_le_center_mass_slice hα_nonneg hα_sum_one hu_mem h_concave_u hx

/-- Auxiliary sampled-family bridge: if a convex combination of sampled affine minorants has least
feasible value `modelMin` and `f xN - modelMin ≤ r_N`, then the raw primal-dual gap against the
canonical lower value at the weighted sampled dual average is bounded by `r_N`. -/
-- Proof sketch: each relative subgradient inequality shows that the affine minorant
-- `x ↦ Ψ (y k) (u k) + ⟪g k, x - y k⟫` is bounded above on `P` by the corresponding slice
-- `x ↦ Ψ x (u k)`. Summing these affine minorants through the canonical affine-map owner
-- `sampledModel` yields a pointwise lower model on `P`. Concavity of `Ψ(x, ·)` on `S` and
-- `ConcaveOn.le_map_centerMass` then give
-- `(Finset.univ).centerMass α (fun k ↦ Ψ x (u k)) ≤ Ψ x uHat` for every `x ∈ P`. The resulting
-- pointwise domination on `P` makes `modelMin` a lower bound for `((fun x ↦ Ψ x uHat) '' P)`,
-- hence `modelMin ≤ lowerValue uHat`. Combining this with the residual bound yields the claim.
theorem duality_gap_le_residual_of_sampled_affine_lower_model
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u k ∈ S)
    (h_subgrad : ∀ k : Fin (N + 1), g k ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (sampledModel '' P) modelMin)
    (h_residual : f xN - modelMin ≤ rN) :
    f xN - lowerValue uHat ≤ rN := by
  have h_modelMin_le_lowerValue :
      modelMin ≤ lowerValue uHat :=
    modelMin_le_lowerValue_uHat
      hα_nonneg hα_sum_one hu_mem h_subgrad h_concave_u h_modelMin
  -- Replace the canonical lower value by the smaller affine-model minimum, then use the residual
  -- estimate against that minimum.
  exact (sub_le_sub_left h_modelMin_le_lowerValue (f xN)).trans h_residual

end SampledAffineLowerModel

section TextbookAffineLowerModel

variable {u : X → U} {g : X → X}

local notation "uHatN" => Finset.univ.centerMass α (u ∘ y)
local notation "samplePoint[" k "]" => y k
local notation "sampledSlice[" k "]" => (((fun x ↦ Ψ x (u (y k))) : X → ℝ))
local notation "lN" =>
  (∑ k, α k • sampledAffineMinorant (y k) (g (y k)) (Ψ (y k) (u (y k))) : X →ᵃ[ℝ] ℝ)

/- The textbook source-facing affine model is the sampled affine-map owner specialized to the dual
and subgradient selections `u(y_k)` and `g(y_k)`. -/

/-- Lemma 3.23: if `x_N` satisfies the residual estimate against the textbook affine model
`l_N = ∑_{k=0}^N α_k [Ψ(y_k, u(y_k)) + ⟪g(y_k), · - y_k⟫]`
built from the sampled selections `u(y_k)` and
`g(y_k) ∈ ∂[P] (fun x ↦ Ψ x (u(y_k))) (y_k)`, then the raw primal-dual gap against the canonical
lower value at the averaged sampled dual point
`\hat u_N = (Finset.univ).centerMass α (u ∘ y)` is bounded above by `r_N`. -/
-- Proof sketch: specialize the auxiliary sampled-family bridge to the concrete sampled families
-- `u ∘ y` and `g ∘ y`. This turns the generic sampled affine-map sum into the textbook model
-- `l_N` and the generic center of mass into the textbook averaged sampled dual point `uHatN`.
theorem duality_gap_le_residual_of_averaged_affine_lower_model
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u (y k) ∈ S)
    (h_subgrad :
      ∀ k : Fin (N + 1), g (y k) ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (lN '' P) modelMin)
    (h_residual : f xN - modelMin ≤ rN) :
    f xN - lowerValue uHatN ≤ rN := by
  let uSample : Fin (N + 1) → U := u ∘ y
  let gSample : Fin (N + 1) → X := g ∘ y
  have hu_mem_sample : ∀ k, uSample k ∈ S := by
    simpa [uSample] using hu_mem
  have h_subgrad_sample :
      ∀ k : Fin (N + 1),
        gSample k ∈ subdifferentialWithin P ((fun x ↦ Ψ x (uSample k)) : X → ℝ) (y k) := by
    simpa [uSample, gSample] using h_subgrad
  simpa [uSample, gSample] using
    duality_gap_le_residual_of_sampled_affine_lower_model
      hα_nonneg hα_sum_one hu_mem_sample h_subgrad_sample h_concave_u h_modelMin h_residual

/-- Interval companion of Lemma 3.23: once `fStar` and `φStar` are known to bound the sampled
primal and dual values at `xN` and `uHatN`, the textbook affine-model residual bound yields the
full decomposition interval estimate. -/
-- Proof sketch: first apply the raw-gap theorem above to obtain
-- `f xN - lowerValue uHatN ≤ rN`. The generic Chapter 3 interval owner
-- `primal_dual_decomposition_mem_Icc_of_gap_le` then applies directly from the local comparison
-- bounds `fStar ≤ f xN` and `lowerValue uHatN ≤ φStar` together with weak duality.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_averaged_affine_lower_model
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u (y k) ∈ S)
    (h_subgrad :
      ∀ k : Fin (N + 1), g (y k) ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (lN '' P) modelMin)
    (h_residual : f xN - modelMin ≤ rN)
    (h_primal : fStar ≤ f xN)
    (h_dual : lowerValue uHatN ≤ φStar)
    (h_weak_duality : φStar ≤ fStar) :
    (f xN - fStar) + (φStar - lowerValue uHatN) ∈
        Set.Icc 0 (f xN - lowerValue uHatN) ∧
      f xN - lowerValue uHatN ≤ rN := by
  have h_gap :
      f xN - lowerValue uHatN ≤ rN :=
    duality_gap_le_residual_of_averaged_affine_lower_model
      hα_nonneg hα_sum_one hu_mem h_subgrad h_concave_u h_modelMin h_residual
  simpa using
    (primal_dual_decomposition_mem_Icc_of_gap_le
      h_primal
      h_dual
      h_weak_duality
      h_gap)

end TextbookAffineLowerModel

end AveragedAffineLowerModel

end
