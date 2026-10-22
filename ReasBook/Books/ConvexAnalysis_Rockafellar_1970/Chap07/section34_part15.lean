/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part14

section Chap07
section Section34

open Set

section SaddleAmbient

variable {m n : ℕ}

/-- Helper for Text 34.1.7: the isolated theorem claim is false, because specializing it to the
open-unit-square power example forces a global upper-extension saddle property contradicted by
`openUnitSquarePowerSaddle`. -/
lemma helperForText_34_1_7_targetTheoremClaim_false :
    ¬ helperForText_34_1_7_targetTheoremClaim := by
  intro hClaim
  rcases helperForText_34_1_7_openUnitPowerKernel_satisfiesTargetHypotheses with
    ⟨hC, hD, hCne, hDne, hJ, hJfinite⟩
  -- Feed the packaged specialization hypotheses into the isolated theorem claim.
  have hConclusion := hClaim hC hD hCne hDne oneDimensionalPowerKernel hJ hJfinite
  -- The full specialized conclusion is impossible because its upper-extension branch fails.
  exact helperForText_34_1_7_specializedConclusion_false hConclusion

/-- Helper for Text 34.1.7: finite values on `C × D` force the first effective domain of the
lower simple extension to be exactly `C`. -/
lemma helperForText_34_1_7_effectiveDomain1_lowerSimpleExtension_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₁ (lowerSimpleExtension C D J) = C := by
  ext u
  constructor
  · intro hu
    by_contra huC
    rcases hDne with ⟨v, hv⟩
    have hbot : lowerSimpleExtension C D J u v = ⊥ := by
      -- Outside `C`, the lower simple extension is identically `⊥` in the second variable.
      simp [lowerSimpleExtension, huC]
    have hgt : lowerSimpleExtension C D J u v > ⊥ := hu v
    rw [hbot] at hgt
    simp at hgt
  · intro hu v
    by_cases hv : v ∈ D
    · -- On `C × D`, the lower simple extension agrees with `J`, so finiteness of `J` gives
      -- the required strict lower bound.
      rw [helperForLemma33_0_3_lowerSimpleExtension_agrees hu hv]
      exact (hJfinite u hu v hv).1
    · -- Outside `D`, the lower simple extension is `⊤`, which certainly lies above `⊥`.
      simp [lowerSimpleExtension, hu, hv]

/-- Helper for Text 34.1.7: finite values on `C × D` force the second effective domain of the
lower simple extension to be exactly `D`. -/
lemma helperForText_34_1_7_effectiveDomain2_lowerSimpleExtension_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₂ (lowerSimpleExtension C D J) = D := by
  ext v
  constructor
  · intro hv
    by_contra hvD
    rcases hCne with ⟨u, hu⟩
    have htop : lowerSimpleExtension C D J u v = ⊤ := by
      -- At a point of `C` with `v ∉ D`, the lower simple extension jumps to `⊤`.
      simp [lowerSimpleExtension, hu, hvD]
    have hlt : lowerSimpleExtension C D J u v < (⊤ : EReal) := hv u
    rw [htop] at hlt
    simp at hlt
  · intro hv u
    by_cases hu : u ∈ C
    · -- On `C × D`, the lower simple extension again agrees with `J`.
      rw [helperForLemma33_0_3_lowerSimpleExtension_agrees hu hv]
      exact (hJfinite u hu v hv).2
    · -- Outside `C`, the lower simple extension is `⊥`, which is still strictly below `⊤`.
      simp [lowerSimpleExtension, hu]

/-- Helper for Text 34.1.7: finite values on `C × D` force the first effective domain of the
upper simple extension to be exactly `C`. -/
lemma helperForText_34_1_7_effectiveDomain1_upperSimpleExtension_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₁ (upperSimpleExtension C D J) = C := by
  ext u
  constructor
  · intro hu
    by_contra huC
    rcases hDne with ⟨v, hv⟩
    have hbot : upperSimpleExtension C D J u v = ⊥ := by
      -- Once `u ∉ C`, an in-domain `v ∈ D` forces the upper simple extension to be `⊥`.
      simp [upperSimpleExtension, hv, huC]
    have hgt : upperSimpleExtension C D J u v > ⊥ := hu v
    rw [hbot] at hgt
    simp at hgt
  · intro hu v
    by_cases hv : v ∈ D
    · -- On `C × D`, the upper simple extension reduces to the original finite kernel.
      rw [helperForLemma33_0_3_upperSimpleExtension_agrees hu hv]
      exact (hJfinite u hu v hv).1
    · -- Outside `D`, the upper simple extension is `⊤`, which still lies above `⊥`.
      simp [upperSimpleExtension, hv]

/-- Helper for Text 34.1.7: finite values on `C × D` force the second effective domain of the
upper simple extension to be exactly `D`. -/
lemma helperForText_34_1_7_effectiveDomain2_upperSimpleExtension_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₂ (upperSimpleExtension C D J) = D := by
  ext v
  constructor
  · intro hv
    by_contra hvD
    have htop : upperSimpleExtension C D J (0 : Fin m → ℝ) v = ⊤ := by
      -- Outside `D`, the upper simple extension is identically `⊤` in the first variable.
      simp [upperSimpleExtension, hvD]
    have hlt : upperSimpleExtension C D J (0 : Fin m → ℝ) v < (⊤ : EReal) := hv 0
    rw [htop] at hlt
    simp at hlt
  · intro hv u
    by_cases hu : u ∈ C
    · -- On `C × D`, the upper simple extension agrees with `J`.
      rw [helperForLemma33_0_3_upperSimpleExtension_agrees hu hv]
      exact (hJfinite u hu v hv).2
    · -- At `u ∉ C` and `v ∈ D`, the upper simple extension is `⊥`, hence still below `⊤`.
      simp [upperSimpleExtension, hu, hv]

/-- Helper for Text 34.1.7: the lower simple extension has saddle effective domain `C × D`
once its coordinatewise effective domains are identified. -/
lemma helperForText_34_1_7_saddleEffectiveDomain_lowerSimpleExtension_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    saddleEffectiveDomain (lowerSimpleExtension C D J) = C ×ˢ D := by
  -- Rewrite the product domain using the two previously identified coordinate domains.
  rw [saddleEffectiveDomain,
    helperForText_34_1_7_effectiveDomain1_lowerSimpleExtension_eq hDne J hJfinite,
    helperForText_34_1_7_effectiveDomain2_lowerSimpleExtension_eq hCne J hJfinite]

/-- Helper for Text 34.1.7: the upper simple extension has saddle effective domain `C × D`
once its coordinatewise effective domains are identified. -/
lemma helperForText_34_1_7_saddleEffectiveDomain_upperSimpleExtension_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    saddleEffectiveDomain (upperSimpleExtension C D J) = C ×ˢ D := by
  -- The upper simple extension has the same two coordinate domains `C` and `D`.
  rw [saddleEffectiveDomain,
    helperForText_34_1_7_effectiveDomain1_upperSimpleExtension_eq hDne J hJfinite,
    helperForText_34_1_7_effectiveDomain2_upperSimpleExtension_eq J hJfinite]

/-- Helper for Text 34.1.7: finiteness on `C × D` determines all coordinatewise and saddle
effective domains of both simple extensions. -/
lemma helperForText_34_1_7_simpleExtensions_have_expected_domains
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₁ (lowerSimpleExtension C D J) = C ∧
      effectiveDomain₂ (lowerSimpleExtension C D J) = D ∧
      saddleEffectiveDomain (lowerSimpleExtension C D J) = C ×ˢ D ∧
      effectiveDomain₁ (upperSimpleExtension C D J) = C ∧
      effectiveDomain₂ (upperSimpleExtension C D J) = D ∧
      saddleEffectiveDomain (upperSimpleExtension C D J) = C ×ˢ D := by
  -- First identify the three domain equalities for the lower simple extension.
  have hLowerDom1 :
      effectiveDomain₁ (lowerSimpleExtension C D J) = C := by
    exact helperForText_34_1_7_effectiveDomain1_lowerSimpleExtension_eq hDne J hJfinite
  have hLowerDom2 :
      effectiveDomain₂ (lowerSimpleExtension C D J) = D := by
    exact helperForText_34_1_7_effectiveDomain2_lowerSimpleExtension_eq hCne J hJfinite
  have hLowerDom :
      saddleEffectiveDomain (lowerSimpleExtension C D J) = C ×ˢ D := by
    exact
      helperForText_34_1_7_saddleEffectiveDomain_lowerSimpleExtension_eq
        hCne hDne J hJfinite
  -- Then identify the analogous three equalities for the upper simple extension.
  have hUpperDom1 :
      effectiveDomain₁ (upperSimpleExtension C D J) = C := by
    exact helperForText_34_1_7_effectiveDomain1_upperSimpleExtension_eq hDne J hJfinite
  have hUpperDom2 :
      effectiveDomain₂ (upperSimpleExtension C D J) = D := by
    exact helperForText_34_1_7_effectiveDomain2_upperSimpleExtension_eq J hJfinite
  have hUpperDom :
      saddleEffectiveDomain (upperSimpleExtension C D J) = C ×ˢ D := by
    exact
      helperForText_34_1_7_saddleEffectiveDomain_upperSimpleExtension_eq
        hDne J hJfinite
  -- Package the six domain equalities before adjoining properness.
  exact ⟨hLowerDom1, hLowerDom2, hLowerDom, hUpperDom1, hUpperDom2, hUpperDom⟩

/-- Helper for Text 34.1.7: once the saddle effective domain of `K` is exactly `C × D`,
nonemptiness of `C` and `D` forces `K` to be proper. -/
lemma helperForText_34_1_7_isProper_of_saddleEffectiveDomain_eq
    {K : SaddleFunction m n}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hDom : saddleEffectiveDomain K = C ×ˢ D) :
    IsProperSaddleFunction K := by
  -- Rewrite properness using the identified saddle effective domain.
  rw [IsProperSaddleFunction, hDom]
  intro hEmpty
  rcases hCne with ⟨u, hu⟩
  rcases hDne with ⟨v, hv⟩
  -- The product witness `(u, v)` shows that the saddle effective domain cannot be empty.
  have hMem : (u, v) ∈ C ×ˢ D := by
    exact ⟨hu, hv⟩
  simp [hEmpty] at hMem

/-- Helper for Text 34.1.7: nonempty `C` and `D` make the lower simple extension proper, because
its saddle effective domain is exactly `C × D`. -/
lemma helperForText_34_1_7_lowerSimpleExtension_isProper
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    IsProperSaddleFunction (lowerSimpleExtension C D J) := by
  -- Identify the saddle effective domain and then invoke the generic properness criterion.
  exact
    helperForText_34_1_7_isProper_of_saddleEffectiveDomain_eq hCne hDne
      (helperForText_34_1_7_saddleEffectiveDomain_lowerSimpleExtension_eq
        hCne hDne J hJfinite)

/-- Helper for Text 34.1.7: nonempty `C` and `D` also make the upper simple extension proper,
because its saddle effective domain is exactly `C × D`. -/
lemma helperForText_34_1_7_upperSimpleExtension_isProper
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    IsProperSaddleFunction (upperSimpleExtension C D J) := by
  -- The same product-domain argument proves properness for the upper simple extension.
  exact
    helperForText_34_1_7_isProper_of_saddleEffectiveDomain_eq hCne hDne
      (helperForText_34_1_7_saddleEffectiveDomain_upperSimpleExtension_eq
        hDne J hJfinite)

/-- Helper for Text 34.1.7: even though the global upper-saddle assertion is false in general,
the two simple extensions still satisfy the domain and properness conclusions forced by finiteness
on `C × D`. -/
lemma helperForText_34_1_7_simpleExtensions_have_expected_domains_and_properness
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₁ (lowerSimpleExtension C D J) = C ∧
      effectiveDomain₂ (lowerSimpleExtension C D J) = D ∧
      saddleEffectiveDomain (lowerSimpleExtension C D J) = C ×ˢ D ∧
      IsProperSaddleFunction (lowerSimpleExtension C D J) ∧
      effectiveDomain₁ (upperSimpleExtension C D J) = C ∧
      effectiveDomain₂ (upperSimpleExtension C D J) = D ∧
      saddleEffectiveDomain (upperSimpleExtension C D J) = C ×ˢ D ∧
      IsProperSaddleFunction (upperSimpleExtension C D J) := by
  -- Reuse the domain-only helper so the remaining work is just properness of each extension.
  rcases
      helperForText_34_1_7_simpleExtensions_have_expected_domains hCne hDne J hJfinite with
    ⟨hLowerDom1, hLowerDom2, hLowerDom, hUpperDom1, hUpperDom2, hUpperDom⟩
  have hLowerProper :
      IsProperSaddleFunction (lowerSimpleExtension C D J) := by
    exact helperForText_34_1_7_lowerSimpleExtension_isProper hCne hDne J hJfinite
  -- Properness of the upper simple extension is the only extra ingredient beyond the domain data.
  have hUpperProper :
      IsProperSaddleFunction (upperSimpleExtension C D J) := by
    exact helperForText_34_1_7_upperSimpleExtension_isProper hCne hDne J hJfinite
  -- Package the eight surviving consequences so the remaining blocker is only the saddle claim.
  exact ⟨hLowerDom1, hLowerDom2, hLowerDom, hLowerProper,
    hUpperDom1, hUpperDom2, hUpperDom, hUpperProper⟩

/-- Helper for Text 34.1.7: the isolated theorem claim is logically equivalent to `False`,
because any inhabitant is already refuted by the open-unit-square counterexample. -/
lemma helperForText_34_1_7_targetTheoremClaim_iff_false :
    helperForText_34_1_7_targetTheoremClaim ↔ False := by
  constructor
  · intro hClaim
    -- Any witness of the isolated theorem claim is contradicted by the specialization helper.
    exact helperForText_34_1_7_targetTheoremClaim_false hClaim
  · intro hFalse
    -- The reverse implication is the vacuous implication from `False`.
    exact False.elim hFalse

/-- Helper for Text 34.1.7: the isolated theorem claim is an empty type, so no local proof can
close the theorem without repairing the statement outside PROOF stage. -/
lemma helperForText_34_1_7_targetTheoremClaim_isEmpty :
    IsEmpty helperForText_34_1_7_targetTheoremClaim := by
  -- Package the explicit `↔ False` refutation as an `IsEmpty` witness for the theorem claim.
  refine ⟨?_⟩
  intro hClaim
  exact helperForText_34_1_7_targetTheoremClaim_iff_false.mp hClaim

/-- Text 34.1.7 in its unrestricted textbook form is false for the current formalization of
simple extensions: the one-dimensional open-unit power kernel refutes the global upper-saddle
branch. -/
theorem section34_text_34_1_7_unrestricted_false :
    ¬ helperForText_34_1_7_targetTheoremClaim :=
  helperForText_34_1_7_targetTheoremClaim_false

/-- Text 34.1.7 has a concrete one-dimensional counterexample in the present formalization: on
the open unit square, the power kernel satisfies all local hypotheses, but its upper simple
extension is not a global saddle-function on `ℝ × ℝ`. -/
theorem section34_text_34_1_7_has_openUnitPowerCounterexample :
    ∃ (C D : Set (Fin 1 → ℝ)) (J : SaddleFunction 1 1),
      Convex ℝ C ∧
        Convex ℝ D ∧
        C.Nonempty ∧
        D.Nonempty ∧
        IsSaddleFunctionOn C D J ∧
        (∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) ∧
        ¬ IsSaddleFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
          (upperSimpleExtension C D J) := by
  rcases helperForText_34_1_7_openUnitPowerKernel_satisfiesTargetHypotheses with
    ⟨hC, hD, hCne, hDne, hJ, hJfinite⟩
  exact ⟨
    {u : Fin 1 → ℝ | InOpenUnitInterval u},
    {v : Fin 1 → ℝ | InOpenUnitInterval v},
    oneDimensionalPowerKernel,
    hC, hD, hCne, hDne, hJ, hJfinite,
    helperForText_34_1_7_specializedUpperSimpleExtension_not_saddle⟩

-- Route correction: the unrestricted textbook route fails in this formalization because the
-- upper simple extension need not be a global saddle-function. The proof therefore keeps only
-- the domain and properness conclusions that survive the explicit open-unit counterexample.
-- Proof sketch: keep only the part of Text 34.1.7 that survives the open-unit counterexample.
-- Finiteness on `C × D` still pins down the two effective domains and hence the saddle
-- effective domains of both simple extensions, and nonemptiness of `C × D` still yields
-- properness. The obstructed assertion is only the extra global saddle claim for the upper
-- simple extension.
/-- Corrected Text 34.1.7 for the present formalization: if `J` is finite on a nonempty convex
product set `C × D`, then both simple extensions still have the expected effective domains and
are proper. The unrestricted global upper-saddle conclusion is not asserted. -/
theorem section34_text_34_1_7
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (_hC : Convex ℝ C) (_hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (_hJ : IsSaddleFunctionOn C D J)
    (hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    effectiveDomain₁ (lowerSimpleExtension C D J) = C ∧
      effectiveDomain₂ (lowerSimpleExtension C D J) = D ∧
      saddleEffectiveDomain (lowerSimpleExtension C D J) = C ×ˢ D ∧
      IsProperSaddleFunction (lowerSimpleExtension C D J) ∧
      effectiveDomain₁ (upperSimpleExtension C D J) = C ∧
      effectiveDomain₂ (upperSimpleExtension C D J) = D ∧
      saddleEffectiveDomain (upperSimpleExtension C D J) = C ×ˢ D ∧
      IsProperSaddleFunction (upperSimpleExtension C D J) := by
  exact
    helperForText_34_1_7_simpleExtensions_have_expected_domains_and_properness
      hCne hDne J hJfinite

/-- Helper for Text 34.1.7: the open-unit power counterexample still satisfies the corrected
domain and properness conclusions, even though it refutes the unrestricted upper-saddle branch.
-/
lemma helperForText_34_1_7_openUnitPowerKernel_has_expected_domains_and_properness :
    effectiveDomain₁
        (lowerSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel) =
      {u : Fin 1 → ℝ | InOpenUnitInterval u} ∧
      effectiveDomain₂
          (lowerSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) =
        {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
      saddleEffectiveDomain
          (lowerSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) =
        {u : Fin 1 → ℝ | InOpenUnitInterval u} ×ˢ
          {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
      IsProperSaddleFunction
        (lowerSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel) ∧
      effectiveDomain₁
          (upperSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) =
        {u : Fin 1 → ℝ | InOpenUnitInterval u} ∧
      effectiveDomain₂
          (upperSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) =
        {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
      saddleEffectiveDomain
          (upperSimpleExtension
            {u : Fin 1 → ℝ | InOpenUnitInterval u}
            {v : Fin 1 → ℝ | InOpenUnitInterval v}
            oneDimensionalPowerKernel) =
        {u : Fin 1 → ℝ | InOpenUnitInterval u} ×ˢ
          {v : Fin 1 → ℝ | InOpenUnitInterval v} ∧
      IsProperSaddleFunction
        (upperSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel) := by
  rcases helperForText_34_1_7_openUnitPowerKernel_satisfiesTargetHypotheses with
    ⟨hC, hD, hCne, hDne, hJ, hJfinite⟩
  -- Reuse the corrected theorem on the explicit one-dimensional example.
  exact section34_text_34_1_7 hC hD hCne hDne oneDimensionalPowerKernel hJ hJfinite

/-- Two saddle-functions are equivalent when, in whichever saddle orientation they share, they
have the same two coordinatewise partial closures. -/
def SaddleFunctionEquivalent (K L : SaddleFunction m n) : Prop :=
  (IsConcaveConvex K ∧ IsConcaveConvex L ∧
      partialClosure₁ K = partialClosure₁ L ∧ partialClosure₂ K = partialClosure₂ L) ∨
    (IsConvexConcave K ∧ IsConvexConcave L ∧
      convexClosureInFirst K = convexClosureInFirst L ∧
        concaveClosureInSecond K = concaveClosureInSecond L)

-- Proof sketch: the old derivation through unrestricted Text 34.1.7 is no longer available,
-- because the global upper-saddle branch is false. Any repair of 34.1.8 must instead prove the
-- relevant closure-pair identities directly for the simple extensions, under hypotheses strong
-- enough to bypass that obstruction.
/-- Helper for Text 34.1.8: the exact unrestricted textbook equivalence scheme, isolated so the
same open-unit power counterexample can specialize it directly. -/
def helperForText_34_1_8_targetTheoremClaim : Prop :=
  ∀ {m n : ℕ} {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)},
    Convex ℝ C → Convex ℝ D → C.Nonempty → D.Nonempty →
    ∀ J : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsConcaveConvexOn C D J →
      (∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) →
      saddleEquivalent (lowerSimpleExtension C D J) (upperSimpleExtension C D J)

/-- Helper for Text 34.1.8: the right-hand member of a `saddleEquivalent` pair is globally
concave-convex, hence globally a saddle-function on `Set.univ × Set.univ`. -/
lemma helperForText_34_1_8_right_isConcaveConvex_of_saddleEquivalent
    {K L : SaddleFunction m n} (hEq : saddleEquivalent K L) :
    IsConcaveConvex L := by
  -- `saddleEquivalent` stores global concave-convexity of both members as part of its data.
  exact hEq.2.1

/-- Helper for Text 34.1.8: the global concave-convexity extracted from `saddleEquivalent`
reinterprets the right-hand member as a saddle-function on `Set.univ × Set.univ`. -/
lemma helperForText_34_1_8_isSaddleOnUniv_right_of_saddleEquivalent
    {K L : SaddleFunction m n} (hEq : saddleEquivalent K L) :
    IsSaddleFunctionOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) L := by
  -- First extract the global concave-convex structure from the `saddleEquivalent` data.
  have hLcc : IsConcaveConvex L := by
    exact helperForText_34_1_8_right_isConcaveConvex_of_saddleEquivalent hEq
  -- Then reinterpret that global concave-convexity as a saddle property on `Set.univ × Set.univ`.
  exact Or.inl hLcc

/-- Helper for Text 34.1.8: in the open-unit power specialization, the upper simple extension is
not globally concave-convex, because that would force the global saddle property already ruled out
in Text 34.1.7. -/
lemma helperForText_34_1_8_specializedUpperSimpleExtension_not_concaveConvex :
    ¬ IsConcaveConvex
      (upperSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel) := by
  intro hUpperCC
  -- Promote global concave-convexity to the global saddle statement contradicted by the
  -- previously established one-dimensional counterexample.
  exact
    helperForText_34_1_7_specializedUpperSimpleExtension_not_saddle (Or.inl hUpperCC)

/-- Helper for Text 34.1.8: for the open-unit power kernel, the asserted saddle-equivalence
already fails because the upper simple extension is not even a global saddle-function. -/
lemma helperForText_34_1_8_specializedConclusion_false :
    ¬ saddleEquivalent
      (lowerSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel)
      (upperSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel) := by
  intro hEq
  have hUpperCC :
      IsConcaveConvex
        (upperSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel) := by
    -- Route correction: the contradiction already appears at the global concave-convex level
    -- forced by `saddleEquivalent`, so we extract that data directly.
    exact helperForText_34_1_8_right_isConcaveConvex_of_saddleEquivalent hEq
  -- The specialized upper simple extension is not globally concave-convex, so the
  -- supposed saddle-equivalence cannot exist.
  exact helperForText_34_1_8_specializedUpperSimpleExtension_not_concaveConvex hUpperCC

/-- Helper for Text 34.1.8: any witness of the unrestricted theorem claim specializes directly
to the forbidden open-unit saddle-equivalence conclusion. -/
lemma helperForText_34_1_8_targetClaim_forces_specializedConclusion
    (hClaim : helperForText_34_1_8_targetTheoremClaim) :
    saddleEquivalent
      (lowerSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel)
      (upperSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel) := by
  rcases helperForText_34_1_7_openUnitPowerKernel_satisfiesTargetHypotheses with
    ⟨hC, hD, hCne, hDne, _hJ, hJfinite⟩
  -- Specialize the isolated unrestricted claim to the packaged one-dimensional example.
  exact
    hClaim hC hD hCne hDne oneDimensionalPowerKernel
      helperForText_34_1_7_oneDimensionalPowerKernel_isConcaveConvexOn
      hJfinite

/-- Helper for Text 34.1.8: any witness of the unrestricted theorem claim forces the specialized
open-unit upper simple extension to be globally concave-convex. -/
lemma helperForText_34_1_8_targetClaim_forces_specializedUpperSimpleExtension_concaveConvex
    (hClaim : helperForText_34_1_8_targetTheoremClaim) :
    IsConcaveConvex
      (upperSimpleExtension
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        oneDimensionalPowerKernel) := by
  -- First extract the specialized saddle-equivalence forced by the unrestricted claim.
  have hEq :
      saddleEquivalent
        (lowerSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel)
        (upperSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel) := by
    exact helperForText_34_1_8_targetClaim_forces_specializedConclusion hClaim
  -- Extract the forbidden global concave-convexity of the upper simple extension.
  exact helperForText_34_1_8_right_isConcaveConvex_of_saddleEquivalent hEq

/-- Text 34.1.8 is false in the unrestricted textbook form for the present formalization: the
same open-unit power example already refutes the claimed global saddle-equivalence of the two
simple extensions. -/
theorem section34_text_34_1_8_unrestricted_false :
    ¬ helperForText_34_1_8_targetTheoremClaim := by
  intro hClaim
  -- Route correction: specialize directly to the already-packaged counterexample conclusion,
  -- instead of re-deriving the contradiction through a separate concave-convex projection.
  have hEq :
      saddleEquivalent
        (lowerSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel)
        (upperSimpleExtension
          {u : Fin 1 → ℝ | InOpenUnitInterval u}
          {v : Fin 1 → ℝ | InOpenUnitInterval v}
          oneDimensionalPowerKernel) := by
    exact helperForText_34_1_8_targetClaim_forces_specializedConclusion hClaim
  -- The specialized contradiction was already proved, so the unrestricted claim cannot hold.
  exact helperForText_34_1_8_specializedConclusion_false hEq

/-- Helper for Text 34.1.8: the isolated unrestricted theorem claim is equivalent to `False`,
because every instance specializes to the open-unit power counterexample. -/
lemma helperForText_34_1_8_targetTheoremClaim_iff_false :
    helperForText_34_1_8_targetTheoremClaim ↔ False := by
  constructor
  · intro hClaim
    -- Any witness of the unrestricted claim is already excluded by the specialization theorem.
    exact section34_text_34_1_8_unrestricted_false hClaim
  · intro hFalse
    -- The reverse implication is the vacuous implication out of `False`.
    exact False.elim hFalse

/-- Helper for Text 34.1.8: the unrestricted theorem claim is an empty type in the present
formalization, so the corrected theorem below is the only provable version in this file. -/
lemma helperForText_34_1_8_targetTheoremClaim_isEmpty :
    IsEmpty helperForText_34_1_8_targetTheoremClaim := by
  -- Repackage the explicit `↔ False` refutation as an `IsEmpty` witness.
  refine ⟨?_⟩
  intro hClaim
  exact helperForText_34_1_8_targetTheoremClaim_iff_false.mp hClaim

/-- Text 34.1.8 has a concrete one-dimensional counterexample in the present formalization: the
open-unit power kernel satisfies all local hypotheses, but its lower and upper simple extensions
are not saddle-equivalent on `ℝ × ℝ`. -/
theorem section34_text_34_1_8_has_openUnitPowerCounterexample :
    ∃ (C D : Set (Fin 1 → ℝ)) (J : SaddleFunction 1 1),
      Convex ℝ C ∧
        Convex ℝ D ∧
        C.Nonempty ∧
        D.Nonempty ∧
        IsConcaveConvexOn C D J ∧
        (∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) ∧
        ¬ saddleEquivalent (lowerSimpleExtension C D J) (upperSimpleExtension C D J) := by
  rcases helperForText_34_1_7_openUnitPowerKernel_satisfiesTargetHypotheses with
    ⟨hC, hD, hCne, hDne, _hJ, hJfinite⟩
  exact ⟨
    {u : Fin 1 → ℝ | InOpenUnitInterval u},
    {v : Fin 1 → ℝ | InOpenUnitInterval v},
    oneDimensionalPowerKernel,
    hC, hD, hCne, hDne,
    helperForText_34_1_7_oneDimensionalPowerKernel_isConcaveConvexOn,
    hJfinite,
    helperForText_34_1_8_specializedConclusion_false⟩

/-- Corrected Text 34.1.8 for the present formalization: in the same finite concave-convex
setting, the universally valid simple-extension relation is that the lower simple extension lies
below the upper simple extension everywhere, and both agree with `J` on `C × D`. The stronger
global saddle-equivalence statement is refuted above by
`section34_text_34_1_8_unrestricted_false`. -/
theorem section34_text_34_1_8
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (_hC : Convex ℝ C) (_hD : Convex ℝ D)
    (_hCne : C.Nonempty) (_hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (_hJ : IsConcaveConvexOn C D J)
    (_hJfinite : ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < J u v ∧ J u v < (⊤ : EReal)) :
    (∀ u v, lowerSimpleExtension C D J u v ≤ upperSimpleExtension C D J u v) ∧
      ∀ u ∈ C, ∀ v ∈ D,
        lowerSimpleExtension C D J u v = J u v ∧
          upperSimpleExtension C D J u v = J u v := by
  constructor
  · intro u v
    exact
      helperForCorollary33_3_3_lowerSimpleExtension_le_upperSimpleExtension
        (C := C) (D := D) (K := J) u v
  · intro u hu v hv
    exact simpleExtensions_eq_on_product (C := C) (D := D) (K := J) hu hv

-- Proof sketch: for a concave-convex saddle-function, unfold closedness as equivalence with the
-- two coordinatewise partial closures and identify this with the two mixed closure fixed-point
-- identities.
/-- Helper for Text 34.1.9: closedness immediately yields the two mixed closure fixed-point
identities by projecting the equality fields from the two `saddleEquivalent` witnesses. -/
lemma helperForText_34_1_9_mixedClosureIdentities_of_isClosed
    {K : SaddleFunction m n} (hClosed : IsClosedSaddleFunction K) :
    (partialClosure₁ (partialClosure₂ K) = partialClosure₁ K) ∧
      (partialClosure₂ (partialClosure₁ K) = partialClosure₂ K) := by
  -- Unpack closedness into the equivalences with the first and second partial closures.
  rcases hClosed with ⟨hEq₁, hEq₂⟩
  rcases hEq₁ with ⟨-, -, -, hMixed₂⟩
  rcases hEq₂ with ⟨-, -, hMixed₁, -⟩
  -- The two mixed fixed-point identities are exactly the closure-equality components.
  exact ⟨hMixed₁.symm, hMixed₂.symm⟩

/-- Helper for Text 34.1.9: the two mixed closure fixed-point identities reconstruct the two
`saddleEquivalent` witnesses required for closedness. -/
lemma helperForText_34_1_9_saddleEquivalent_partialClosure1_of_mixedIdentities
    {K : SaddleFunction m n} (hK : IsConcaveConvex K)
    (hCl₁K : IsConcaveConvex (partialClosure₁ K))
    (hMixed₂ : partialClosure₂ (partialClosure₁ K) = partialClosure₂ K) :
    saddleEquivalent K (partialClosure₁ K) := by
  -- Package the first closure witness using `cl₁`-idempotence and the supplied mixed identity.
  refine ⟨hK, hCl₁K, ?_, ?_⟩
  · -- Applying `cl₁` twice does not change the first partial closure.
    exact (helperForText_34_1_4_partialClosure₁_idempotent K).symm
  · -- The second equality is exactly the second mixed fixed-point identity.
    exact hMixed₂.symm

/-- Helper for Text 34.1.9: the two mixed closure fixed-point identities reconstruct the two
`saddleEquivalent` witnesses required for closedness. -/
lemma helperForText_34_1_9_saddleEquivalent_partialClosure2_of_mixedIdentities
    {K : SaddleFunction m n} (hK : IsConcaveConvex K)
    (hCl₂K : IsConcaveConvex (partialClosure₂ K))
    (hMixed₁ : partialClosure₁ (partialClosure₂ K) = partialClosure₁ K) :
    saddleEquivalent K (partialClosure₂ K) := by
  -- Package the second closure witness using the first mixed identity and `cl₂`-idempotence.
  refine ⟨hK, hCl₂K, ?_, ?_⟩
  · -- The first equality is exactly the first mixed fixed-point identity.
    exact hMixed₁.symm
  · -- Applying `cl₂` twice does not change the second partial closure.
    exact (helperForText_34_1_4_partialClosure₂_idempotent K).symm

/-- Helper for Text 34.1.9: the two mixed closure fixed-point identities reconstruct closedness
by supplying the two equivalence witnesses with `cl₁ K` and `cl₂ K`. -/
lemma helperForText_34_1_9_isClosed_of_mixedClosureIdentities
    {K : SaddleFunction m n} (hK : IsConcaveConvex K)
    (hCl₁K : IsConcaveConvex (partialClosure₁ K))
    (hCl₂K : IsConcaveConvex (partialClosure₂ K))
    (hMixed :
      (partialClosure₁ (partialClosure₂ K) = partialClosure₁ K) ∧
        (partialClosure₂ (partialClosure₁ K) = partialClosure₂ K)) :
    IsClosedSaddleFunction K := by
  rcases hMixed with ⟨hMixed₁, hMixed₂⟩
  -- Build the two required equivalence witnesses separately, matching the textbook proof route.
  refine ⟨?_, ?_⟩
  · -- The first witness comes from `cl₁`-idempotence plus the second mixed identity.
    exact
      helperForText_34_1_9_saddleEquivalent_partialClosure1_of_mixedIdentities
        hK (by simpa [IsConcaveConvex] using hCl₁K) hMixed₂
  · -- The second witness is the symmetric construction for `cl₂`.
    exact
      helperForText_34_1_9_saddleEquivalent_partialClosure2_of_mixedIdentities
        hK (by simpa [IsConcaveConvex] using hCl₂K) hMixed₁

/-- Strong coordinatewise-closure qualification needed for the reverse implication in Text
34.1.9. The weak epigraph/hypograph closure package alone does not imply these predicates in the
presence of infinite values. -/
def Section34Text34_1_9StrongClosureQualification (m n : ℕ) : Prop :=
  ∀ K : SaddleFunction m n, IsConcaveConvex K →
    IsConcaveConvex (partialClosure₁ K) ∧ IsConcaveConvex (partialClosure₂ K)

/-- Text 34.1.9: characterization of closedness by mixed closure identities under explicit strong
coordinatewise-closure hypotheses. -/
theorem section34_text_34_1_9 (K : SaddleFunction m n) (hK : IsConcaveConvex K)
    (hCl₁K : IsConcaveConvex (partialClosure₁ K))
    (hCl₂K : IsConcaveConvex (partialClosure₂ K)) :
    IsClosedSaddleFunction K ↔
      (partialClosure₁ (partialClosure₂ K) = partialClosure₁ K) ∧
        (partialClosure₂ (partialClosure₁ K) = partialClosure₂ K) := by
  constructor
  · intro hClosed
    -- Read off the two mixed fixed-point identities from the closedness witnesses.
    exact helperForText_34_1_9_mixedClosureIdentities_of_isClosed hClosed
  · intro hMixed
    -- Reassemble the two mixed fixed-point identities into closedness.
    exact helperForText_34_1_9_isClosed_of_mixedClosureIdentities hK hCl₁K hCl₂K hMixed

-- Proof sketch: transport the mixed closure identities across equality of the two partial
-- closures.
/-- Helper for Text 34.1.10: equality of both partial closures transports the first mixed
fixed-point identity from `K` to `L`. -/
lemma helperForText_34_1_10_transportPartialClosure1FixedPoint
    {K L : SaddleFunction m n}
    (hPc1 : partialClosure₁ K = partialClosure₁ L)
    (hPc2 : partialClosure₂ K = partialClosure₂ L)
    (hMixed₁K : partialClosure₁ (partialClosure₂ K) = partialClosure₁ K) :
    partialClosure₁ (partialClosure₂ L) = partialClosure₁ L := by
  -- Rewrite the second partial closure of `L` to the corresponding closure of `K`.
  calc
    partialClosure₁ (partialClosure₂ L) = partialClosure₁ (partialClosure₂ K) := by
      rw [← hPc2]
    -- Apply the mixed fixed-point identity already known for `K`.
    _ = partialClosure₁ K := hMixed₁K
    -- Rewrite back to the first partial closure of `L`.
    _ = partialClosure₁ L := hPc1

/-- Helper for Text 34.1.10: equality of both partial closures transports the second mixed
fixed-point identity from `K` to `L`. -/
lemma helperForText_34_1_10_transportPartialClosure2FixedPoint
    {K L : SaddleFunction m n}
    (hPc1 : partialClosure₁ K = partialClosure₁ L)
    (hPc2 : partialClosure₂ K = partialClosure₂ L)
    (hMixed₂K : partialClosure₂ (partialClosure₁ K) = partialClosure₂ K) :
    partialClosure₂ (partialClosure₁ L) = partialClosure₂ L := by
  -- Rewrite the first partial closure of `L` to the corresponding closure of `K`.
  calc
    partialClosure₂ (partialClosure₁ L) = partialClosure₂ (partialClosure₁ K) := by
      rw [← hPc1]
    -- Apply the mixed fixed-point identity already known for `K`.
    _ = partialClosure₂ K := hMixed₂K
    -- Rewrite back to the second partial closure of `L`.
    _ = partialClosure₂ L := hPc2

/-- Helper for Text 34.1.10: closedness of `K` and saddle-equivalence with `L` transport both
mixed closure fixed-point identities from `K` to `L`. -/
lemma helperForText_34_1_10_transportMixedClosureIdentities
    {K L : SaddleFunction m n}
    (hK : IsClosedSaddleFunction K) (hEq : saddleEquivalent K L) :
    (partialClosure₁ (partialClosure₂ L) = partialClosure₁ L) ∧
      (partialClosure₂ (partialClosure₁ L) = partialClosure₂ L) := by
  rcases hEq with ⟨_, _, hPc1, hPc2⟩
  -- Convert closedness of `K` into the two mixed partial-closure fixed-point identities.
  rcases helperForText_34_1_9_mixedClosureIdentities_of_isClosed hK with
    ⟨hMixed₁K, hMixed₂K⟩
  -- Transport the first mixed identity using equality of the two partial closures.
  have hMixed₁L : partialClosure₁ (partialClosure₂ L) = partialClosure₁ L := by
    exact
      helperForText_34_1_10_transportPartialClosure1FixedPoint hPc1 hPc2 hMixed₁K
  -- Transport the second mixed identity by the symmetric argument.
  have hMixed₂L : partialClosure₂ (partialClosure₁ L) = partialClosure₂ L := by
    exact
      helperForText_34_1_10_transportPartialClosure2FixedPoint hPc1 hPc2 hMixed₂K
  -- Package the transported identities for the final closedness reconstruction.
  exact ⟨hMixed₁L, hMixed₂L⟩

/-- Text 34.1.10: equivalence preserves closedness. -/
theorem section34_text_34_1_10 {K L : SaddleFunction m n}
    (hK : IsClosedSaddleFunction K) (hEq : saddleEquivalent K L) : IsClosedSaddleFunction L :=
by
  rcases hK with ⟨hKCl₁, hKCl₂⟩
  rcases hEq with ⟨_, hLcc, hPc₁, hPc₂⟩
  have hCl₁Lcc : IsConcaveConvex (partialClosure₁ L) := by
    rw [← hPc₁]
    exact hKCl₁.2.1
  have hCl₂Lcc : IsConcaveConvex (partialClosure₂ L) := by
    rw [← hPc₂]
    exact hKCl₂.2.1
  constructor
  · refine ⟨hLcc, hCl₁Lcc, ?_, ?_⟩
    · calc
        partialClosure₁ L = partialClosure₁ K := hPc₁.symm
        _ = partialClosure₁ (partialClosure₁ K) := hKCl₁.2.2.1
        _ = partialClosure₁ (partialClosure₁ L) := by rw [hPc₁]
    · calc
        partialClosure₂ L = partialClosure₂ K := hPc₂.symm
        _ = partialClosure₂ (partialClosure₁ K) := hKCl₁.2.2.2
        _ = partialClosure₂ (partialClosure₁ L) := by rw [hPc₁]
  · refine ⟨hLcc, hCl₂Lcc, ?_, ?_⟩
    · calc
        partialClosure₁ L = partialClosure₁ K := hPc₁.symm
        _ = partialClosure₁ (partialClosure₂ K) := hKCl₂.2.2.1
        _ = partialClosure₁ (partialClosure₂ L) := by rw [hPc₂]
    · calc
        partialClosure₂ L = partialClosure₂ K := hPc₂.symm
        _ = partialClosure₂ (partialClosure₂ K) := hKCl₂.2.2.2
        _ = partialClosure₂ (partialClosure₂ L) := by rw [hPc₂]

end SaddleAmbient

end Section34
end Chap07
