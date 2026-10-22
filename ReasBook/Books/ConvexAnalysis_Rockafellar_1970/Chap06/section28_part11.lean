/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part10

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Proposition 6.28.2: the dual space is nonempty, so its universal set cannot be
empty. This is a small utility for discharging contradictions of the form `Set.univ = ∅`. -/
lemma helperForProposition_6_28_2_univ_ne_empty_dual
    {n : ℕ} :
    (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) ≠
      (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
  classical
  intro hunivEqEmpty
  -- The zero functional is always an element of the universal set.
  have hmemUniv :
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
        (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    trivial
  -- Transport that membership along `Set.univ = ∅` to get a contradiction.
  have hmemEmpty :
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
        (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    simpa [hunivEqEmpty] using hmemUniv
  simpa using hmemEmpty

/-- Proposition 6.28.2: For a convex real-valued constraint function `constraint` on `ℝ^n`, let
`C = {y | constraint y ≤ 0}` and assume `C` is nonempty. Then the subdifferential of the
indicator function `δ(· | C)` at `x` is the normal cone to `C` at `x`. Moreover, if
`constraint x = 0`, the boundary formula requires the additional strict-feasibility hypothesis
`∃ z, constraint z < 0`; if `constraint x < 0`, the subdifferential is the singleton `{0}`; and
if `constraint x > 0`, it is empty. This is the version compatible with the current Chapter 23
conventions used in this development. -/
theorem subdifferential_indicator_sublevelSet_eq_normalCone_and_constraint_cases
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint)
    (hne : ∃ y : Fin n → ℝ, constraint y ≤ 0)
    (x : Fin n → ℝ) :
    subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
        normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x ∧
      (constraint x = 0 → (∃ z : Fin n → ℝ, constraint z < 0) →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
          Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
            a.1 • subdifferentialAt
              (fun y : Fin n → ℝ => ((constraint y : ℝ) : EReal)) x) ∧
      (constraint x < 0 →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
          ({0} : Set (Module.Dual ℝ (Fin n → ℝ)))) ∧
      (0 < constraint x →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x = ∅) := by
  simpa using
    helperForProposition_6_28_2_repaired
      (constraint := constraint) (hconstraint := hconstraint) (hne := hne) (x := x)

/-- Helper for Proposition 6.28.2: if the sublevel set `C = {y | constraint y ≤ 0}` is empty, then
the main equality `∂ δ_C(x) = N_C(x)` cannot hold, since Definition 23.0.6 gives `∂ δ_∅(x) = Set.univ`
while `N_∅(x) = ∅` by definition of the normal cone. -/
lemma helperForProposition_6_28_2_main_equality_fails_of_sublevelSet_eq_empty
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hEmpty : ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)) = ∅) :
    subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x ≠
      normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x := by
  classical
  intro hEq
  -- Step 1: rewrite the subdifferential using the lemma for the empty indicator.
  have hSubUniv :
      subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
        (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    simpa [hEmpty] using
      (helperForProposition_6_28_2_subdifferentialAt_indicator_empty_eq_univ (n := n) (x := x))
  -- Step 2: rewrite the normal cone using the lemma for the empty set.
  have hNormalEmpty :
      normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x =
        (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    simpa [hEmpty] using (helperForProposition_6_28_2_normalConeAt_empty_eq_empty (n := n) (x := x))
  -- Step 3: combine the assumed equality with the two computations to get `Set.univ = ∅`,
  -- which is impossible.
  have hunivEqEmpty :
      (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) =
        (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) :=
    hSubUniv.symm.trans (hEq.trans hNormalEmpty)
  have : (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    have : (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
        (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
      trivial
    simpa [hunivEqEmpty] using this
  simpa using this

/-- Helper for Proposition 6.28.2: if the feasible set `C = {y | constraint y ≤ 0}` is empty, then
the proposition’s outside-case implication (`0 < constraint x → ∂ δ_C(x) = ∅`) cannot hold at any
point with `0 < constraint x`, because Definition 23.0.6 yields `∂ δ_∅(x) = Set.univ`. -/
lemma helperForProposition_6_28_2_outside_case_implication_fails_of_sublevelSet_eq_empty
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ}
    (hEmpty : ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)) = ∅) (hx : 0 < constraint x) :
    ¬ (0 < constraint x →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x = ∅) := by
  classical
  intro hOutside
  -- Use the outside-case implication at `x` (non-vacuous thanks to `hx`).
  have hSubEmpty :
      subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x = ∅ :=
    hOutside hx
  -- But when `C = ∅`, the indicator is identically `⊤` and its subdifferential is `Set.univ`.
  have hSubUniv :
      subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
        (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    simpa [hEmpty] using
      (helperForProposition_6_28_2_subdifferentialAt_indicator_empty_eq_univ (n := n) (x := x))
  have hunivEqEmpty :
      (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) =
        (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) :=
    hSubUniv.symm.trans hSubEmpty
  -- Witness `0` to contradict `Set.univ = ∅`.
  have : (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    have : (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
        (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
      trivial
    simpa [hunivEqEmpty] using this
  simpa using this

/-- Helper for Proposition 6.28.2: the boundary-case formula is false without a constraint
qualification.  In dimension `1`, for `constraint(y) = (y 0)^2` at `x = 0`, one has
`∂ δ_C(0) = Set.univ` (since `C = {0}`) but the conic hull `⋃_{t≥0} t • ∂ constraint(0)` is
contained in `{0}`. -/
lemma helperForProposition_6_28_2_counterexample_boundary_case :
    ∃ (constraint : (Fin 1 → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint) (x : Fin 1 → ℝ),
      constraint x = 0 ∧
        subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x ≠
          Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
            a.1 • subdifferentialAt (fun y : Fin 1 → ℝ => ((constraint y : ℝ) : EReal)) x := by
  classical
  -- Choose the quadratic constraint `constraint(y) = (y 0)^2` and the boundary point `x = 0`.
  refine ⟨(fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)), ?_, (0 : Fin 1 → ℝ), ?_⟩
  · -- Convexity: `x ↦ x^2` is convex on `Set.univ` for an even exponent, and convexity is preserved
    -- under precomposition by a linear map (here, the coordinate projection).
    have hpow : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ (2 : ℕ)) := by
      have hn : Even (2 : ℕ) := by
        decide
      simpa using (Even.convexOn_pow (𝕜 := ℝ) (n := (2 : ℕ)) hn)
    let π₀ : (Fin 1 → ℝ) →ₗ[ℝ] ℝ :=
      LinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℝ) (0 : Fin 1)
    -- The preimage of `Set.univ` under `π₀` is `Set.univ`, so we get convexity on all of `ℝ¹`.
    simpa [π₀] using hpow.comp_linearMap π₀
  · constructor
    · -- Boundary condition: `constraint 0 = 0`.
      simp
    · -- Show the two claimed sets differ by exhibiting a nonzero functional that lies in
      -- `∂ δ_C(0) = Set.univ` but cannot lie in the conic hull of `∂ constraint(0) = {0}`.
      intro hEq
      -- Step 1: compute the feasible set `C` and its normal cone; in this example `C = {0}`.
      have hSet :
          ({y : Fin 1 → ℝ | (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0} : Set (Fin 1 → ℝ)) =
            ({0} : Set (Fin 1 → ℝ)) := by
        simpa using helperForProposition_6_28_2_sublevelSet_evalSq_eq_singleton_zero
      have hne :
          ∃ y : Fin 1 → ℝ, (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0 := by
        refine ⟨(0 : Fin 1 → ℝ), ?_⟩
        simp
      have hSubEqNormal :
          subdifferentialAt
              (indicatorFunction {y : Fin 1 → ℝ | (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0})
              (0 : Fin 1 → ℝ) =
            normalConeAt
              ({y : Fin 1 → ℝ | (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0} : Set (Fin 1 → ℝ))
              (0 : Fin 1 → ℝ) :=
        helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_normalCone_of_exists_feasible
          (constraint := fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) hne (0 : Fin 1 → ℝ)
      have hNormalUniv :
          normalConeAt
              ({y : Fin 1 → ℝ | (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0} : Set (Fin 1 → ℝ))
              (0 : Fin 1 → ℝ) =
            (Set.univ : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
        -- Rewrite `C` as `{0}` and use the explicit normal-cone computation.
        rw [hSet]
        exact helperForProposition_6_28_2_normalConeAt_singleton_zero_eq_univ
      have hSubUniv :
          subdifferentialAt
              (indicatorFunction {y : Fin 1 → ℝ | (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0})
              (0 : Fin 1 → ℝ) =
            (Set.univ : Set (Module.Dual ℝ (Fin 1 → ℝ))) :=
        hSubEqNormal.trans hNormalUniv
      -- Step 2: compute `∂ constraint(0) = {0}`, so every dilate is still `{0}`.
      have hSubConstraint :
          subdifferentialAt
              (fun y : Fin 1 → ℝ =>
                (((fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y : ℝ) : EReal))
              (0 : Fin 1 → ℝ) =
            ({0} : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
        -- This is exactly the dedicated computation for the square function.
        simpa using helperForProposition_6_28_2_subdifferentialAt_evalSq_coeEReal_zero_eq_singleton
      -- Step 3: pick the coordinate functional `π₀` and derive a contradiction from the assumed equality.
      let π₀ : (Fin 1 → ℝ) →ₗ[ℝ] ℝ :=
        LinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℝ) (0 : Fin 1)
      have hπ₀memLeft :
          (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) ∈
            subdifferentialAt
              (indicatorFunction {y : Fin 1 → ℝ | (fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y ≤ 0})
              (0 : Fin 1 → ℝ) := by
        -- Since this subdifferential is `Set.univ`, membership is automatic.
        rw [hSubUniv]
        trivial
      have hπ₀memCone :
          (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) ∈
            Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
              a.1 •
                subdifferentialAt
                  (fun y : Fin 1 → ℝ =>
                    (((fun y : Fin 1 → ℝ => (y 0) ^ (2 : ℕ)) y : ℝ) : EReal))
                  (0 : Fin 1 → ℝ) := by
        -- Rewrite the left-hand membership using the assumed equality.
        exact hEq ▸ hπ₀memLeft
      rcases Set.mem_iUnion.1 hπ₀memCone with ⟨a, ha⟩
      have ha₁ :
          (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) ∈
            a.1 •
              subdifferentialAt
                (fun y : Fin 1 → ℝ => (((y 0) ^ (2 : ℕ) : ℝ) : EReal))
                (0 : Fin 1 → ℝ) := by
        simpa using ha
      have ha' :
          (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) ∈
            a.1 • ({0} : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
        -- Replace `∂ constraint(0)` by `{0}`.
        rw [hSubConstraint] at ha₁
        exact ha₁
      have hπ₀zero : (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) = 0 := by
        -- Membership in a scalar multiple of `{0}` forces equality to `0`.
        simpa using ha'
      have hπ₀ne : (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) ≠ 0 := by
        intro h0
        -- Evaluate at the constant-`1` vector: `π₀` sends it to `1`, while the zero map sends it to `0`.
        have hzero :
            (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
          simpa [h0]
        have hone :
            (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
          simp [π₀]
        have : (1 : ℝ) = 0 := by
          calc
            (1 : ℝ) =
                (π₀ : Module.Dual ℝ (Fin 1 → ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
                  simpa using hone.symm
            _ = 0 := hzero
        exact one_ne_zero this
      exact hπ₀ne hπ₀zero

/-- Helper for Proposition 6.28.2: the stated three-case conclusion cannot hold without a
feasibility hypothesis.  For the constant constraint `constraint ≡ 1`, the feasible set
`{y | constraint y ≤ 0}` is empty, but the indicator subdifferential is `Set.univ` (by the
definition used in Chapter 23), contradicting the claimed emptiness when `0 < constraint x`. -/
lemma helperForProposition_6_28_2_counterexample_outside_case :
    ∃ (constraint : (Fin 1 → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint) (x : Fin 1 → ℝ),
      ¬ (subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x =
            normalConeAt {y : Fin 1 → ℝ | constraint y ≤ 0} x ∧
          (constraint x = 0 →
              subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x =
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 • subdifferentialAt (fun y : Fin 1 → ℝ => ((constraint y : ℝ) : EReal)) x) ∧
          (constraint x < 0 →
              subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x =
                ({0} : Set (Module.Dual ℝ (Fin 1 → ℝ)))) ∧
          (0 < constraint x →
              subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x = ∅)) := by
  classical
  -- Choose the constant convex constraint `constraint ≡ 1` and the point `x = 0`.
  refine ⟨(fun _ : Fin 1 → ℝ => (1 : ℝ)), ?_, (0 : Fin 1 → ℝ), ?_⟩
  · -- Constant functions are convex on any set.
    refine
      (convexOn_const (𝕜 := ℝ) (E := (Fin 1 → ℝ)) (s := (Set.univ : Set (Fin 1 → ℝ)))
        (c := (1 : ℝ))) ?_
    -- The universal set is convex.
    simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin 1 → ℝ)))
  · intro h
    -- Extract the claimed outside-case implication and apply it at `x = 0`, since `0 < 1`.
    have hx : (0 : ℝ) < (1 : ℝ) := by
      -- This is a purely arithmetic fact.
      linarith
    have hx' : (0 : ℝ) < (fun _ : Fin 1 → ℝ => (1 : ℝ)) (0 : Fin 1 → ℝ) := by
      -- Re-express `0 < 1` in the form required by the hypothesis.
      simpa using hx
    have hOutside :
        subdifferentialAt
            (indicatorFunction {y : Fin 1 → ℝ | (fun _ : Fin 1 → ℝ => (1 : ℝ)) y ≤ 0})
            (0 : Fin 1 → ℝ) = ∅ :=
      (h.2.2.2) hx'
    -- But the feasible set is empty, so the indicator subdifferential is `Set.univ`.
    have hEmpty :
        ({y : Fin 1 → ℝ | (fun _ : Fin 1 → ℝ => (1 : ℝ)) y ≤ 0} : Set (Fin 1 → ℝ)) = ∅ := by
      ext y
      constructor
      · intro hy
        have : (1 : ℝ) ≤ 0 := by simpa using hy
        linarith
      · intro hy
        cases hy
    have hUniv :
        subdifferentialAt
            (indicatorFunction {y : Fin 1 → ℝ | (fun _ : Fin 1 → ℝ => (1 : ℝ)) y ≤ 0})
            (0 : Fin 1 → ℝ) =
          (Set.univ : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
      -- Rewrite by `hEmpty` and use the in-file lemma for the empty feasible set.
      simpa [hEmpty] using
        (helperForProposition_6_28_2_subdifferentialAt_indicator_empty_eq_univ
          (n := 1) (x := (0 : Fin 1 → ℝ)))
    -- Combine the two equalities to get `Set.univ = ∅`, which is impossible (witness `0`).
    have hunivEqEmpty :
        (Set.univ : Set (Module.Dual ℝ (Fin 1 → ℝ))) =
          (∅ : Set (Module.Dual ℝ (Fin 1 → ℝ))) :=
      hUniv.symm.trans hOutside
    have : (0 : Module.Dual ℝ (Fin 1 → ℝ)) ∈ (∅ : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
      have : (0 : Module.Dual ℝ (Fin 1 → ℝ)) ∈
          (Set.univ : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
        trivial
      simpa [hunivEqEmpty] using this
    simpa using this

/-- Helper for Proposition 6.28.2: the unqualified conjunction asserted by the proposition is
already refuted in dimension `1`.  This packages
`helperForProposition_6_28_2_counterexample_outside_case` into a direct negation of the
corresponding universally-quantified statement. -/
lemma helperForProposition_6_28_2_statement_refuted_in_dim1 :
    ¬ (∀ (constraint : (Fin 1 → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint)
        (x : Fin 1 → ℝ),
        subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x =
            normalConeAt {y : Fin 1 → ℝ | constraint y ≤ 0} x ∧
          (constraint x = 0 →
              subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x =
                Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
                  a.1 • subdifferentialAt (fun y : Fin 1 → ℝ => ((constraint y : ℝ) : EReal)) x) ∧
          (constraint x < 0 →
              subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x =
                ({0} : Set (Module.Dual ℝ (Fin 1 → ℝ)))) ∧
          (0 < constraint x →
              subdifferentialAt (indicatorFunction {y : Fin 1 → ℝ | constraint y ≤ 0}) x = ∅)) := by
  classical
  intro hAll
  -- Specialize the purported universal statement to the explicit convex counterexample.
  rcases helperForProposition_6_28_2_counterexample_outside_case with
    ⟨constraint, hconstraint, x, hnot⟩
  exact hnot (hAll constraint hconstraint x)

end Section28
end Chap06
