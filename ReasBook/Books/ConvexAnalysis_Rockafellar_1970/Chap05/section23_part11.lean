/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part10

section Chap05
section Section23

/-- The Euclidean norm on `ℝⁿ`, written using the standard dot product. -/
noncomputable def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

/-- The Euclidean identification of a vector in `ℝⁿ` with the corresponding dual vector. -/
def euclideanDualVector {n : ℕ} (x : Fin n → ℝ) : Module.Dual ℝ (Fin n → ℝ) :=
  dotProductEquiv ℝ (Fin n) x

/-- The Euclidean norm viewed as an extended-real-valued function. -/
noncomputable def euclideanNormFunction {n : ℕ} (x : Fin n → ℝ) : EReal :=
  (euclideanNorm x : EReal)

/-- Membership in the class of indicator functions of a set. -/
def IsIndicatorFunctionOfSet {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal) : Prop :=
  f = indicatorFunction C

/-- The Chebyshev norm on `ℝⁿ`, viewed as an extended-real-valued function. -/
noncomputable def chebyshevNormFunction {n : ℕ} (x : Fin n → ℝ) : EReal :=
  ((sSup (Set.range fun i : Fin n => |x i|) : ℝ) : EReal)

/-- The active coordinate set for the Chebyshev norm at `x`. -/
def chebyshevActiveIndices {n : ℕ} (x : Fin n → ℝ) : Set (Fin n) :=
  {i | |x i| = sSup (Set.range fun j : Fin n => |x j|)}

/-- The convex example `x ↦ -sqrt (1 - |x|^2)` on the Euclidean unit ball and `+∞` outside. -/
noncomputable def unitBallBarrierFunction {n : ℕ} (x : Fin n → ℝ) : EReal :=
  if euclideanNorm (n := n) x < 1 then
    ((-Real.sqrt (1 - (euclideanNorm (n := n) x) ^ 2) : ℝ) : EReal)
  else ⊤

theorem subdifferential_indicatorFunction_eq_normalConeAt_of_mem {n : ℕ}
    {C : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ C) :
    subdifferentialAt (indicatorFunction C) x = normalConeAt C x := by
  ext xStar
  constructor
  · intro hxStar
    refine (mem_normalConeAt_iff).2 ⟨hx, ?_⟩
    intro z hz
    have hineq :
        indicatorFunction C z ≥
          indicatorFunction C x + (((xStar (z - x) : ℝ) : EReal)) :=
      hxStar z
    have hineq' : (((xStar (z - x) : ℝ) : EReal)) ≤ (0 : EReal) := by
      simpa [indicatorFunction, hx, hz] using hineq
    exact_mod_cast hineq'
  · intro hxStar z
    by_cases hz : z ∈ C
    · have hzle : xStar (z - x) ≤ 0 := (mem_normalConeAt_iff.1 hxStar).2 z hz
      have hzle' : (((xStar (z - x) : ℝ) : EReal)) ≤ (0 : EReal) := by
        exact_mod_cast hzle
      calc
        indicatorFunction C z = (0 : EReal) := by simp [indicatorFunction, hz]
        _ ≥ (((xStar (z - x) : ℝ) : EReal)) := hzle'
        _ = indicatorFunction C x + (((xStar (z - x) : ℝ) : EReal)) := by
              simp [indicatorFunction, hx]
    · simp [indicatorFunction, hz]

theorem subdifferential_indicatorFunction_eq_empty_of_not_mem {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : C.Nonempty) {x : Fin n → ℝ} (hx : x ∉ C) :
    subdifferentialAt (indicatorFunction C) x = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro xStar hxStar
  rcases hC with ⟨z0, hz0⟩
  have hbad :
      indicatorFunction C z0 ≥
        indicatorFunction C x + (((xStar (z0 - x) : ℝ) : EReal)) :=
    hxStar z0
  have : ¬ (((0 : EReal)) ≥ (⊤ : EReal)) := by simp
  apply this
  calc
    (0 : EReal) = indicatorFunction C z0 := by simp [indicatorFunction, hz0]
    _ ≥ indicatorFunction C x + (((xStar (z0 - x) : ℝ) : EReal)) := hbad
    _ = (⊤ : EReal) := by
          rw [show indicatorFunction C x = (⊤ : EReal) by simp [indicatorFunction, hx]]
          simpa using (EReal.top_add_coe (xStar (z0 - x)))

/-- Helper for Theorem 23.7: after identifying vectors with dual vectors, the normal cone of the
sublevel set is the polar of the translated `≤ 0` sublevel directions. -/
lemma helperForTheorem_23_7_euclideanNormalCone_preimage_eq_polar_translatedSublevel
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt {z : Fin n → ℝ | f z ≤ f x} x) =
      ((dotProductEquiv ℝ (Fin n)) ⁻¹'
        polarCone {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0}) := by
  ext v
  constructor
  · intro hv
    -- Read normal-cone membership as the supporting inequality on the original sublevel set.
    have hvNormal :
        dotProductEquiv ℝ (Fin n) v ∈ normalConeAt {z : Fin n → ℝ | f z ≤ f x} x := hv
    refine (mem_polarCone_iff
      (E := Fin n → ℝ)
      (K := {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0})
      (φ := dotProductEquiv ℝ (Fin n) v)).2 ?_
    intro y hy
    have hySublevel : f (x + y) ≤ f x := by
      exact (EReal.sub_nonpos).1 (by simpa [translatedDifferenceFunctionAt] using hy)
    have hyNormal :
        (dotProductEquiv ℝ (Fin n) v) ((x + y) - x) ≤ 0 :=
      (mem_normalConeAt_iff.1 hvNormal).2 (x + y) hySublevel
    -- Translating by `x` turns the normal-cone inequality into the polar inequality on `y`.
    simpa [dotProduct_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hyNormal
  · intro hv
    -- Conversely, test the polar inequality on translated points `y = z - x`.
    have hvPolar :
        dotProductEquiv ℝ (Fin n) v ∈
          polarCone {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0} := hv
    refine (mem_normalConeAt_iff).2 ?_
    refine ⟨by simp, ?_⟩
    intro z hz
    have hzTranslated :
        translatedDifferenceFunctionAt f x (z - x) ≤ 0 := by
      exact (EReal.sub_nonpos).2 (by simpa [translatedDifferenceFunctionAt, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hz)
    have hzPolar :
        (dotProductEquiv ℝ (Fin n) v) (z - x) ≤ 0 :=
      (mem_polarCone_iff
        (E := Fin n → ℝ)
        (K := {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0})
        (φ := dotProductEquiv ℝ (Fin n) v)).1 hvPolar (z - x) hzTranslated
    simpa [dotProduct_comm] using hzPolar

/-- Helper for Theorem 23.7: the vectorized polar of the closed cone generated by the
subdifferential is exactly the nonpositive sublevel set of the subdifferential support function. -/
lemma helperForTheorem_23_7_vectorizedPolar_subdifferentialCone_eq_support_nonpos
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹'
        polarCone
          (closure
            (((ConvexCone.hull ℝ
              (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))) :
                ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) =
      {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} := by
  let S : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  ext y
  constructor
  · intro hy
    have hyPolar :
        dotProductEquiv ℝ (Fin n) y ∈
          polarCone
            (closure
              (((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
      simpa [S] using hy
    have hyOnS :
        ∀ v : Fin n → ℝ, v ∈ S → ((dotProduct v y : ℝ) : EReal) ≤ (0 : EReal) := by
      intro v hv
      have hv' :
          (dotProductEquiv ℝ (Fin n) y) v ≤ 0 := by
        have hyPolar' :
            dotProductEquiv ℝ (Fin n) y ∈ polarCone S := by
          simpa [section14_polarCone_closure_eq, section14_polarCone_hull_eq, S] using hyPolar
        exact
          (mem_polarCone_iff (E := Fin n → ℝ) (K := S)
            (φ := dotProductEquiv ℝ (Fin n) y)).1 hyPolar' v hv
      simpa [dotProduct_comm] using hv'
    have hsuppLe :
        supportFunctionEReal S y ≤ (0 : EReal) := by
      -- Every point in the support-function image set is nonpositive, so the supremum is too.
      unfold supportFunctionEReal
      refine sSup_le ?_
      rintro z ⟨v, hv, rfl⟩
      exact hyOnS v hv
    simpa [S, helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq] using hsuppLe
  · intro hy
    have hsuppLe :
        supportFunctionEReal S y ≤ (0 : EReal) := by
      simpa [S, helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq] using hy
    have hyOnS :
        ∀ v : Fin n → ℝ, v ∈ S → ((dotProduct v y : ℝ) : EReal) ≤ (0 : EReal) := by
      intro v hv
      have hvImage :
          ((dotProduct v y : ℝ) : EReal) ∈
            {z : EReal | ∃ w ∈ S, z = ((dotProduct w y : ℝ) : EReal)} :=
        ⟨v, hv, rfl⟩
      exact le_trans (le_sSup hvImage) hsuppLe
    have hyPolarS :
        dotProductEquiv ℝ (Fin n) y ∈ polarCone S := by
      refine (mem_polarCone_iff (E := Fin n → ℝ) (K := S)
        (φ := dotProductEquiv ℝ (Fin n) y)).2 ?_
      intro v hv
      simpa [dotProduct_comm] using hyOnS v hv
    -- Hull and closure do not change the polar cone, so the same inequality holds on the closed
    -- cone generated by the subdifferential.
    simpa [section14_polarCone_closure_eq, section14_polarCone_hull_eq, S] using hyPolarS

/-- Helper for Theorem 23.7: a nonempty subdifferential forces `f x` to be finite. -/
lemma helperForTheorem_23_7_finiteAt_of_subdifferentiable
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
  -- A subgradient at `x` gives a finite supporting inequality, so only the `⊤` case needs work.
  refine ⟨?_, hproper.2.2 x (by simp)⟩
  let xStar : Module.Dual ℝ (Fin n → ℝ) := Classical.choose hsub
  have hxStar : xStar ∈ subdifferentialAt f x := Classical.choose_spec hsub
  obtain ⟨z0, r0, hz0⟩ :=
    properConvexFunctionOn_exists_finite_point (n := n) (f := f) hproper
  intro htop
  have hineq : f z0 ≥ f x + ((xStar (z0 - x) : ℝ) : EReal) :=
    hxStar z0
  rw [htop, hz0] at hineq
  have htopLe : (⊤ : EReal) ≤ (r0 : EReal) := by
    have htopAdd :
        (⊤ : EReal) + ((xStar (z0 - x) : ℝ) : EReal) = (⊤ : EReal) :=
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    exact htopAdd ▸ hineq
  simp at htopLe

/-- Helper for Theorem 23.7: every strictly negative directional derivative comes from scaling an
actual translated descent direction, so it already lies in the cone generated by the translated
`≤ 0` sublevel set. -/
lemma helperForTheorem_23_7_strictDirectionalSublevel_subset_coneHull_translatedDirections
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ)
    (hf : ConvexFunction f) (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hy : upperDirectionalDerivativeAt f x y < (0 : EReal)) :
    y ∈ ↑(ConvexCone.hull ℝ
      {z : Fin n → ℝ | translatedDifferenceFunctionAt f x z ≤ 0}) := by
  let D : Set (Fin n → ℝ) := {z : Fin n → ℝ | translatedDifferenceFunctionAt f x z ≤ 0}
  let Q : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt f x y) (Set.Ioi (0 : ℝ)) :=
    helperForTheorem_23_1_differenceQuotient_monotone f hf x y hxFinite
  have hQ_bdd : BddBelow Q := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp [Q] at hq ⊢
  have hOnePos : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    simp
  have hQ_nonempty : Q.Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f x y 1, ?_⟩
    exact ⟨1, hOnePos, rfl⟩
  have hsInf_lt_zero : sInf Q < (0 : EReal) := by
    -- Rewrite the upper derivative as the infimum of positive-step quotients.
    simpa [Q, helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y hmono] using hy
  rcases (csInf_lt_iff hQ_bdd hQ_nonempty).1 hsInf_lt_zero with ⟨q, hqQ, hq_lt_zero⟩
  rcases hqQ with ⟨t, ht, hqt⟩
  have ht0 : 0 < t := by
    simpa using ht
  have hquot_le_zero : directionalDifferenceQuotientAt f x y t ≤ (0 : EReal) := by
    simpa [hqt] using (le_of_lt hq_lt_zero : q ≤ (0 : EReal))
  have hvalue_le : f (x + t • y) ≤ f x := by
    -- A nonpositive quotient at one positive step forces a nonincreasing translated value.
    have hbound :=
      helperForTheorem_23_1_valueBound_of_differenceQuotient_le_real
        f x y t hxFinite ht0 (μ := 0) hquot_le_zero
    have hx_toReal : (((f x).toReal : ℝ) : EReal) = f x := by
      exact EReal.coe_toReal hxFinite.1 hxFinite.2
    simpa [hx_toReal] using hbound
  have hty_mem : t • y ∈ D := by
    -- Repackage the endpoint inequality as membership in the translated `≤ 0` sublevel set.
    change translatedDifferenceFunctionAt f x (t • y) ≤ (0 : EReal)
    exact (EReal.sub_nonpos).2 (by simpa [translatedDifferenceFunctionAt] using hvalue_le)
  have hty_hull : t • y ∈ ↑(ConvexCone.hull ℝ D) :=
    ConvexCone.subset_hull (R := ℝ) (s := D) hty_mem
  have hInvPos : 0 < 1 / t := by
    positivity
  have hy_hull : (1 / t) • (t • y) ∈ ↑(ConvexCone.hull ℝ D) :=
    ConvexCone.smul_mem (C := ConvexCone.hull ℝ D) hInvPos hty_hull
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  simpa [D, smul_smul, inv_mul_cancel₀ ht_ne] using hy_hull

/-- Helper for Theorem 23.7: transfer the `≤ 0` closure formula from Theorem 7.6 back to
`Fin n → ℝ`. -/
lemma helperForTheorem_23_7_closure_nonposSublevel_eq_sublevel_convexFunctionClosure
    {n : ℕ} {h : (Fin n → ℝ) → EReal}
    (hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hInf : iInf (fun x => h x) < (0 : EReal)) :
    closure {x : Fin n → ℝ | h x ≤ (0 : EReal)} =
      {x : Fin n → ℝ | convexFunctionClosure h x ≤ (0 : EReal)} := by
  classical
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | h (x : Fin n → ℝ) ≤ (0 : EReal)}
  let B : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | convexFunctionClosure h (x : Fin n → ℝ) ≤ (0 : EReal)}
  have hEq :
      closure A = B := by
    have hlevel :=
      properConvexFunction_levelSets_same_closure_ri_dim
        (n := n) (f := h) hh (α := (0 : ℝ)) hInf
    simpa [A, B] using hlevel.1
  have hEq' : closure (e '' A) = e '' B := by
    have hEq'' : (e.toHomeomorph) '' closure A = (e.toHomeomorph) '' B := by
      simpa using congrArg (fun S => (e.toHomeomorph) '' S) hEq
    have hcl :
        (e.toHomeomorph) '' closure A = closure ((e.toHomeomorph) '' A) := by
      simpa using (Homeomorph.image_closure (h := e.toHomeomorph) (s := A))
    calc
      closure (e '' A) = (e.toHomeomorph) '' closure A := by
        simpa [e] using hcl.symm
      _ = (e.toHomeomorph) '' B := hEq''
      _ = e '' B := by simp [e]
  have hA : e '' A = {x : Fin n → ℝ | h x ≤ (0 : EReal)} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [A] using hu
    · intro hx
      refine ⟨e.symm x, ?_, by simp [e]⟩
      simpa [A, e] using hx
  have hB : e '' B = {x : Fin n → ℝ | convexFunctionClosure h x ≤ (0 : EReal)} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [B] using hu
    · intro hx
      refine ⟨e.symm x, ?_, by simp [e]⟩
      simpa [B, e] using hx
  simpa [hA, hB] using hEq'

/-- Helper for Theorem 23.7: transfer the strict `< 0` closure formula from Theorem 7.6 back to
`Fin n → ℝ`. -/
lemma helperForTheorem_23_7_closure_strictSublevel_eq_sublevel_convexFunctionClosure
    {n : ℕ} {h : (Fin n → ℝ) → EReal}
    (hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hInf : iInf (fun x => h x) < (0 : EReal)) :
    closure {x : Fin n → ℝ | h x < (0 : EReal)} =
      {x : Fin n → ℝ | convexFunctionClosure h x ≤ (0 : EReal)} := by
  classical
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | h (x : Fin n → ℝ) < (0 : EReal)}
  let B : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | convexFunctionClosure h (x : Fin n → ℝ) ≤ (0 : EReal)}
  have hEq :
      closure A = B := by
    have hlevel :=
      properConvexFunction_levelSets_same_closure_ri_dim
        (n := n) (f := h) hh (α := (0 : ℝ)) hInf
    simpa [A, B] using hlevel.2.1
  have hEq' : closure (e '' A) = e '' B := by
    have hEq'' : (e.toHomeomorph) '' closure A = (e.toHomeomorph) '' B := by
      simpa using congrArg (fun S => (e.toHomeomorph) '' S) hEq
    have hcl :
        (e.toHomeomorph) '' closure A = closure ((e.toHomeomorph) '' A) := by
      simpa using (Homeomorph.image_closure (h := e.toHomeomorph) (s := A))
    calc
      closure (e '' A) = (e.toHomeomorph) '' closure A := by
        simpa [e] using hcl.symm
      _ = (e.toHomeomorph) '' B := hEq''
      _ = e '' B := by simp [e]
  have hA : e '' A = {x : Fin n → ℝ | h x < (0 : EReal)} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [A] using hu
    · intro hx
      refine ⟨e.symm x, ?_, by simp [e]⟩
      simpa [A, e] using hx
  have hB : e '' B = {x : Fin n → ℝ | convexFunctionClosure h x ≤ (0 : EReal)} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [B] using hu
    · intro hx
      refine ⟨e.symm x, ?_, by simp [e]⟩
      simpa [B, e] using hx
  simpa [hA, hB] using hEq'

/-- Helper for Theorem 23.7: every translated `≤ 0` direction already lies in the nonpositive
sublevel set of the support function of `∂f(x)`. -/
lemma helperForTheorem_23_7_translatedDirections_subset_supportNonpos
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0} ⊆
      {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} := by
  let H : (Fin n → ℝ) → EReal := subdifferentialSupportAt f x
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨hdirData, _hpos, _hconv, _hzero, _hsymm⟩
  intro y hy
  have hdirEq :
      upperDirectionalDerivativeAt f x y =
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) := by
    simpa using
      helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y (hdirData y).1
  have hupper_le :
      upperDirectionalDerivativeAt f x y ≤ directionalDifferenceQuotientAt f x y 1 := by
    -- Compare the upper derivative with the positive-step quotient at `t = 1`.
    rw [hdirEq]
    exact csInf_le (by refine ⟨⊥, ?_⟩; intro q hq; simp at hq ⊢) ⟨1, by simp, rfl⟩
  have hquot_le :
      directionalDifferenceQuotientAt f x y 1 ≤ (0 : EReal) := by
    -- The translated inequality is exactly the `t = 1` difference quotient bound.
    simpa [directionalDifferenceQuotientAt, translatedDifferenceFunctionAt] using hy
  have hdir_nonpos : upperDirectionalDerivativeAt f x y ≤ (0 : EReal) :=
    le_trans hupper_le hquot_le
  -- The support function always lies below the upper directional derivative.
  exact le_trans (subdifferentialSupportAt_le_upperDirectionalDerivative f hproper y) hdir_nonpos

/-- Helper for Theorem 23.7: `subdifferentialSupportAt f x` is a closed proper positively
homogeneous support function whenever `∂f(x)` is nonempty. -/
lemma helperForTheorem_23_7_supportFunction_closedProper_posHom
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    ClosedConvexFunction (subdifferentialSupportAt f x) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (subdifferentialSupportAt f x) ∧
        PositivelyHomogeneous (subdifferentialSupportAt f x) := by
  let C : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  rcases hsub with ⟨g, hg⟩
  have h23_2 :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite g
  have hCconv : Convex ℝ C := h23_2.2.2.1
  have hCne : C.Nonempty := by
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
    simpa [C] using hg
  have hSupport :
      ClosedConvexFunction (supportFunctionEReal C) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (supportFunctionEReal C) ∧
          PositivelyHomogeneous (supportFunctionEReal C) :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv
  have hEq : supportFunctionEReal C = subdifferentialSupportAt f x := by
    funext y
    exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
  -- Rewrite the packaged support-function regularity along Theorem 23.2's support identity.
  simpa [hEq] using hSupport

/-- Helper for Theorem 23.7: the nonpositive support sublevel is closed. -/
lemma helperForTheorem_23_7_supportNonpos_isClosed
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    IsClosed {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} := by
  have hclosed :
      ClosedConvexFunction (subdifferentialSupportAt f x) :=
    (helperForTheorem_23_7_supportFunction_closedProper_posHom f hproper x hsub).1
  -- Closedness is just lower semicontinuity of the support function evaluated at the `0`-sublevel.
  simpa using
    (lowerSemicontinuous_iff_closed_sublevel (f := subdifferentialSupportAt f x)).1 hclosed.2 0

/-- Helper for Theorem 23.7: a nonempty subdifferential makes the directional derivative a proper
convex function on `ℝⁿ`. -/
lemma helperForTheorem_23_7_upperDirectionalDerivative_properConvex_of_subdifferentiable
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hdirData, _hpos, hconvD, hzero, _hsymm⟩
  rcases hsub with ⟨g, hg⟩
  refine (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
    (S := (Set.univ : Set (Fin n → ℝ))) (f := D)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · -- Theorem 23.1 already packages convexity of the directional derivative.
    simpa [ConvexFunction, D] using hconvD
  · -- The zero direction gives a finite epigraph point because `f'(x; 0) = 0`.
    refine ⟨0, ⟨0, ?_⟩⟩
    refine ⟨Set.mem_univ 0, ?_⟩
    simp [D, hzero]
  · intro y hy
    constructor
    · -- A chosen subgradient provides a finite linear minorant, so `D y` cannot be `⊥`.
      have hminor : ((g y : ℝ) : EReal) ≤ D y :=
        le_upperDirectionalDerivative_of_mem_subdifferential f hproper g hg y
      intro hybot
      exact (EReal.bot_lt_coe (g y)).not_ge (hybot ▸ hminor)
    · -- Membership in the effective domain rules out `⊤`.
      exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := D) hy

/-- Helper for Theorem 23.7: if `x` is not a minimizer, then the directional derivative itself has
infimum below `0`. -/
lemma helperForTheorem_23_7_upperDirectionalDerivative_infimum_neg
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) (hnotmin : ∃ z, f z < f x) :
    iInf (fun y : Fin n → ℝ => upperDirectionalDerivativeAt f x y) < (0 : EReal) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨hdirData, _hpos, _hconv, _hzero, _hsymm⟩
  rcases hnotmin with ⟨z, hzlt⟩
  let w : Fin n → ℝ := z - x
  let Q : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x w t
  have hQbdd : BddBelow Q := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp [Q] at hq ⊢
  have hdirEq :
      upperDirectionalDerivativeAt f x w = sInf Q := by
    -- The upper directional derivative is the infimum of positive-step difference quotients.
    simpa [Q] using
      helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x w (hdirData w).1
  have hupper_le :
      upperDirectionalDerivativeAt f x w ≤ directionalDifferenceQuotientAt f x w 1 := by
    -- Evaluating the infimum at `t = 1` gives a concrete strict upper bound.
    rw [hdirEq]
    exact csInf_le hQbdd ⟨1, by simp, rfl⟩
  have hquot_eq :
      directionalDifferenceQuotientAt f x w 1 = f z - f x := by
    -- The direction `w = z - x` reaches `z` exactly at time `t = 1`.
    simp [w, directionalDifferenceQuotientAt, sub_eq_add_neg]
  have hquot_lt : directionalDifferenceQuotientAt f x w 1 < (0 : EReal) := by
    rw [hquot_eq]
    have hz_ne_top : f z ≠ (⊤ : EReal) := by
      exact ne_of_lt (lt_of_lt_of_le hzlt (le_of_lt (lt_top_iff_ne_top.2 hxFinite.1)))
    have hz_ne_bot : f z ≠ (⊥ : EReal) := hproper.2.2 z (by simp)
    exact (EReal.sub_neg (Or.inl hz_ne_top) (Or.inl hz_ne_bot)).2 hzlt
  have hupper_lt : upperDirectionalDerivativeAt f x w < (0 : EReal) :=
    lt_of_le_of_lt hupper_le hquot_lt
  -- The witness direction `w` immediately pushes the global infimum below `0`.
  exact lt_of_le_of_lt (iInf_le (fun y : Fin n → ℝ => upperDirectionalDerivativeAt f x y) w) hupper_lt

/-- Helper for Theorem 23.7: the nonpositive support sublevel already lies in the closure of the
cone generated by translated `≤ 0` directions. -/
lemma helperForTheorem_23_7_supportNonpos_subset_closure_coneHull_translatedDirections
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) (hnotmin : ∃ z, f z < f x) :
    {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} ⊆
      closure ((((ConvexCone.hull ℝ
        {z : Fin n → ℝ | translatedDifferenceFunctionAt f x z ≤ 0}) :
          ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
  let Dfun : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let T : Set (Fin n → ℝ) := {z : Fin n → ℝ | translatedDifferenceFunctionAt f x z ≤ 0}
  let H : (Fin n → ℝ) → EReal := subdifferentialSupportAt f x
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  have hDproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) Dfun :=
    helperForTheorem_23_7_upperDirectionalDerivative_properConvex_of_subdifferentiable
      f hproper x hsub
  have hDinf : iInf (fun y : Fin n → ℝ => Dfun y) < (0 : EReal) :=
    helperForTheorem_23_7_upperDirectionalDerivative_infimum_neg f hproper x hsub hnotmin
  have hstrictClosure :
      closure {y : Fin n → ℝ | Dfun y < (0 : EReal)} =
        {y : Fin n → ℝ | convexFunctionClosure Dfun y ≤ (0 : EReal)} :=
    helperForTheorem_23_7_closure_strictSublevel_eq_sublevel_convexFunctionClosure
      (h := Dfun) hDproper hDinf
  have hclosureEq : convexFunctionClosure Dfun = H := by
    -- Route correction: use Theorem 23.2 only at the closure level, not as a pointwise equality.
    simpa [Dfun, H] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hxFinite (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.2
  have hstrictSubset :
      {y : Fin n → ℝ | Dfun y < (0 : EReal)} ⊆
        (((ConvexCone.hull ℝ T) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    intro y hy
    -- Strict directional descent already lands in the translated-direction cone.
    simpa [Dfun, T] using
      helperForTheorem_23_7_strictDirectionalSublevel_subset_coneHull_translatedDirections
        f x y hf hxFinite hy
  have hclosureSubset :
      closure {y : Fin n → ℝ | Dfun y < (0 : EReal)} ⊆
        closure ((((ConvexCone.hull ℝ T) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) :=
    closure_mono hstrictSubset
  intro y hy
  have hyClosure : y ∈ closure {z : Fin n → ℝ | Dfun z < (0 : EReal)} := by
    have hy' : y ∈ {z : Fin n → ℝ | convexFunctionClosure Dfun z ≤ (0 : EReal)} := by
      simpa [H, hclosureEq] using hy
    rw [← hstrictClosure] at hy'
    exact hy'
  exact hclosureSubset hyClosure

/-- Helper for Theorem 23.7: the nonpositive support sublevel is already a convex cone, so taking
its convex-cone hull does not enlarge it. -/
lemma helperForTheorem_23_7_supportNonpos_is_convexCone
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    ((ConvexCone.hull ℝ {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0}) :
        Set (Fin n → ℝ)) =
      {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} := by
  let H : (Fin n → ℝ) → EReal := subdifferentialSupportAt f x
  have hpack :=
    helperForTheorem_23_7_supportFunction_closedProper_posHom f hproper x hsub
  have hnotbot : ∀ y : Fin n → ℝ, H y ≠ (⊥ : EReal) := by
    intro y
    exact hpack.2.1.2.2 y (by simp)
  have hsubadd : ∀ u v : Fin n → ℝ, H (u + v) ≤ H u + H v :=
    subadditive_of_convex_posHom (hpos := hpack.2.2) hpack.1.1 hnotbot
  let Ck : ConvexCone ℝ (Fin n → ℝ) :=
    { carrier := {y : Fin n → ℝ | H y ≤ 0}
      add_mem' := by
        intro u hu v hv
        -- Subadditivity keeps the nonpositive sublevel closed under addition.
        have huv : H (u + v) ≤ H u + H v := hsubadd u v
        have hsum : H u + H v ≤ (0 : EReal) + (0 : EReal) := add_le_add hu hv
        exact le_trans huv (by simpa using hsum)
      smul_mem' := by
        intro a ha y hy
        -- Positive homogeneity keeps the nonpositive sublevel closed under positive scaling.
        have hsmul : H (a • y) = ((a : ℝ) : EReal) * H y := hpack.2.2 y a ha
        have haE : (0 : EReal) ≤ ((a : ℝ) : EReal) := by
          exact_mod_cast le_of_lt ha
        have hmul : ((a : ℝ) : EReal) * H y ≤ ((a : ℝ) : EReal) * (0 : EReal) :=
          mul_le_mul_of_nonneg_left hy haE
        simpa [H, hsmul] using hmul }
  have hsubset : {y : Fin n → ℝ | H y ≤ 0} ⊆ (Ck : Set (Fin n → ℝ)) := by
    intro y hy
    exact hy
  have hhull : (ConvexCone.hull ℝ {y : Fin n → ℝ | H y ≤ 0} : Set (Fin n → ℝ)) ⊆ (Ck : Set _) :=
    ConvexCone.hull_min (C := Ck) hsubset
  have hcarrier : (Ck : Set (Fin n → ℝ)) = {y : Fin n → ℝ | H y ≤ 0} := rfl
  -- The hull is squeezed between the generators and the explicit cone with the same carrier.
  exact Set.Subset.antisymm hhull (by
    intro y hy
    exact ConvexCone.subset_hull hy)

/-- Helper for Theorem 23.7: the support function of `∂f(x)` takes a strictly negative value when
`x` is not a minimizer, hence its infimum is below `0`. -/
lemma helperForTheorem_23_7_supportFunction_infimum_neg
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) (hnotmin : ∃ z, f z < f x) :
    iInf (fun y : Fin n → ℝ => subdifferentialSupportAt f x y) < (0 : EReal) := by
  let H : (Fin n → ℝ) → EReal := subdifferentialSupportAt f x
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :=
    helperForTheorem_23_7_finiteAt_of_subdifferentiable f hproper x hsub
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨hdirData, _hpos, _hconv, _hzero, _hsymm⟩
  rcases hnotmin with ⟨z, hzlt⟩
  let w : Fin n → ℝ := z - x
  let Q : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x w t
  have hQbdd : BddBelow Q := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp [Q] at hq ⊢
  have hdirEq :
      upperDirectionalDerivativeAt f x w = sInf Q :=
    by
      simpa [Q] using
        helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x w (hdirData w).1
  have hupper_le :
      upperDirectionalDerivativeAt f x w ≤ directionalDifferenceQuotientAt f x w 1 := by
    -- Test the infimum representation at the positive step `t = 1`.
    rw [hdirEq]
    exact csInf_le hQbdd ⟨1, by simp, rfl⟩
  have hquot_eq :
      directionalDifferenceQuotientAt f x w 1 = f z - f x := by
    -- The direction `w = z - x` reaches the lower point `z` at time `t = 1`.
    simp [w, directionalDifferenceQuotientAt, sub_eq_add_neg]
  have hquot_lt : directionalDifferenceQuotientAt f x w 1 < (0 : EReal) := by
    rw [hquot_eq]
    have hz_ne_top : f z ≠ (⊤ : EReal) := by
      exact ne_of_lt (lt_of_lt_of_le hzlt (le_of_lt (lt_top_iff_ne_top.2 hxFinite.1)))
    have hz_ne_bot : f z ≠ (⊥ : EReal) := hproper.2.2 z (by simp)
    exact (EReal.sub_neg (Or.inl hz_ne_top) (Or.inl hz_ne_bot)).2 hzlt
  have hupper_lt : upperDirectionalDerivativeAt f x w < (0 : EReal) :=
    lt_of_le_of_lt hupper_le hquot_lt
  have hsupport_lt : H w < (0 : EReal) := by
    -- The support function is bounded above by the upper directional derivative.
    exact lt_of_le_of_lt
      (subdifferentialSupportAt_le_upperDirectionalDerivative f hproper w) hupper_lt
  exact lt_of_le_of_lt (iInf_le (fun y : Fin n → ℝ => H y) w) hsupport_lt

/-- Helper for Theorem 23.7: the closed cone generated by the translated `≤ 0` directions is the
nonpositive sublevel set of the subdifferential support function. -/
lemma helperForTheorem_23_7_translatedDirectionCone_closure_eq_support_nonpos
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) (hnotmin : ∃ z, f z < f x) :
    closure
      ((((ConvexCone.hull ℝ
        {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0}) :
          ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
      {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} := by
  let D : Set (Fin n → ℝ) := {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0}
  let H : (Fin n → ℝ) → EReal := subdifferentialSupportAt f x
  have hleft :
      {y : Fin n → ℝ | H y ≤ 0} ⊆
        closure ((((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
    -- Route correction: only the closure-level inclusion is needed here.
    simpa [D, H] using
      helperForTheorem_23_7_supportNonpos_subset_closure_coneHull_translatedDirections
        f hproper x hsub hnotmin
  have hDsubset :
      D ⊆ {y : Fin n → ℝ | H y ≤ 0} :=
    helperForTheorem_23_7_translatedDirections_subset_supportNonpos f hproper x hsub
  have hHullSubset :
      (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
        {y : Fin n → ℝ | H y ≤ 0} := by
    have hgen : D ⊆ ((ConvexCone.hull ℝ {y : Fin n → ℝ | H y ≤ 0}) : Set (Fin n → ℝ)) := by
      intro y hy
      exact ConvexCone.subset_hull (hDsubset hy)
    have hhull :
        (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
          ((ConvexCone.hull ℝ {y : Fin n → ℝ | H y ≤ 0}) : Set (Fin n → ℝ)) :=
      ConvexCone.hull_min (C := ConvexCone.hull ℝ {y : Fin n → ℝ | H y ≤ 0}) hgen
    simpa [H, helperForTheorem_23_7_supportNonpos_is_convexCone f hproper x hsub] using hhull
  have hright :
      closure ((((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) ⊆
        {y : Fin n → ℝ | H y ≤ 0} :=
    closure_minimal hHullSubset (helperForTheorem_23_7_supportNonpos_isClosed f hproper x hsub)
  exact Set.Subset.antisymm hright hleft

/-- Helper for Theorem 23.7: after the translated-direction cone is identified with the support
side, it becomes the vectorized polar of the closed cone generated by the subdifferential. -/
lemma helperForTheorem_23_7_closure_translatedDirectionCone_eq_vectorizedPolar_subdifferentialCone
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) (hnotmin : ∃ z, f z < f x) :
    closure
      ((((ConvexCone.hull ℝ
        {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0}) :
          ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
      ((dotProductEquiv ℝ (Fin n)) ⁻¹'
        polarCone
          (closure
            (((ConvexCone.hull ℝ
              (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))) :
                ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) := by
  -- Rewrite the translated-direction cone through the support-function description first.
  calc
    closure
        ((((ConvexCone.hull ℝ
          {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0}) :
            ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
        {y : Fin n → ℝ | subdifferentialSupportAt f x y ≤ 0} := by
          exact
            helperForTheorem_23_7_translatedDirectionCone_closure_eq_support_nonpos
              f hproper x hsub hnotmin
    _ =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          polarCone
            (closure
              (((ConvexCone.hull ℝ
                (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))) :
                  ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) := by
          symm
          exact helperForTheorem_23_7_vectorizedPolar_subdifferentialCone_eq_support_nonpos f x

/-- Helper for Theorem 23.7: vectorized polar cones can be rewritten as raw dot-product
inequalities on vectors. -/
lemma helperForTheorem_23_7_vectorizedPolar_preimage_eq_dotProductPolarHull
    {n : ℕ} (K : Set (Fin n → ℝ)) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone K) =
      {z : Fin n → ℝ | ∀ x ∈ K, dotProduct x z ≤ 0} := by
  ext z
  constructor
  · intro hz
    have hzPolar : dotProductEquiv ℝ (Fin n) z ∈ polarCone K := hz
    -- Expand polar-cone membership into its pointwise inequality formulation.
    refine Set.mem_setOf.2 ?_
    intro x hx
    have hxineq :
        (dotProductEquiv ℝ (Fin n) z) x ≤ 0 :=
      (mem_polarCone_iff (E := Fin n → ℝ) (K := K)
        (φ := dotProductEquiv ℝ (Fin n) z)).1 hzPolar x hx
    simpa [dotProduct_comm] using hxineq
  · intro hz
    have hzPolar : dotProductEquiv ℝ (Fin n) z ∈ polarCone K := by
      -- The raw dot-product inequalities are exactly the polar-cone conditions.
      refine (mem_polarCone_iff (E := Fin n → ℝ) (K := K)
        (φ := dotProductEquiv ℝ (Fin n) z)).2 ?_
      intro x hx
      simpa [dotProduct_comm] using hz x hx
    exact hzPolar

/-- Helper for Theorem 23.7: vectorizing the double polar of a convex cone recovers its closure. -/
lemma helperForTheorem_23_7_vectorizedBipolar_eq_closure_convexCone
    {n : ℕ} (K : Set (Fin n → ℝ)) (hK : K.Nonempty) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹'
        polarCone (((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone K))) =
      closure ↑(ConvexCone.hull ℝ K) := by
  let H : ConvexCone ℝ (Fin n → ℝ) := ConvexCone.hull ℝ K
  have hH_nonempty : ((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)).Nonempty := by
    rcases hK with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [H] using (ConvexCone.subset_hull (R := ℝ) (s := K) hx)
  have hinner :
      {z : Fin n → ℝ | ∀ x ∈ K, dotProduct x z ≤ 0} =
        {z : Fin n → ℝ | ∀ x ∈ ((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)),
          dotProduct x z ≤ 0} := by
    calc
      {z : Fin n → ℝ | ∀ x ∈ K, dotProduct x z ≤ 0} =
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone K) := by
            symm
            exact helperForTheorem_23_7_vectorizedPolar_preimage_eq_dotProductPolarHull (K := K)
      _ =
          ((dotProductEquiv ℝ (Fin n)) ⁻¹'
            polarCone (((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) := by
            have hpolar :
                polarCone (((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
                  polarCone K := by
              simpa [H] using section14_polarCone_hull_eq (E := Fin n → ℝ) (S := K)
            have hpre :=
              congrArg
                (fun S : Set (Module.Dual ℝ (Fin n → ℝ)) =>
                  ((dotProductEquiv ℝ (Fin n)) ⁻¹' S))
                hpolar.symm
            simpa using hpre
      _ =
          {z : Fin n → ℝ | ∀ x ∈ ((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)),
            dotProduct x z ≤ 0} := by
            exact
              helperForTheorem_23_7_vectorizedPolar_preimage_eq_dotProductPolarHull
                (K := ((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))
  -- After extensionalizing both polars, the result is exactly the finite-dimensional bipolar theorem.
  calc
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone (((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone K))) =
        {xStar : Fin n → ℝ |
          ∀ x ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone K), dotProduct x xStar ≤ 0} := by
          exact
            helperForTheorem_23_7_vectorizedPolar_preimage_eq_dotProductPolarHull
              (K := ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone K))
    _ =
        {xStar : Fin n → ℝ |
          ∀ x ∈ {z : Fin n → ℝ | ∀ y ∈ ((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)),
            dotProduct y z ≤ 0}, dotProduct x xStar ≤ 0} := by
          rw [helperForTheorem_23_7_vectorizedPolar_preimage_eq_dotProductPolarHull (K := K)]
          rw [hinner]
    _ = closure (((H : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
          exact section16_polar_polar_eq_closure_convexCone (K := H) hH_nonempty
    _ = closure ↑(ConvexCone.hull ℝ K) := by
          simp [H]

/-- Theorem 23.7: Let `f` be a proper convex function, assume `f` is subdifferentiable at `x`, and
`x` is not a minimizer of `f` in the sense that `∃ z, f z < f x`. Then, under the Euclidean
identification of vectors with dual vectors, the normal cone of the sublevel set
`C = {z | f z ≤ f x}` at `x` is the closure of the convex cone generated by `∂f(x)`. -/
theorem normalCone_sublevelSet_eq_closure_convexConeHull_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) (hnotmin : ∃ z, f z < f x) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt {z | f z ≤ f x} x) =
      closure ↑(ConvexCone.hull ℝ (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))) := by
  -- Route correction: the remaining Lean blocker is the cone-identification package, not the
  -- initial normal-cone reduction. Once the translated cone/support equality and the vectorized
  -- bipolar lemma are available, the theorem is a short chain of rewrites through those helpers.
  let D : Set (Fin n → ℝ) := {y : Fin n → ℝ | translatedDifferenceFunctionAt f x y ≤ 0}
  let S : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  have hpolarTranslated :
      polarCone
          (closure
            (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
        polarCone D := by
    calc
      polarCone
          (closure
            (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
          polarCone ((((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
            exact
              section14_polarCone_closure_eq
                (E := Fin n → ℝ)
                (K := (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))
      _ = polarCone D := by
            exact section14_polarCone_hull_eq (E := Fin n → ℝ) (S := D)
  have hpreTranslated :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone D) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          polarCone
            (closure
              (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) := by
    have hpre :=
      congrArg
        (fun T : Set (Module.Dual ℝ (Fin n → ℝ)) =>
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' T))
        hpolarTranslated.symm
    simpa using hpre
  have hpolarSubdiff :
      polarCone
          (closure
            (((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
        polarCone S := by
    calc
      polarCone
          (closure
            (((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) =
          polarCone ((((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
            exact
              section14_polarCone_closure_eq
                (E := Fin n → ℝ)
                (K := (((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))
      _ = polarCone S := by
            exact section14_polarCone_hull_eq (E := Fin n → ℝ) (S := S)
  have hinnerSubdiff :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          polarCone
            (closure
              (((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone S) := by
    have hpre :=
      congrArg
        (fun T : Set (Module.Dual ℝ (Fin n → ℝ)) =>
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' T))
        hpolarSubdiff
    simpa using hpre
  have hS_nonempty : S.Nonempty := by
    rcases hsub with ⟨g, hg⟩
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
    simpa [S] using hg
  calc
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt {z | f z ≤ f x} x) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone D) := by
          simpa [D] using
            helperForTheorem_23_7_euclideanNormalCone_preimage_eq_polar_translatedSublevel f x
    _ =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          polarCone
            (closure
              (((ConvexCone.hull ℝ D) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)))) := by
          exact hpreTranslated
    _ =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          polarCone
            (((dotProductEquiv ℝ (Fin n)) ⁻¹'
              polarCone
                (closure
                  (((ConvexCone.hull ℝ S) : ConvexCone ℝ (Fin n → ℝ)) :
                    Set (Fin n → ℝ)))))) := by
          rw [helperForTheorem_23_7_closure_translatedDirectionCone_eq_vectorizedPolar_subdifferentialCone
            f hproper x hsub hnotmin]
    _ =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          polarCone (((dotProductEquiv ℝ (Fin n)) ⁻¹' polarCone S))) := by
          rw [hinnerSubdiff]
    _ = closure ↑(ConvexCone.hull ℝ S) := by
          exact helperForTheorem_23_7_vectorizedBipolar_eq_closure_convexCone (K := S) hS_nonempty
    _ = closure ↑(ConvexCone.hull ℝ (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))) := by
          simp [S]

/-- Helper for Corollary 23.7.1: if `x` is not a minimizer, then the zero vector cannot be a
Euclidean subgradient at `x`. -/
lemma helperForCorollary_23_7_1_zero_not_mem_vectorizedSubdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (hnotmin : ∃ z, f z < f x) :
    (0 : Fin n → ℝ) ∉ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
  intro hzero
  rcases hnotmin with ⟨z, hzlt⟩
  have hsub : dotProductEquiv ℝ (Fin n) (0 : Fin n → ℝ) ∈ subdifferentialAt f x := hzero
  have hineq : f z ≥ f x := by
    -- The zero subgradient would force `f z ≥ f x` for every `z`, contradicting the witness.
    simpa [IsSubgradientAt] using hsub z
  exact (not_le_of_gt hzlt) hineq

end Section23
end Chap05
