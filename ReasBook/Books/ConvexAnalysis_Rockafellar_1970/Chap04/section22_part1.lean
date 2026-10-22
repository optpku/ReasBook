/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part12

section Chap04
section Section22

/-- Helper for Theorem 22.1: convert the `EReal` dual margin inequality from Theorem 21.4
into an ordinary real inequality over the finite support. -/
lemma helperForTheorem_22_1_dualMargin_realForm
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    (lam : Fin m →₀ ℝ) (ε : ℝ)
    (hmargin : ∀ x : Fin n → ℝ,
      ((ε : ℝ) : EReal) ≤
        Finset.sum lam.support
          (fun i => ((lam i : ℝ) : EReal) * ((((dotProduct (a i) x - α i : ℝ)) : EReal)))) :
    ∀ x : Fin n → ℝ,
      ε ≤ Finset.sum lam.support (fun i => lam i * (dotProduct (a i) x - α i)) := by
  intro x
  -- Rewrite the `EReal` weighted sum as the coercion of a real-valued weighted sum.
  have hsumE :
      Finset.sum lam.support
          (fun i => ((lam i : ℝ) : EReal) * ((((dotProduct (a i) x - α i : ℝ)) : EReal))) =
        (((Finset.sum lam.support
            (fun i => lam i * (dotProduct (a i) x - α i)) : ℝ)) : EReal) := by
    rw [helperForTheorem_21_1_coe_finset_sum_real]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [EReal.coe_mul]
  -- After the coercion rewrite, `exact_mod_cast` returns to the real inequality.
  have hx := hmargin x
  rw [hsumE] at hx
  exact_mod_cast hx

/-- Helper for Theorem 22.1: a dual margin certificate for the affine family yields the
classical nonnegative linear multiplier certificate. -/
lemma helperForTheorem_22_1_dualMargin_to_linearCertificate
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    (lam : Fin m →₀ ℝ) (ε : ℝ)
    (hlamNonneg : ∀ i : Fin m, 0 ≤ lam i)
    (hε : 0 < ε)
    (hmargin : ∀ x : Fin n → ℝ,
      ε ≤ Finset.sum lam.support (fun i => lam i * (dotProduct (a i) x - α i))) :
    ∃ l : Fin m → ℝ, 0 ≤ l ∧ (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0 := by
  let s : Fin n → ℝ := Finset.sum lam.support (fun i => lam i • a i)
  let c : ℝ := Finset.sum lam.support (fun i => lam i * α i)
  -- Package the weighted linear terms as a single dot product against the summed normal.
  have hsum_dot : ∀ x : Fin n → ℝ,
      Finset.sum lam.support (fun i => lam i * dotProduct (a i) x) = dotProduct s x := by
    intro x
    calc
      Finset.sum lam.support (fun i => lam i * dotProduct (a i) x)
          = Finset.sum lam.support (fun i => dotProduct (lam i • a i) x) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul]
      _ = dotProduct (Finset.sum lam.support (fun i => lam i • a i)) x := by
            symm
            simpa using
              (sum_dotProduct (s := lam.support) (u := fun i => lam i • a i) (v := x))
      _ = dotProduct s x := by
            rfl
  -- The support sum is therefore an affine function `x ↦ ⟪s,x⟫ - c`.
  have hsum_margin : ∀ x : Fin n → ℝ,
      Finset.sum lam.support (fun i => lam i * (dotProduct (a i) x - α i)) =
        dotProduct s x - c := by
    intro x
    calc
      Finset.sum lam.support (fun i => lam i * (dotProduct (a i) x - α i))
          = Finset.sum lam.support (fun i => (lam i * dotProduct (a i) x) - (lam i * α i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = Finset.sum lam.support (fun i => lam i * dotProduct (a i) x) -
            Finset.sum lam.support (fun i => lam i * α i) := by
              rw [Finset.sum_sub_distrib]
      _ = dotProduct s x - c := by
            simp [hsum_dot, c]
  -- Evaluating at `x = 0` forces the scalar part to be strictly negative.
  have hc_neg : c < 0 := by
    have h0 := hmargin 0
    rw [hsum_margin 0] at h0
    simp [c] at h0
    linarith
  -- If the summed normal were nonzero, evaluating on a suitable multiple of itself would
  -- violate the global lower bound. Hence the summed normal must vanish.
  have hs_zero : s = 0 := by
    by_contra hs_ne
    have hss_nonneg : 0 ≤ dotProduct s s := dotProduct_self_nonneg (v := s)
    have hss_ne : dotProduct s s ≠ 0 := by
      intro hzero
      exact hs_ne ((dotProduct_self_eq_zero (v := s)).1 hzero)
    let t : ℝ := (c + ε - 1) / dotProduct s s
    have ht_eval := hmargin (t • s)
    rw [hsum_margin (t • s)] at ht_eval
    have hdot_t : dotProduct s (t • s) - c = ε - 1 := by
      calc
        dotProduct s (t • s) - c = t * dotProduct s s - c := by
          simp
        _ = ε - 1 := by
              dsimp [t]
              field_simp [hss_ne]
              ring
    rw [hdot_t] at ht_eval
    linarith
  -- Finally, expand the `Finsupp` support sums back to finite-type sums over `Fin m`.
  have hsupport_vec_to_univ : s = ∑ i : Fin m, lam i • a i := by
    calc
      s = Finset.sum lam.support (fun i => lam i • a i) := by
            rfl
      _ = lam.sum (fun i coeff => coeff • a i) := by
            rfl
      _ = ∑ i : Fin m, lam i • a i := by
            simpa using
              (Finsupp.sum_fintype lam (fun i coeff => coeff • a i) (by intro i; simp))
  have hsupport_scalar_to_univ : c = ∑ i : Fin m, lam i * α i := by
    calc
      c = Finset.sum lam.support (fun i => lam i * α i) := by
            rfl
      _ = lam.sum (fun i coeff => coeff * α i) := by
            rfl
      _ = ∑ i : Fin m, lam i * α i := by
            simpa using
              (Finsupp.sum_fintype lam (fun i coeff => coeff * α i) (by intro i; simp))
  refine ⟨fun i => lam i, ?_, ?_, ?_⟩
  · intro i
    exact hlamNonneg i
  · simpa [hsupport_vec_to_univ] using hs_zero
  · simpa [hsupport_scalar_to_univ] using hc_neg

/-- Helper for Theorem 22.1: a feasible point and a negative nonnegative-multiplier
certificate cannot coexist. -/
lemma helperForTheorem_22_1_certificate_excludes_feasible
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ i : Fin m, dotProduct (a i) x ≤ α i)
    {l : Fin m → ℝ}
    (hl_nonneg : 0 ≤ l)
    (hsum_zero : (∑ i, l i • a i) = 0)
    (hscalar_neg : (∑ i, l i * α i) < 0) : False := by
  -- Multiply each inequality by the corresponding nonnegative coefficient and sum.
  have hweighted :
      ∑ i : Fin m, l i * dotProduct (a i) x ≤ ∑ i : Fin m, l i * α i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx i) (hl_nonneg i)
  -- The left-hand sum is the dot product against the certificate's summed normal.
  have hdot_sum :
      ∑ i : Fin m, l i * dotProduct (a i) x = dotProduct (∑ i : Fin m, l i • a i) x := by
    calc
      ∑ i : Fin m, l i * dotProduct (a i) x
          = ∑ i : Fin m, dotProduct (l i • a i) x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul]
      _ = dotProduct (∑ i : Fin m, l i • a i) x := by
            symm
            simpa using
              (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
                (u := fun i => l i • a i) (v := x))
  -- The vanishing normal sum turns the weighted left side into `0`, contradicting negativity.
  have hscalar_nonneg : 0 ≤ ∑ i : Fin m, l i * α i := by
    have hleft_nonneg : 0 ≤ ∑ i : Fin m, l i * dotProduct (a i) x := by
      rw [hdot_sum, hsum_zero]
      simp
    exact le_trans hleft_nonneg hweighted
  linarith

-- Proof sketch: this is the classical Farkas alternative for a finite system of linear
-- inequalities. Show first that a feasible point `x` and a nonnegative multiplier vector
-- `λ` with `∑ i, λ i • a i = 0` and `∑ i, λ i * α i < 0` cannot coexist by taking the
-- weighted sum of the inequalities. Then obtain existence of one alternative from the
-- separating-hyperplane form developed in the preceding section.
/-- Theorem 22.1: Let `a_i ∈ ℝ^n` and `α_i ∈ ℝ` for `i = 1, ..., m`. Exactly one of the
following alternatives holds: (a) there exists `x ∈ ℝ^n` such that `⟪a_i, x⟫ ≤ α_i` for
every `i`; (b) there exist nonnegative real numbers `λ_1, ..., λ_m` such that
`∑ i, λ_i a_i = 0` and `∑ i, λ_i α_i < 0`. -/
theorem farkasAlternative_linearInequalities
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) :
    ((∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i) ∨
        ∃ l : Fin m → ℝ, 0 ≤ l ∧ (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0) ∧
      ¬((∃ x : Fin n → ℝ, ∀ i, dotProduct (a i) x ≤ α i) ∧
        ∃ l : Fin m → ℝ, 0 ≤ l ∧ (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0) := by
  let f : Fin m → (Fin n → ℝ) → EReal :=
    fun i x => (((dotProduct x (a i) - α i : ℝ) : EReal))
  -- Route correction: use Theorem 21.4's affine-family alternative directly; the stronger
  -- Chapter 21 route is not needed once these inequalities are encoded as affine `EReal` maps.
  have hfProper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) := by
    intro i
    let g : AffineMap ℝ (Fin n → ℝ) ℝ :=
      (dotProductLinear n (a i)).toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (α i)
    -- Each inequality function is affine, hence proper convex on all of `ℝⁿ`.
    simpa [f, g, dotProductLinear] using
      helperForTheorem_21_2_shifted_affine_properConvex (n := n) g 0
  have hfClosed :
      ∀ i : Fin m, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)} := by
    intro i
    let g : AffineMap ℝ (Fin n → ℝ) ℝ :=
      (dotProductLinear n (a i)).toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (α i)
    -- The epigraph of each affine function is closed.
    simpa [f, g, dotProductLinear] using
      helperForTheorem_21_4_affine_ereal_epigraph_closed (n := n) g
  have hWeaker :
      ∃ I0 : Finset (Fin m),
        (∀ i : Fin m, i ∈ I0 →
          ∃ g : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (g x : EReal)) ∧
        (∀ d : Fin n → ℝ,
          (∀ i : Fin m, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
            ∀ i : Fin m, i ∉ I0 →
              ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x) := by
    refine ⟨Finset.univ, ?_⟩
    constructor
    · intro i hi
      let g : AffineMap ℝ (Fin n → ℝ) ℝ :=
        (dotProductLinear n (a i)).toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (α i)
      -- With `I₀ = univ`, every member lies in the affine block.
      refine ⟨g, ?_⟩
      intro x
      simp [f, g, dotProductLinear]
    · intro d hmono i hi
      -- Outside `univ` there are no indices, so the constancy clause is vacuous.
      exfalso
      exact hi (by simp)
  have h21_4 := theorem21_4_univ_weaker_recession_hypothesis
    (n := n) (I := Fin m) f hfProper hfClosed hWeaker
  dsimp at h21_4
  have hxor := h21_4.1.1
  rw [xor_def] at hxor
  refine ⟨?_, ?_⟩
  · rcases hxor with hPrimal | hDual
    · left
      rcases hPrimal with ⟨⟨x, hx⟩, _⟩
      -- Translate the nonpositive `EReal` inequalities back to the original real system.
      refine ⟨x, ?_⟩
      intro i
      have hxi : (((dotProduct x (a i) - α i : ℝ) : EReal)) ≤ (0 : EReal) := hx i
      have hxi' : dotProduct x (a i) - α i ≤ 0 := by
        exact_mod_cast hxi
      linarith [show dotProduct x (a i) = dotProduct (a i) x by simp [dotProduct_comm]]
    · right
      rcases hDual with ⟨hDual, _⟩
      rcases hDual with ⟨lam, hlamNonneg, ε, hε, hmargin⟩
      -- Reorder the dot products, then convert the abstract dual margin into the textbook
      -- multiplier certificate.
      have hmargin' : ∀ x : Fin n → ℝ,
          ((ε : ℝ) : EReal) ≤
            Finset.sum lam.support
              (fun i => ((lam i : ℝ) : EReal) * ((((dotProduct (a i) x - α i : ℝ)) : EReal))) := by
        intro x
        simpa [f, dotProduct_comm] using hmargin x
      have hrealMargin := helperForTheorem_22_1_dualMargin_realForm a α lam ε hmargin'
      exact
        helperForTheorem_22_1_dualMargin_to_linearCertificate
          a α lam ε hlamNonneg hε hrealMargin
  · intro hBoth
    rcases hBoth with ⟨⟨x, hx⟩, l, hl_nonneg, hsum_zero, hscalar_neg⟩
    -- The easy weighted-sum contradiction discharges exclusivity of the two alternatives.
    exact
      helperForTheorem_22_1_certificate_excludes_feasible
        a α hx hl_nonneg hsum_zero hscalar_neg

end Section22
end Chap04
