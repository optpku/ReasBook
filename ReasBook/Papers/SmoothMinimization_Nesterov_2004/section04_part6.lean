/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section04_part5

open scoped NNReal

/-- `DualNormDef` is nonnegative. -/
lemma dualNormDef_nonneg' {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Module.Dual ℝ E) : 0 ≤ DualNormDef s := by
  classical
  set S : Set ℝ := { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s x } with hSdef
  have hDual : DualNormDef s = sSup S := by
    unfold DualNormDef
    rw [hSdef.symm]
  by_cases hS : S = ∅
  · have : DualNormDef s = 0 := by simp [hDual, hS, Real.sSup_empty]
    simp [this]
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hS
    rcases hSne with ⟨r, hr⟩
    have hneg : (-r) ∈ S := by
      rcases hr with ⟨x, hx, rfl⟩
      refine ⟨-x, ?_, ?_⟩
      · simpa [norm_neg] using hx
      · simp [DualPairing]
    have hex : ∃ t ∈ S, 0 ≤ t := by
      by_cases hr0 : 0 ≤ r
      · exact ⟨r, hr, hr0⟩
      · have : 0 ≤ -r := by linarith
        exact ⟨-r, hneg, this⟩
    have : 0 ≤ sSup S := Real.sSup_nonneg' hex
    simpa [hDual] using this

set_option maxHeartbeats 400000 in
/-- For the linear map `A'` induced from `A : E1 →L E2*`, `OperatorNormDef` is the supremum of
`DualNormDef` over unit vectors. -/
lemma operatorNormDef_eq_sSup_dualNormDef_of_continuous {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro r x
          ext u
          simp }
    OperatorNormDef A' =
      sSup { r : ℝ | ∃ x : E1, ‖x‖ = 1 ∧ r = DualNormDef (A' x) } := by
  classical
  intro A'
  -- auxiliary sets from the definitions
  set S : Set ℝ :=
      { r : ℝ | ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A' x) u }
  set T : Set ℝ := { r : ℝ | ∃ x : E1, ‖x‖ = 1 ∧ r = DualNormDef (A' x) }
  have hOp : OperatorNormDef A' = sSup S := by
    simp [OperatorNormDef, S]
  have hSbdd : BddAbove S := by
    refine ⟨‖A‖, ?_⟩
    rintro r ⟨x, u, hx, hu, rfl⟩
    have h0 : (A x u) ≤ ‖A x u‖ := by
      simpa [Real.norm_eq_abs] using (le_abs_self (A x u))
    have h1 : ‖A x u‖ ≤ ‖A x‖ * ‖u‖ := by
      simpa using (A x).le_opNorm u
    have h2 : ‖A x‖ ≤ ‖A‖ * ‖x‖ := by
      simpa using A.le_opNorm x
    have h1' : ‖A x u‖ ≤ ‖A x‖ := by
      simpa [hu] using h1
    have h3 : ‖A x‖ ≤ ‖A‖ := by
      simpa [hx] using h2
    have h4 : ‖A x u‖ ≤ ‖A‖ := h1'.trans h3
    exact h0.trans h4
  have hT_nonneg : 0 ≤ sSup T := by
    by_cases hT : T = ∅
    · simp [hT, Real.sSup_empty]
    · have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.2 hT
      rcases hTne with ⟨r, hr⟩
      rcases hr with ⟨x, hx, rfl⟩
      have : 0 ≤ DualNormDef (A' x) := dualNormDef_nonneg' (s := A' x)
      refine Real.sSup_nonneg' ?_
      exact ⟨DualNormDef (A' x), ⟨x, hx, rfl⟩, this⟩
  have hST : sSup S ≤ sSup T := by
    refine Real.sSup_le ?_ hT_nonneg
    intro r hr
    rcases hr with ⟨x, u, hx, hu, rfl⟩
    -- bound `⟪A' x, u⟫` by the corresponding dual norm, then by `sSup T`
    set Sx : Set ℝ := { r : ℝ | ∃ v : E2, ‖v‖ = 1 ∧ r = DualPairing (A' x) v }
    have hSx_bdd : BddAbove Sx := by
      refine ⟨‖A x‖, ?_⟩
      rintro r ⟨v, hv, rfl⟩
      have h0 : (A x v) ≤ ‖A x v‖ := by
        simpa [Real.norm_eq_abs] using (le_abs_self (A x v))
      have h1 : ‖A x v‖ ≤ ‖A x‖ * ‖v‖ := by
        simpa using (A x).le_opNorm v
      have h2 : ‖A x v‖ ≤ ‖A x‖ := by
        simpa [hv] using h1
      exact h0.trans h2
    have hmemSx : DualPairing (A' x) u ∈ Sx := ⟨u, hu, rfl⟩
    have hle_dual : DualPairing (A' x) u ≤ DualNormDef (A' x) := by
      simpa [DualNormDef, Sx] using (le_csSup hSx_bdd hmemSx)
    have hT_bdd : BddAbove T := by
      refine ⟨‖A‖, ?_⟩
      rintro r ⟨x, hx, rfl⟩
      have hdual_le : DualNormDef (A' x) ≤ ‖A x‖ := by
        unfold DualNormDef
        refine Real.sSup_le ?_ (norm_nonneg (A x))
        intro r hr
        rcases hr with ⟨v, hv, rfl⟩
        have h0 : (A x v) ≤ ‖A x v‖ := by
          simpa [Real.norm_eq_abs] using (le_abs_self (A x v))
        have h1 : ‖A x v‖ ≤ ‖A x‖ * ‖v‖ := by
          simpa using (A x).le_opNorm v
        have h2 : ‖A x v‖ ≤ ‖A x‖ := by
          simpa [hv] using h1
        exact h0.trans h2
      have hAx_le : ‖A x‖ ≤ ‖A‖ * ‖x‖ := by
        simpa using A.le_opNorm x
      have hAx_le' : ‖A x‖ ≤ ‖A‖ := by
        simpa [hx] using hAx_le
      exact hdual_le.trans hAx_le'
    have hle_sSupT : DualNormDef (A' x) ≤ sSup T := by
      exact le_csSup hT_bdd ⟨x, hx, rfl⟩
    exact le_trans hle_dual hle_sSupT
  have hTS : sSup T ≤ sSup S := by
    have hS_nonneg : 0 ≤ sSup S := by
      simpa [hOp] using (operatorNormDef_nonneg (A := A'))
    refine Real.sSup_le ?_ hS_nonneg
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    unfold DualNormDef
    refine Real.sSup_le ?_ hS_nonneg
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    have hmemS : DualPairing (A' x) u ∈ S := ⟨x, u, hx, hu, rfl⟩
    exact le_csSup hSbdd hmemS
  exact le_antisymm (by simpa [hOp] using hST) (by simpa [hOp] using hTS)

set_option maxHeartbeats 400000 in
/-- For a continuous bilinear map `A : ℓ¹ → (ℓ¹)*` on finite-dimensional coordinate spaces, the
operator norm `‖A‖_{1,2}` is the maximum absolute entry of the induced matrix. -/
lemma operatorNormDef_eq_maxEntry_l1 (n m : ℕ)
    (A :
      (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) →L[ℝ]
        ((PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) →L[ℝ] ℝ)) :
    let A' :
        (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) →ₗ[ℝ]
          Module.Dual ℝ (PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro r x
          ext u
          simp }
    let AEntry : Fin n → Fin m → ℝ :=
      fun i j =>
        A' (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin n) i)
          (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin m) j)
    let maxEntry : ℝ := sSup { r : ℝ | ∃ i j, r = |AEntry i j| }
    OperatorNormDef A' = maxEntry := by
  classical
  -- unfold the `let`-bindings and introduce names for readability
  dsimp
  set A' :
      (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) →ₗ[ℝ]
        Module.Dual ℝ (PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro r x
        ext u
        simp } with hA'
  set AEntry : Fin n → Fin m → ℝ :=
    fun i j =>
      A' (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin n) i)
        (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin m) j) with hAEntry
  set maxEntry : ℝ := sSup { r : ℝ | ∃ i j, r = |AEntry i j| } with hmaxEntry

  let E1 := PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)
  let E2 := PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)
  let e1 : Fin n → E1 := fun i => PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin n) i
  let e2 : Fin m → E2 := fun j => PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin m) j

  have he1_norm : ∀ i, ‖e1 i‖ = (1 : ℝ) := by
    classical
    intro i
    have hsum :
        (∑ k : Fin n, |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) k|) = (1 : ℝ) := by
      classical
      have h' :
          (∑ k ∈ (Finset.univ : Finset (Fin n)),
                |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) k|) =
              |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) i| := by
        refine
          Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
            (f := fun k : Fin n => |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) k|) i ?_ ?_
        · intro j hj hji
          simp [Pi.single_eq_of_ne hji]
        · intro hi
          simp at hi
      have h'' :
          (∑ k : Fin n, |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) k|) =
              |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) i| := by
        simpa using h'
      -- `Pi.single i 1 i = 1`
      simp [h'', Pi.single_eq_same]
    have hb :
        e1 i = (WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) : E1) := by
      simp [e1, PiLp.basisFun_apply]
    have hnorm0 :
        ‖e1 i‖ = ‖(WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) : E1)‖ :=
      congrArg norm hb
    calc
      ‖e1 i‖ = ‖(WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) : E1)‖ := hnorm0
      _ = ∑ k : Fin n, ‖(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) k‖ := by
          simpa using
            (PiLp.norm_eq_of_L1
              (x :=
                (WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) : E1)))
      _ = ∑ k : Fin n, |(Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) k| := by
          simp [Real.norm_eq_abs]
      _ = (1 : ℝ) := hsum

  have he2_norm : ∀ j, ‖e2 j‖ = (1 : ℝ) := by
    classical
    intro j
    have hsum :
        (∑ k : Fin m, |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) k|) = (1 : ℝ) := by
      classical
      have h' :
          (∑ k ∈ (Finset.univ : Finset (Fin m)),
                |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) k|) =
              |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) j| := by
        refine
          Finset.sum_eq_single (s := (Finset.univ : Finset (Fin m)))
            (f := fun k : Fin m => |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) k|) j ?_ ?_
        · intro l hl hjl
          simp [Pi.single_eq_of_ne hjl]
        · intro hj
          simp at hj
      have h'' :
          (∑ k : Fin m, |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) k|) =
              |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) j| := by
        simpa using h'
      simp [h'', Pi.single_eq_same]
    have hb :
        e2 j = (WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) : E2) := by
      simp [e2, PiLp.basisFun_apply]
    have hnorm0 :
        ‖e2 j‖ = ‖(WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) : E2)‖ :=
      congrArg norm hb
    calc
      ‖e2 j‖ = ‖(WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) : E2)‖ := hnorm0
      _ = ∑ k : Fin m, ‖(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) k‖ := by
          simpa using
            (PiLp.norm_eq_of_L1
              (x :=
                (WithLp.toLp (1 : ENNReal) (Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) : E2)))
      _ = ∑ k : Fin m, |(Pi.single (M := fun _ : Fin m => ℝ) j (1 : ℝ)) k| := by
          simp [Real.norm_eq_abs]
      _ = (1 : ℝ) := hsum

  -- boundedness of the defining sets for `sSup`
  set S : Set ℝ :=
      { r : ℝ |
        ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A' x) u }
  have hSbdd : BddAbove S := by
    refine ⟨‖A‖, ?_⟩
    rintro r ⟨x, u, hx, hu, rfl⟩
    have h0 : (A x u) ≤ ‖A x u‖ := by
      simpa [Real.norm_eq_abs] using (le_abs_self (A x u))
    have h1 : ‖A x u‖ ≤ ‖A x‖ * ‖u‖ := by
      simpa using (A x).le_opNorm u
    have h2 : ‖A x‖ ≤ ‖A‖ * ‖x‖ := by
      simpa using A.le_opNorm x
    have h1' : ‖A x u‖ ≤ ‖A x‖ := by
      simpa [hu] using h1
    have h3 : ‖A x‖ ≤ ‖A‖ := by
      simpa [hx] using h2
    have h4 : ‖A x u‖ ≤ ‖A‖ := h1'.trans h3
    exact h0.trans h4

  set T : Set ℝ := { r : ℝ | ∃ i j, r = |AEntry i j| }
  have hTbdd : BddAbove T := by
    refine ⟨‖A‖, ?_⟩
    rintro r ⟨i, j, rfl⟩
    have h1 : ‖A (e1 i) (e2 j)‖ ≤ ‖A (e1 i)‖ * ‖e2 j‖ := by
      simpa using (A (e1 i)).le_opNorm (e2 j)
    have h2 : ‖A (e1 i)‖ ≤ ‖A‖ * ‖e1 i‖ := by
      simpa using A.le_opNorm (e1 i)
    have h3 : ‖A (e1 i) (e2 j)‖ ≤ ‖A‖ := by
      have : ‖A (e1 i)‖ * ‖e2 j‖ ≤ (‖A‖ * ‖e1 i‖) * ‖e2 j‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg (e2 j))
      have h4' : ‖A (e1 i) (e2 j)‖ ≤ (‖A‖ * ‖e1 i‖) * ‖e2 j‖ := h1.trans this
      simpa [he1_norm i, he2_norm j, mul_assoc] using h4'
    have hAEntry' : AEntry i j = A (e1 i) (e2 j) := by
      -- `A' x u = A x u`
      simp [AEntry, e1, e2, hA']
    simpa [hAEntry', Real.norm_eq_abs] using h3

  have hmaxEntry_nonneg : 0 ≤ maxEntry := by
    by_cases hT : T = ∅
    · simp [hmaxEntry, T, hT]
    · have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.2 hT
      rcases hTne with ⟨r, hr⟩
      rcases hr with ⟨i, j, rfl⟩
      refine Real.sSup_nonneg' ?_
      exact ⟨|AEntry i j|, ⟨i, j, rfl⟩, abs_nonneg _⟩

  have hEntry_le : ∀ i j, |AEntry i j| ≤ maxEntry := by
    intro i j
    have : |AEntry i j| ∈ T := ⟨i, j, rfl⟩
    simpa [hmaxEntry, T, maxEntry] using (le_csSup hTbdd this)

  -- Core bound: matrix entries control the bilinear form on `ℓ¹` via triangle inequality.
  have habs_apply :
      ∀ x : E1, ∀ u : E2, |DualPairing (A' x) u| ≤ maxEntry * ‖x‖ * ‖u‖ := by
    classical
    intro x u
    -- decompose `x` and `u` using `PiLp.basisFun`
    have hx :
        x = ∑ i : Fin n, (x.ofLp i) • (e1 i) := by
      simpa [e1, PiLp.basisFun_repr] using
        (Module.Basis.sum_repr (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin n)) x).symm
    have hu :
        u = ∑ j : Fin m, (u.ofLp j) • (e2 j) := by
      simpa [e2, PiLp.basisFun_repr] using
        (Module.Basis.sum_repr (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin m)) u).symm

    have hx_eval :
        DualPairing (A' x) u =
          ∑ i : Fin n, (x.ofLp i) * DualPairing (A' (e1 i)) u := by
      -- work with sums over `Finset.univ` to use `map_sum` and `Finset.sum_apply` cleanly
      have hx' :
          x = (Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (x.ofLp i) • e1 i) := by
        simpa using hx
      -- unfold `DualPairing` and expand along `x`
      simp only [DualPairing]
      have hL :
          (A' x) u =
            (A' ((Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (x.ofLp i) • e1 i))) u :=
        congrArg (fun y : E1 => (A' y) u) hx'
      -- reduce to a calculation in `Finset`-notation
      have hmap :
          A' ((Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (x.ofLp i) • e1 i)) =
            (Finset.univ : Finset (Fin n)).sum (fun i : Fin n => A' ((x.ofLp i) • e1 i)) := by
        simp
      -- evaluate at `u`
      have hmap_u := congrArg (fun s : Module.Dual ℝ E2 => s u) hmap
      -- rewrite evaluation of sums and scalar multiplication pointwise
      have hsum_apply :
          (((Finset.univ : Finset (Fin n)).sum (fun i : Fin n => A' ((x.ofLp i) • e1 i))) u) =
            (Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (A' ((x.ofLp i) • e1 i)) u) := by
        -- `Finset.sum_apply` expects a sum written with a membership-binder, so use the definitional equality
        simp
      -- finish
      -- `A' (c • v) = c • A' v`, and `(c • s) u = c * s u`
      have :
          (A' x) u =
            (Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (x.ofLp i) * (A' (e1 i)) u) := by
        -- start from `hmap_u` and use `hsum_apply`
        -- normalize the RHS termwise
        have hmap_u' :
            (A' ((Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (x.ofLp i) • e1 i))) u =
              (Finset.univ : Finset (Fin n)).sum (fun i : Fin n => (A' ((x.ofLp i) • e1 i)) u) := by
          exact hmap_u.trans hsum_apply
        -- now rewrite `A' ((x_i) • e1 i)` and simplify scalar evaluation
        -- rewrite the sums in `Finset.sum` form to avoid notation issues
        -- use `hL` to replace the leftmost `A' x` and then simplify
        have := hL.trans hmap_u'
        simpa [smul_eq_mul, LinearMap.map_smulₛₗ] using this
      -- switch back to `∑ i : Fin n` notation and restore `DualPairing`
      simpa [DualPairing] using this

    have hu_eval :
        ∀ i : Fin n,
          DualPairing (A' (e1 i)) u = ∑ j : Fin m, (u.ofLp j) * AEntry i j := by
      intro i
      have hu' : u = (Finset.univ : Finset (Fin m)).sum (fun j : Fin m => (u.ofLp j) • e2 j) := by
        simpa using hu
      -- unfold `DualPairing`
      simp only [DualPairing]
      -- rewrite `u` using its basis expansion
      have hu1 :
          (A' (e1 i)) u =
            (A' (e1 i)) ((Finset.univ : Finset (Fin m)).sum (fun j : Fin m => (u.ofLp j) • e2 j)) :=
        congrArg (fun v : E2 => (A' (e1 i)) v) hu'
      -- expand the sum by linearity
      have hu2 :
          (A' (e1 i)) ((Finset.univ : Finset (Fin m)).sum (fun j : Fin m => (u.ofLp j) • e2 j)) =
            (Finset.univ : Finset (Fin m)).sum (fun j : Fin m => (A' (e1 i)) ((u.ofLp j) • e2 j)) := by
        simp
      -- simplify scalar multiplication in each term and recognize `AEntry`
      have :
          (A' (e1 i)) u =
            (Finset.univ : Finset (Fin m)).sum (fun j : Fin m => (u.ofLp j) * AEntry i j) := by
        -- start from `hu1` and `hu2`
        have : (A' (e1 i)) u =
            (Finset.univ : Finset (Fin m)).sum (fun j : Fin m => (A' (e1 i)) ((u.ofLp j) • e2 j)) :=
          hu1.trans hu2
        -- rewrite the terms
        simpa [AEntry, e1, e2, smul_eq_mul, LinearMap.map_smulₛₗ] using this
      -- convert back to `∑ j : Fin m`
      simpa using this

    have hnormx : ‖x‖ = ∑ i : Fin n, |x.ofLp i| := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_eq_of_L1 (x := x))
    have hnormu : ‖u‖ = ∑ j : Fin m, |u.ofLp j| := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_eq_of_L1 (x := u))

    have hsum_i :
        |∑ i : Fin n, (x.ofLp i) * DualPairing (A' (e1 i)) u| ≤
          ∑ i : Fin n, |(x.ofLp i) * DualPairing (A' (e1 i)) u| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (f := fun i : Fin n =>
          (x.ofLp i) * DualPairing (A' (e1 i)) u) (s := (Finset.univ : Finset (Fin n))))

    have hsum_j :
        ∀ i : Fin n,
          |DualPairing (A' (e1 i)) u| ≤ maxEntry * ‖u‖ := by
      intro i
      have h1 :
          |DualPairing (A' (e1 i)) u| ≤
            ∑ j : Fin m, |(u.ofLp j) * AEntry i j| := by
        simpa [hu_eval i] using
          (Finset.abs_sum_le_sum_abs (f := fun j : Fin m => (u.ofLp j) * AEntry i j)
            (s := (Finset.univ : Finset (Fin m))))
      have h2 :
          (∑ j : Fin m, |(u.ofLp j) * AEntry i j|) ≤
            ∑ j : Fin m, (|u.ofLp j| * maxEntry) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hij : |AEntry i j| ≤ maxEntry := hEntry_le i j
        -- `|u_j * A_ij| = |u_j| * |A_ij|`
        have : |(u.ofLp j) * AEntry i j| = |u.ofLp j| * |AEntry i j| := by
          simp [abs_mul]
        -- compare with `|u_j| * maxEntry`
        simpa [this] using mul_le_mul_of_nonneg_left hij (abs_nonneg _)
      have h3 :
          (∑ j : Fin m, |u.ofLp j| * maxEntry) = maxEntry * ∑ j : Fin m, |u.ofLp j| := by
        simp [Finset.mul_sum, mul_comm]
      have h4 : maxEntry * ∑ j : Fin m, |u.ofLp j| = maxEntry * ‖u‖ := by
        simp [hnormu]
      exact le_trans h1 (le_trans h2 (by simp [h3, h4]))

    -- combine bounds in `i`
    have hsum_i' :
        ∑ i : Fin n, |(x.ofLp i) * DualPairing (A' (e1 i)) u| ≤
          ∑ i : Fin n, |x.ofLp i| * (maxEntry * ‖u‖) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi' : |(x.ofLp i) * DualPairing (A' (e1 i)) u| = |x.ofLp i| * |DualPairing (A' (e1 i)) u| := by
        simp [abs_mul]
      -- use the bound on `|⟪A'(e1 i),u⟫|`
      have := mul_le_mul_of_nonneg_left (hsum_j i) (abs_nonneg (x.ofLp i))
      -- rewrite
      simpa [hi', mul_assoc, mul_left_comm, mul_comm] using this

    have hsum_i'' :
        (∑ i : Fin n, |x.ofLp i| * (maxEntry * ‖u‖)) =
          maxEntry * ‖u‖ * ∑ i : Fin n, |x.ofLp i| := by
      -- commute factors to use `Finset.mul_sum`
      calc
        (∑ i : Fin n, |x.ofLp i| * (maxEntry * ‖u‖)) =
            ∑ i : Fin n, (maxEntry * ‖u‖) * |x.ofLp i| := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring_nf
        _ = (maxEntry * ‖u‖) * ∑ i : Fin n, |x.ofLp i| := by
              simp [Finset.mul_sum]
        _ = maxEntry * ‖u‖ * ∑ i : Fin n, |x.ofLp i| := by ring

    have hfinal :
        |∑ i : Fin n, (x.ofLp i) * DualPairing (A' (e1 i)) u| ≤
          maxEntry * ‖u‖ * ∑ i : Fin n, |x.ofLp i| := by
      have := le_trans hsum_i hsum_i'
      simpa [hsum_i''] using this

    -- conclude
    have hrew :
        maxEntry * ‖u‖ * ∑ i : Fin n, |x.ofLp i| = maxEntry * ‖x‖ * ‖u‖ := by
      simp [hnormx, mul_assoc, mul_left_comm, mul_comm]
    simpa [hx_eval, hrew, mul_assoc, mul_left_comm, mul_comm] using hfinal

  have hop_le : OperatorNormDef A' ≤ maxEntry := by
    unfold OperatorNormDef
    refine Real.sSup_le ?_ hmaxEntry_nonneg
    intro r hr
    rcases hr with ⟨x, u, hx, hu, rfl⟩
    have hle : DualPairing (A' x) u ≤ |DualPairing (A' x) u| := le_abs_self _
    have hbound : |DualPairing (A' x) u| ≤ maxEntry := by
      have := habs_apply x u
      simpa [hx, hu] using this
    exact hle.trans hbound

  have hop_ge : maxEntry ≤ OperatorNormDef A' := by
    -- each entry is realized on (signed) basis vectors
    have hOp_nonneg : 0 ≤ OperatorNormDef A' := operatorNormDef_nonneg (A := A')
    unfold maxEntry
    refine Real.sSup_le ?_ hOp_nonneg
    intro r hr
    rcases hr with ⟨i, j, rfl⟩
    -- show `|AEntry i j| ≤ OperatorNormDef A'`
    have hmem :
        |AEntry i j| ∈
          { r : ℝ |
            ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A' x) u } := by
      by_cases hij : 0 ≤ AEntry i j
      · refine ⟨e1 i, e2 j, ?_, ?_, ?_⟩
        · simp [he1_norm i]
        · simp [he2_norm j]
        · -- `|AEntry i j| = AEntry i j = ⟪A'(e1 i), e2 j⟫`
          have hval : DualPairing (A' (e1 i)) (e2 j) = AEntry i j := by
            simp [DualPairing, AEntry, e1, e2]
          calc
            |AEntry i j| = AEntry i j := abs_of_nonneg hij
            _ = DualPairing (A' (e1 i)) (e2 j) := hval.symm
      · have hij' : AEntry i j < 0 := lt_of_not_ge hij
        refine ⟨-e1 i, e2 j, ?_, ?_, ?_⟩
        · simp [he1_norm i]
        · simp [he2_norm j]
        · -- `⟪A' (-e1 i), e2 j⟫ = -AEntry i j = |AEntry i j|`
          have hneg : DualPairing (A' (-e1 i)) (e2 j) = -AEntry i j := by
            simp [DualPairing, AEntry, e1, e2]
          calc
            |AEntry i j| = -AEntry i j := abs_of_neg hij'
            _ = DualPairing (A' (-e1 i)) (e2 j) := hneg.symm
    have :
        |AEntry i j| ≤
          sSup
            { r : ℝ |
              ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A' x) u } :=
      le_csSup hSbdd hmem
    simpa [OperatorNormDef] using this

  -- return to the original goal, rewriting `maxEntry` back from the auxiliary set `T`
  have hmax : maxEntry = sSup T := by
    simpa [T] using hmaxEntry
  calc
    OperatorNormDef A' = sSup T := le_antisymm hop_le hop_ge
    _ = maxEntry := by
        exact hmax.symm
