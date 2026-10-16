module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.SecondPivots
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.MidpointRows5

@[expose] public section

namespace ConsensusADMM
namespace Period48
namespace FractionFree

/-- Row `16 * c + k` of the matrix reached after forty-eight elimination steps is the
corresponding row of the recorded intermediate stage. -/
lemma stageMidRow (c : Fin 6) (k : Fin 16) :
    (fun j : Fin 96 => (runFromAt 0 j0 48).1 ⟨k.val + 16 * c.val, by omega⟩ j) =
      (fun j : Fin 96 => stageMid ⟨k.val + 16 * c.val, by omega⟩ j) := by
  -- Read the row off the kernel-checked block of sixteen rows containing it.
  fin_cases c
  · exact congrFun (List.ofFn_inj.mp stageMidBlockFst_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockSnd_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockThird_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockForth_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockFifth_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockSixth_checked) k

/-- The matrix reached after the first forty-eight elimination steps is the recorded
intermediate stage. -/
lemma stageMid_eq : (runFromAt 0 j0 48).1 = stageMid := by
  -- Decompose an arbitrary row index into its block of sixteen rows and its position in
  -- that block, and read the corresponding row comparison off `stageMidRow`.
  funext i j
  have hdecomp : i = (⟨i.val % 16 + 16 * (i.val / 16), by omega⟩ : Fin 96) :=
    Fin.ext (Nat.mod_add_div i.val 16).symm
  rw [hdecomp]
  exact congrFun (stageMidRow ⟨i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩) j



/-- The diagonal pivots of the elimination are the recorded ones. -/
lemma pivotsComputed_eq : pivotsComputed = List.ofFn pivotTable := by
  -- The run of ninety-six steps splits after forty-eight steps, and each half is identified
  -- with the corresponding half of the recorded pivots by the kernel checks above.
  have hsplit : (runFromAt 0 j0 96).2 =
      (runFromAt 0 j0 48).2 ++ (runFromAt 48 (runFromAt 0 j0 48).1 48).2 :=
    runFromAt_snd_add 0 48 48 j0
  rw [pivotsComputed, pivotsRun, hsplit, pivotsFirstHalf_eq, stageMid_eq,
    pivotsSecondHalf_eq, List.take_append_drop]

/-- The matrix reached by the elimination after `n` steps is the `n`-th elimination stage. -/
lemma pivotsRun_fst (n : ℕ) (hn : n < 96) : (pivotsRun n).1 = stage ⟨n, hn⟩ := by
  -- Each step of the run is a step of the stage recursion, so one unfolding of both
  -- recursions compares the two matrices.
  induction n with
  | zero => rfl
  | succ n ih =>
      -- Unfold one step of the run and identify its matrix with the stage reached after `n`
      -- steps; the two recursions are then the same function of that matrix.
      rw [show (pivotsRun (n + 1)).1 = bareissStep n (pivotsRun n).1 from rfl, ih (by omega)]
      simp only [stage, stage.go.eq_2]
      rfl

/-- The collected pivots are exactly the pivots taken at the steps already performed, in
the order in which they were taken. -/
lemma pivotsRun_snd (n : ℕ) :
    (pivotsRun n).2 =
      (List.range n).map (fun m ↦ (pivotsRun m).1 (Fin.ofNat 96 m) (Fin.ofNat 96 m)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show (pivotsRun (n + 1)).2 =
        (pivotsRun n).2 ++ [(pivotsRun n).1 (Fin.ofNat 96 n) (Fin.ofNat 96 n)] from rfl, ih]
      simp only [List.range_succ, List.map_append, List.map_singleton]

/-- The `m`-th collected pivot is the diagonal pivot of the `m`-th elimination stage. -/
lemma pivotsRun_getElem? (m : ℕ) (hm : m < 96) :
    (pivotsRun 96).2[m]? = some (pivot ⟨m, hm⟩) := by
  -- Read the entry off the collected list and identify the stage reached after `m` steps.
  rw [pivotsRun_snd, List.getElem?_map, List.getElem?_range hm, Option.map_some]
  congr 1
  rw [pivotsRun_fst m hm,
    show Fin.ofNat 96 m = (⟨m, hm⟩ : Fin 96) from Fin.ext (Nat.mod_eq_of_lt hm)]
  rfl

/-- The `k`-th collected pivot is the `k`-th recorded pivot. -/
lemma pivotsComputed_getElem? (k : Fin 96) :
    pivotsComputed[k.val]? = some (pivot k) := by
  -- The collected list is the run's list, and the `k`-th entry of that list is the `k`-th
  -- diagonal pivot.
  rw [pivotsComputed, pivotsRun_getElem? k.val k.isLt]

/-- The `k`-th pivot of the fraction-free elimination is the `k`-th recorded pivot. -/
lemma pivot_eq_table (k : Fin 96) : pivot k = pivotTable k := by
  -- Compare the recorded literals with the collected pivots through the closed kernel
  -- check and read off the entry at the index `k`.
  have h := pivotsComputed_getElem? k
  rw [pivotsComputed_eq] at h
  simp only [List.getElem?_ofFn, dif_pos k.isLt] at h
  have h' : pivotTable ⟨k.val, k.isLt⟩ = pivot k := Option.some.inj h
  exact h'.symm

/-- Every leading principal minor of the integer matrix `2K - I₉₆` is strictly
positive.

This is the numeric content of the fraction-free definiteness certificate: the appendix
computes the leading principal determinants of `2K - I₉₆` and finds each of them at least
`1`, which the exact-division identity `previousPivot_dvd_update` turns into the strictly
positive fraction-free pivots. -/
lemma principal_det_pos (k : Fin 96) : 0 < (principal k).det := by
  -- The pivot is the determinant of the leading principal submatrix, and the recorded
  -- literals show that every pivot is positive.
  rw [← pivot_eq_det, pivot_eq_table k]
  fin_cases k <;> decide

/-- Every pivot of the fraction-free elimination of `2K - I₉₆` is at least `1`. -/
theorem one_le_pivot (k : Fin 96) : 1 ≤ pivot k := by
  -- The pivot is the determinant of the leading principal submatrix, which the
  -- certificate shows to be a strictly positive integer.
  rw [pivot_eq_det]
  have h := principal_det_pos k
  omega

-- ---------------------------------------------------------------------------------------
-- The `LDLᵀ` certificate behind the definiteness of `2K - I₉₆`.
--
-- The elimination stages are leading bordered minors (`stage_eq_borderedMinor`), so the
-- definiteness of `2K - I₉₆` can be read off from the sequence of leading principal
-- minors rather than from the integer elimination itself (whose pivots have up to 771
-- bits).  The lemmas below build the resulting `ldlL * diagonal ldlD * ldlLᵀ`
-- factorization purely algebraically: the multiplier `ldlL i k` is the bordered minor of
-- the rows `{0, …, k - 1, i}` and the columns `{0, …, k - 1, k}` divided by the `k`-th
-- leading principal minor, and the diagonal entry `ldlD k` is the quotient of consecutive
-- leading principal minors.  The residual identity `ldlResidual_eq` shows by induction on
-- `m` that after `m` outer-product terms the remainder is the level-`m` bordered minor
-- divided by the preceding leading principal minor, its successor step being Dodgson's
-- condensation identity `borderedMinor_dodgson`.  The factorization `j0_map_eq_ldl` then
-- follows by stopping the expansion at `min i j`.
-- ---------------------------------------------------------------------------------------
/-- The leading principal minor of `2K - I₉₆` through coordinate `k`, which is also the
`k`-th pivot of the fraction-free elimination, as a real number. -/
def beta (k : Fin 96) : ℝ := (borderedMinor k k k : ℝ)

/-- Every leading principal minor of `2K - I₉₆` is strictly positive. -/
lemma beta_pos (k : Fin 96) : 0 < beta k := by
  rw [beta, borderedMinor_self]
  exact_mod_cast principal_det_pos k

/-- Every leading principal minor of `2K - I₉₆` is nonzero. -/
lemma beta_ne_zero (k : Fin 96) : beta k ≠ 0 := ne_of_gt (beta_pos k)

/-- The leading principal minor at the first coordinate is the entry `(0, 0)` of
`2K - I₉₆`. -/
lemma beta_zero :
    beta (⟨0, by omega⟩ : Fin 96) =
      (j0 (⟨0, by omega⟩ : Fin 96) (⟨0, by omega⟩ : Fin 96) : ℝ) := by
  rw [beta]
  exact congrArg (fun z : ℤ ↦ (z : ℝ))
    (borderedMinor_zero (⟨0, by omega⟩ : Fin 96) (⟨0, by omega⟩ : Fin 96))

/-- The real level-zero bordered minor is the corresponding entry of `2K - I₉₆`. -/
lemma borderedMinor_zero_cast (x y : Fin 96) :
    (borderedMinor (⟨0, by omega⟩ : Fin 96) x y : ℝ) = (j0 x y : ℝ) :=
  congrArg (fun z : ℤ ↦ (z : ℝ)) (borderedMinor_zero x y)

/-- A bordered minor is unchanged when its two border coordinates are exchanged. -/
lemma borderedMinor_comm (k r c : Fin 96) : borderedMinor k r c = borderedMinor k c r := by
  rw [borderedMinor_apply, borderedMinor_apply, ← Matrix.det_transpose,
    Matrix.transpose_submatrix, Matrix.IsSymm.eq j0_isSymm]

/-- The unit lower-triangular factor of the `LDLᵀ` decomposition of `2K - I₉₆`: its
`(i, k)` entry is the bordered minor of the rows `{0, …, k - 1, i}` and the columns
`{0, …, k - 1, k}` divided by the `k`-th leading principal minor, and is zero above the
diagonal. -/
noncomputable def ldlL : Matrix (Fin 96) (Fin 96) ℝ :=
  fun i k ↦ if k ≤ i then (borderedMinor k i k : ℝ) / beta k else 0

/-- The diagonal factor of the `LDLᵀ` decomposition of `2K - I₉₆`: the quotient of
consecutive leading principal minors, with the value `1` at the first coordinate. -/
noncomputable def ldlD (k : Fin 96) : ℝ :=
  beta k / (if k.val = 0 then 1 else beta ⟨k.val - 1, by omega⟩)

/-- Every entry of the diagonal factor of the `LDLᵀ` decomposition is strictly positive. -/
lemma ldlD_pos (k : Fin 96) : 0 < ldlD k := by
  rw [ldlD]
  by_cases h : k.val = 0
  · rw [if_pos h, div_one]
    exact beta_pos k
  · rw [if_neg h]
    exact div_pos (beta_pos k) (beta_pos _)

/-- The unit lower-triangular factor of the `LDLᵀ` decomposition has unit diagonal. -/
lemma ldlL_self (k : Fin 96) : ldlL k k = 1 := by
  rw [ldlL, if_pos le_rfl]
  exact div_self (beta_ne_zero k)

/-- The unit lower-triangular factor of the `LDLᵀ` decomposition vanishes strictly above
the diagonal. -/
lemma ldlL_eq_zero_of_lt (i k : Fin 96) (h : i < k) : ldlL i k = 0 := by
  rw [ldlL, if_neg (not_le.mpr h)]

/-- The sum of the first `m` outer-product terms of the `LDLᵀ` decomposition of
`2K - I₉₆`. -/
noncomputable def ldlPartialSum (m : ℕ) (i j : Fin 96) : ℝ :=
  ∑ k : Fin 96, if k.val < m then ldlL i k * ldlD k * ldlL j k else 0

/-- The residual of the `LDLᵀ` decomposition of `2K - I₉₆` after `m` terms: the difference
between the entry of the matrix and the first `m` outer-product terms. -/
noncomputable def ldlResidual (m : ℕ) (i j : Fin 96) : ℝ :=
  (j0 i j : ℝ) - ldlPartialSum m i j

/-- Passing from `m` to `m + 1` terms of the `LDLᵀ` decomposition adds the single
outer-product term indexed by `⟨m⟩`. -/
lemma ldlPartialSum_succ (m : ℕ) (hm : m < 96) (i j : Fin 96) :
    ldlPartialSum (m + 1) i j =
      ldlPartialSum m i j + ldlL i ⟨m, hm⟩ * ldlD ⟨m, hm⟩ * ldlL j ⟨m, hm⟩ := by
  have hsplit : ldlPartialSum (m + 1) i j =
      ldlPartialSum m i j +
        ∑ k : Fin 96, if k = (⟨m, hm⟩ : Fin 96) then
          ldlL i k * ldlD k * ldlL j k else 0 := by
    rw [ldlPartialSum, ldlPartialSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases lt_trichotomy k.val m with h | h | h
    · have hk : ¬ k = (⟨m, hm⟩ : Fin 96) :=
        fun hkm ↦ (by omega : k.val ≠ m) (by rw [hkm])
      rw [if_pos (by omega), if_pos h, if_neg hk]
      ring
    · rw [if_pos (by omega), if_neg (by omega : ¬ k.val < m), if_pos (Fin.ext h)]
      ring
    · have hk : ¬ k = (⟨m, hm⟩ : Fin 96) :=
        fun hkm ↦ (by omega : k.val ≠ m) (by rw [hkm])
      rw [if_neg (by omega : ¬ k.val < m + 1), if_neg (by omega : ¬ k.val < m), if_neg hk]
      ring
  rw [hsplit, Finset.sum_ite_eq' Finset.univ]
  simp

/-- The residual of the `LDLᵀ` decomposition after `m + 1` terms is the residual after `m`
terms with the `⟨m⟩`-th outer-product term removed. -/
lemma ldlResidual_succ (m : ℕ) (hm : m < 96) (i j : Fin 96) :
    ldlResidual (m + 1) i j =
      ldlResidual m i j - ldlL i ⟨m, hm⟩ * ldlD ⟨m, hm⟩ * ldlL j ⟨m, hm⟩ := by
  rw [ldlResidual, ldlResidual, ldlPartialSum_succ m hm i j]
  ring

/-- The residual of the `LDLᵀ` decomposition before any term is removed is the entry of
`2K - I₉₆` itself. -/
lemma ldlResidual_zero (i j : Fin 96) : ldlResidual 0 i j = (j0 i j : ℝ) := by
  rw [ldlResidual, ldlPartialSum]
  simp

/-- Combining two real fractions with nested denominators. -/
lemma div_sub_mul_div_eq (a b c p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    a / p - b * c / (q * p) = (a * q - b * c) / (p * q) := by
  field_simp

/-- Clearing the denominator of a single removal step of the `LDLᵀ` decomposition. -/
lemma sub_div_mul_mul_div (a x y c : ℝ) (hc : c ≠ 0) :
    a - x / c * c * (y / c) = (c * a - y * x) / c := by
  field_simp

/-- A real fraction whose numerator is a product that factors through `p`. -/
lemma mul_div_mul_div_eq_div (A b c p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : A * p = b * c) : b * c / (p * q) = A / q := by
  rw [← h]
  field_simp

/-- The residual of the `LDLᵀ` decomposition of `2K - I₉₆` after `m` terms is the bordered
minor at level `m` divided by the preceding leading principal minor. -/
lemma ldlResidual_eq (m : ℕ) :
    ∀ (hm : m < 96) (i j : Fin 96), m ≤ i.val → m ≤ j.val →
      ldlResidual m i j = (borderedMinor ⟨m, hm⟩ i j : ℝ) /
        (if m = 0 then 1 else beta ⟨m - 1, by omega⟩) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm i j hi hj
    rcases m with _ | _ | k
    · -- Level zero: the residual is the entry of `2K - I₉₆` itself.
      have hz : (0 : ℕ) = 0 := rfl
      rw [ldlResidual_zero, if_pos hz, div_one]
      exact (congrArg (fun z : ℤ ↦ (z : ℝ)) (borderedMinor_zero i j)).symm
    · -- Level one: the divisor is the first pivot and the removed term carries the
      -- leading `2 × 2` minor, so the residual is a single fraction identity.
      have hstep := ldlResidual_succ 0 (by omega) i j
      have hz1 : ¬ (0 + 1 : ℕ) = 0 := by omega
      have hidx0 : (⟨0 + 1 - 1, by omega⟩ : Fin 96) = (⟨0, by omega⟩ : Fin 96) :=
        Fin.ext (by show 0 + 1 - 1 = 0; omega)
      rw [hstep, ldlResidual_zero, if_neg hz1, hidx0]
      have hL : ∀ x : Fin 96, ldlL x (⟨0, by omega⟩ : Fin 96) =
          (j0 x (⟨0, by omega⟩ : Fin 96) : ℝ) /
            (j0 (⟨0, by omega⟩ : Fin 96) (⟨0, by omega⟩ : Fin 96) : ℝ) := by
        intro x
        have h0x : (⟨0, by omega⟩ : Fin 96) ≤ x := Nat.zero_le _
        rw [ldlL, if_pos h0x, beta, borderedMinor_zero_cast, borderedMinor_zero_cast]
      have hD : ldlD (⟨0, by omega⟩ : Fin 96) =
          (j0 (⟨0, by omega⟩ : Fin 96) (⟨0, by omega⟩ : Fin 96) : ℝ) := by
        have hz : (⟨0, by omega⟩ : Fin 96).val = 0 := rfl
        rw [ldlD, if_pos hz, div_one, beta_zero]
      have h00 : (j0 (⟨0, by omega⟩ : Fin 96) (⟨0, by omega⟩ : Fin 96) : ℝ) ≠ 0 := by
        have h := beta_pos (⟨0, by omega⟩ : Fin 96)
        rw [beta_zero] at h
        exact ne_of_gt h
      have hbm : (borderedMinor (⟨0 + 1, hm⟩ : Fin 96) i j : ℝ) =
          (j0 (⟨0, by omega⟩ : Fin 96) (⟨0, by omega⟩ : Fin 96) : ℝ) * (j0 i j : ℝ) -
            (j0 (⟨0, by omega⟩ : Fin 96) j : ℝ) * (j0 i (⟨0, by omega⟩ : Fin 96) : ℝ) := by
        have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (borderedMinor_one i j)
        push_cast at h
        exact h
      have hsym : (j0 j (⟨0, by omega⟩ : Fin 96) : ℝ) =
          (j0 (⟨0, by omega⟩ : Fin 96) j : ℝ) :=
        congrArg (fun z : ℤ ↦ (z : ℝ))
          (Matrix.IsSymm.apply j0_isSymm (⟨0, by omega⟩ : Fin 96) j)
      rw [hL i, hL j, hD, hsym, hbm, beta_zero]
      exact sub_div_mul_mul_div _ _ _ _ h00
    · -- Level `k + 2`: the induction hypothesis at level `k + 1` describes the residual,
      -- and Desnanot–Jacobi at level `k + 1` evaluates the single removed term.
      have hk1 : k + 1 < 96 := by omega
      have hstep := ldlResidual_succ (k + 1) hk1 i j
      have hne : ¬ (k + 1 + 1 : ℕ) = 0 := by omega
      have hzero : ¬ (k + 1 : ℕ) = 0 := by omega
      have hidxk : (⟨k + 1 - 1, by omega⟩ : Fin 96) = (⟨k, by omega⟩ : Fin 96) :=
        Fin.ext (by show k + 1 - 1 = k; omega)
      have ihraw := ih (k + 1) (by omega) hk1 i j (by omega) (by omega)
      rw [if_neg hzero, hidxk] at ihraw
      have hidx2 : (⟨k + 1 + 1 - 1, by omega⟩ : Fin 96) = (⟨k + 1, hk1⟩ : Fin 96) :=
        Fin.ext (by show k + 1 + 1 - 1 = k + 1; omega)
      rw [hstep, ihraw, hidx2, if_neg hne]
      have hL : ∀ x : Fin 96, k + 1 ≤ x.val → ldlL x (⟨k + 1, hk1⟩ : Fin 96) =
          (borderedMinor ⟨k + 1, hk1⟩ x ⟨k + 1, hk1⟩ : ℝ) / beta ⟨k + 1, hk1⟩ := by
        intro x hx
        have hle : (⟨k + 1, hk1⟩ : Fin 96) ≤ x := by
          show k + 1 ≤ x.val
          exact hx
        rw [ldlL, if_pos hle]
      have hD : ldlD (⟨k + 1, hk1⟩ : Fin 96) = beta ⟨k + 1, hk1⟩ / beta ⟨k, by omega⟩ := by
        have hne0 : ¬ (⟨k + 1, hk1⟩ : Fin 96).val = 0 := by show ¬ k + 1 = 0; omega
        have hidx : (⟨k + 1 - 1, by omega⟩ : Fin 96) = (⟨k, by omega⟩ : Fin 96) :=
          Fin.ext (by show k + 1 - 1 = k; omega)
        rw [ldlD, if_neg hne0, hidx]
      rw [hL i (by omega), hL j (by omega), hD]
      -- Desnanot–Jacobi expresses the removed term through the next bordered minor.
      have hA : (borderedMinor ⟨k + 1, hk1⟩ i j : ℝ) * beta ⟨k + 1, hk1⟩ -
            (borderedMinor ⟨k + 1, hk1⟩ i ⟨k + 1, hk1⟩ : ℝ) *
              (borderedMinor ⟨k + 1, hk1⟩ j ⟨k + 1, hk1⟩ : ℝ) =
          (borderedMinor ⟨k + 2, hm⟩ i j : ℝ) * beta ⟨k, by omega⟩ := by
        have hdod := borderedMinor_dodgson (k + 1) (by omega) (by omega) i j
          (by omega) (by omega)
        rw [borderedMinor_comm (⟨k + 1, by omega⟩ : Fin 96) (⟨k + 1, by omega⟩ : Fin 96) j]
          at hdod
        have hcast := congrArg (fun z : ℤ ↦ (z : ℝ)) hdod.symm
        push_cast at hcast
        have h1 : (borderedMinor ⟨k + 1, by omega⟩ ⟨k + 1, by omega⟩ ⟨k + 1, by omega⟩ : ℝ) *
              (borderedMinor ⟨k + 1, by omega⟩ i j : ℝ) =
            (borderedMinor ⟨k + 1, hk1⟩ i j : ℝ) * beta ⟨k + 1, hk1⟩ := by
          rw [beta]
          ring
        have h2 : (borderedMinor ⟨k, by omega⟩ ⟨k, by omega⟩ ⟨k, by omega⟩ : ℝ) =
            beta ⟨k, by omega⟩ := by
          rw [beta]
        rw [h1, h2] at hcast
        exact hcast
      have hp : beta ⟨k, by omega⟩ ≠ 0 := beta_ne_zero _
      have hq : beta ⟨k + 1, hk1⟩ ≠ 0 := beta_ne_zero _
      -- Combine the three factors of the removed term into a single fraction.
      have hmul : ((borderedMinor ⟨k + 1, hk1⟩ i ⟨k + 1, hk1⟩ : ℝ) / beta ⟨k + 1, hk1⟩) *
            (beta ⟨k + 1, hk1⟩ / beta ⟨k, by omega⟩) *
            ((borderedMinor ⟨k + 1, hk1⟩ j ⟨k + 1, hk1⟩ : ℝ) / beta ⟨k + 1, hk1⟩) =
          (borderedMinor ⟨k + 1, hk1⟩ i ⟨k + 1, hk1⟩ : ℝ) *
              (borderedMinor ⟨k + 1, hk1⟩ j ⟨k + 1, hk1⟩ : ℝ) /
            (beta ⟨k + 1, hk1⟩ * beta ⟨k, by omega⟩) := by
        field_simp
      rw [hmul, div_sub_mul_div_eq _ _ _ _ _ hp hq, hA,
        mul_comm ((borderedMinor ⟨k + 2, hm⟩ i j : ℝ)) (beta ⟨k, by omega⟩)]
      rw [mul_div_mul_left _ _ hp]

/-- At a coordinate equal to one of the border indices the bordered minor factors through
that coordinate, which is what makes the last removal step of the decomposition exact. -/
lemma borderedMinor_mul_self (m : ℕ) (hm : m < 96) (i j : Fin 96)
    (h : m = i.val ∨ m = j.val) :
    borderedMinor ⟨m, hm⟩ i j * borderedMinor ⟨m, hm⟩ ⟨m, hm⟩ ⟨m, hm⟩ =
      borderedMinor ⟨m, hm⟩ i ⟨m, hm⟩ * borderedMinor ⟨m, hm⟩ j ⟨m, hm⟩ := by
  rcases h with h | h
  · have hie : i = (⟨m, hm⟩ : Fin 96) := Fin.ext h.symm
    subst hie
    rw [borderedMinor_comm (⟨m, hm⟩ : Fin 96) (⟨m, hm⟩ : Fin 96) j]
    ring
  · have hje : j = (⟨m, hm⟩ : Fin 96) := Fin.ext h.symm
    subst hje
    ring

/-- The last removal step of the `LDLᵀ` decomposition is exact: a fraction with denominator
the preceding leading principal minor equals the product of the two multipliers and the
diagonal entry. -/
lemma div_eq_div_mul_mul (A B C p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (h : A * p = B * C) :
    A / q = B / p * (p / q) * (C / p) := by
  field_simp
  linarith [h]

/-- At its last coordinate the residual of the `LDLᵀ` decomposition equals the single
outer-product term removed there. -/
lemma ldlResidual_eq_last (m : ℕ) (hm : m < 96) (i j : Fin 96)
    (hi : m ≤ i.val) (hj : m ≤ j.val) (hmin : m = i.val ∨ m = j.val) :
    ldlResidual m i j = ldlL i ⟨m, hm⟩ * ldlD ⟨m, hm⟩ * ldlL j ⟨m, hm⟩ := by
  have hres := ldlResidual_eq m hm i j hi hj
  have hL : ∀ x : Fin 96, m ≤ x.val → ldlL x (⟨m, hm⟩ : Fin 96) =
      (borderedMinor ⟨m, hm⟩ x ⟨m, hm⟩ : ℝ) / beta ⟨m, hm⟩ := by
    intro x hx
    have hle : (⟨m, hm⟩ : Fin 96) ≤ x := by
      show m ≤ x.val
      exact hx
    rw [ldlL, if_pos hle]
  have hD : ldlD (⟨m, hm⟩ : Fin 96) =
      beta ⟨m, hm⟩ / (if m = 0 then 1 else beta ⟨m - 1, by omega⟩) := rfl
  rw [hres, hL i hi, hL j hj, hD]
  have hbne : beta ⟨m, hm⟩ ≠ 0 := beta_ne_zero _
  have hDne : (if m = 0 then 1 else beta ⟨m - 1, by omega⟩) ≠ 0 := by
    by_cases h : m = 0
    · rw [if_pos h]
      exact one_ne_zero
    · rw [if_neg h]
      exact beta_ne_zero _
  have hnum : (borderedMinor ⟨m, hm⟩ i j : ℝ) * beta ⟨m, hm⟩ =
      (borderedMinor ⟨m, hm⟩ i ⟨m, hm⟩ : ℝ) *
        (borderedMinor ⟨m, hm⟩ j ⟨m, hm⟩ : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (borderedMinor_mul_self m hm i j hmin)
    push_cast at h
    rw [beta]
    exact h
  exact div_eq_div_mul_mul _ _ _ _ _ hbne hDne hnum

/-- Past the last coordinate of the decomposition the removed terms vanish, because one of
the two multipliers of such a term is zero. -/
lemma ldlPartialSum_eq_self (m : ℕ) (hm : m ≤ 96) (i j : Fin 96)
    (h : ∀ k : Fin 96, m ≤ k.val → ldlL i k * ldlD k * ldlL j k = 0) :
    ldlPartialSum 96 i j = ldlPartialSum m i j := by
  rw [ldlPartialSum, ldlPartialSum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k.val < m
  · rw [if_pos (lt_of_lt_of_le hk hm), if_pos hk]
  · rw [if_pos k.isLt, if_neg hk, h k (not_lt.mp hk)]

/-- The `LDLᵀ` factorization of the real matrix `2K - I₉₆` underlying the definiteness
certificate. -/
lemma j0_map_eq_ldl :
    j0.map (Int.castRingHom ℝ) = ldlL * Matrix.diagonal ldlD * ldlL.transpose := by
  ext i j
  rw [Matrix.map_apply]
  -- The decomposition is exact as soon as its residual vanishes, which happens right after
  -- the `min i.val j.val`-th term.
  have hm0 : min i.val j.val < 96 := lt_of_le_of_lt (min_le_left _ _) i.isLt
  have hle_i : min i.val j.val ≤ i.val := min_le_left _ _
  have hle_j : min i.val j.val ≤ j.val := min_le_right _ _
  have hmin : min i.val j.val = i.val ∨ min i.val j.val = j.val := by
    rcases le_total i.val j.val with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  -- Unfold the residual identity at the last coordinate and remove the final term.
  have hzero : ldlResidual (min i.val j.val + 1) i j = 0 := by
    rw [ldlResidual_succ _ hm0, ldlResidual_eq_last _ hm0 i j hle_i hle_j hmin]
    ring
  have hsum : ldlPartialSum 96 i j = ldlPartialSum (min i.val j.val + 1) i j := by
    refine ldlPartialSum_eq_self (min i.val j.val + 1) (by omega) i j fun k hk ↦ ?_
    have hgt : min i.val j.val < k.val := by omega
    rcases le_total i.val j.val with h | h
    · have hik : i < k := by show i.val < k.val; omega
      rw [ldlL_eq_zero_of_lt i k hik, zero_mul, zero_mul]
    · have hjk : j < k := by show j.val < k.val; omega
      rw [ldlL_eq_zero_of_lt j k hjk, mul_zero]
  have hres96 : ldlResidual 96 i j = 0 := by
    rw [ldlResidual, hsum, ← ldlResidual]
    exact hzero
  have hj0 : ldlPartialSum 96 i j = (j0 i j : ℝ) := by
    have h := hres96
    rw [ldlResidual] at h
    linarith
  -- The sum is the `(i, j)` entry of the matrix product `L * diagonal d * Lᵀ`.
  have hinner : ∀ k : Fin 96,
      (∑ l : Fin 96, ldlL i l * (if l = k then ldlD l else 0)) = ldlL i k * ldlD k := by
    intro k
    have hpt : ∀ l : Fin 96, ldlL i l * (if l = k then ldlD l else 0) =
        (if l = k then ldlL i l * ldlD l else 0) := by
      intro l
      by_cases h : l = k
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun l _ ↦ hpt l), Finset.sum_ite_eq' Finset.univ]
    simp
  have hmat : (ldlL * Matrix.diagonal ldlD * ldlL.transpose) i j = ldlPartialSum 96 i j := by
    rw [ldlPartialSum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
    rw [hinner k, if_pos k.isLt]
  -- The two spellings of the integer-to-real cast (`Int.castRingHom ℝ` from `Matrix.map`
  -- and the coercion in the residual) are definitionally equal, so the final comparison is
  -- closed by the residual identity rather than by `rw`.
  rw [hmat]
  exact hj0.symm

end FractionFree

/-- The real matrix obtained from the integer matrix `2K - I₉₆` is positive definite. -/
theorem j0_posDef : (j0.map (Int.castRingHom ℝ)).PosDef := by
  -- Replace the matrix by its `LDLᵀ` factorization, which is exact by `j0_map_eq_ldl`.
  rw [FractionFree.j0_map_eq_ldl]
  -- The multiplier vanishes strictly above the diagonal and has unit diagonal, so it is
  -- lower triangular with determinant the product of its diagonal entries, namely `1`.
  have htri : FractionFree.ldlL.BlockTriangular OrderDual.toDual := by
    intro i k hik
    exact FractionFree.ldlL_eq_zero_of_lt i k hik
  have hdet : FractionFree.ldlL.det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ htri]
    simp [FractionFree.ldlL_self]
  -- Consequently the multiplier is invertible, so conjugating by it does not change the
  -- definiteness of the quadratic form.
  have hU : IsUnit FractionFree.ldlL := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  -- The diagonal factor is positive definite because every leading principal minor of
  -- `2K - I₉₆` is strictly positive (`ldlD_pos`).
  have hpos : (Matrix.diagonal FractionFree.ldlD).PosDef :=
    Matrix.PosDef.diagonal fun k ↦ FractionFree.ldlD_pos k
  -- Over `ℝ` the conjugate transpose is the transpose, so the invertible-conjugation
  -- criterion transfers positive definiteness from the diagonal factor to `2K - I₉₆`.
  have hstar : star FractionFree.ldlL = FractionFree.ldlL.transpose := by
    ext i j
    simp
  have key : (FractionFree.ldlL * Matrix.diagonal FractionFree.ldlD *
      star FractionFree.ldlL).PosDef :=
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (x := Matrix.diagonal FractionFree.ldlD) hU).mpr hpos
  rw [hstar] at key
  exact key

end Period48
end ConsensusADMM
