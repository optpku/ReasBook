/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_42

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

section

variable {T : ℕ} {X : Fin (T + 1) → Ω → ℝ} (hBinary : IsBinaryModel X)

local notation "ℱX" => generatedFiltration X hBinary.isStochasticProcess

/-- Helper for Theorem 9.43: the positive-time price history of length `n`, namely
`(X₁(ω), …, Xₙ(ω))`. -/
def priceHistory (n : ℕ) (hn : n ≤ T) : Ω → Fin n → ℝ :=
  fun ω i ↦ X ⟨i.1 + 1, lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.succ_le_succ hn)⟩ ω

/-- Helper for Theorem 9.43: the innovation history of length `n`, namely
`(D₀(ω), …, Dₙ₋₁(ω))`. -/
def innovationHistory
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (n : ℕ) (hn : n ≤ T) :
    Ω → Fin n → {x : ℝ // x = -1 ∨ x = 1} :=
  fun ω i ↦ D ⟨i.1, lt_of_lt_of_le i.2 hn⟩ ω

/-- Helper for Theorem 9.43: recover the current price from the positive-time history, using the
deterministic initial value when the history is empty. -/
def currentPriceFromHistory (x0 : ℝ) : ∀ n : ℕ, (Fin n → ℝ) → ℝ
  | 0, _ => x0
  | n + 1, hist => hist (Fin.last n)

/-- Helper for Theorem 9.43: reconstruct the length-`n` price history from a deterministic
innovation history using the binary update maps. -/
def priceHistoryFromInnovation
    (x0 : ℝ)
    (f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ) :
    ∀ n : ℕ, n ≤ T → (Fin n → {x : ℝ // x = -1 ∨ x = 1}) → Fin n → ℝ
  | 0, _, _, i => nomatch i
  | n + 1, hn, z, i =>
      let hist := priceHistoryFromInnovation x0 f n (Nat.le_of_succ_le hn) (Fin.init z)
      (Fin.snoc hist
        (f ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩ hist (z (Fin.last n))) : Fin (n + 1) → ℝ) i

/-- Helper for Theorem 9.43: the coordinate description of `priceHistory`. -/
@[simp] lemma priceHistory_apply (n : ℕ) (hn : n ≤ T) (ω : Ω) (i : Fin n) :
    priceHistory (X := X) n hn ω i =
      X ⟨i.1 + 1, lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.succ_le_succ hn)⟩ ω := rfl

/-- Helper for Theorem 9.43: the coordinate description of `innovationHistory`. -/
@[simp] lemma innovationHistory_apply
    (D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}) (n : ℕ) (hn : n ≤ T) (ω : Ω) (i : Fin n) :
    innovationHistory (T := T) D n hn ω i = D ⟨i.1, lt_of_lt_of_le i.2 hn⟩ ω := rfl

/-- Helper for Theorem 9.43: the current price extracted from an empty history is the initial
value. -/
@[simp] lemma currentPriceFromHistory_zero (x0 : ℝ) :
    currentPriceFromHistory x0 0 = fun _ ↦ x0 := rfl

/-- Helper for Theorem 9.43: for a nonempty history, the current price is its last entry. -/
@[simp] lemma currentPriceFromHistory_succ (x0 : ℝ) (n : ℕ) (hist : Fin (n + 1) → ℝ) :
    currentPriceFromHistory x0 (n + 1) hist = hist (Fin.last n) := rfl

/-- Helper for Theorem 9.43: the last coordinate of a snoc history is the appended value. -/
@[simp] lemma priceHistoryFromInnovation_last
    (x0 : ℝ)
    (f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ)
    (n : ℕ) (hn : n + 1 ≤ T) (z : Fin (n + 1) → {x : ℝ // x = -1 ∨ x = 1}) :
    priceHistoryFromInnovation (T := T) x0 f (n + 1) hn z (Fin.last n) =
      f ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
        (priceHistoryFromInnovation (T := T) x0 f n (Nat.le_of_succ_le hn) (Fin.init z))
        (z (Fin.last n)) := by
  simp [priceHistoryFromInnovation]

/-- Helper for Theorem 9.43: the earlier coordinates of a snoc history agree with the prefix
history. -/
@[simp] lemma priceHistoryFromInnovation_castSucc
    (x0 : ℝ)
    (f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ)
    (n : ℕ) (hn : n + 1 ≤ T) (z : Fin (n + 1) → {x : ℝ // x = -1 ∨ x = 1}) (i : Fin n) :
    priceHistoryFromInnovation (T := T) x0 f (n + 1) hn z i.castSucc =
      priceHistoryFromInnovation (T := T) x0 f n (Nat.le_of_succ_le hn) (Fin.init z) i := by
  simp [priceHistoryFromInnovation]

/-- Helper for Theorem 9.43: the finite innovation history is measurable when each innovation
coordinate is measurable. -/
lemma innovationHistory_measurable
    {D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}}
    (hD : ∀ n, Measurable (D n)) (n : ℕ) (hn : n ≤ T) :
    Measurable (innovationHistory (T := T) D n hn) := by
  simpa [innovationHistory] using
    measurable_pi_lambda (innovationHistory (T := T) D n hn) fun i ↦
      hD ⟨i.1, lt_of_lt_of_le i.2 hn⟩

/-- Helper for Theorem 9.43: a function factoring through a finite-valued history map has finite
range. -/
lemma finite_range_of_factorsThrough_finite
    {α β γ : Type*} [Finite β] [Nonempty γ] {f : α → β} {g : α → γ} (hg : g.FactorsThrough f) :
    (Set.range g).Finite := by
  classical
  rcases (Function.factorsThrough_iff g).1 hg with ⟨e, rfl⟩
  exact (Set.toFinite (Set.range e)).subset fun y hy ↦ by
    rcases hy with ⟨x, rfl⟩
    exact ⟨f x, rfl⟩

/-- Helper for Theorem 9.43: if a function factors through a history map with finite range, then
it is measurable with respect to the pullback σ-algebra of that history map. -/
lemma measurable_of_factorsThrough_of_finiteRange
    {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] {f : Ω → β} {u : Ω → ℝ}
    (hu : u.FactorsThrough f) (hfin : (Set.range f).Finite) :
    Measurable[MeasurableSpace.comap f inferInstance] u := by
  classical
  rcases (Function.factorsThrough_iff u).1 hu with ⟨e, rfl⟩
  have hrange : MeasurableSet (Set.range f) := hfin.measurableSet
  let erange : Set.range f → ℝ := fun y ↦ e y.1
  haveI : Finite (Set.range f) := hfin.to_subtype
  have herange : Measurable erange := by
    -- On the finite range subtype, every real-valued map is measurable.
    exact measurable_of_finite erange
  obtain ⟨e', he'meas, he'⟩ :=
    (MeasurableEmbedding.subtype_coe hrange).exists_measurable_extend herange fun _ ↦ ⟨0⟩
  have hcomp : e ∘ f = e' ∘ f := by
    funext ω
    have hω := congrFun he' ⟨f ω, ⟨ω, rfl⟩⟩
    simpa [erange, Function.comp] using hω.symm
  -- Replace the original factorization map by a measurable extension from the finite range.
  rw [hcomp]
  exact he'meas.comp (comap_measurable f)

/-- Helper for Theorem 9.43: the current price can be read off from the corresponding positive-time
price history. -/
lemma currentPriceFromHistory_priceHistory
    {x0 : ℝ} (hX0 : X 0 = fun _ ↦ x0) :
    ∀ n : ℕ, (hn : n ≤ T) →
      (fun ω ↦ currentPriceFromHistory x0 n (priceHistory (X := X) n hn ω)) =
        X ⟨n, lt_of_le_of_lt hn (Nat.lt_succ_self T)⟩
  | 0, _ => by
      funext ω
      simpa [currentPriceFromHistory] using (congrFun hX0 ω).symm
  | n + 1, hn => by
      funext ω
      simp [currentPriceFromHistory, priceHistory]

/-- Helper for Theorem 9.43: a real-valued function with finite range is bounded. -/
lemma bounded_of_factorsThrough_finite {α β : Type*} [Finite β] {g : α → β} {u : α → ℝ}
    (hu : u.FactorsThrough g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ a, |u a| ≤ R := by
  classical
  letI := Fintype.ofFinite β
  rcases (Function.factorsThrough_iff u).1 hu with ⟨e, rfl⟩
  refine ⟨∑ b, |e b|, Finset.sum_nonneg fun _ _ ↦ abs_nonneg _, ?_⟩
  intro a
  simpa using Finset.single_le_sum
    (fun b _ ↦ abs_nonneg (e b))
    (Finset.mem_univ (g a))

/-- Helper for Theorem 9.43: solve the two branch equations for one backward replication step. -/
lemma solveTwoBranchLinearSystem
    {xPrev xMinus xPlus vMinus vPlus : ℝ}
    (hCompat : xMinus = xPlus → vMinus = vPlus) :
    let stake := if hEq : xPlus = xMinus then 0 else (vPlus - vMinus) / (xPlus - xMinus)
    let vPrev := vPlus - stake * (xPlus - xPrev)
    vPrev + stake * (xMinus - xPrev) = vMinus ∧
      vPrev + stake * (xPlus - xPrev) = vPlus := by
  classical
  by_cases hEq : xPlus = xMinus
  · subst hEq
    simp [hCompat rfl]
  · have hx : xPlus - xMinus ≠ 0 := sub_ne_zero.mpr hEq
    have hx' : xMinus ≠ xPlus := by simpa [eq_comm] using hEq
    simp [hEq]
    field_simp [hx]
    ring

/-- Helper for Theorem 9.43: the finite positive-time price history is measurable with respect to
the generated filtration at the same time. -/
lemma priceHistory_measurable (n : ℕ) (hn : n ≤ T) :
    Measurable[ℱX ⟨n, lt_of_le_of_lt hn (Nat.lt_succ_self T)⟩] (priceHistory (X := X) n hn) := by
  exact @measurable_pi_lambda Ω (Fin n) (fun _ : Fin n => ℝ)
    (ℱX ⟨n, lt_of_le_of_lt hn (Nat.lt_succ_self T)⟩) (fun _ => inferInstance)
    (priceHistory (X := X) n hn) fun i ↦ by
      simpa [priceHistory] using
        (comap_measurable (X ⟨i.1 + 1,
          lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.succ_le_succ hn)⟩)).mono
          (by
            rw [generatedFiltration_apply]
            refine le_iSup_of_le ⟨i.1 + 1,
              lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.succ_le_succ hn)⟩ ?_
            refine le_iSup_of_le ?_ le_rfl
            simpa using Nat.succ_le_of_lt i.2)
          le_rfl

/-- Helper for Theorem 9.43: every coordinate up to time `n` is measurable with respect to the
length-`n` price history. -/
lemma generatedFiltration_le_comap_priceHistory (n : ℕ) (hn : n ≤ T) :
    ℱX ⟨n, lt_of_le_of_lt hn (Nat.lt_succ_self T)⟩ ≤
      MeasurableSpace.comap (priceHistory (X := X) n hn) inferInstance := by
  obtain ⟨x0, hX0, -, -, -, -⟩ := IsBinaryModel.exists_representation hBinary
  rw [generatedFiltration_apply]
  refine iSup₂_le fun s hs ↦ ?_
  rw [← measurable_iff_comap_le]
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ s
  · simpa [hX0] using (measurable_const : Measurable fun _ : Ω ↦ x0)
  · let i : Fin n := ⟨j.1, Nat.lt_of_lt_of_le (Nat.lt_succ_self j.1) (by simpa using hs)⟩
    have hcoord :
        X j.succ = fun ω ↦ priceHistory (X := X) n hn ω i := by
      funext ω
      have hindex :
          j.succ = ⟨j.1 + 1, lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.succ_le_succ hn)⟩ := by
        ext
        rfl
      rw [hindex]
      simp [priceHistory, i]
    rw [hcoord]
    exact (measurable_pi_apply i).comp (comap_measurable (priceHistory (X := X) n hn))

/-- Helper for Theorem 9.43: the binary update rule can be written using `priceHistory`. -/
lemma binaryStep_eq_priceHistory
    {x0 : ℝ}
    {D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}}
    {f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ}
    (hX0 : X 0 = fun _ ↦ x0)
    (hStep : ∀ n : Fin T,
      X ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ =
        fun ω ↦ f n (binaryModelHistory X n ω) (D n ω))
    (n : ℕ) (hn : n < T) :
    X ⟨n + 1, Nat.succ_lt_succ hn⟩ =
      fun ω ↦ f ⟨n, hn⟩ (priceHistory (X := X) n (Nat.le_of_lt hn) ω) (D ⟨n, hn⟩ ω) := by
  -- Route correction: switch from `binaryModelHistory` to the theorem-local `priceHistory`
  -- normal form before attempting any history recursion.
  funext ω
  have hω := congrFun (hStep ⟨n, hn⟩) ω
  simpa [priceHistory, binaryModelHistory] using hω

/-- Helper for Theorem 9.43: the length-`n` price history is a deterministic function of the
length-`n` innovation history. -/
lemma priceHistory_eq_priceHistoryFromInnovation
    {x0 : ℝ}
    {D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}}
    {f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ}
    (hX0 : X 0 = fun _ ↦ x0)
    (hStep : ∀ n : Fin T,
      X ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ =
        fun ω ↦ f n (binaryModelHistory X n ω) (D n ω)) :
    ∀ n : ℕ, (hn : n ≤ T) →
      priceHistory (X := X) n hn =
        fun ω ↦ priceHistoryFromInnovation (T := T) x0 f n hn
          (innovationHistory (T := T) D n hn ω)
  | 0, _ => by
      funext ω
      ext i
      exact nomatch i
  | n + 1, hn => by
      funext ω
      ext i
      obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
      · simpa [innovationHistory, priceHistoryFromInnovation, priceHistory] using
          congrFun (congrFun
            (priceHistory_eq_priceHistoryFromInnovation hX0 hStep n (Nat.le_of_succ_le hn)) ω) j
      · let nFin : Fin T := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
        have hω :=
          congrFun (binaryStep_eq_priceHistory (X := X) hX0 hStep n (lt_of_lt_of_le
            (Nat.lt_succ_self n) hn)) ω
        have hprefix :=
          congrFun (priceHistory_eq_priceHistoryFromInnovation hX0 hStep n
            (Nat.le_of_succ_le hn)) ω
        have hinit :
            Fin.init (innovationHistory (T := T) D (n + 1) hn ω) =
              innovationHistory (T := T) D n (Nat.le_of_succ_le hn) ω := by
          funext j
          simp [innovationHistory, Fin.init]
        simpa [innovationHistory, priceHistoryFromInnovation, priceHistory, nFin] using
          hω.trans (by rw [hprefix, hinit])

/-- Helper for Theorem 9.43: `priceHistory` factors through the finite innovation history. -/
lemma priceHistory_factorsThrough_innovationHistory
    {x0 : ℝ}
    {D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1}}
    {f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ}
    (hX0 : X 0 = fun _ ↦ x0)
    (hStep : ∀ n : Fin T,
      X ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ =
        fun ω ↦ f n (binaryModelHistory X n ω) (D n ω))
    (n : ℕ) (hn : n ≤ T) :
    (priceHistory (X := X) n hn).FactorsThrough (innovationHistory (T := T) D n hn) := by
  rw [Function.factorsThrough_iff]
  refine ⟨priceHistoryFromInnovation (T := T) x0 f n hn, ?_⟩
  simpa using priceHistory_eq_priceHistoryFromInnovation (X := X) hX0 hStep n hn

/-- Helper for Theorem 9.43: every finite positive-time price history of a binary model takes
only finitely many values. -/
lemma priceHistory_range_finite (hBinary : IsBinaryModel X) (n : ℕ) (hn : n ≤ T) :
    (Set.range (priceHistory (X := X) n hn)).Finite := by
  classical
  obtain ⟨x0, hX0, D, hD, f, hStep⟩ := IsBinaryModel.exists_representation hBinary
  have hRangeBinary :
      ({x : ℝ | x = -1 ∨ x = 1} : Set ℝ).Finite := by
    simpa [Set.setOf_or] using
      (Set.finite_singleton (-1 : ℝ)).union (Set.finite_singleton (1 : ℝ))
  haveI : Finite {x : ℝ // x = -1 ∨ x = 1} := hRangeBinary.to_subtype
  have hFactor :
      (priceHistory (X := X) n hn).FactorsThrough (innovationHistory (T := T) D n hn) :=
    priceHistory_factorsThrough_innovationHistory (X := X) hX0 hStep n hn
  -- The innovation history takes values in a finite function space, so every factor through it
  -- has finite range.
  exact finite_range_of_factorsThrough_finite hFactor

/-- Helper for Theorem 9.43: a real-valued function that factors through the empty history is
constant. -/
lemma factorsThrough_emptyHistory_eq_const
    {α : Type*} {u : Ω → ℝ} {h : Ω → Fin 0 → α} (hu : u.FactorsThrough h) :
    ∃ c : ℝ, u = fun _ ↦ c := by
  classical
  rcases (Function.factorsThrough_iff u).1 hu with ⟨e, rfl⟩
  refine ⟨e (fun i ↦ nomatch i), ?_⟩
  funext ω
  have : h ω = (fun i ↦ nomatch i) := by
    funext i
    exact nomatch i
  simpa [this]

/-- Helper for Theorem 9.43: truncating a binary model at the final time preserves the binary-model
structure. -/
lemma isBinaryModel_castSucc
    {n : ℕ} {Y : Fin (n + 2) → Ω → ℝ} (hY : IsBinaryModel Y) :
    IsBinaryModel (fun i : Fin (n + 1) ↦ Y i.castSucc) := by
  obtain ⟨x0, hY0, D, hD, f, hStep⟩ := IsBinaryModel.exists_representation hY
  refine ⟨fun i ↦ hY.isStochasticProcess i.castSucc, x0, ?_, ?_⟩
  · simpa using hY0
  · refine ⟨fun i : Fin n ↦ D i.castSucc, ?_, fun i : Fin n ↦ f i.castSucc, ?_⟩
    · intro i
      exact hD i.castSucc
    · intro i
      -- Route correction: use the cast-succ truncation directly rather than rebuilding the
      -- history object by hand at each coordinate.
      simpa [binaryModelHistory] using hStep i.castSucc

/-- Helper for Theorem 9.43: the generated filtration of the truncated process agrees with the
original generated filtration on the earlier times. -/
lemma generatedFiltration_castSucc
    {n : ℕ} {Y : Fin (n + 2) → Ω → ℝ} (hY : IsStochasticProcess Y) (i : Fin (n + 1)) :
    generatedFiltration (fun j : Fin (n + 1) ↦ Y j.castSucc) (fun j ↦ hY j.castSucc) i =
      generatedFiltration Y hY i.castSucc := by
  rw [generatedFiltration_apply, generatedFiltration_apply]
  apply le_antisymm
  · refine iSup₂_le fun j hj ↦ ?_
    refine le_iSup_of_le j.castSucc ?_
    refine le_iSup_of_le (Fin.castSucc_le_castSucc_iff.mpr hj) le_rfl
  · refine iSup₂_le fun j hj ↦ ?_
    have hj_last : j ≠ Fin.last (n + 1) := by
      exact Fin.ne_of_lt (lt_of_le_of_lt hj i.castSucc_lt_last)
    obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hj_last
    refine le_iSup_of_le k ?_
    refine le_iSup_of_le (Fin.castSucc_le_castSucc_iff.mp hj) le_rfl

/-- Helper for Theorem 9.43: `Fin.lastCases` returns the truncated branch on a `castSucc`
index. -/
@[simp] lemma finLastCases_castSucc
    {α : Type*} {n : ℕ} (lastValue : α) (truncValue : Fin (n + 1) → α) (j : Fin (n + 1)) :
    Fin.lastCases lastValue truncValue j.castSucc = truncValue j := by
  simp [Fin.lastCases]

/-- Helper for Theorem 9.43: `Fin.lastCases` returns the terminal branch at the last index. -/
@[simp] lemma finLastCases_last
    {α : Type*} {n : ℕ} (lastValue : α) (truncValue : Fin (n + 1) → α) :
    Fin.lastCases lastValue truncValue (Fin.last (n + 1)) = lastValue := by
  simp [Fin.lastCases]

/-- Helper for Theorem 9.43: on the finite time set `Fin (T + 1)`, predictability follows from
measurability of the time-`0` slice and of each successor slice with respect to the previous
σ-algebra. -/
lemma isPredictable_of_measurableSuccFin
    {H : Fin (T + 1) → Ω → ℝ}
    (h0 : Measurable[ℱX 0] (H 0))
    (hsucc : ∀ i : Fin T, Measurable[ℱX i.castSucc] (H i.succ)) :
    IsPredictable ℱX H := by
  refine Measurable.stronglyMeasurable ?_
  intro s hs
  have hsplit :
      Function.uncurry H ⁻¹' s =
        ({(0 : Fin (T + 1))} ×ˢ (H 0 ⁻¹' s) ∪
          ⋃ i : Fin T, ({i.succ} : Set (Fin (T + 1))) ×ˢ (H i.succ ⁻¹' s)) := by
    ext p
    rcases p with ⟨i, ω⟩
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simp [Set.mem_iUnion]
      intro x hx _
      exact (Fin.succ_ne_zero x hx.symm).elim
    · simp [Set.mem_iUnion]
  rw [hsplit]
  refine (measurableSet_predictable_singleton_bot_prod (h0 hs)).union ?_
  refine MeasurableSet.iUnion fun i ↦ ?_
  have hsingleton : ({i.succ} : Set (Fin (T + 1))) = Set.Ioc i.castSucc i.succ := by
    ext j
    constructor
    · intro hj
      subst hj
      exact ⟨by simpa using (Nat.lt_succ_self i.1), le_rfl⟩
    · intro hj
      have hjne : j ≠ 0 := by
        intro hzero
        have : ¬ i.castSucc < (0 : Fin (T + 1)) := not_lt_of_ge (Fin.zero_le _)
        exact this (hzero ▸ hj.1)
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hjne
      have hki : k ≤ i := by
        simpa using hj.2
      have hik : i ≤ k := by
        simpa using hj.1
      have hk : k = i := le_antisymm hki hik
      simpa [hk]
  rw [hsingleton]
  -- After normalizing the singleton as an interval slice, the standard predictable generator
  -- applies directly.
  exact measurableSet_predictable_Ioc_prod i.castSucc i.succ (hsucc i hs)

/-- Helper for Theorem 9.43: at the terminal time of a finite binary model, a terminal-measurable
payoff can be written as a previous-time continuation value plus a bounded last stake times the
last increment. -/
lemma backwardStep_replication_terminal
    {n : ℕ} {Y : Fin (n + 2) → Ω → ℝ} (hY : IsBinaryModel Y) {V : Ω → ℝ}
    (hV : Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.last (n + 1))] V) :
    ∃ Vprev Hlast : Ω → ℝ,
      Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.castSucc (Fin.last n))] Vprev ∧
      Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.castSucc (Fin.last n))] Hlast ∧
      (∃ R : ℝ, 0 ≤ R ∧ ∀ ω, |Hlast ω| ≤ R) ∧
      V = fun ω ↦
        Vprev ω +
          Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω) := by
  classical
  obtain ⟨x0, hY0, D, hD, f, hStep⟩ := IsBinaryModel.exists_representation hY
  let prevHistory : Ω → Fin n → ℝ :=
    priceHistory (X := Y) n (Nat.le_of_lt (Nat.lt_succ_self n))
  let terminalHistory : Ω → Fin (n + 1) → ℝ :=
    priceHistory (X := Y) (n + 1) (Nat.le_refl _)
  let nFin : Fin (n + 1) := Fin.last n
  -- Route correction: factor the payoff through the terminal price history first, then solve the
  -- two-branch linear system on deterministic prefix histories.
  have hVterminal :
      Measurable[MeasurableSpace.comap terminalHistory inferInstance] V :=
    (show Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.last (n + 1))] V from hV).mono
      (generatedFiltration_le_comap_priceHistory (X := Y) hY (n + 1) (Nat.le_refl _)) le_rfl
  have hfactor : V.FactorsThrough terminalHistory := hVterminal.factorsThrough
  rcases (Function.factorsThrough_iff V).1 hfactor with ⟨g, hg⟩
  let xPrevFn : (Fin n → ℝ) → ℝ := currentPriceFromHistory x0 n
  let xMinus : (Fin n → ℝ) → ℝ := fun hist ↦ f nFin hist ⟨-1, Or.inl rfl⟩
  let xPlus : (Fin n → ℝ) → ℝ := fun hist ↦ f nFin hist ⟨1, Or.inr rfl⟩
  let vMinus : (Fin n → ℝ) → ℝ := fun hist ↦ g (Fin.snoc hist (xMinus hist))
  let vPlus : (Fin n → ℝ) → ℝ := fun hist ↦ g (Fin.snoc hist (xPlus hist))
  have hCompat : ∀ hist, xMinus hist = xPlus hist → vMinus hist = vPlus hist := by
    intro hist hEq
    dsimp [vMinus, vPlus]
    congr 1
    ext i
    obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · simp
    · simpa [xMinus, xPlus] using hEq
  let stakeFn : (Fin n → ℝ) → ℝ := fun hist ↦
    if hEq : xPlus hist = xMinus hist then
      0
    else
      (vPlus hist - vMinus hist) / (xPlus hist - xMinus hist)
  let prevFn : (Fin n → ℝ) → ℝ := fun hist ↦
    vPlus hist - stakeFn hist * (xPlus hist - xPrevFn hist)
  have hSolve : ∀ hist,
      prevFn hist + stakeFn hist * (xMinus hist - xPrevFn hist) = vMinus hist ∧
        prevFn hist + stakeFn hist * (xPlus hist - xPrevFn hist) = vPlus hist := by
    intro hist
    simpa [prevFn, stakeFn, xPrevFn, xMinus, xPlus, vMinus, vPlus] using
      (solveTwoBranchLinearSystem
        (xPrev := xPrevFn hist) (xMinus := xMinus hist) (xPlus := xPlus hist)
        (vMinus := vMinus hist) (vPlus := vPlus hist) (hCompat hist))
  let Vprev : Ω → ℝ := fun ω ↦ prevFn (prevHistory ω)
  let Hlast : Ω → ℝ := fun ω ↦ stakeFn (prevHistory ω)
  have hPrevFactor : Vprev.FactorsThrough prevHistory := by
    rw [Function.factorsThrough_iff]
    exact ⟨prevFn, rfl⟩
  have hLastFactor : Hlast.FactorsThrough prevHistory := by
    rw [Function.factorsThrough_iff]
    exact ⟨stakeFn, rfl⟩
  have hPrevHistoryFinite : (Set.range prevHistory).Finite :=
    priceHistory_range_finite (X := Y) hY n (Nat.le_of_lt (Nat.lt_succ_self n))
  have hPrevHistoryMeas :
      Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.castSucc (Fin.last n))]
        prevHistory :=
    priceHistory_measurable (X := Y) hY n (Nat.le_of_lt (Nat.lt_succ_self n))
  have hPrevComapLe :
      MeasurableSpace.comap prevHistory inferInstance ≤
        generatedFiltration Y hY.isStochasticProcess (Fin.castSucc (Fin.last n)) :=
    (measurable_iff_comap_le).mp hPrevHistoryMeas
  have hVprevMeas :
      Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.castSucc (Fin.last n))] Vprev :=
    (measurable_of_factorsThrough_of_finiteRange hPrevFactor hPrevHistoryFinite).mono hPrevComapLe
      le_rfl
  have hHlastMeas :
      Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.castSucc (Fin.last n))] Hlast :=
    (measurable_of_factorsThrough_of_finiteRange hLastFactor hPrevHistoryFinite).mono hPrevComapLe
      le_rfl
  let prevHistoryRange : Ω → Set.range prevHistory := fun ω ↦ ⟨prevHistory ω, ⟨ω, rfl⟩⟩
  have hLastRangeFactor : Hlast.FactorsThrough prevHistoryRange := by
    rw [Function.factorsThrough_iff]
    exact ⟨fun z ↦ stakeFn z.1, rfl⟩
  have hHlastBound :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ω, |Hlast ω| ≤ R := by
    letI : Finite (Set.range prevHistory) := hPrevHistoryFinite.to_subtype
    exact bounded_of_factorsThrough_finite hLastRangeFactor
  refine ⟨Vprev, Hlast, hVprevMeas, hHlastMeas, hHlastBound, ?_⟩
  -- Evaluate the deterministic branch solver on the realized prefix history and the realized
  -- terminal branch.
  funext ω
  let hist := prevHistory ω
  have hPrevPrice :
      xPrevFn hist = Y (Fin.castSucc (Fin.last n)) ω := by
    simpa [hist, prevHistory, xPrevFn] using
      congrFun (currentPriceFromHistory_priceHistory (X := Y) hY0 n
        (Nat.le_of_lt (Nat.lt_succ_self n))) ω
  have hLastStep :
      Y (Fin.last (n + 1)) ω = f nFin hist (D nFin ω) := by
    simpa [hist, prevHistory, nFin] using
      congrFun (binaryStep_eq_priceHistory (X := Y) hY0 hStep n (Nat.lt_succ_self n)) ω
  have hLastIndex :
      (⟨n + 1, Nat.succ_lt_succ (Nat.lt_succ_self n)⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
    ext
    rfl
  have hTerminalHistory :
      terminalHistory ω = Fin.snoc hist (Y (Fin.last (n + 1)) ω) := by
    ext i
    obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · simp [terminalHistory, prevHistory, hist]
    · simpa [terminalHistory, prevHistory, hist, priceHistory, hLastIndex]
  have hVvalue :
      V ω = g (Fin.snoc hist (Y (Fin.last (n + 1)) ω)) := by
    simpa [Function.comp, hTerminalHistory] using congrFun hg ω
  rcases (D nFin ω).property with hMinus | hPlus
  · have hBranch :
        D nFin ω = ⟨-1, Or.inl rfl⟩ := by
      apply Subtype.ext
      simpa using hMinus
    have hLastValue : Y (Fin.last (n + 1)) ω = xMinus hist := by
      simpa [xMinus, hist, hBranch] using hLastStep
    have hVminus : V ω = vMinus hist := by
      calc
        V ω = g (Fin.snoc hist (Y (Fin.last (n + 1)) ω)) := hVvalue
        _ = g (Fin.snoc hist (xMinus hist)) := by rw [hLastValue]
        _ = vMinus hist := by simp [vMinus]
    calc
      V ω = vMinus hist := hVminus
      _ = prevFn hist + stakeFn hist * (xMinus hist - xPrevFn hist) := by
        symm
        exact (hSolve hist).1
      _ = Vprev ω +
            Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω) := by
        simp [Vprev, Hlast, hist, hLastValue, hPrevPrice]
  · have hBranch :
        D nFin ω = ⟨1, Or.inr rfl⟩ := by
      apply Subtype.ext
      simpa using hPlus
    have hLastValue : Y (Fin.last (n + 1)) ω = xPlus hist := by
      simpa [xPlus, hist, hBranch] using hLastStep
    have hVplus : V ω = vPlus hist := by
      calc
        V ω = g (Fin.snoc hist (Y (Fin.last (n + 1)) ω)) := hVvalue
        _ = g (Fin.snoc hist (xPlus hist)) := by rw [hLastValue]
        _ = vPlus hist := by simp [vPlus]
    calc
      V ω = vPlus hist := hVplus
      _ = prevFn hist + stakeFn hist * (xPlus hist - xPrevFn hist) := by
        symm
        exact (hSolve hist).2
      _ = Vprev ω +
            Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω) := by
        simp [Vprev, Hlast, hist, hLastValue, hPrevPrice]

/-- Helper for Theorem 9.43: extending a truncated hedge by `Fin.lastCases` splits the full gain
sum into the truncated gain and the terminal increment term. -/
lemma gainSum_finLastCases
    {n : ℕ} {Y : Fin (n + 2) → Ω → ℝ}
    {Htrunc : Fin (n + 1) → Ω → ℝ} {Hlast : Ω → ℝ} :
    (fun ω ↦
      ∑ k : Fin (n + 1),
        Fin.lastCases (Hlast ω) (fun j ↦ Htrunc j ω) k.succ *
          (Y k.succ ω - Y k.castSucc ω)) =
      fun ω ↦
        (∑ k : Fin n,
          Htrunc k.succ ω *
            ((fun i : Fin (n + 1) ↦ Y i.castSucc) k.succ ω -
              (fun i : Fin (n + 1) ↦ Y i.castSucc) k.castSucc ω)) +
          Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω) := by
  funext ω
  -- Split the sum over `Fin (n + 1)` into the cast-succ part and the last index.
  rw [Fin.sum_univ_castSucc]
  -- Then normalize the two `Fin.lastCases` branches and the truncated coordinates.
  have hLastTerm :
      Fin.lastCases (Hlast ω) (fun j ↦ Htrunc j ω) (Fin.last n).succ = Hlast ω := by
    simp [Fin.lastCases]
  rw [hLastTerm]
  refine congrArg (fun t ↦ t + Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω))
    ?_
  · apply Finset.sum_congr rfl
    intro i hi
    have hIndex : i.castSucc.succ = (i.succ).castSucc := by
      ext
      rfl
    have hValue :
        Fin.lastCases (Hlast ω) (fun j ↦ Htrunc j ω) i.castSucc.succ = Htrunc i.succ ω := by
      rw [hIndex]
      simpa using
        (finLastCases_castSucc (lastValue := Hlast ω) (truncValue := fun j ↦ Htrunc j ω)
          (j := i.succ))
    rw [hValue]
    rfl

/-- Helper for Theorem 9.43: at horizon `0`, filtration measurability means the payoff is
constant. -/
lemma binaryModelRepresentationBase
    {Y : Fin 1 → Ω → ℝ} (hY : IsBinaryModel Y) {V : Ω → ℝ}
    (hV : Measurable[generatedFiltration Y hY.isStochasticProcess 0] V) :
    ∃ c : ℝ, V = fun _ ↦ c := by
  have hVhist :
      Measurable[MeasurableSpace.comap (priceHistory (X := Y) 0 (Nat.zero_le 0)) inferInstance] V :=
    hV.mono
      (generatedFiltration_le_comap_priceHistory (X := Y) hY 0 (Nat.zero_le 0)) le_rfl
  have hfactor :
      V.FactorsThrough (priceHistory (X := Y) 0 (Nat.zero_le 0)) :=
    hVhist.factorsThrough
  -- The length-`0` history has only one value, so every factor through it is constant.
  exact factorsThrough_emptyHistory_eq_const hfactor

/-- Helper for Theorem 9.43: a terminal-measurable payoff in a finite binary model admits a
representation by an initial capital and a bounded strategy with measurable successor slices. -/
lemma binaryModelRepresentationAux
    {n : ℕ} {Y : Fin (n + 1) → Ω → ℝ} (hY : IsBinaryModel Y) {V : Ω → ℝ}
    (hV : Measurable[generatedFiltration Y hY.isStochasticProcess (Fin.last n)] V) :
    ∃ H : Fin (n + 1) → Ω → ℝ, ∃ c : ℝ,
      H 0 = 0 ∧
      (∀ i : Fin n,
        Measurable[generatedFiltration Y hY.isStochasticProcess i.castSucc] (H i.succ)) ∧
      (∀ i : Fin (n + 1), ∃ R : ℝ, 0 ≤ R ∧ ∀ ω, |H i ω| ≤ R) ∧
      V = fun ω ↦ c + ∑ k : Fin n, H k.succ ω * (Y k.succ ω - Y k.castSucc ω) := by
  classical
  induction n generalizing V with
  | zero =>
      rcases binaryModelRepresentationBase (Y := Y) hY hV with ⟨c, hconst⟩
      refine ⟨fun _ _ ↦ 0, c, rfl, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        refine ⟨0, le_rfl, ?_⟩
        intro ω
        simp
      · funext ω
        simp [hconst]
  | succ n ih =>
      rcases backwardStep_replication_terminal (Y := Y) hY hV with
        ⟨Vprev, Hlast, hVprevMeas, hHlastMeas, hHlastBound, hStepRep⟩
      let Ytrunc : Fin (n + 1) → Ω → ℝ := fun i ↦ Y i.castSucc
      have hYtrunc : IsBinaryModel Ytrunc :=
        isBinaryModel_castSucc (Y := Y) hY
      have hYtruncProcess :
          hYtrunc.isStochasticProcess = (fun i : Fin (n + 1) ↦ hY.isStochasticProcess i.castSucc) := by
        funext i
        exact Subsingleton.elim _ _
      have hVprevTrunc :
          Measurable[generatedFiltration Ytrunc hYtrunc.isStochasticProcess (Fin.last n)] Vprev := by
        have hVprevExplicit :
            Measurable[generatedFiltration (fun i : Fin (n + 1) ↦ Y i.castSucc)
              (fun i : Fin (n + 1) ↦ hY.isStochasticProcess i.castSucc) (Fin.last n)] Vprev := by
          rw [generatedFiltration_castSucc (Y := Y) hY.isStochasticProcess (Fin.last n)]
          exact hVprevMeas
        simpa [hYtruncProcess] using hVprevExplicit
      rcases ih (Y := Ytrunc) hYtrunc hVprevTrunc with
        ⟨Htrunc, c, hHtrunc0, hHtruncsucc, hHtruncBound, hRepPrev⟩
      let H : Fin (n + 2) → Ω → ℝ := fun j ω ↦
        Fin.lastCases (Hlast ω) (fun k ↦ Htrunc k ω) j
      refine ⟨H, c, ?_, ?_, ?_, ?_⟩
      · -- The extended hedge inherits the zero initial position from the truncated hedge.
        funext ω
        have hZeroValue : H 0 ω = Htrunc 0 ω := by
          change Fin.lastCases (Hlast ω) (fun k ↦ Htrunc k ω) (0 : Fin (n + 2)) = Htrunc 0 ω
          simpa using
            (finLastCases_castSucc (lastValue := Hlast ω) (truncValue := fun k ↦ Htrunc k ω)
              (j := (0 : Fin (n + 1))))
        rw [hZeroValue]
        exact congrFun hHtrunc0 ω
      · intro i
        obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
        · -- Earlier successor slices come from the induction hypothesis on the truncated model.
          have hSlice :
              Measurable[generatedFiltration Y hY.isStochasticProcess (j.castSucc).castSucc]
                (Htrunc j.succ) := by
            rw [← generatedFiltration_castSucc (Y := Y) hY.isStochasticProcess j.castSucc]
            have hSliceExplicit :
                Measurable[generatedFiltration (fun i : Fin (n + 1) ↦ Y i.castSucc)
                  (fun i : Fin (n + 1) ↦ hY.isStochasticProcess i.castSucc) j.castSucc]
                  (Htrunc j.succ) := by
              simpa [hYtruncProcess] using hHtruncsucc j
            exact hSliceExplicit
          have hIndex : j.castSucc.succ = (j.succ).castSucc := by
            ext
            rfl
          have hHeq : H j.castSucc.succ = Htrunc j.succ := by
            funext ω
            rw [hIndex]
            change Fin.lastCases (Hlast ω) (fun k ↦ Htrunc k ω) (j.succ).castSucc = Htrunc j.succ ω
            simpa [H] using
              (finLastCases_castSucc (lastValue := Hlast ω) (truncValue := fun k ↦ Htrunc k ω)
                (j := j.succ))
          rw [hHeq]
          exact hSlice
        · -- The terminal successor slice is exactly the last-step hedge.
          simpa [H] using hHlastMeas
      · intro i
        obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
        · -- Bounds on earlier slices are inherited from the truncated hedge.
          simpa [H] using hHtruncBound j
        · -- The terminal slice uses the bound supplied by the backward step.
          simpa [H] using hHlastBound
      · -- Assemble the truncated representation with the final one-step replication identity.
        funext ω
        have hGain :=
          congrFun (gainSum_finLastCases (Y := Y) (Htrunc := Htrunc) (Hlast := Hlast)) ω
        calc
          V ω =
              Vprev ω +
                Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω) := by
            simpa using congrFun hStepRep ω
          _ =
              (c + ∑ k : Fin n,
                Htrunc k.succ ω * (Ytrunc k.succ ω - Ytrunc k.castSucc ω)) +
                Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω) := by
            rw [congrFun hRepPrev ω]
          _ =
              c +
                ((∑ k : Fin n,
                  Htrunc k.succ ω * (Ytrunc k.succ ω - Ytrunc k.castSucc ω)) +
                  Hlast ω * (Y (Fin.last (n + 1)) ω - Y (Fin.castSucc (Fin.last n)) ω)) := by
            rw [add_assoc]
          _ =
              c + ∑ k : Fin (n + 1), H k.succ ω * (Y k.succ ω - Y k.castSucc ω) := by
            rw [← hGain]

-- Proof sketch: argue by backward induction on time. At each step, an
-- `generatedFiltration X hBinary.isStochasticProcess i.succ`-measurable claim has two branch
-- values over the two successors of the binary model, so solving the resulting two-point linear
-- system produces the next predictable stake and a new
-- `generatedFiltration X hBinary.isStochasticProcess i.castSucc`-measurable continuation value.
/-- Theorem 9.43: in a binary model, every terminal payoff measurable with respect to the terminal
generated filtration is replicated by an initial capital and a bounded predictable strategy whose
finite gain sum matches the terminal payoff at time `T`. -/
theorem binary_model_representation {V_T : Ω → ℝ}
    (hV_T : Measurable[ℱX (Fin.last T)] V_T) :
    ∃ H : Fin (T + 1) → Ω → ℝ,
      IsPredictable ℱX H ∧
        (∀ n : Fin (T + 1), ∃ R : ℝ, 0 ≤ R ∧ ∀ ω, |H n ω| ≤ R) ∧
        ∃ initialCapital : ℝ,
          V_T = fun ω ↦ initialCapital +
            ∑ k : Fin T, H k.succ ω * (X k.succ ω - X k.castSucc ω) :=
      by
        classical
        rcases binaryModelRepresentationAux (Y := X) hBinary hV_T with
          ⟨H, initialCapital, hH0, hHsucc, hHbounded, hrepr⟩
        have hHpredictable : IsPredictable ℱX H := by
          have hHmeas0 : Measurable[ℱX 0] (H 0) := by
            -- The auxiliary theorem fixes the initial slice to zero, so time-`0`
            -- measurability is immediate.
            rw [hH0]
            exact measurable_const
          exact isPredictable_of_measurableSuccFin (hBinary := hBinary) hHmeas0 hHsucc
        -- Package the predictable strategy, the slice bounds, and the gain representation.
        exact ⟨H, hHpredictable, hHbounded, ⟨initialCapital, hrepr⟩⟩

end

end ProbabilityTheory
