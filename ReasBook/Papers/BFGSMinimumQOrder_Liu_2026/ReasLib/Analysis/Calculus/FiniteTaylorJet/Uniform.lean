module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Algebra
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Sqrt
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.CompositionBounds
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformAt
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

universe u v w x

namespace FiniteTaylorJet

variable {Θ : Type u} {E : Type v} {F : Type w} {G : Type x}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A jet family is uniform on `K` when each coefficient family is uniformly
bounded there and its order-`m` Peano remainder has every positive coefficient
on one common radius. -/
def IsUniformOn {m : ℕ} (f : Θ → E → F)
    (J : Θ → FiniteTaylorJet ℝ E F m) (a : E) (K : Set Θ) : Prop :=
  (∀ n : Fin (m + 1), ∃ B ≥ 0, ∀ θ ∈ K, ‖(J θ).coeff n‖ ≤ B) ∧
    ∀ C > 0, IsUniformRemainderOn f J a K C (m : ℝ)

namespace IsUniformOn

/-- The defining coefficient-boundedness and every-positive-coefficient
remainder characterization of a uniform finite jet family. -/
theorem spec {m : ℕ} (f : Θ → E → F)
    (J : Θ → FiniteTaylorJet ℝ E F m) (a : E) (K : Set Θ) :
    FiniteTaylorJet.IsUniformOn f J a K ↔
      (∀ n : Fin (m + 1), ∃ B ≥ 0, ∀ θ ∈ K, ‖(J θ).coeff n‖ ≤ B) ∧
        ∀ C > 0, IsUniformRemainderOn f J a K C (m : ℝ) := by
  -- Unfolding exposes precisely the coefficient and remainder clauses.
  rfl

/-- A uniform finite jet family has uniformly bounded coefficients in every
degree through `m`. -/
theorem boundedCoeff {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J a K) (n : Fin (m + 1)) :
    ∃ B ≥ 0, ∀ θ ∈ K, ‖(J θ).coeff n‖ ≤ B := by
  -- Project the degreewise boundedness clause of uniformity.
  exact hJ.1 n

/-- A uniform finite jet family supplies an order-`m` remainder estimate with
every prescribed positive coefficient. -/
theorem remainder {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J a K) (C : ℝ) (hC : 0 < C) :
    IsUniformRemainderOn f J a K C (m : ℝ) := by
  -- Specialize the every-positive-coefficient remainder clause.
  exact hJ.2 C hC

/-- At every parameter in the uniformity set, the function value at the base
equals the constant coefficient of its jet. -/
theorem value_eq_constantCoeff {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J a K) {θ : Θ} (hθ : θ ∈ K) :
    f θ a = (J θ).constantCoeff := by
  have hzero : (J θ).remainder (f θ) a 0 = 0 := by
    -- Bounds with arbitrarily small positive coefficients force the remainder at zero to vanish.
    apply norm_eq_zero.mp
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (norm_nonneg _)
    obtain ⟨δ, hδ, hbound⟩ :=
      IsUniformRemainderOn.bound (hJ.remainder ε hε)
    have hzeroBound := hbound θ hθ 0 (by simpa only [norm_zero] using hδ)
    calc
      ‖(J θ).remainder (f θ) a 0‖ ≤ ε * 0 ^ (m : ℝ) := by
        simpa only [norm_zero] using hzeroBound
      _ ≤ 0 + ε := by
        nlinarith [Real.zero_rpow_nonneg (m : ℝ), Real.zero_rpow_le_one (m : ℝ)]
  -- Expanding the zero increment identifies the two base values.
  rw [remainder_def, add_zero] at hzero
  rw [constantCoeff_apply]
  exact sub_eq_zero.mp hzero

/-- Uniform finite jets are closed under pointwise addition at a common input
base. -/
theorem add {m : ℕ} {f g : Θ → E → F}
    {P Q : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hQ : FiniteTaylorJet.IsUniformOn g Q a K) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ f θ z + g θ z)
      (fun θ ↦ FiniteTaylorJet.add (P θ) (Q θ)) a K := by
  constructor
  · intro n
    obtain ⟨BP, hBP, hPbound⟩ := hP.boundedCoeff n
    obtain ⟨BQ, hBQ, hQbound⟩ := hQ.boundedCoeff n
    refine ⟨BP + BQ, add_nonneg hBP hBQ, ?_⟩
    intro θ hθ
    -- Coefficientwise addition is controlled by the sum of the two bounds.
    rw [coeff_add]
    exact (norm_add_le _ _).trans (add_le_add (hPbound θ hθ) (hQbound θ hθ))
  · intro C hC
    -- Cross the opaque remainder predicate through its public radius projection.
    obtain ⟨δP, hδP, hPrem⟩ :=
      IsUniformRemainderOn.bound (hP.remainder (C / 2) (half_pos hC))
    obtain ⟨δQ, hδQ, hQrem⟩ :=
      IsUniformRemainderOn.bound (hQ.remainder (C / 2) (half_pos hC))
    refine (IsUniformRemainderOn.spec
      (fun θ z ↦ f θ z + g θ z) (fun θ ↦ FiniteTaylorJet.add (P θ) (Q θ))
      a K C (m : ℝ)).mpr ⟨min δP δQ, lt_min hδP hδQ, ?_⟩
    intro θ hθ h hh
    have hPsmall : ‖h‖ < δP := hh.trans_le (min_le_left _ _)
    have hQsmall : ‖h‖ < δQ := hh.trans_le (min_le_right _ _)
    have hrem :
        (FiniteTaylorJet.add (P θ) (Q θ)).remainder
            (fun z ↦ f θ z + g θ z) a h =
          (P θ).remainder (f θ) a h + (Q θ).remainder (g θ) a h := by
      -- Expand the three remainders and use additivity of jet evaluation.
      rw [remainder_def, remainder_def, remainder_def, eval_add]
      abel
    rw [hrem]
    calc
      ‖(P θ).remainder (f θ) a h + (Q θ).remainder (g θ) a h‖
          ≤ ‖(P θ).remainder (f θ) a h‖ + ‖(Q θ).remainder (g θ) a h‖ :=
        norm_add_le _ _
      _ ≤ (C / 2) * ‖h‖ ^ (m : ℝ) + (C / 2) * ‖h‖ ^ (m : ℝ) :=
        add_le_add (hPrem θ hθ h hPsmall) (hQrem θ hθ h hQsmall)
      _ = C * ‖h‖ ^ (m : ℝ) := by ring

/-- Uniformity is unchanged when both the function family and jet family agree
on the parameter set under consideration. -/
theorem congr {m : ℕ} {f g : Θ → E → F}
    {P Q : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hfun : ∀ θ ∈ K, f θ = g θ) (hjet : ∀ θ ∈ K, P θ = Q θ) :
    FiniteTaylorJet.IsUniformOn g Q a K := by
  constructor
  · intro n
    obtain ⟨B, hB, hbound⟩ := hP.boundedCoeff n
    refine ⟨B, hB, ?_⟩
    intro θ hθ
    -- Replace the target jet by the equal source jet before applying its coefficient bound.
    rw [← hjet θ hθ]
    exact hbound θ hθ
  · intro C hC
    obtain ⟨δ, hδ, hbound⟩ := IsUniformRemainderOn.bound (hP.remainder C hC)
    refine (IsUniformRemainderOn.spec g Q a K C (m : ℝ)).mpr ⟨δ, hδ, ?_⟩
    intro θ hθ h hh
    -- The concrete remainder only depends on the function and jet at this parameter.
    rw [← hfun θ hθ, ← hjet θ hθ]
    exact hbound θ hθ h hh

/-- All coefficients in a uniform finite jet family admit one common bound of
size at least one. -/
lemma exists_one_le_coeff_bound {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J a K) :
    ∃ B, 1 ≤ B ∧ ∀ n : Fin (m + 1), ∀ θ ∈ K, ‖(J θ).coeff n‖ ≤ B := by
  classical
  choose bound hboundNonneg hbound using hJ.boundedCoeff
  refine ⟨1 + ∑ n : Fin (m + 1), bound n, ?_, ?_⟩
  · -- The sum of nonnegative degreewise bounds can only enlarge one.
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ ↦ hboundNonneg n)
  · intro n θ hθ
    calc
      ‖(J θ).coeff n‖ ≤ bound n := hbound n θ hθ
      _ ≤ ∑ i : Fin (m + 1), bound i :=
        Finset.single_le_sum (fun i _ ↦ hboundNonneg i) (Finset.mem_univ n)
      _ ≤ 1 + ∑ i : Fin (m + 1), bound i := le_add_of_nonneg_left zero_le_one

/-- An order-zero jet has constant evaluation. -/
private lemma eval_orderZero (J : FiniteTaylorJet ℝ E F 0) (h : E) :
    J.eval h = J.constantCoeff := by
  -- The only coefficient has no input coordinates, so its value is independent of `h`.
  rw [constantCoeff_apply, eval_eq_sum, eval_eq_sum, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Two finite jets are equal when all their coefficient maps are equal. -/
private lemma ext_coeff {m : ℕ} {P Q : FiniteTaylorJet ℝ E F m}
    (h : ∀ n, P.coeff n = Q.coeff n) : P = Q := by
  cases P
  cases Q
  congr 1
  funext n
  exact h n

/-- Composition preserves the constant coefficient of the outer jet. -/
private lemma constantCoeff_comp {m : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) :
    (FiniteTaylorJet.comp Q P).constantCoeff = Q.constantCoeff := by
  -- The zeroth coefficient of formal composition is the outer zeroth coefficient.
  rw [constantCoeff_eq_coeff_zero, constantCoeff_eq_coeff_zero, coeff_comp]
  have hzero := FormalMultilinearSeries.comp_coeff_zero Q.toFormalMultilinearSeries
    P.toFormalMultilinearSeries (fun _ : Fin 0 ↦ (0 : E)) (fun _ : Fin 0 ↦ (0 : F))
  rw [toFormalMultilinearSeries_coeff_of_le Q (Nat.zero_le m)] at hzero
  convert hzero using 1 <;> rfl

/-- Uniform jets compose when the outer jets have uniform coefficients and
remainders at a parameter-dependent family of matching base points. -/
private lemma comp_of_uniformOuterAt {m : ℕ} {f : Θ → E → F} {g : Θ → F → G}
    {P : Θ → FiniteTaylorJet ℝ E F m}
    {Q : Θ → FiniteTaylorJet ℝ F G m} {a : E} {b : Θ → F} {K : Set Θ}
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hQcoeff : ∀ n : Fin (m + 1), ∃ B ≥ 0, ∀ θ ∈ K, ‖(Q θ).coeff n‖ ≤ B)
    (hQrem : ∀ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ k : F, ‖k‖ < δ →
      ‖(Q θ).remainder (g θ) (b θ) k‖ ≤ C * ‖k‖ ^ (m : ℝ))
    (hbase : ∀ θ ∈ K, f θ a = b θ) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ g θ (f θ z))
      (fun θ ↦ FiniteTaylorJet.comp (Q θ) (P θ)) a K := by
  obtain ⟨BP, hBP, hPcoeff⟩ := hP.exists_one_le_coeff_bound
  choose qbound hqboundNonneg hqbound using hQcoeff
  let BQ := 1 + ∑ n : Fin (m + 1), qbound n
  have hBQ : 1 ≤ BQ := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ ↦ hqboundNonneg n)
  have hQcoeff' : ∀ n : Fin (m + 1), ∀ θ ∈ K, ‖(Q θ).coeff n‖ ≤ BQ := by
    intro n θ hθ
    calc
      ‖(Q θ).coeff n‖ ≤ qbound n := hqbound n θ hθ
      _ ≤ ∑ i : Fin (m + 1), qbound i :=
        Finset.single_le_sum (fun i _ ↦ hqboundNonneg i) (Finset.mem_univ n)
      _ ≤ BQ := le_add_of_nonneg_left zero_le_one
  constructor
  · intro n
    refine ⟨∑ c : Composition (n : ℕ), BQ * BP ^ c.length, ?_, ?_⟩
    · exact Finset.sum_nonneg fun c _ ↦
        mul_nonneg (zero_le_one.trans hBQ) (pow_nonneg (zero_le_one.trans hBP) _)
    · intro θ hθ
      -- The formal composition estimate gives a parameter-independent coefficient bound.
      exact norm_coeff_comp_le (P θ) (Q θ)
        (fun i ↦ hPcoeff i θ hθ) (fun i ↦ hQcoeff' i θ hθ) n
  · intro C hC
    cases m with
    | zero =>
        obtain ⟨δQ, hδQ, hQbound⟩ := hQrem C hC
        obtain ⟨δP, hδP, hPbound⟩ :=
          IsUniformRemainderOn.bound (hP.remainder (δQ / 2) (half_pos hδQ))
        refine (IsUniformRemainderOn.spec
          (fun θ z ↦ g θ (f θ z))
          (fun θ ↦ FiniteTaylorJet.comp (Q θ) (P θ)) a K C ((0 : ℕ) : ℝ)).mpr
          ⟨δP, hδP, ?_⟩
        intro θ hθ h hh
        let k := f θ (a + h) - b θ
        have hkrem : k = (P θ).remainder (f θ) a h := by
          dsimp only [k]
          rw [remainder_def, eval_orderZero, ← hP.value_eq_constantCoeff hθ,
            hbase θ hθ]
        have hkδ : ‖k‖ < δQ := by
          have hp := hPbound θ hθ h hh
          norm_num [Real.rpow_zero] at hp
          calc
            ‖k‖ = ‖(P θ).remainder (f θ) a h‖ := by rw [hkrem]
            _ ≤ δQ / 2 := hp
            _ < δQ := half_lt_self hδQ
        have hrem :
            (FiniteTaylorJet.comp (Q θ) (P θ)).remainder
                (fun z ↦ g θ (f θ z)) a h =
              (Q θ).remainder (g θ) (b θ) k := by
          rw [remainder_def, remainder_def, eval_orderZero, eval_orderZero]
          rw [constantCoeff_comp]
          have hbk : b θ + k = f θ (a + h) := by
            dsimp only [k]
            abel
          rw [hbk]
        rw [hrem]
        have hout := hQbound θ hθ k hkδ
        norm_num [Real.rpow_zero] at hout ⊢
        exact hout
    | succ n =>
        let LP := ∑ i : Fin (n + 2), BP * (i : ℕ)
        let LQ := ∑ i : Fin (n + 2), BQ * (i : ℕ)
        have hLP : 0 ≤ LP := Finset.sum_nonneg fun i _ ↦
          mul_nonneg (zero_le_one.trans hBP) (Nat.cast_nonneg (i : ℕ))
        have hLQ : 0 ≤ LQ := Finset.sum_nonneg fun i _ ↦
          mul_nonneg (zero_le_one.trans hBQ) (Nat.cast_nonneg (i : ℕ))
        let εP := C / (3 * (LQ + 1))
        have hεP : 0 < εP := div_pos hC (mul_pos (by norm_num) (by linarith))
        let M := LP + εP + 1
        have hM : 0 < M := by dsimp only [M]; linarith
        have hMone : 1 ≤ M := by dsimp only [M]; linarith
        let εQ := C / (3 * M ^ (n + 1))
        have hεQ : 0 < εQ := div_pos hC (mul_pos (by norm_num) (pow_pos hM _))
        obtain ⟨D, hD, htail⟩ := exists_compEvalTailBound (E := E) (F := F)
          (G := G) (n + 1) BP BQ (zero_le_one.trans hBP) (zero_le_one.trans hBQ)
        obtain ⟨δP, hδP, hPbound⟩ :=
          IsUniformRemainderOn.bound (hP.remainder εP hεP)
        obtain ⟨δQ, hδQ, hQbound⟩ := hQrem εQ hεQ
        let δ := min δP
          (min (δQ / M) (min (1 / M) (C / (3 * (D + 1)))))
        have hδ : 0 < δ := by
          dsimp only [δ]
          exact lt_min hδP (lt_min (div_pos hδQ hM)
            (lt_min (one_div_pos.mpr hM)
              (div_pos hC (mul_pos (by norm_num) (by linarith)))))
        refine (IsUniformRemainderOn.spec
          (fun θ z ↦ g θ (f θ z))
          (fun θ ↦ FiniteTaylorJet.comp (Q θ) (P θ)) a K C _).mpr
          ⟨δ, hδ, ?_⟩
        intro θ hθ h hh
        have hhP : ‖h‖ < δP := hh.trans_le (min_le_left _ _)
        have hhQ : ‖h‖ < δQ / M :=
          hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have hhM : ‖h‖ < 1 / M :=
          hh.trans_le ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))
        have hhTail : ‖h‖ < C / (3 * (D + 1)) :=
          hh.trans_le ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _)))
        have hunit : ‖h‖ ≤ 1 := by
          have hmul : ‖h‖ * M < 1 := (lt_div_iff₀ hM).mp hhM
          nlinarith [norm_nonneg h]
        have hpow_le : ‖h‖ ^ (n + 1) ≤ ‖h‖ := by
          simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg h) hunit
            (Nat.succ_le_succ (Nat.zero_le n))
        let u := (P θ).eval h - (P θ).constantCoeff
        let k := f θ (a + h) - b θ
        let rP := (P θ).remainder (f θ) a h
        have hsumP :
            ∑ i : Fin (n + 2), ‖(P θ).coeff i‖ * (i : ℕ) *
                (1 : ℝ) ^ ((i : ℕ) - 1) ≤ LP := by
          simp only [one_pow, mul_one, LP]
          exact Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_right (hPcoeff i θ hθ) (Nat.cast_nonneg (i : ℕ))
        have hu : ‖u‖ ≤ LP * ‖h‖ := by
          have hu' := norm_eval_sub_eval_le (P θ) h 0 1 hunit (by simp)
          calc
            ‖u‖ = ‖(P θ).eval h - (P θ).eval 0‖ := by
              dsimp only [u]
              rw [constantCoeff_apply]
            _ ≤ ‖h - 0‖ * ∑ i : Fin (n + 2), ‖(P θ).coeff i‖ *
                (i : ℕ) * (1 : ℝ) ^ ((i : ℕ) - 1) := hu'
            _ ≤ ‖h‖ * LP := by
              simpa only [sub_zero] using
                mul_le_mul_of_nonneg_left hsumP (norm_nonneg h)
            _ = LP * ‖h‖ := mul_comm _ _
        have hrP : ‖rP‖ ≤ εP * ‖h‖ ^ (n + 1) := by
          simpa only [rP, Real.rpow_natCast] using hPbound θ hθ h hhP
        have hkdecomp : k = u + rP := by
          dsimp only [k, u, rP]
          rw [remainder_def, ← hP.value_eq_constantCoeff hθ, hbase θ hθ]
          abel
        have hk : ‖k‖ ≤ M * ‖h‖ := by
          rw [hkdecomp]
          calc
            ‖u + rP‖ ≤ ‖u‖ + ‖rP‖ := norm_add_le _ _
            _ ≤ LP * ‖h‖ + εP * ‖h‖ ^ (n + 1) := add_le_add hu hrP
            _ ≤ LP * ‖h‖ + εP * ‖h‖ :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow_le hεP.le)
            _ ≤ M * ‖h‖ := by
              dsimp only [M]
              nlinarith [norm_nonneg h]
        have hMh : M * ‖h‖ < 1 := by
          have := (lt_div_iff₀ hM).mp hhM
          simpa only [mul_comm] using this
        have hkunit : ‖k‖ ≤ 1 := hk.trans (le_of_lt hMh)
        have huunit : ‖u‖ ≤ 1 := by
          calc
            ‖u‖ ≤ LP * ‖h‖ := hu
            _ ≤ M * ‖h‖ := mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith)
              (norm_nonneg h)
            _ ≤ 1 := le_of_lt hMh
        have hkδ : ‖k‖ < δQ := by
          calc
            ‖k‖ ≤ M * ‖h‖ := hk
            _ < δQ := by
              have := (lt_div_iff₀ hM).mp hhQ
              simpa only [mul_comm] using this
        have hsumQ :
            ∑ i : Fin (n + 2), ‖(Q θ).coeff i‖ * (i : ℕ) *
                (1 : ℝ) ^ ((i : ℕ) - 1) ≤ LQ := by
          simp only [one_pow, mul_one, LQ]
          exact Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_right (hQcoeff' i θ hθ) (Nat.cast_nonneg (i : ℕ))
        have hku : k - u = rP := by rw [hkdecomp, add_sub_cancel_left]
        have hmiddle : ‖(Q θ).eval k - (Q θ).eval u‖ ≤
            (C / 3) * ‖h‖ ^ (n + 1) := by
          calc
            ‖(Q θ).eval k - (Q θ).eval u‖ ≤
                ‖k - u‖ * ∑ i : Fin (n + 2), ‖(Q θ).coeff i‖ *
                  (i : ℕ) * (1 : ℝ) ^ ((i : ℕ) - 1) :=
              norm_eval_sub_eval_le (Q θ) k u 1 hkunit huunit
            _ ≤ ‖rP‖ * LQ := by
              rw [hku]
              exact mul_le_mul_of_nonneg_left hsumQ (norm_nonneg rP)
            _ ≤ (εP * ‖h‖ ^ (n + 1)) * LQ :=
              mul_le_mul_of_nonneg_right hrP hLQ
            _ ≤ (C / 3) * ‖h‖ ^ (n + 1) := by
              have hεPLQ : εP * LQ ≤ C / 3 := by
                dsimp only [εP]
                rw [div_mul_eq_mul_div,
                  div_le_iff₀ (mul_pos (by norm_num) (by linarith : 0 < LQ + 1))]
                calc
                  C * LQ ≤ C * (LQ + 1) := by nlinarith
                  _ = C / 3 * (3 * (LQ + 1)) := by ring
              nlinarith [pow_nonneg (norm_nonneg h) (n + 1)]
        have houter : ‖(Q θ).remainder (g θ) (b θ) k‖ ≤
            (C / 3) * ‖h‖ ^ (n + 1) := by
          have hout := hQbound θ hθ k hkδ
          rw [Real.rpow_natCast] at hout
          calc
            ‖(Q θ).remainder (g θ) (b θ) k‖ ≤ εQ * ‖k‖ ^ (n + 1) := hout
            _ ≤ εQ * (M * ‖h‖) ^ (n + 1) :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg k) hk (n + 1)) hεQ.le
            _ = (C / 3) * ‖h‖ ^ (n + 1) := by
              dsimp only [εQ]
              rw [mul_pow]
              field_simp [ne_of_gt hM]
        have htail' : ‖(Q θ).eval u -
            (FiniteTaylorJet.comp (Q θ) (P θ)).eval h‖ ≤
              (C / 3) * ‖h‖ ^ (n + 1) := by
          have ht := htail (P θ) (Q θ) (fun i ↦ hPcoeff i θ hθ)
            (fun i ↦ hQcoeff' i θ hθ) h hunit
          have hDh : D * ‖h‖ ≤ C / 3 := by
            have hden : 0 < 3 * (D + 1) := mul_pos (by norm_num) (by linarith)
            have hscaled : ‖h‖ * (3 * (D + 1)) < C :=
              (lt_div_iff₀ hden).mp hhTail
            nlinarith [norm_nonneg h]
          calc
            ‖(Q θ).eval u - (FiniteTaylorJet.comp (Q θ) (P θ)).eval h‖ ≤
                D * ‖h‖ ^ (n + 2) := by simpa only [u] using ht
            _ = (D * ‖h‖) * ‖h‖ ^ (n + 1) := by ring
            _ ≤ (C / 3) * ‖h‖ ^ (n + 1) :=
              mul_le_mul_of_nonneg_right hDh (pow_nonneg (norm_nonneg h) _)
        have hrem :
            (FiniteTaylorJet.comp (Q θ) (P θ)).remainder
                (fun z ↦ g θ (f θ z)) a h =
              (Q θ).remainder (g θ) (b θ) k +
                ((Q θ).eval k - (Q θ).eval u) +
                  ((Q θ).eval u - (FiniteTaylorJet.comp (Q θ) (P θ)).eval h) := by
          rw [remainder_def, remainder_def]
          have hbk : b θ + k = f θ (a + h) := by
            dsimp only [k]
            abel
          rw [hbk]
          abel
        rw [hrem]
        calc
          ‖(Q θ).remainder (g θ) (b θ) k +
              ((Q θ).eval k - (Q θ).eval u) +
                ((Q θ).eval u - (FiniteTaylorJet.comp (Q θ) (P θ)).eval h)‖ ≤
              ‖(Q θ).remainder (g θ) (b θ) k‖ +
                ‖(Q θ).eval k - (Q θ).eval u‖ +
                  ‖(Q θ).eval u - (FiniteTaylorJet.comp (Q θ) (P θ)).eval h‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ ≤ (C / 3) * ‖h‖ ^ (n + 1) +
              (C / 3) * ‖h‖ ^ (n + 1) +
                (C / 3) * ‖h‖ ^ (n + 1) :=
            add_le_add (add_le_add houter hmiddle) htail'
          _ = C * ‖h‖ ^ ((n + 1 : ℕ) : ℝ) := by
            rw [Real.rpow_natCast]
            ring

/-- The derivative-constructed jet of a fixed smooth function is uniform over
an arbitrary parameter set. -/
private lemma const_ofFunction {m : ℕ} (g : F → G) (b : F) (K : Set Θ)
    (hg : ContDiffAt ℝ m g b) :
    FiniteTaylorJet.IsUniformOn (fun _ : Θ ↦ g)
      (fun _ ↦ FiniteTaylorJet.ofFunction ℝ m g b) b K := by
  constructor
  · intro n
    refine ⟨‖(FiniteTaylorJet.ofFunction ℝ m g b).coeff n‖, norm_nonneg _, ?_⟩
    intro θ hθ
    exact le_rfl
  · intro C hC
    have hjoint : ContDiffAt ℝ m (Function.uncurry (fun _ : F ↦ g)) (0, b) := by
      -- The auxiliary parameter is ignored, so only smoothness in the second factor matters.
      change ContDiffAt ℝ m (g ∘ Prod.snd) (0, b)
      exact hg.comp (0, b) contDiffAt_snd
    have hsingle := uniformRemainderOn_of_contDiffAt m (fun _ : F ↦ g) b
      ({0} : Set F) isCompact_singleton (fun θ hθ ↦ by
        rw [Set.mem_singleton_iff] at hθ
        subst θ
        exact hjoint) C hC
    obtain ⟨δ, hδ, hbound⟩ := IsUniformRemainderOn.bound hsingle
    refine (IsUniformRemainderOn.spec (fun _ : Θ ↦ g)
      (fun _ ↦ FiniteTaylorJet.ofFunction ℝ m g b) b K C (m : ℝ)).mpr
      ⟨δ, hδ, ?_⟩
    intro θ hθ h hh
    exact hbound 0 (Set.mem_singleton 0) h hh

/-- Pairing two uniform jet families preserves uniformity. -/
private lemma prod_uniform {m : ℕ} {f : Θ → E → F} {g : Θ → E → G}
    {P : Θ → FiniteTaylorJet ℝ E F m} {Q : Θ → FiniteTaylorJet ℝ E G m}
    {a : E} {K : Set Θ} (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hQ : FiniteTaylorJet.IsUniformOn g Q a K) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ (f θ z, g θ z))
      (fun θ ↦ FiniteTaylorJet.prod (P θ) (Q θ)) a K := by
  constructor
  · intro n
    obtain ⟨BP, hBP, hPbound⟩ := hP.boundedCoeff n
    obtain ⟨BQ, hBQ, hQbound⟩ := hQ.boundedCoeff n
    refine ⟨max BP BQ, hBP.trans (le_max_left _ _), ?_⟩
    intro θ hθ
    rw [coeff_prod, ContinuousMultilinearMap.opNorm_prod]
    exact max_le_max (hPbound θ hθ) (hQbound θ hθ)
  · intro C hC
    obtain ⟨δP, hδP, hPbound⟩ :=
      IsUniformRemainderOn.bound (hP.remainder C hC)
    obtain ⟨δQ, hδQ, hQbound⟩ :=
      IsUniformRemainderOn.bound (hQ.remainder C hC)
    refine (IsUniformRemainderOn.spec (fun θ z ↦ (f θ z, g θ z))
      (fun θ ↦ FiniteTaylorJet.prod (P θ) (Q θ)) a K C (m : ℝ)).mpr
      ⟨min δP δQ, lt_min hδP hδQ, ?_⟩
    intro θ hθ h hh
    have hhP : ‖h‖ < δP := hh.trans_le (min_le_left _ _)
    have hhQ : ‖h‖ < δQ := hh.trans_le (min_le_right _ _)
    have heval : (FiniteTaylorJet.prod (P θ) (Q θ)).eval h =
        ((P θ).eval h, (Q θ).eval h) := by
      -- Pairing coefficients commutes with the finite diagonal sum.
      rw [eval_eq_sum]
      simp only [coeff_prod, ContinuousMultilinearMap.prod_apply]
      apply Prod.ext
      · simp only [Prod.fst_sum, eval_eq_sum]
      · simp only [Prod.snd_sum, eval_eq_sum]
    have hrem : (FiniteTaylorJet.prod (P θ) (Q θ)).remainder
        (fun z ↦ (f θ z, g θ z)) a h =
          ((P θ).remainder (f θ) a h, (Q θ).remainder (g θ) a h) := by
      rw [remainder_def, heval, remainder_def, remainder_def]
      rfl
    rw [hrem, Prod.norm_def]
    apply max_le
    · exact hPbound θ hθ h hhP
    · exact hQbound θ hθ h hhQ

/-- The derivative of algebra multiplication at `b` has norm at most `2 * ‖b‖`. -/
private lemma norm_mulDeriv_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (b : A × A) :
    ‖(ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).deriv₂ b‖ ≤ 2 * ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (norm_nonneg b)) ?_
  intro k
  rw [ContinuousLinearMap.coe_deriv₂]
  calc
    ‖b.1 * k.2 + k.1 * b.2‖ ≤ ‖b.1 * k.2‖ + ‖k.1 * b.2‖ := norm_add_le _ _
    _ ≤ ‖b.1‖ * ‖k.2‖ + ‖k.1‖ * ‖b.2‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖b‖ * ‖k‖ + ‖k‖ * ‖b‖ := by
      gcongr
      · exact norm_fst_le b
      · exact norm_snd_le k
      · exact norm_fst_le k
      · exact norm_snd_le b
    _ = 2 * ‖b‖ * ‖k‖ := by ring

/-- The quadratic coefficient of algebra multiplication has norm at most one. -/
private lemma norm_mulBilinear_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] :
    ‖(ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).uncurryBilinear‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one ?_
  intro v
  rw [ContinuousLinearMap.uncurryBilinear_apply, one_mul]
  calc
    ‖(v 0).1 * (v 1).2‖ ≤ ‖(v 0).1‖ * ‖(v 1).2‖ := norm_mul_le _ _
    _ ≤ ‖v 0‖ * ‖v 1‖ := by
      gcongr
      · exact norm_fst_le (v 0)
      · exact norm_snd_le (v 1)
    _ = ∏ i, ‖v i‖ := by rw [Fin.prod_univ_two]

/-- Every coefficient of the explicit bilinear power series is bounded in
terms of a bound for its expansion center. -/
private lemma norm_mulPowerSeries_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {B : ℝ} (hB : 1 ≤ B) {b : A × A} (hb : ‖b‖ ≤ B) (n : ℕ) :
    ‖(ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear b n‖ ≤
      B ^ 2 + 2 * B + 1 := by
  let M := (ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A)
  cases n with
  | zero =>
      rw [ContinuousLinearMap.fpowerSeriesBilinear_apply_zero,
        ContinuousMultilinearMap.uncurry0_norm]
      calc
        ‖b.1 * b.2‖ ≤ ‖b.1‖ * ‖b.2‖ := norm_mul_le _ _
        _ ≤ B ^ 2 := by
          rw [pow_two]
          exact mul_le_mul (norm_fst_le b |>.trans hb) (norm_snd_le b |>.trans hb)
            (norm_nonneg _) (zero_le_one.trans hB)
        _ ≤ B ^ 2 + 2 * B + 1 := by nlinarith
  | succ n =>
      cases n with
      | zero =>
          rw [ContinuousLinearMap.fpowerSeriesBilinear_apply_one,
            LinearIsometryEquiv.norm_map]
          exact (norm_mulDeriv_le b).trans (by nlinarith)
      | succ n =>
          cases n with
          | zero =>
              rw [ContinuousLinearMap.fpowerSeriesBilinear_apply_two]
              exact norm_mulBilinear_le.trans (by nlinarith)
          | succ n =>
              rw [ContinuousLinearMap.fpowerSeriesBilinear_apply_add_three]
              have hnonneg : (0 : ℝ) ≤ B ^ 2 + 2 * B + 1 := by positivity
              simpa only [norm_zero] using hnonneg

/-- The iterated derivative of multiplication is bounded by the factorial
times the corresponding explicit power-series coefficient. -/
private lemma norm_iteratedFDeriv_mul_le_factorial {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] (b : A × A) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z : A × A ↦ z.1 * z.2) b‖ ≤
      n.factorial *
        ‖(ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear b n‖ := by
  let M := (ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A)
  let p := M.fpowerSeriesBilinear b
  have hf := M.hasFPowerSeriesOnBall_bilinear b
  have ha := M.analyticOn_bilinear Set.univ
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg (p n))) ?_
  intro v
  change ‖iteratedFDeriv ℝ n (fun z : A × A ↦ M z.1 z.2) b v‖ ≤
    n.factorial * ‖p n‖ * ∏ i, ‖v i‖
  rw [hf.iteratedFDeriv_eq_sum ha v]
  calc
    ‖∑ σ : Equiv.Perm (Fin n), p n (fun i ↦ v (σ i))‖ ≤
        ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i ↦ v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
      gcongr with σ
      calc
        ‖p n (fun i ↦ v (σ i))‖ ≤ ‖p n‖ * ∏ i, ‖v (σ i)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖p n‖ * ∏ i, ‖v i‖ := by
          congr 1
          exact Equiv.prod_comp σ (fun i ↦ ‖v i‖)
    _ = n.factorial * ‖p n‖ * ∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]
      ring

/-- For an everywhere analytic function, the derivative-constructed finite
jet evaluates as the corresponding power-series partial sum. -/
private lemma eval_ofFunction_eq_partialSum {f : E → F}
    {p : FormalMultilinearSeries ℝ E F} {x : E} {r : ENNReal}
    (hf : HasFPowerSeriesOnBall f p x r) (ha : AnalyticOn ℝ f Set.univ)
    (m : ℕ) (h : E) :
    (FiniteTaylorJet.ofFunction ℝ m f x).eval h = p.partialSum (m + 1) h := by
  rw [FiniteTaylorJet.eval_eq_sum, FormalMultilinearSeries.partialSum,
    ← Fin.sum_univ_eq_sum_range]
  congr with n
  rw [FiniteTaylorJet.coeff_ofFunction_apply,
    hf.iteratedFDeriv_eq_sum ha (fun _ ↦ h)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n : ℕ))), one_smul]

/-- The zeroth partial sum of the multiplication series is its center value. -/
private lemma mulPowerSeries_partialSum_one {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] (b k : A × A) :
    ((ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear b).partialSum
        1 k = b.1 * b.2 := by
  rw [FormalMultilinearSeries.partialSum]
  simp [ContinuousLinearMap.fpowerSeriesBilinear]

/-- The first-order partial sum of the multiplication series is its affine part. -/
private lemma mulPowerSeries_partialSum_two {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] (b k : A × A) :
    ((ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear b).partialSum
        2 k = b.1 * b.2 + (b.1 * k.2 + k.1 * b.2) := by
  rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp [ContinuousLinearMap.fpowerSeriesBilinear,
    continuousMultilinearCurryFin1_symm_apply, ContinuousLinearMap.coe_deriv₂]

/-- Every partial sum through degree at least two evaluates multiplication exactly. -/
private lemma mulPowerSeries_partialSum_add_three {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] (b k : A × A) (n : ℕ) :
    ((ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear b).partialSum
        (n + 3) k = (b.1 + k.1) * (b.2 + k.2) := by
  let M := (ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A)
  let p := M.fpowerSeriesBilinear b
  have hf := M.hasFPowerSeriesOnBall_bilinear b
  have hfinite : HasFiniteFPowerSeriesOnBall (fun z : A × A ↦ z.1 * z.2)
      p b 3 ⊤ := by
    refine ⟨hf, ?_⟩
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm]
    exact ContinuousLinearMap.fpowerSeriesBilinear_apply_add_three _ _ _
  simpa only [Prod.fst_add, Prod.snd_add, p] using
    (hfinite.eq_partialSum k (by simp) (n + 3) (by omega)).symm

/-- Uniform finite jets compose when the inner family sends its common base to
the common expansion base of the outer family. -/
theorem comp {m : ℕ} {f : Θ → E → F} {g : Θ → F → G}
    {P : Θ → FiniteTaylorJet ℝ E F m}
    {Q : Θ → FiniteTaylorJet ℝ F G m} {a : E} {b : F} {K : Set Θ}
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hQ : FiniteTaylorJet.IsUniformOn g Q b K)
    (hbase : ∀ θ ∈ K, f θ a = b) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ g θ (f θ z))
      (fun θ ↦ FiniteTaylorJet.comp (Q θ) (P θ)) a K := by
  -- Apply the variable-base composition estimate to the constant outer base family.
  exact comp_of_uniformOuterAt hP (fun n ↦ hQ.boundedCoeff n)
    (fun C hC ↦ IsUniformRemainderOn.bound (hQ.remainder C hC))
    (fun θ hθ ↦ hbase θ hθ)

/-- Uniform finite jets with values in a normed real algebra are closed under
pointwise multiplication. -/
theorem mul {A : Type w} [NormedRing A] [NormedAlgebra ℝ A]
    {m : ℕ} {f g : Θ → E → A} {P Q : Θ → FiniteTaylorJet ℝ E A m}
    {a : E} {K : Set Θ} (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hQ : FiniteTaylorJet.IsUniformOn g Q a K) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ f θ z * g θ z)
      (fun θ ↦ FiniteTaylorJet.mul (P θ) (Q θ)) a K := by
  let μ : A × A → A := fun z ↦ z.1 * z.2
  let pair : Θ → FiniteTaylorJet ℝ E (A × A) m :=
    fun θ ↦ FiniteTaylorJet.prod (P θ) (Q θ)
  have hpair :
      FiniteTaylorJet.IsUniformOn (fun θ z ↦ (f θ z, g θ z)) pair a K := by
    exact prod_uniform hP hQ
  obtain ⟨B, hB, hcoeff⟩ := hpair.exists_one_le_coeff_bound
  let b : Θ → A × A := fun θ ↦ (pair θ).constantCoeff
  let outer : Θ → FiniteTaylorJet ℝ (A × A) A m :=
    fun θ ↦ FiniteTaylorJet.ofFunction ℝ m μ (b θ)
  have hb : ∀ θ ∈ K, ‖b θ‖ ≤ B := by
    intro θ hθ
    dsimp [b]
    rw [constantCoeff_eq_coeff_zero]
    calc
      ‖((pair θ).coeff (0 : Fin (m + 1))) (fun _ ↦ 0)‖ =
          ‖(pair θ).coeff (0 : Fin (m + 1))‖ := by
        exact ContinuousMultilinearMap.fin0_apply_norm _
      _ ≤ B := hcoeff 0 θ hθ
  have houterCoeff :
      ∀ n : Fin (m + 1), ∃ Cn ≥ 0, ∀ θ ∈ K, ‖(outer θ).coeff n‖ ≤ Cn := by
    intro n
    let D : ℝ := B ^ 2 + 2 * B + 1
    let Cn : ℝ := ‖(((n : ℕ).factorial : ℝ)⁻¹)‖ *
      (((n : ℕ).factorial : ℝ) * D)
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    refine ⟨Cn, ?_, ?_⟩
    · dsimp [Cn]
      positivity
    · intro θ hθ
      dsimp [outer]
      rw [FiniteTaylorJet.coeff_ofFunction, norm_smul]
      calc
        ‖(((n : ℕ).factorial : ℝ)⁻¹)‖ *
              ‖iteratedFDeriv ℝ (n : ℕ) μ (b θ)‖ ≤
            ‖(((n : ℕ).factorial : ℝ)⁻¹)‖ *
              (((n : ℕ).factorial : ℝ) *
                ‖(ContinuousLinearMap.mul ℝ A :
                  A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear (b θ) (n : ℕ)‖) := by
          have hderiv :
              ‖iteratedFDeriv ℝ (n : ℕ) μ (b θ)‖ ≤
                ((n : ℕ).factorial : ℝ) *
                  ‖(ContinuousLinearMap.mul ℝ A :
                    A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear (b θ) (n : ℕ)‖ := by
            simpa [μ] using
              (norm_iteratedFDeriv_mul_le_factorial (A := A) (b θ) (n : ℕ))
          have hscaled := mul_le_mul_of_nonneg_left hderiv
            (norm_nonneg (((n : ℕ).factorial : ℝ)⁻¹))
          simpa only [mul_assoc] using hscaled
        _ ≤ Cn := by
          dsimp [Cn, D]
          have hseries :
              ((n : ℕ).factorial : ℝ) *
                  ‖(ContinuousLinearMap.mul ℝ A :
                    A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear (b θ) (n : ℕ)‖ ≤
                ((n : ℕ).factorial : ℝ) * (B ^ 2 + 2 * B + 1) :=
            mul_le_mul_of_nonneg_left
              (norm_mulPowerSeries_le (A := A) hB (hb θ hθ) (n : ℕ))
              (Nat.cast_nonneg _)
          have hscaled := mul_le_mul_of_nonneg_left hseries
            (norm_nonneg (((n : ℕ).factorial : ℝ)⁻¹))
          simpa only [Real.norm_eq_abs] using hscaled
  have houterEval : ∀ (θ : Θ) (k : A × A),
      (outer θ).eval k =
        ((ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A).fpowerSeriesBilinear
          (b θ)).partialSum (m + 1) k := by
    intro θ k
    dsimp [outer, μ]
    exact eval_ofFunction_eq_partialSum
      ((ContinuousLinearMap.mul ℝ A).hasFPowerSeriesOnBall_bilinear (b θ))
      ((ContinuousLinearMap.mul ℝ A).analyticOn_bilinear Set.univ) m k
  have houterRem :
      ∀ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ k : A × A, ‖k‖ < δ →
        ‖(outer θ).remainder (fun z : A × A ↦ z.1 * z.2) (b θ) k‖ ≤
          C * ‖k‖ ^ (m : ℝ) := by
    intro C hC
    cases m with
    | zero =>
        let δ : ℝ := min 1 (C / (2 * B + 1))
        have hden : 0 < 2 * B + 1 := by
          nlinarith [hB]
        have hone : (0 : ℝ) < 1 := by
          norm_num
        have hδ : 0 < δ := by
          dsimp [δ]
          exact lt_min hone (div_pos hC hden)
        refine ⟨δ, hδ, ?_⟩
        intro θ hθ k hk
        have hkunit : ‖k‖ ≤ 1 :=
          (le_of_lt (hk.trans_le (min_le_left _ _)))
        have hb1 : ‖(b θ).1‖ ≤ B :=
          (norm_fst_le (b θ)).trans (hb θ hθ)
        have hb2 : ‖(b θ).2‖ ≤ B :=
          (norm_snd_le (b θ)).trans (hb θ hθ)
        have hk1 : ‖k.1‖ ≤ ‖k‖ := norm_fst_le k
        have hk2 : ‖k.2‖ ≤ ‖k‖ := norm_snd_le k
        have hkk : ‖k‖ * ‖k‖ ≤ ‖k‖ := by
          calc
            ‖k‖ * ‖k‖ ≤ ‖k‖ * 1 :=
              mul_le_mul_of_nonneg_left hkunit (norm_nonneg _)
            _ = ‖k‖ := by ring
        have hpoly :
            ‖(b θ).1 * k.2 + k.1 * (b θ).2 + k.1 * k.2‖ ≤
              (2 * B + 1) * ‖k‖ := by
          calc
            ‖(b θ).1 * k.2 + k.1 * (b θ).2 + k.1 * k.2‖ ≤
                ‖(b θ).1‖ * ‖k.2‖ + ‖k.1‖ * ‖(b θ).2‖ +
                  ‖k.1‖ * ‖k.2‖ := by
              calc
                ‖(b θ).1 * k.2 + k.1 * (b θ).2 + k.1 * k.2‖ ≤
                    ‖(b θ).1 * k.2‖ + ‖k.1 * (b θ).2‖ +
                      ‖k.1 * k.2‖ := by
                  exact (norm_add_le _ _).trans
                    (add_le_add (norm_add_le _ _) (le_refl _))
                _ ≤ ‖(b θ).1‖ * ‖k.2‖ + ‖k.1‖ * ‖(b θ).2‖ +
                    ‖k.1‖ * ‖k.2‖ := by
                  exact add_le_add
                    (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
                    (norm_mul_le _ _)
            _ ≤ B * ‖k‖ + ‖k‖ * B + ‖k‖ * ‖k‖ := by
              exact add_le_add
                (add_le_add
                  (mul_le_mul hb1 hk2 (norm_nonneg _) (zero_le_one.trans hB))
                  (mul_le_mul hk1 hb2 (norm_nonneg _) (norm_nonneg _)))
                (mul_le_mul hk1 hk2 (norm_nonneg _) (norm_nonneg _))
            _ ≤ (2 * B + 1) * ‖k‖ := by
              nlinarith [hkk]
        have heval : (outer θ).eval k = (b θ).1 * (b θ).2 := by
          rw [houterEval θ k]
          exact mulPowerSeries_partialSum_one _ _
        rw [remainder_def, heval]
        have hdiff :
            (b θ + k).1 * (b θ + k).2 - (b θ).1 * (b θ).2 =
              (b θ).1 * k.2 + k.1 * (b θ).2 + k.1 * k.2 := by
          simp only [Prod.fst_add, Prod.snd_add]
          noncomm_ring
        rw [hdiff]
        have hkC : (2 * B + 1) * ‖k‖ < C := by
          have hkdiv : ‖k‖ < C / (2 * B + 1) :=
            hk.trans_le (min_le_right _ _)
          have htmp := (lt_div_iff₀ hden).mp hkdiv
          simpa [mul_comm] using htmp
        have hlt :
            ‖(b θ).1 * k.2 + k.1 * (b θ).2 + k.1 * k.2‖ < C :=
          hpoly.trans_lt hkC
        simpa [Real.rpow_zero] using hlt.le
    | succ m' =>
        cases m' with
        | zero =>
            let δ : ℝ := C
            have hδ : 0 < δ := by simpa [δ] using hC
            refine ⟨δ, hδ, ?_⟩
            intro θ hθ k hk
            have hk1 : ‖k.1‖ ≤ ‖k‖ := norm_fst_le k
            have hk2 : ‖k.2‖ ≤ ‖k‖ := norm_snd_le k
            have hprod : ‖k.1 * k.2‖ ≤ ‖k‖ * ‖k‖ := by
              exact (norm_mul_le _ _).trans
                (mul_le_mul hk1 hk2 (norm_nonneg _) (norm_nonneg _))
            have hprodC : ‖k‖ * ‖k‖ ≤ C * ‖k‖ := by
              have hmul := mul_le_mul_of_nonneg_left (le_of_lt hk) (norm_nonneg k)
              simpa [mul_comm] using hmul
            have heval : (outer θ).eval k =
                (b θ).1 * (b θ).2 +
                  ((b θ).1 * k.2 + k.1 * (b θ).2) := by
              rw [houterEval θ k]
              exact mulPowerSeries_partialSum_two _ _
            rw [remainder_def, heval]
            have hdiff :
                (b θ + k).1 * (b θ + k).2 -
                    ((b θ).1 * (b θ).2 +
                      ((b θ).1 * k.2 + k.1 * (b θ).2)) =
                  k.1 * k.2 := by
              simp only [Prod.fst_add, Prod.snd_add]
              noncomm_ring
            rw [hdiff]
            simpa [Real.rpow_one] using hprod.trans hprodC
        | succ n =>
            let δ : ℝ := 1
            have hδ : 0 < δ := by norm_num [δ]
            refine ⟨δ, hδ, ?_⟩
            intro θ hθ k hk
            have heval : (outer θ).eval k =
                (b θ + k).1 * (b θ + k).2 := by
              rw [houterEval θ k]
              have hsum := mulPowerSeries_partialSum_add_three
                (A := A) (b θ) k n
              simpa [Prod.fst_add, Prod.snd_add, Nat.succ_eq_add_one,
                Nat.add_assoc] using hsum
            rw [remainder_def, heval]
            simp only [Prod.fst_add, Prod.snd_add, sub_self, norm_zero]
            exact mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg _) _)
  have hbasePair : ∀ θ ∈ K, (f θ a, g θ a) = b θ := by
    intro θ hθ
    simpa [b] using hpair.value_eq_constantCoeff hθ
  have hcomp := comp_of_uniformOuterAt (f := fun θ z ↦ (f θ z, g θ z))
    (g := fun _ z ↦ μ z) (P := pair) (Q := outer) hpair houterCoeff houterRem
      hbasePair
  simpa [pair, b, outer, μ, FiniteTaylorJet.mul_def, postcomp_def] using hcomp

/-- Reciprocal postcomposition preserves a real uniform finite jet family when
all constant coefficients equal one nonzero base value. -/
theorem inv {m : ℕ} {f : Θ → E → ℝ}
    {P : Θ → FiniteTaylorJet ℝ E ℝ m} {a : E} {K : Set Θ} (c : ℝ)
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hbase : ∀ θ ∈ K, (P θ).constantCoeff = c) (hc : c ≠ 0) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ (f θ z)⁻¹)
      (fun θ ↦ FiniteTaylorJet.inv (P θ)) a K := by
  have houter := const_ofFunction (Θ := Θ) (m := m) (fun z : ℝ ↦ z⁻¹) c K
    (contDiffAt_inv ℝ hc)
  have hcomp := hP.comp houter fun θ hθ ↦ by
    rw [hP.value_eq_constantCoeff hθ, hbase θ hθ]
  -- On `K`, the stored constant coefficient is the prescribed expansion base `c`.
  exact hcomp.congr (fun θ hθ ↦ rfl) fun θ hθ ↦ by
    rw [FiniteTaylorJet.inv_def, postcomp_def, hbase θ hθ]

/-- Square-root postcomposition preserves a real uniform finite jet family when
all constant coefficients equal one positive base value. -/
theorem sqrt {m : ℕ} {f : Θ → E → ℝ}
    {P : Θ → FiniteTaylorJet ℝ E ℝ m} {a : E} {K : Set Θ} (c : ℝ)
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hbase : ∀ θ ∈ K, (P θ).constantCoeff = c) (hc : 0 < c) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ Real.sqrt (f θ z))
      (fun θ ↦ FiniteTaylorJet.sqrt (P θ)) a K := by
  have houter := const_ofFunction (Θ := Θ) (m := m) Real.sqrt c K
    (Real.contDiffAt_sqrt hc.ne')
  have hcomp := hP.comp houter fun θ hθ ↦ by
    rw [hP.value_eq_constantCoeff hθ, hbase θ hθ]
  -- Replace the fixed-base outer jet by the definition using each equal constant coefficient.
  exact hcomp.congr (fun θ hθ ↦ rfl) fun θ hθ ↦ by
    rw [FiniteTaylorJet.sqrt_def, postcomp_def, hbase θ hθ]

/-- Norm postcomposition preserves uniform finite jets in a real inner product
space when all constant coefficients equal one nonzero vector. -/
theorem norm {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} {f : Θ → E → H} {P : Θ → FiniteTaylorJet ℝ E H m}
    {a : E} {K : Set Θ} (c : H)
    (hP : FiniteTaylorJet.IsUniformOn f P a K)
    (hbase : ∀ θ ∈ K, (P θ).constantCoeff = c) (hc : c ≠ 0) :
    FiniteTaylorJet.IsUniformOn (fun θ z ↦ ‖f θ z‖)
      (fun θ ↦ FiniteTaylorJet.norm (P θ)) a K := by
  have houter := const_ofFunction (Θ := Θ) (m := m) (fun z : H ↦ ‖z‖) c K
    (contDiffAt_norm ℝ hc)
  have hcomp := hP.comp houter fun θ hθ ↦ by
    rw [hP.value_eq_constantCoeff hθ, hbase θ hθ]
  -- Replace the fixed-base norm jet by the definition at the equal constant coefficient.
  exact hcomp.congr (fun θ hθ ↦ rfl) fun θ hθ ↦ by
    rw [FiniteTaylorJet.norm_def, postcomp_def, hbase θ hθ]

/-- Restriction along `ε ↦ (ε, ε ^ 2)` turns a uniform two-variable finite jet
family at `(0, 0)` into a uniform one-variable jet family at zero. -/
theorem weightedPath {m : ℕ} {f : Θ → (ℝ × ℝ) → F}
    {J : Θ → FiniteTaylorJet ℝ (ℝ × ℝ) F m} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J (0, 0) K) :
    FiniteTaylorJet.IsUniformOn (fun θ ε ↦ f θ (ε, ε ^ 2))
      (fun θ ↦ FiniteTaylorJet.comp (J θ) (weightedPathJet m)) 0 K := by
  have hpath := const_ofFunction (Θ := Θ) (m := m)
    (fun ε : ℝ ↦ (ε, ε ^ 2)) 0 K (by fun_prop)
  have hweighted : weightedPathJet m =
      ofFunction ℝ m (fun ε : ℝ ↦ (ε, ε ^ 2)) 0 := by
    -- Both jets store the same factorial-normalized derivatives in every degree.
    apply ext_coeff
    intro n
    rw [coeff_weightedPathJet, coeff_ofFunction]
  -- Compose with the fixed polynomial path, whose value at zero is `(0, 0)`.
  rw [hweighted]
  exact hpath.comp hJ (fun θ hθ ↦ by norm_num)

end IsUniformOn

variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- The iterated derivative of a fixed-parameter slice is the joint iterated
derivative restricted to directions in the second factor. -/
private lemma iteratedFDeriv_slice_eq_comp_inr {m n : ℕ} {f : Θ → E → F}
    (hf : ContDiff ℝ m (Function.uncurry f)) (hn : n ≤ m) (θ : Θ) (a : E) :
    iteratedFDeriv ℝ n (f θ) a =
      (iteratedFDeriv ℝ n (Function.uncurry f) (θ, a)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E) := by
  let shifted : Θ × E → F := fun z ↦ Function.uncurry f ((θ, 0) + z)
  have hshifted : ContDiff ℝ m shifted := by
    -- Translation by `(θ, 0)` preserves the joint finite-order regularity.
    exact hf.comp (contDiff_const.add contDiff_id)
  have hcomp := (ContinuousLinearMap.inr ℝ Θ E).iteratedFDeriv_comp_right
    (i := n) hshifted a (by exact_mod_cast hn)
  -- The translated right inclusion is exactly the fixed-parameter slice.
  simpa only [shifted, Function.comp_def, Function.uncurry_apply_pair,
    ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add, iteratedFDeriv_comp_add_left] using hcomp

/-- A jointly `C^m` family on a compact parameter set produces a uniform family
of derivative-constructed order-`m` finite jets at every fixed input base. -/
theorem isUniformOn_of_contDiff (m : ℕ) (f : Θ → E → F) (a : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ContDiff ℝ m (Function.uncurry f)) :
    IsUniformOn f (fun θ ↦ ofFunction ℝ m (f θ) a) a K := by
  constructor
  · intro n
    have hderivContinuous : Continuous (fun θ ↦
        iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)) := by
      -- Restrict the continuous joint iterated derivative to the compact fiber.
      exact (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_of_lt_succ n.isLt)).comp
        (continuous_id.prodMk continuous_const)
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hderivContinuous.continuousOn
    refine ⟨‖(((n : ℕ).factorial : ℝ)⁻¹)‖ * max R 0,
      mul_nonneg (norm_nonneg _) (le_max_right _ _), ?_⟩
    intro θ hθ
    rw [coeff_ofFunction, iteratedFDeriv_slice_eq_comp_inr hf
      (Nat.le_of_lt_succ n.isLt) θ a, norm_smul]
    have hrestriction :
        ‖(iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)).compContinuousLinearMap
            (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E)‖ ≤
          ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ := by
      -- Restriction along the isometric right inclusion cannot increase operator norm.
      calc
        ‖(iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)).compContinuousLinearMap
            (fun _ ↦ ContinuousLinearMap.inr ℝ Θ E)‖
            ≤ ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ *
                ∏ _i : Fin (n : ℕ), ‖ContinuousLinearMap.inr ℝ Θ E‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ *
              ∏ _i : Fin (n : ℕ), 1 := by
          gcongr
          exact ContinuousLinearMap.norm_inr_le_one ℝ Θ E
        _ = ‖iteratedFDeriv ℝ (n : ℕ) (Function.uncurry f) (θ, a)‖ := by
          simp only [Finset.prod_const_one, mul_one]
    exact mul_le_mul_of_nonneg_left
      (hrestriction.trans ((hR θ hθ).trans (le_max_left R 0))) (norm_nonneg _)
  · intro C hC
    -- The compact-uniform Taylor theorem supplies every requested Peano coefficient.
    exact uniformRemainderOn_of_contDiff m f a K hK hf C hC

/-- Joint finite-order differentiability at every point of a compact parameter fiber
produces a uniform family of derivative-constructed finite jets at the fixed input base. -/
theorem isUniformOn_of_contDiffAt (m : ℕ) (f : Θ → E → F) (a : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K, ContDiffAt ℝ m (Function.uncurry f) (θ, a)) :
    IsUniformOn f (fun θ ↦ ofFunction ℝ m (f θ) a) a K := by
  rw [IsUniformOn.spec]
  constructor
  · exact uniformCoeffBounds_of_contDiffAt m f a K hK hf
  · intro C hC
    exact uniformRemainderOn_of_contDiffAt m f a K hK hf C hC

end FiniteTaylorJet
