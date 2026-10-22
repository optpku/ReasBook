/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section01

universe u v

/-- Definition 1.2.1 (Main problem).
Let `Q1` be a bounded closed convex set in a finite-dimensional real vector space `E1`, and let
`f : E1 → ℝ` be continuous and convex on `Q1`. The main optimization problem is
`f* = min { f x : x ∈ Q1 }` (equation (2.1)). -/
noncomputable def MainOptimizationProblemValue {E1 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] (Q1 : Set E1) (f : E1 → ℝ) : ℝ :=
  sInf (f '' Q1)

/-- Definition 1.2.2 (Explicit max-structure model).
We say that `f` admits an explicit max-structure if there exist a finite-dimensional real vector
space `E2`, a closed convex bounded set `Q2` in `E2`, a linear operator `A : E1 → E2*`, and
continuous
convex functions `fhat : Q1 → ℝ` and `phihat : Q2 → ℝ`, such that for all `x ∈ Q1`,
`f x = fhat x + max { <A x, u>_2 - phihat u : u ∈ Q2 }` (equation (2.2)). The text also notes an
implicit simplicity assumption on `phihat` and `Q2`, and illustrates non-uniqueness via the
conjugate representation (equation (conjugate_representation)). -/
def AdmitsExplicitMaxStructure {E1 : Type u} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1]
    (Q1 : Set E1) (f : E1 → ℝ) : Prop :=
  ∃ (E2 : Type v) (_ : NormedAddCommGroup E2) (_ : NormedSpace ℝ E2)
    (_ : FiniteDimensional ℝ E2),
    ∃ (Q2 : Set E2), IsClosed Q2 ∧ Convex ℝ Q2 ∧ Bornology.IsBounded Q2 ∧
    ∃ (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)),
    ∃ (fhat : E1 → ℝ), ContinuousOn fhat Q1 ∧ ConvexOn ℝ Q1 fhat ∧
    ∃ (phihat : E2 → ℝ), ContinuousOn phihat Q2 ∧ ConvexOn ℝ Q2 phihat ∧
      ∀ x ∈ Q1, f x = fhat x + sSup ((fun u => A x u - phihat u) '' Q2)

/-- Definition 1.2.3 (Adjoint form).
Assume equation (2.2). Define `φ : Q2 → ℝ` by
`φ(u) = -phihat u + min { ⟪A x, u⟫_2 + fhat x : x ∈ Q1 }` (equation (2.3)). -/
noncomputable def AdjointFormPotential {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (fhat : E1 → ℝ) (phihat : E2 → ℝ) : Q2 → ℝ :=
  fun u => -phihat u + sInf ((fun x => A x u + fhat x) '' Q1)

/-- Definition 1.2.3 (Adjoint form, adjoint optimization problem).
Assume equation (2.2). The associated adjoint optimization problem is
`max { φ(u) : u ∈ Q2 }` (equation (adjoint_problem)). -/
noncomputable def AdjointOptimizationProblemValue {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (Q1 : Set E1) (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ))
    (fhat : E1 → ℝ) (phihat : E2 → ℝ) : ℝ :=
  sSup (Set.range (AdjointFormPotential Q1 Q2 A fhat phihat))

/-- Rewriting an image as a set of existence statements. -/
lemma image_eq_setOf_exists_eq {α : Type*} (g : α → ℝ) (p : α → Prop) :
    g '' {x | p x} = {r : ℝ | ∃ x, p x ∧ r = g x} := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The `ℓ¹`-`ℓ∞` duality identity for `Fin (succ m)` indices. -/
lemma maxAbs_l1_duality_fin_succ {m : ℕ} (t : Fin (Nat.succ m) → ℝ) :
    sSup (Set.range (fun j => |t j|)) =
      sSup {r : ℝ | ∃ u : Fin (Nat.succ m) → ℝ,
        (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
        r = Finset.univ.sum (fun j => u j * t j)} := by
  classical
  set S : Set ℝ := Set.range (fun j : Fin (Nat.succ m) => |t j|)
  set T : Set ℝ := {r : ℝ | ∃ u : Fin (Nat.succ m) → ℝ,
    (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
    r = Finset.univ.sum (fun j => u j * t j)}
  have hS_finite : S.Finite := by
    simpa [S] using (Set.finite_range (fun j : Fin (Nat.succ m) => |t j|))
  have hS_nonempty : S.Nonempty := by
    simpa [S] using (Set.range_nonempty (fun j : Fin (Nat.succ m) => |t j|))
  have hS_bdd : BddAbove S := hS_finite.bddAbove
  have hT_upper : ∀ r ∈ T, r ≤ sSup S := by
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    have hsup_nonneg : 0 ≤ sSup S := by
      have h0 : |t (0 : Fin (Nat.succ m))| ≤ sSup S :=
        le_csSup hS_bdd ⟨0, rfl⟩
      exact (abs_nonneg _).trans h0
    calc
      Finset.univ.sum (fun j => u j * t j)
          ≤ Finset.univ.sum (fun j => |u j * t j|) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact le_abs_self _
      _ = Finset.univ.sum (fun j => |u j| * |t j|) := by
            simp [abs_mul]
      _ ≤ Finset.univ.sum (fun j => |u j| * sSup S) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have htj : |t j| ≤ sSup S := le_csSup hS_bdd ⟨j, rfl⟩
            exact mul_le_mul_of_nonneg_left htj (abs_nonneg _)
      _ = (Finset.univ.sum (fun j => |u j|)) * sSup S := by
            simpa using
              (Finset.sum_mul (s := Finset.univ) (f := fun j => |u j|) (a := sSup S)).symm
      _ ≤ 1 * sSup S := by
            exact mul_le_mul_of_nonneg_right hu hsup_nonneg
      _ = sSup S := by simp
  have hT_bdd : BddAbove T := ⟨sSup S, hT_upper⟩
  have hT_nonempty : T.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩ <;> simp
  have h_le : sSup T ≤ sSup S :=
    (csSup_le_iff hT_bdd hT_nonempty).2 hT_upper
  have hSsup_mem : sSup S ∈ S := Set.Nonempty.csSup_mem hS_nonempty hS_finite
  have h_mem_T : sSup S ∈ T := by
    rcases (by simpa [S] using hSsup_mem) with ⟨j0, hj0⟩
    by_cases hneg : t j0 < 0
    · let u : Fin (Nat.succ m) → ℝ := Pi.single j0 (-1)
      refine ⟨u, ?_, ?_⟩
      · have hsum : (Finset.univ.sum (fun j => |u j|)) = |(-1 : ℝ)| := by
          have hfun : (fun j => |u j|) = Pi.single j0 |(-1 : ℝ)| := by
            funext j
            by_cases h : j = j0
            · subst h
              simp [u]
            · simp [u, h]
          simp [hfun]
        simp [hsum]
      · have hsum : (Finset.univ.sum (fun j => u j * t j)) = (-1 : ℝ) * t j0 := by
          have hfun : (fun j => u j * t j) = Pi.single j0 ((-1 : ℝ) * t j0) := by
            funext j
            by_cases h : j = j0
            · subst h
              simp [u]
            · simp [u, h]
          simp [hfun]
        have habs : |t j0| = (-1 : ℝ) * t j0 := by
          simp [abs_of_neg hneg, mul_comm]
        exact hj0.symm.trans (habs.trans hsum.symm)
    · have hnonneg : 0 ≤ t j0 := le_of_not_gt hneg
      let u : Fin (Nat.succ m) → ℝ := Pi.single j0 (1)
      refine ⟨u, ?_, ?_⟩
      · have hsum : (Finset.univ.sum (fun j => |u j|)) = |(1 : ℝ)| := by
          have hfun : (fun j => |u j|) = Pi.single j0 |(1 : ℝ)| := by
            funext j
            by_cases h : j = j0
            · subst h
              simp [u]
            · simp [u, h]
          simp [hfun]
        simp [hsum]
      · have hsum : (Finset.univ.sum (fun j => u j * t j)) = (1 : ℝ) * t j0 := by
          have hfun : (fun j => u j * t j) = Pi.single j0 ((1 : ℝ) * t j0) := by
            funext j
            by_cases h : j = j0
            · subst h
              simp [u]
            · simp [u, h]
          simp [hfun]
        have habs : |t j0| = (1 : ℝ) * t j0 := by
          simp [abs_of_nonneg hnonneg]
        exact hj0.symm.trans (habs.trans hsum.symm)
  have h_ge : sSup S ≤ sSup T := le_csSup hT_bdd h_mem_T
  exact le_antisymm h_ge h_le

/-- The `ℓ¹`-ball in `Fin (succ m) → ℝ` is closed, convex, and bounded. -/
lemma l1Ball_closed_convex_bounded_succ {m : ℕ} :
    let Q2 : Set (Fin (Nat.succ m) → ℝ) := {u | Finset.univ.sum (fun j => |u j|) ≤ 1}
    IsClosed Q2 ∧ Convex ℝ Q2 ∧ Bornology.IsBounded Q2 := by
  classical
  intro Q2
  let g : (Fin (Nat.succ m) → ℝ) → ℝ := fun u => Finset.univ.sum (fun j => |u j|)
  have hcont : Continuous g := by
    refine continuous_finset_sum _ ?_
    intro j hj
    exact (continuous_abs.comp (continuous_apply j))
  have hclosed : IsClosed Q2 := by
    simpa [Q2, g, Set.preimage, Set.Iic] using (isClosed_Iic.preimage hcont)
  have hconv : Convex ℝ Q2 := by
    refine (convex_iff_add_mem).2 ?_
    intro u hu v hv a b ha hb hab
    have hu' : Finset.univ.sum (fun j => |u j|) ≤ 1 := by simpa [Q2] using hu
    have hv' : Finset.univ.sum (fun j => |v j|) ≤ 1 := by simpa [Q2] using hv
    have hsum_le :
        Finset.univ.sum (fun j => |a * u j + b * v j|) ≤
          Finset.univ.sum (fun j => a * |u j| + b * |v j|) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      calc
        |a * u j + b * v j| ≤ |a * u j| + |b * v j| := by
          simpa using abs_add_le (a * u j) (b * v j)
        _ = a * |u j| + b * |v j| := by
          simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hsum_eq :
        Finset.univ.sum (fun j => a * |u j| + b * |v j|) =
          a * (Finset.univ.sum (fun j => |u j|)) +
            b * (Finset.univ.sum (fun j => |v j|)) := by
      have hsum_u :
          Finset.univ.sum (fun j => a * |u j|) =
            a * (Finset.univ.sum (fun j => |u j|)) := by
        simpa using
          (Finset.mul_sum (s := Finset.univ) (f := fun j => |u j|) (a := a)).symm
      have hsum_v :
          Finset.univ.sum (fun j => b * |v j|) =
            b * (Finset.univ.sum (fun j => |v j|)) := by
        simpa using
          (Finset.mul_sum (s := Finset.univ) (f := fun j => |v j|) (a := b)).symm
      calc
        Finset.univ.sum (fun j => a * |u j| + b * |v j|)
            = (Finset.univ.sum (fun j => a * |u j|)) +
                (Finset.univ.sum (fun j => b * |v j|)) := by
              simp [Finset.sum_add_distrib]
        _ = a * (Finset.univ.sum (fun j => |u j|)) +
            b * (Finset.univ.sum (fun j => |v j|)) := by
              simp [hsum_u, hsum_v]
    have hsum_le_one :
        a * (Finset.univ.sum (fun j => |u j|)) +
            b * (Finset.univ.sum (fun j => |v j|)) ≤ 1 := by
      have ha' := mul_le_mul_of_nonneg_left hu' ha
      have hb' := mul_le_mul_of_nonneg_left hv' hb
      have hsum_le' : a * (Finset.univ.sum (fun j => |u j|)) +
          b * (Finset.univ.sum (fun j => |v j|)) ≤ a * (1 : ℝ) + b * (1 : ℝ) :=
        add_le_add ha' hb'
      simpa [hab] using hsum_le'
    calc
      Finset.univ.sum (fun j => |(a • u + b • v) j|)
          = Finset.univ.sum (fun j => |a * u j + b * v j|) := by
              simp [Pi.add_apply, Pi.smul_apply]
      _ ≤ Finset.univ.sum (fun j => a * |u j| + b * |v j|) := hsum_le
      _ = a * (Finset.univ.sum (fun j => |u j|)) +
          b * (Finset.univ.sum (fun j => |v j|)) := hsum_eq
      _ ≤ 1 := hsum_le_one
  have hbounded : Bornology.IsBounded Q2 := by
    refine (Bornology.forall_isBounded_image_eval_iff).1 ?_
    intro j
    refine (Metric.isBounded_Icc (-1 : ℝ) 1).subset ?_
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    have hu' : Finset.univ.sum (fun i => |u i|) ≤ 1 := by
      simpa [Q2] using hu
    have hle' : |u j| ≤ Finset.univ.sum (fun i => |u i|) := by
      refine Finset.single_le_sum (f := fun i => |u i|) ?_ ?_
      · intro i hi
        exact abs_nonneg _
      · simp
    have hle : |u j| ≤ (1 : ℝ) := le_trans hle' hu'
    exact (abs_le.mp hle)
  exact ⟨hclosed, hconv, hbounded⟩

/-- Simplex lifting: split an ℓ¹-ball element into nonnegative parts with slack. -/
lemma maxAbs_simplexLift_exists_of_l1Ball_succ {m : ℕ} {u : Fin (Nat.succ m) → ℝ}
    (hu : Finset.univ.sum (fun j => |u j|) ≤ 1) :
    ∃ u1 u2 : Fin (Nat.succ m) → ℝ,
      (∀ j, 0 ≤ u1 j) ∧
      (∀ j, 0 ≤ u2 j) ∧
      (Finset.univ.sum (fun j => (u1 j + u2 j)) = 1) ∧
      (∀ j, u j = u1 j - u2 j) := by
  classical
  let u1' : Fin (Nat.succ m) → ℝ := fun j => (|u j| + u j) / 2
  let u2' : Fin (Nat.succ m) → ℝ := fun j => (|u j| - u j) / 2
  have hu1' : ∀ j, 0 ≤ u1' j := by
    intro j
    dsimp [u1']
    have h : -(u j) ≤ |u j| := by
      simpa using (neg_le_abs (u j))
    linarith
  have hu2' : ∀ j, 0 ≤ u2' j := by
    intro j
    dsimp [u2']
    have h : u j ≤ |u j| := by
      simpa using (le_abs_self (u j))
    linarith
  have hsum' :
      Finset.univ.sum (fun j => (u1' j + u2' j)) =
        Finset.univ.sum (fun j => |u j|) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    dsimp [u1', u2']
    ring
  let slack : ℝ := (1 - Finset.univ.sum (fun j => |u j|)) / 2
  have hslack : 0 ≤ slack := by
    dsimp [slack]
    linarith
  let j0 : Fin (Nat.succ m) := 0
  let s : Fin (Nat.succ m) → ℝ := Pi.single j0 slack
  let u1 : Fin (Nat.succ m) → ℝ := fun j => u1' j + s j
  let u2 : Fin (Nat.succ m) → ℝ := fun j => u2' j + s j
  have hs_nonneg : ∀ j, 0 ≤ s j := by
    intro j
    by_cases h : j = j0
    · subst h
      simp [s, hslack]
    · simp [s, h]
  have hu1 : ∀ j, 0 ≤ u1 j := by
    intro j
    dsimp [u1]
    exact add_nonneg (hu1' j) (hs_nonneg j)
  have hu2 : ∀ j, 0 ≤ u2 j := by
    intro j
    dsimp [u2]
    exact add_nonneg (hu2' j) (hs_nonneg j)
  have hsum_s : Finset.univ.sum (fun j => s j) = slack := by
    simp [s]
  have hsum :
      Finset.univ.sum (fun j => (u1 j + u2 j)) = 1 := by
    calc
      Finset.univ.sum (fun j => (u1 j + u2 j))
          = Finset.univ.sum (fun j => (u1' j + u2' j) + (2 * s j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              dsimp [u1, u2]
              ring
      _ = (Finset.univ.sum (fun j => (u1' j + u2' j))) +
          (Finset.univ.sum (fun j => 2 * s j)) := by
              simp [Finset.sum_add_distrib]
      _ = (Finset.univ.sum (fun j => |u j|)) + (2 * slack) := by
              have hsum_s2 :
                  Finset.univ.sum (fun j => 2 * s j) =
                    2 * (Finset.univ.sum (fun j => s j)) := by
                  simpa using
                    (Finset.mul_sum (s := Finset.univ) (f := fun j => s j) (a := (2:ℝ))).symm
              simp [hsum', hsum_s, hsum_s2]
      _ = 1 := by
              dsimp [slack]
              ring
  have hdiff : ∀ j, u j = u1 j - u2 j := by
    intro j
    dsimp [u1, u2, u1', u2']
    ring
  exact ⟨u1, u2, hu1, hu2, hsum, hdiff⟩

/-- Simplex lifting: a simplex point yields an ℓ¹-ball point. -/
lemma maxAbs_l1Ball_exists_of_simplexLift_succ {m : ℕ} {u1 u2 : Fin (Nat.succ m) → ℝ}
    (hu1 : ∀ j, 0 ≤ u1 j) (hu2 : ∀ j, 0 ≤ u2 j)
    (hsum : Finset.univ.sum (fun j => (u1 j + u2 j)) = 1) :
    Finset.univ.sum (fun j => |(u1 j - u2 j)|) ≤ 1 := by
  have hpoint : ∀ j, |u1 j - u2 j| ≤ u1 j + u2 j := by
    intro j
    have h1 : |u1 j| = u1 j := abs_of_nonneg (hu1 j)
    have h2 : |u2 j| = u2 j := abs_of_nonneg (hu2 j)
    calc
      |u1 j - u2 j| ≤ |u1 j| + |u2 j| := by
        simpa [sub_eq_add_neg] using (abs_add_le (u1 j) (-u2 j))
      _ = u1 j + u2 j := by simp [h1, h2]
  calc
    Finset.univ.sum (fun j => |(u1 j - u2 j)|)
        ≤ Finset.univ.sum (fun j => u1 j + u2 j) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact hpoint j
    _ = 1 := hsum

/-- Simplex lifting for the `ℓ¹`-ball representation on `Fin (succ m)`. -/
lemma maxAbs_simplex_lifting_valueSet_eq_succ {m : ℕ} (t : Fin (Nat.succ m) → ℝ) :
    {r : ℝ | ∃ u : Fin (Nat.succ m) → ℝ,
        (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
        r = Finset.univ.sum (fun j => u j * t j)} =
      {r : ℝ | ∃ u1 u2 : Fin (Nat.succ m) → ℝ,
        (∀ j, 0 ≤ u1 j) ∧
        (∀ j, 0 ≤ u2 j) ∧
        (Finset.univ.sum (fun j => (u1 j + u2 j)) = 1) ∧
        r = Finset.univ.sum (fun j => (u1 j - u2 j) * t j)} := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases maxAbs_simplexLift_exists_of_l1Ball_succ (u := u) hu with
      ⟨u1, u2, hu1, hu2, hsum, hdiff⟩
    refine ⟨u1, u2, hu1, hu2, hsum, ?_⟩
    have hfun : (fun j => u j * t j) = fun j => (u1 j - u2 j) * t j := by
      funext j
      simp [hdiff j]
    simp [hfun]
  · rintro ⟨u1, u2, hu1, hu2, hsum, rfl⟩
    refine ⟨fun j => u1 j - u2 j, ?_, rfl⟩
    exact maxAbs_l1Ball_exists_of_simplexLift_succ (hu1 := hu1) (hu2 := hu2) hsum

/-- Evaluation formula for the `Fin (succ m)` linear maps. -/
lemma maxAbs_A_phihat_succ_eval {E1 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    {m : ℕ} (a : Fin (Nat.succ m) → E1 →L[ℝ] ℝ) (b : Fin (Nat.succ m) → ℝ)
    (x : E1) (u : Fin (Nat.succ m) → ℝ) :
    let projCLM : Fin (Nat.succ m) → (Fin (Nat.succ m) → ℝ) →L[ℝ] ℝ :=
      fun j =>
        LinearMap.toContinuousLinearMap
          { toFun := fun u : (Fin (Nat.succ m) → ℝ) => u j
            map_add' := by
              intro u v
              rfl
            map_smul' := by
              intro c u
              rfl }
    (∑ j, (a j).smulRight (projCLM j)) x u - (∑ j, (b j) • (projCLM j)) u =
      Finset.univ.sum (fun j => u j * (a j x - b j)) := by
  classical
  intro projCLM
  calc
    (∑ j, (a j).smulRight (projCLM j)) x u - (∑ j, (b j) • (projCLM j)) u =
        (Finset.univ.sum (fun j => a j x * u j)) - (Finset.univ.sum (fun j => b j * u j)) := by
          simp [ContinuousLinearMap.smulRight_apply, projCLM]
    _ = Finset.univ.sum (fun j => a j x * u j - b j * u j) := by
          simp [Finset.sum_sub_distrib]
    _ = Finset.univ.sum (fun j => u j * (a j x - b j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

set_option maxHeartbeats 1000000 in
-- large heartbeats for the explicit max-structure construction
/-- Explicit max-structure in the `Fin (succ m)` case. -/
lemma maxAbs_admitsExplicitMaxStructure_succ {E1 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] {m : ℕ}
    (a : Fin (Nat.succ m) → E1 →L[ℝ] ℝ) (b : Fin (Nat.succ m) → ℝ) :
    AdmitsExplicitMaxStructure.{_,0} (Q1 := Set.univ)
      (fun x => sSup (Set.range (fun j : Fin (Nat.succ m) => |a j x - b j|))) := by
  classical
  let f : E1 → ℝ := fun x => sSup (Set.range (fun j : Fin (Nat.succ m) => |a j x - b j|))
  have hf : AdmitsExplicitMaxStructure.{_,0} (Q1 := Set.univ) f := by
    let E2 := (Fin (Nat.succ m) → ℝ)
    letI instE2 : NormedAddCommGroup E2 := inferInstance
    letI instE2' : NormedSpace ℝ E2 := inferInstance
    letI instE2'' : FiniteDimensional ℝ E2 := inferInstance
    letI instBorn : Bornology E2 := PseudoMetricSpace.toBornology
    let Q2 : Set E2 := {u | Finset.univ.sum (fun j => |u j|) ≤ 1}
    have hQ2 : IsClosed Q2 ∧ Convex ℝ Q2 ∧ Bornology.IsBounded Q2 := by
      classical
      let g : E2 → ℝ := fun u => Finset.univ.sum (fun j => |u j|)
      have hcont : Continuous g := by
        refine continuous_finset_sum _ ?_
        intro j hj
        let eval : E2 →ₗ[ℝ] ℝ :=
          { toFun := fun u => u j
            map_add' := by
              intro u v
              rfl
            map_smul' := by
              intro c u
              rfl }
        have hproj : Continuous (fun u : E2 => u j) :=
          (LinearMap.continuous_of_finiteDimensional eval)
        exact continuous_abs.comp hproj
      have hclosed : IsClosed Q2 := by
        simpa [Q2, g, Set.preimage, Set.Iic] using (isClosed_Iic.preimage hcont)
      have hconv : Convex ℝ Q2 := by
        refine (convex_iff_add_mem).2 ?_
        intro u hu v hv a b ha hb hab
        have hu' : Finset.univ.sum (fun j => |u j|) ≤ 1 := by simpa [Q2] using hu
        have hv' : Finset.univ.sum (fun j => |v j|) ≤ 1 := by simpa [Q2] using hv
        have hsum_le :
            Finset.univ.sum (fun j => |a * u j + b * v j|) ≤
              Finset.univ.sum (fun j => a * |u j| + b * |v j|) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          calc
            |a * u j + b * v j| ≤ |a * u j| + |b * v j| := by
              simpa using abs_add_le (a * u j) (b * v j)
            _ = a * |u j| + b * |v j| := by
              simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        have hsum_eq :
            Finset.univ.sum (fun j => a * |u j| + b * |v j|) =
              a * (Finset.univ.sum (fun j => |u j|)) +
                b * (Finset.univ.sum (fun j => |v j|)) := by
          have hsum_u :
              Finset.univ.sum (fun j => a * |u j|) =
                a * (Finset.univ.sum (fun j => |u j|)) := by
            simpa using
              (Finset.mul_sum (s := Finset.univ) (f := fun j => |u j|) (a := a)).symm
          have hsum_v :
              Finset.univ.sum (fun j => b * |v j|) =
                b * (Finset.univ.sum (fun j => |v j|)) := by
            simpa using
              (Finset.mul_sum (s := Finset.univ) (f := fun j => |v j|) (a := b)).symm
          calc
            Finset.univ.sum (fun j => a * |u j| + b * |v j|)
                = (Finset.univ.sum (fun j => a * |u j|)) +
                    (Finset.univ.sum (fun j => b * |v j|)) := by
                  simp [Finset.sum_add_distrib]
            _ = a * (Finset.univ.sum (fun j => |u j|)) +
                b * (Finset.univ.sum (fun j => |v j|)) := by
                  simp [hsum_u, hsum_v]
        have hsum_le_one :
            a * (Finset.univ.sum (fun j => |u j|)) +
                b * (Finset.univ.sum (fun j => |v j|)) ≤ 1 := by
          have ha' := mul_le_mul_of_nonneg_left hu' ha
          have hb' := mul_le_mul_of_nonneg_left hv' hb
          have hsum_le' : a * (Finset.univ.sum (fun j => |u j|)) +
              b * (Finset.univ.sum (fun j => |v j|)) ≤ a * (1 : ℝ) + b * (1 : ℝ) :=
            add_le_add ha' hb'
          simpa [hab] using hsum_le'
        calc
          Finset.univ.sum (fun j => |(a • u + b • v) j|)
              = Finset.univ.sum (fun j => |a * u j + b * v j|) := by
                  rfl
          _ ≤ Finset.univ.sum (fun j => a * |u j| + b * |v j|) := hsum_le
          _ = a * (Finset.univ.sum (fun j => |u j|)) +
              b * (Finset.univ.sum (fun j => |v j|)) := hsum_eq
          _ ≤ 1 := hsum_le_one
      have hbounded : Bornology.IsBounded Q2 := by
        have hsubset : Q2 ⊆ Metric.closedBall (0 : E2) 1 := by
          intro u hu
          have hu' : Finset.univ.sum (fun j => |u j|) ≤ 1 := by
            simpa [Q2] using hu
          have hcoord : ∀ j, ‖u j‖ ≤ (1 : ℝ) := by
            intro j
            have hle' : |u j| ≤ Finset.univ.sum (fun i => |u i|) := by
              refine Finset.single_le_sum (f := fun i => |u i|) ?_ ?_
              · intro i hi
                exact abs_nonneg _
              · simp
            exact (hle'.trans hu')
          have hnorm : ‖u‖ ≤ (1 : ℝ) :=
            (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun j => by simpa using hcoord j)
          have hdist : dist u 0 ≤ (1 : ℝ) := by
            simpa [dist_eq_norm] using hnorm
          simpa [Metric.mem_closedBall] using hdist
        exact (Metric.isBounded_closedBall.subset hsubset)
      exact ⟨hclosed, hconv, hbounded⟩
    let projCLM : Fin (Nat.succ m) → E2 →L[ℝ] ℝ :=
      fun j =>
        LinearMap.toContinuousLinearMap
          { toFun := fun u : E2 => u j
            map_add' := by
              intro u v
              rfl
            map_smul' := by
              intro c u
              rfl }
    let A : E1 →L[ℝ] (E2 →L[ℝ] ℝ) := ∑ j, (a j).smulRight (projCLM j)
    let phihatCLM : E2 →L[ℝ] ℝ := ∑ j, (b j) • (projCLM j)
    let fhat : E1 → ℝ := fun _ => 0
    let phihat : E2 → ℝ := fun u => phihatCLM u
    refine ⟨E2, instE2, instE2', instE2'', Q2, hQ2.1, hQ2.2.1, hQ2.2.2,
      (by simpa using A), fhat, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [fhat] using (continuous_const.continuousOn :
        ContinuousOn (fun _ : E1 => (0:ℝ)) (Set.univ : Set E1))
    · refine ⟨?_, ?_⟩
      · simpa [fhat] using (convexOn_const (s := (Set.univ : Set E1)) (c := (0:ℝ))
          (convex_univ : Convex ℝ (Set.univ : Set E1)))
      · refine ⟨phihat, ?_, ?_, ?_⟩
        · have : ContinuousOn (fun u : E2 => phihatCLM u) Q2 :=
            phihatCLM.continuous.continuousOn
          simpa [phihat] using this
        · have hconvQ2 : Convex ℝ Q2 := hQ2.2.1
          have : ConvexOn ℝ Q2 (fun u : E2 => phihatCLM u) := by
            simpa using (LinearMap.convexOn (f := phihatCLM.toLinearMap) hconvQ2)
          simpa [phihat] using this
        · intro x _
          have hAphi : ∀ u : E2, A x u - phihat u =
              Finset.univ.sum (fun j => u j * (a j x - b j)) := by
            intro u
            simpa [A, phihat, phihatCLM, projCLM] using
              (maxAbs_A_phihat_succ_eval (a := a) (b := b) x u)
          have hset :
              {r : ℝ | ∃ u : E2,
                (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
                r = Finset.univ.sum (fun j => u j * (a j x - b j))} =
                (fun u => A x u - phihat u) '' Q2 := by
            ext r
            constructor
            · rintro ⟨u, hu, rfl⟩
              refine ⟨u, hu, ?_⟩
              exact hAphi u
            · rintro ⟨u, hu, rfl⟩
              refine ⟨u, hu, ?_⟩
              exact hAphi u
          have hdual :
              sSup (Set.range (fun j : Fin (Nat.succ m) => |a j x - b j|)) =
                sSup {r : ℝ | ∃ u : E2,
                  (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
                  r = Finset.univ.sum (fun j => u j * (a j x - b j))} := by
            simpa using (maxAbs_l1_duality_fin_succ (t := fun j => a j x - b j))
          calc
            f x = sSup (Set.range (fun j : Fin (Nat.succ m) => |a j x - b j|)) := rfl
            _ = sSup {r : ℝ | ∃ u : E2,
                  (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
                  r = Finset.univ.sum (fun j => u j * (a j x - b j))} := hdual
            _ = sSup ((fun u => A x u - phihat u) '' Q2) := by simp [hset]
            _ = fhat x + sSup ((fun u => A x u - phihat u) '' Q2) := by simp [fhat]
  simpa [f] using hf

/-- Proposition 1.2.1.
Let `a_1, …, a_m ∈ E1*` and `b ∈ ℝ^m`, and define
`f(x) = max_{1 ≤ j ≤ m} |⟪a_j, x⟫_1 - b^(j)|` (equation (eq:ex1:f_def)). Then `f` admits explicit
max-structure representations (equation (2.2)). In particular:
1) (Conjugate-style representation.) Taking `A = I`, `E2 = E1*`, one can define `phihat` by the
minimum over `s ∈ ℝ^m` with `u = ∑ s^(j) a_j` and `∑ |s^(j)| ≤ 1`
(equation (eq:ex1:phi_hat_conjugate_like)).
2) (`ℝ^m` representation.) One can write
`f(x) = max_{u ∈ ℝ^m} { ∑ u^(j)(⟪a_j, x⟫_1 - b^(j)) : ∑ |u^(j)| ≤ 1 }`
 (equation (eq:ex1:Rm_representation)), so `Q2` is the `l1`-ball and `phihat(u) = ⟪b, u⟫_2`.
3) (Simplex lifting.) Using `u = (u_1, u_2) ∈ ℝ^{2m}` with `u ≥ 0` and
`∑ (u_1^(j) + u_2^(j)) = 1`, one obtains the simplex representation
(equation (eq:ex1:simplex_representation)). -/
theorem maxAbs_explicit_max_structure {E1 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] {m : ℕ}
    (a : Fin m → E1 →L[ℝ] ℝ) (b : Fin m → ℝ) :
    let f : E1 → ℝ := fun x => sSup (Set.range (fun j : Fin m => |a j x - b j|))
    AdmitsExplicitMaxStructure.{_,0} (Q1 := Set.univ) f ∧
      (∃ phihat : (E1 →L[ℝ] ℝ) → ℝ,
        ∀ u : (E1 →L[ℝ] ℝ),
          phihat u =
            sInf { r : ℝ |
              ∃ s : Fin m → ℝ,
                u = Finset.univ.sum (fun j => s j • a j) ∧
                (Finset.univ.sum (fun j => |s j|) ≤ 1) ∧
                r = Finset.univ.sum (fun j => s j * b j) }) ∧
      (∀ x : E1,
        f x =
          sSup { r : ℝ |
            ∃ u : Fin m → ℝ,
              (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
              r = Finset.univ.sum (fun j => u j * (a j x - b j)) }) ∧
      (∀ x : E1,
        f x =
          sSup { r : ℝ |
            ∃ u1 u2 : Fin m → ℝ,
              (∀ j, 0 ≤ u1 j) ∧
              (∀ j, 0 ≤ u2 j) ∧
              (Finset.univ.sum (fun j => (u1 j + u2 j)) = 1) ∧
              r = Finset.univ.sum (fun j => (u1 j - u2 j) * (a j x - b j)) }) := by
  classical
  cases m with
  | zero =>
      simp
      refine ⟨?_, ?_⟩
      · refine ⟨ULift ℝ, ?_, ?_, ?_, ?_⟩
        · infer_instance
        · infer_instance
        · infer_instance
        refine ⟨({(0 : ULift ℝ)} : Set (ULift ℝ)), ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp
        refine ⟨0, ?_⟩
        refine ⟨fun _ : E1 => (0:ℝ), ?_, ?_, ?_⟩
        · exact (continuous_const.continuousOn :
            ContinuousOn (fun _ : E1 => (0:ℝ)) (Set.univ : Set E1))
        · exact (convexOn_const (s := (Set.univ : Set E1)) (c := (0:ℝ))
            (convex_univ : Convex ℝ (Set.univ : Set E1)))
        refine ⟨fun _ : ULift ℝ => (0:ℝ), ?_, ?_, ?_⟩
        · exact (continuous_const.continuousOn :
            ContinuousOn (fun _ : ULift ℝ => (0:ℝ)) ({(0 : ULift ℝ)} : Set (ULift ℝ)))
        · exact (convexOn_const (s := ({(0 : ULift ℝ)} : Set (ULift ℝ))) (c := (0:ℝ))
            (convex_singleton (0 : ULift ℝ)))
        · intro x hx
          simp
      · refine ⟨fun _ => (0:ℝ), ?_⟩
        intro u
        by_cases h : u = 0
        · simp [h]
        · simp [h]
  | succ m =>
      dsimp
      refine ⟨?_, ?_⟩
      · exact maxAbs_admitsExplicitMaxStructure_succ (a := a) (b := b)
      · refine ⟨?_, ?_⟩
        · refine ⟨fun u => sInf { r : ℝ |
            ∃ s : Fin (Nat.succ m) → ℝ,
              u = Finset.univ.sum (fun j => s j • a j) ∧
              (Finset.univ.sum (fun j => |s j|) ≤ 1) ∧
              r = Finset.univ.sum (fun j => s j * b j) }, ?_⟩
          intro u
          rfl
        · refine ⟨?_, ?_⟩
          · intro x
            simpa using (maxAbs_l1_duality_fin_succ (t := fun j => a j x - b j))
          · intro x
            have hset :
                {r : ℝ | ∃ u : Fin (Nat.succ m) → ℝ,
                    (Finset.univ.sum (fun j => |u j|) ≤ 1) ∧
                    r = Finset.univ.sum (fun j => u j * (a j x - b j))} =
                  {r : ℝ | ∃ u1 u2 : Fin (Nat.succ m) → ℝ,
                    (∀ j, 0 ≤ u1 j) ∧
                    (∀ j, 0 ≤ u2 j) ∧
                    (Finset.univ.sum (fun j => (u1 j + u2 j)) = 1) ∧
                    r = Finset.univ.sum (fun j => (u1 j - u2 j) * (a j x - b j))} := by
              simpa using (maxAbs_simplex_lifting_valueSet_eq_succ (t := fun j => a j x - b j))
            simpa [hset] using (maxAbs_l1_duality_fin_succ (t := fun j => a j x - b j))

/-- Definition 1.2.4 (Prox-function and prox-center).
Let `Q2 ⊆ E2` be closed, convex, and bounded. A function `d2 : Q2 → ℝ` is a prox-function for `Q2`
if it is continuous and `σ2`-strongly convex on `Q2` for some `σ2 > 0`. We may normalize `d2` so
that `d2 u0 = 0` at a prox-center. -/
def IsProxFunction {E2 : Type*} [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (d2 : E2 → ℝ) : Prop :=
  ∃ σ2 > 0, ContinuousOn d2 Q2 ∧ StrongConvexOn Q2 σ2 d2

/-- Definition 1.2.4 (Prox-function and prox-center).
A prox-center `u0 ∈ Q2` is any minimizer `u0 ∈ argmin { d2 u : u ∈ Q2 }`
(equation (prox_center_def)). -/
def IsProxCenter {E2 : Type*} [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (d2 : E2 → ℝ) (u0 : E2) : Prop :=
  u0 ∈ Q2 ∧ IsMinOn d2 Q2 u0

/-- If `a + (1 - t) * c ≤ b` for all `t ∈ (0,1)`, then `a + c ≤ b`. -/
lemma le_of_forall_one_sub_mul_le {a b c : ℝ}
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a + (1 - t) * c ≤ b) :
    a + c ≤ b := by
  by_cases hc : c ≤ 0
  · have ht : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith
    have h' : a + (1 / 2 : ℝ) * c ≤ b := by
      have h'' := h (1 / 2) ht
      ring_nf at h''
      simpa [mul_comm, mul_left_comm, mul_assoc] using h''
    have hmon : a + c ≤ a + (1 / 2) * c := by linarith
    exact le_trans hmon h'
  · have hc' : 0 < c := lt_of_not_ge hc
    by_contra hbc
    have hlt : b < a + c := lt_of_not_ge hbc
    by_cases hba : b ≤ a
    · have ht : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith
      have h' : a + (1 / 2 : ℝ) * c ≤ b := by
        have h'' := h (1 / 2) ht
        ring_nf at h''
        simpa [mul_comm, mul_left_comm, mul_assoc] using h''
      have hgt : b < a + (1 / 2) * c := by linarith [hba, hc']
      exact (lt_irrefl b (lt_of_lt_of_le hgt h'))
    · have hba' : a < b := lt_of_not_ge hba
      set t : ℝ := (a + c - b) / (2 * c) with htdef
      have htpos : 0 < t := by
        have hnum : 0 < a + c - b := by linarith
        have hden : 0 < 2 * c := by linarith
        exact div_pos hnum hden
      have htlt : t < 1 := by
        have hnum : a + c - b < 2 * c := by linarith [hba']
        have hden : 0 < 2 * c := by linarith
        exact (div_lt_one hden).2 hnum
      have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨htpos, htlt⟩
      have hineq := h t htIoo
      have hc0 : c ≠ 0 := by linarith
      have htc : t * c = (a + c - b) / 2 := by
        have htc' : (a + c - b) / (2 * c) * c = (a + c - b) / 2 := by
          field_simp [hc0]
        simpa [htdef] using htc'
      have hcalc : a + (1 - t) * c = (a + c + b) / 2 := by
        calc
          a + (1 - t) * c = a + c - t * c := by ring
          _ = a + c - (a + c - b) / 2 := by simp [htc]
          _ = (a + c + b) / 2 := by ring_nf
      have hgt : b < a + (1 - t) * c := by
        have : b < (a + c + b) / 2 := by linarith [hlt]
        simpa [hcalc] using this
      exact (lt_irrefl b (lt_of_lt_of_le hgt hineq))

/-- Intermediate inequality for a fixed `t ∈ (0,1)`. -/
lemma prox_center_lower_bound_aux_t {E2 : Type*} [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (d2 : E2 → ℝ) (σ2 : ℝ) (u0 : E2)
    (hconv : StrongConvexOn Q2 σ2 d2) (hu0 : IsProxCenter Q2 d2 u0)
    {u : E2} (hu : u ∈ Q2) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    d2 u0 + (1 - t) * ((σ2 / 2) * ‖u0 - u‖ ^ (2 : ℕ)) ≤ d2 u := by
  rcases hconv with ⟨hQ2conv, hconvI⟩
  have ht0 : 0 < t := ht.1
  have hnonneg_t : 0 ≤ t := le_of_lt ht0
  have hnonneg_one_sub : 0 ≤ 1 - t := by linarith [ht.2]
  have hsum : (1 - t) + t = 1 := by linarith
  have hut : (1 - t) • u0 + t • u ∈ Q2 := by
    refine hQ2conv hu0.1 hu hnonneg_one_sub hnonneg_t ?_
    linarith
  have hmin : d2 u0 ≤ d2 ((1 - t) • u0 + t • u) := by
    have hmin' : ∀ x ∈ Q2, d2 u0 ≤ d2 x := (isMinOn_iff).1 hu0.2
    exact hmin' _ hut
  have hsc0 := hconvI (x:=u0) hu0.1 (y:=u) hu
  have hsc1 := hsc0 (a:=1 - t) (b:=t) hnonneg_one_sub hnonneg_t hsum
  have hsc :
      d2 ((1 - t) • u0 + t • u) ≤ (1 - t) * d2 u0 + t * d2 u -
        (1 - t) * t * (σ2 / 2 * ‖u0 - u‖ ^ (2 : ℕ)) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsc1
  have hle :
      d2 u0 ≤ (1 - t) * d2 u0 + t * d2 u -
        (1 - t) * t * (σ2 / 2 * ‖u0 - u‖ ^ (2 : ℕ)) := le_trans hmin hsc
  have hle' :
      t * (d2 u0 + (1 - t) * (σ2 / 2 * ‖u0 - u‖ ^ (2 : ℕ))) ≤ t * d2 u := by
    linarith
  have hle'' :
      d2 u0 + (1 - t) * (σ2 / 2 * ‖u0 - u‖ ^ (2 : ℕ)) ≤ d2 u := by
    exact le_of_mul_le_mul_left hle' ht0
  exact hle''

/-- Proposition 1.2.2.
Assume `d2` is `σ2`-strongly convex on `Q2`, and let `u0` be a prox-center normalized by
`d2 u0 = 0`. Then for all `u ∈ Q2`, `d2 u ≥ (1/2) σ2 ‖u - u0‖^2` (equation (2.4)). -/
theorem prox_center_lower_bound {E2 : Type*} [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (d2 : E2 → ℝ) (σ2 : ℝ) (u0 : E2)
    (hconv : StrongConvexOn Q2 σ2 d2) (hu0 : IsProxCenter Q2 d2 u0)
    (h0 : d2 u0 = 0) :
    ∀ u ∈ Q2, d2 u ≥ (1 / 2 : ℝ) * σ2 * ‖u - u0‖ ^ (2 : ℕ) := by
  intro u hu
  have haux : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      d2 u0 + (1 - t) * ((σ2 / 2) * ‖u0 - u‖ ^ (2 : ℕ)) ≤ d2 u := by
    intro t ht
    exact prox_center_lower_bound_aux_t Q2 d2 σ2 u0 hconv hu0 hu ht
  have hle : d2 u0 + (σ2 / 2) * ‖u0 - u‖ ^ (2 : ℕ) ≤ d2 u :=
    le_of_forall_one_sub_mul_le haux
  have hle' : (σ2 / 2) * ‖u0 - u‖ ^ (2 : ℕ) ≤ d2 u := by
    simpa [h0] using hle
  have hle'' : (1 / 2 : ℝ) * σ2 * ‖u - u0‖ ^ (2 : ℕ) ≤ d2 u := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, norm_sub_rev] using hle'
  exact hle''

/-- Definition 1.2.5 (Smoothed max-function).
Let `μ > 0`. Define `f_μ(x) = max { ⟪A x, u⟫_2 - phihat u - μ d2 u : u ∈ Q2 }`
(equation (2.5)). Denote by `u_μ(x) ∈ Q2` an optimal solution (a maximizer) of (2.5).
Since `d2` is strongly convex and `phihat` is convex on `Q2`, the maximizer is unique. -/
noncomputable def SmoothedMaxFunction {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) :
    E1 → ℝ :=
  fun x => sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2)

/-- Definition 1.2.5 (Smoothed max-function, maximizers).
A point `u ∈ Q2` is a maximizer for the smoothed max-function at `x` if it attains the maximum in
(2.5). -/
def IsSmoothedMaximizer {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1) (u : E2) : Prop :=
  u ∈ Q2 ∧
    ∀ v ∈ Q2, A x v - phihat v - μ * d2 v ≤ A x u - phihat u - μ * d2 u

/-- A maximizer attains the smoothed max-function and yields a bounded-above image set. -/
lemma smoothedMaxFunction_eq_of_isSmoothedMaximizer {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1) (u : E2)
    (hU : IsSmoothedMaximizer Q2 A phihat d2 μ x u) :
    SmoothedMaxFunction Q2 A phihat d2 μ x = A x u - phihat u - μ * d2 u ∧
      BddAbove ((fun u => A x u - phihat u - μ * d2 u) '' Q2) := by
  classical
  set f : E2 → ℝ := fun u => A x u - phihat u - μ * d2 u
  have hmem : f u ∈ f '' Q2 := ⟨u, hU.1, rfl⟩
  have hne : (f '' Q2).Nonempty := ⟨f u, hmem⟩
  have hle : ∀ r ∈ f '' Q2, r ≤ f u := by
    intro r hr
    rcases hr with ⟨v, hv, rfl⟩
    exact hU.2 v hv
  have hbdd : BddAbove (f '' Q2) := ⟨f u, hle⟩
  have hsup_le : sSup (f '' Q2) ≤ f u := csSup_le hne hle
  have hle_sup : f u ≤ sSup (f '' Q2) := le_csSup hbdd hmem
  have hsup_eq : sSup (f '' Q2) = f u := le_antisymm hsup_le hle_sup
  refine ⟨?_, hbdd⟩
  simp [SmoothedMaxFunction, f, hsup_eq]

/-- The smoothed max-function is convex on `Set.univ` when maximizers exist everywhere. -/
lemma smoothedMaxFunction_convexOn_univ {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (uμ : E1 → E2)
    (hmax : ∀ x, IsSmoothedMaximizer Q2 A phihat d2 μ x (uμ x)) :
    ConvexOn ℝ Set.univ (SmoothedMaxFunction Q2 A phihat d2 μ) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hsum
  have hne :
      ((fun u => A (a • x + b • y) u - phihat u - μ * d2 u) '' Q2).Nonempty := by
    refine ⟨A (a • x + b • y) (uμ (a • x + b • y)) - phihat (uμ (a • x + b • y)) -
      μ * d2 (uμ (a • x + b • y)), ?_⟩
    refine ⟨uμ (a • x + b • y), (hmax (a • x + b • y)).1, rfl⟩
  refine csSup_le hne ?_
  intro r hr
  rcases hr with ⟨u, hu, rfl⟩
  have hx_bdd :
      BddAbove ((fun u => A x u - phihat u - μ * d2 u) '' Q2) :=
    (smoothedMaxFunction_eq_of_isSmoothedMaximizer Q2 A phihat d2 μ x (uμ x) (hmax x)).2
  have hy_bdd :
      BddAbove ((fun u => A y u - phihat u - μ * d2 u) '' Q2) :=
    (smoothedMaxFunction_eq_of_isSmoothedMaximizer Q2 A phihat d2 μ y (uμ y) (hmax y)).2
  have hx_le : A x u - phihat u - μ * d2 u ≤ SmoothedMaxFunction Q2 A phihat d2 μ x := by
    have hmem : A x u - phihat u - μ * d2 u ∈
        (fun u => A x u - phihat u - μ * d2 u) '' Q2 := ⟨u, hu, rfl⟩
    simpa [SmoothedMaxFunction] using (le_csSup hx_bdd hmem)
  have hy_le : A y u - phihat u - μ * d2 u ≤ SmoothedMaxFunction Q2 A phihat d2 μ y := by
    have hmem : A y u - phihat u - μ * d2 u ∈
        (fun u => A y u - phihat u - μ * d2 u) '' Q2 := ⟨u, hu, rfl⟩
    simpa [SmoothedMaxFunction] using (le_csSup hy_bdd hmem)
  have hlin :
      A (a • x + b • y) u - phihat u - μ * d2 u =
        a * (A x u - phihat u - μ * d2 u) + b * (A y u - phihat u - μ * d2 u) := by
    have hb' : b = 1 - a := by linarith [hsum]
    calc
      A (a • x + b • y) u - phihat u - μ * d2 u
          = a * A x u + b * A y u - phihat u - μ * d2 u := by
              simp [map_add, map_smul, smul_eq_mul]
      _ = a * (A x u - phihat u - μ * d2 u) + b * (A y u - phihat u - μ * d2 u) := by
            rw [hb']; ring
  have hcomb :
      a * (A x u - phihat u - μ * d2 u) + b * (A y u - phihat u - μ * d2 u) ≤
        a * SmoothedMaxFunction Q2 A phihat d2 μ x +
          b * SmoothedMaxFunction Q2 A phihat d2 μ y := by
    exact add_le_add (mul_le_mul_of_nonneg_left hx_le ha) (mul_le_mul_of_nonneg_left hy_le hb)
  calc
    A (a • x + b • y) u - phihat u - μ * d2 u
        = a * (A x u - phihat u - μ * d2 u) + b * (A y u - phihat u - μ * d2 u) := hlin
    _ ≤ a * SmoothedMaxFunction Q2 A phihat d2 μ x +
          b * SmoothedMaxFunction Q2 A phihat d2 μ y := hcomb

/-- Values of `d2` on `Q2` are bounded above by the supremum `D2`. -/
lemma d2_le_D2_section02 {E2 : Type*} (Q2 : Set E2) (d2 : E2 → ℝ)
    (hbdd_d2 : BddAbove (d2 '' Q2)) {u : E2} (hu : u ∈ Q2) :
    d2 u ≤ sSup (d2 '' Q2) := by
  exact le_csSup hbdd_d2 ⟨u, hu, rfl⟩

/-- Boundedness of the smoothed image set from boundedness of the unsmoothed one. -/
lemma bddAbove_smoothedImage_of_bddAbove_base_section02 {E1 E2 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    (Q2 : Set E2) (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1)
    (hbdd0x : BddAbove ((fun u => A x u - phihat u) '' Q2)) (hμ : 0 ≤ μ)
    (hd2_nonneg : ∀ u ∈ Q2, 0 ≤ d2 u) :
    BddAbove ((fun u => A x u - phihat u - μ * d2 u) '' Q2) := by
  rcases hbdd0x with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro r hr
  rcases hr with ⟨u, hu, rfl⟩
  have hle : A x u - phihat u - μ * d2 u ≤ A x u - phihat u := by
    have hnonneg : 0 ≤ μ * d2 u := mul_nonneg hμ (hd2_nonneg u hu)
    exact sub_le_self _ hnonneg
  have hM' : A x u - phihat u ≤ M := hM ⟨u, hu, rfl⟩
  exact hle.trans hM'

/-- Smoothed max-function is bounded above by the unsmoothed max-function. -/
lemma smoothedMaxFunction_le_f0_section02 {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1)
    (hbdd0x : BddAbove ((fun u => A x u - phihat u) '' Q2)) (hμ : 0 ≤ μ)
    (hd2_nonneg : ∀ u ∈ Q2, 0 ≤ d2 u) :
    sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2) ≤
      sSup ((fun u => A x u - phihat u) '' Q2) := by
  classical
  by_cases hQ2 : Q2 = ∅
  · simp [hQ2]
  · have hne : ((fun u => A x u - phihat u - μ * d2 u) '' Q2).Nonempty := by
      rcases (Set.nonempty_iff_ne_empty.mpr hQ2) with ⟨u, hu⟩
      exact ⟨A x u - phihat u - μ * d2 u, ⟨u, hu, rfl⟩⟩
    refine csSup_le hne ?_
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    have hle_base : A x u - phihat u - μ * d2 u ≤ A x u - phihat u := by
      have hnonneg : 0 ≤ μ * d2 u := mul_nonneg hμ (hd2_nonneg u hu)
      exact sub_le_self _ hnonneg
    have hle_sup :
        A x u - phihat u ≤ sSup ((fun u => A x u - phihat u) '' Q2) := by
      exact le_csSup hbdd0x ⟨u, hu, rfl⟩
    exact hle_base.trans hle_sup

/-- Unsmooth max-function is bounded by the smoothed max plus `μ * D2`. -/
lemma f0_le_smoothedMaxFunction_add_section02 {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ) (x : E1)
    (hbdd0x : BddAbove ((fun u => A x u - phihat u) '' Q2)) (hbdd_d2 : BddAbove (d2 '' Q2))
    (hμ : 0 ≤ μ) (hd2_nonneg : ∀ u ∈ Q2, 0 ≤ d2 u) :
    sSup ((fun u => A x u - phihat u) '' Q2) ≤
      sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2) + μ * sSup (d2 '' Q2) := by
  classical
  by_cases hQ2 : Q2 = ∅
  · simp [hQ2]
  · have hne : ((fun u => A x u - phihat u) '' Q2).Nonempty := by
      rcases (Set.nonempty_iff_ne_empty.mpr hQ2) with ⟨u, hu⟩
      exact ⟨A x u - phihat u, ⟨u, hu, rfl⟩⟩
    have hbdd_smoothed :
        BddAbove ((fun u => A x u - phihat u - μ * d2 u) '' Q2) :=
      bddAbove_smoothedImage_of_bddAbove_base_section02 Q2 A phihat d2 μ x hbdd0x hμ hd2_nonneg
    refine csSup_le hne ?_
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    have hD2 : d2 u ≤ sSup (d2 '' Q2) :=
      d2_le_D2_section02 Q2 d2 hbdd_d2 hu
    have hmul : μ * d2 u ≤ μ * sSup (d2 '' Q2) :=
      mul_le_mul_of_nonneg_left hD2 hμ
    have hineq :
        A x u - phihat u ≤ (A x u - phihat u - μ * d2 u) + μ * sSup (d2 '' Q2) := by
      linarith
    have hle_smoothed :
        A x u - phihat u - μ * d2 u ≤
          sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2) := by
      exact le_csSup hbdd_smoothed ⟨u, hu, rfl⟩
    have hle_add :
        (A x u - phihat u - μ * d2 u) + μ * sSup (d2 '' Q2) ≤
          sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2) + μ * sSup (d2 '' Q2) :=
      add_le_add_left hle_smoothed _
    exact hineq.trans hle_add

/-- Proposition 1.2.3.
Define `D2 = max { d2 u : u ∈ Q2 }` (equation (eq:D2_def)) and
`f0(x) = max { ⟪A x, u⟫_2 - phihat u : u ∈ Q2 }` (equation (eq:f0_def)).
Then for all `x ∈ E1`, `f_μ(x) ≤ f0(x) ≤ f_μ(x) + μ D2` (equation (2.7)). -/
theorem smoothedMaxFunction_bounds {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (phihat d2 : E2 → ℝ) (μ : ℝ)
    (hμ : 0 ≤ μ) (hd2_nonneg : ∀ u ∈ Q2, 0 ≤ d2 u)
    (hbdd0 : ∀ x, BddAbove ((fun u => A x u - phihat u) '' Q2))
    (hbdd_d2 : BddAbove (d2 '' Q2)) :
    let D2 : ℝ := sSup (d2 '' Q2)
    let f0 : E1 → ℝ := fun x => sSup ((fun u => A x u - phihat u) '' Q2)
    let fμ : E1 → ℝ := SmoothedMaxFunction Q2 A phihat d2 μ
    ∀ x : E1, fμ x ≤ f0 x ∧ f0 x ≤ fμ x + μ * D2 := by
  classical
  intro D2 f0 fμ x
  have h_le :
      sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2) ≤
        sSup ((fun u => A x u - phihat u) '' Q2) :=
    smoothedMaxFunction_le_f0_section02 Q2 A phihat d2 μ x (hbdd0 x) hμ hd2_nonneg
  have h_ge :
      sSup ((fun u => A x u - phihat u) '' Q2) ≤
        sSup ((fun u => A x u - phihat u - μ * d2 u) '' Q2) + μ * sSup (d2 '' Q2) :=
    f0_le_smoothedMaxFunction_add_section02 Q2 A phihat d2 μ x (hbdd0 x) hbdd_d2 hμ hd2_nonneg
  refine ⟨?_, ?_⟩
  · simpa [D2, f0, fμ, SmoothedMaxFunction] using h_le
  · simpa [D2, f0, fμ, SmoothedMaxFunction] using h_ge
