/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.Problem
public import Mathlib.Logic.Godel.GodelBetaFunction
public import Mathlib.NumberTheory.Dioph

@[expose] public section

namespace QuadraticIntegerFeasibility

/-- Helper for Theorem 1.4: an integer is forced to be zero exactly when it satisfies the paired
inequalities `z ≤ 0` and `-z ≤ 0`. -/
lemma eqZero_iff_nonpos_and_neg_nonpos (z : ℤ) :
    z = 0 ↔ z ≤ 0 ∧ -z ≤ 0 := by
  constructor
  · intro hz
    -- Rewriting by `z = 0` turns both inequalities into the tautology `0 ≤ 0`.
    subst hz
    simp
  · rintro ⟨hz_nonpos, hz_neg_nonpos⟩
    -- The second inequality is `0 ≤ z`, so antisymmetry forces `z = 0`.
    exact le_antisymm hz_nonpos (neg_nonpos.mp hz_neg_nonpos)

/-- Helper for Theorem 1.4: a nonnegative integer is exactly an integer coming from a natural
number. -/
lemma nonneg_iff_exists_natCast (z : ℤ) :
    0 ≤ z ↔ ∃ n : ℕ, z = (n : ℤ) := by
  constructor
  · intro hz
    -- Recover the natural witness by `Int.toNat` and fold it back with the nonnegativity
    -- hypothesis.
    refine ⟨Int.toNat z, ?_⟩
    exact (Int.toNat_of_nonneg hz).symm
  · rintro ⟨n, rfl⟩
    -- Any natural-number cast to `ℤ` is nonnegative.
    exact Int.natCast_nonneg n

/-- Helper for Theorem 1.4: mapping a natural assignment into `ℤ` commutes with `List.getD`. -/
lemma getD_map_natCast (assignment : List ℕ) (i : ℕ) :
    (assignment.map fun n ↦ (n : ℤ)).getD i 0 = (assignment.getD i 0 : ℤ) := by
  induction assignment generalizing i with
  | nil =>
      -- Both default values are used on the empty assignment.
      simp
  | cons head tail ih =>
      -- Split on whether `getD` asks for the head coordinate or a tail coordinate.
      cases i with
      | zero =>
          simp
      | succ j =>
          simpa using ih j

/-- Helper for Theorem 1.4: an existential arithmetic relation selecting the two branches of
`Nat.pair` using complementary natural selectors. -/
def pairRelation (n a b : ℕ) : Prop :=
  ∃ e f u v : ℕ,
    e + f = 1 ∧
      e * b = e * (a + u + 1) ∧
      f * a = f * (b + v) ∧
      n = e * (b * b + a) + f * (a * a + a + b)

/-- Helper for Theorem 1.4: the selector-based arithmetic relation is exactly the graph of
`Nat.pair`. -/
lemma pairRelation_iff (n a b : ℕ) :
    pairRelation n a b ↔ n = Nat.pair a b := by
  constructor
  · rintro ⟨e, f, u, v, hSelectors, hLeft, hRight, hValue⟩
    -- The complementary selectors force exactly one of the two ordered pairing branches.
    rcases Nat.eq_zero_or_pos e with rfl | he
    · have hf : f = 1 := by omega
      subst f
      simp only [one_mul] at hRight
      have hab : b ≤ a := by
        omega
      simpa [Nat.pair, Nat.not_lt.mpr hab] using hValue
    · have heOne : e = 1 := by omega
      have hf : f = 0 := by omega
      subst e
      subst f
      simp only [one_mul] at hLeft
      have hab : a < b := by
        omega
      simpa [Nat.pair, hab] using hValue
  · intro hPair
    -- Choose the active selector and the corresponding difference witness from the order of the
    -- two inputs.
    by_cases hab : a < b
    · refine ⟨1, 0, b - a - 1, 0, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · simp
      · simpa [Nat.pair, hab] using hPair
    · have hba : b ≤ a := Nat.le_of_not_gt hab
      refine ⟨0, 1, 0, a - b, ?_, ?_, ?_, ?_⟩
      · omega
      · simp
      · omega
      · simpa [Nat.pair, hab] using hPair

/-- Helper for Theorem 1.4: the selector presentation of the graph of `Nat.pair` is a
Diophantine relation. -/
lemma pairRelation_dioph :
    Dioph {x : Vector3 ℕ 3 |
      pairRelation (x (Fin2.ofNat' 0)) (x (Fin2.ofNat' 1)) (x (Fin2.ofNat' 2))} := by
  -- First express the four arithmetic equations with four explicit witness coordinates. The
  -- coordinate order lets existential elimination leave exactly the graph coordinates `n,a,b`.
  have d0 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 0)) :=
    Dioph.proj_dioph _
  have d1 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 1)) :=
    Dioph.proj_dioph _
  have d2 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 2)) :=
    Dioph.proj_dioph _
  have d3 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 3)) :=
    Dioph.proj_dioph _
  have d4 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 4)) :=
    Dioph.proj_dioph _
  have d5 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 5)) :=
    Dioph.proj_dioph _
  have d6 : Dioph.DiophFn (fun x : Vector3 ℕ 7 ↦ x (Fin2.ofNat' 6)) :=
    Dioph.proj_dioph _
  have hSelectors : Dioph {x : Vector3 ℕ 7 |
      x (Fin2.ofNat' 3) + x (Fin2.ofNat' 2) = 1} :=
    Dioph.eq_dioph (Dioph.add_dioph d3 d2) (Dioph.const_dioph 1)
  have hLeft : Dioph {x : Vector3 ℕ 7 |
      x (Fin2.ofNat' 3) * x (Fin2.ofNat' 6) =
        x (Fin2.ofNat' 3) * (x (Fin2.ofNat' 5) + x (Fin2.ofNat' 1) + 1)} :=
    Dioph.eq_dioph (Dioph.mul_dioph d3 d6)
      (Dioph.mul_dioph d3
        (Dioph.add_dioph (Dioph.add_dioph d5 d1) (Dioph.const_dioph 1)))
  have hRight : Dioph {x : Vector3 ℕ 7 |
      x (Fin2.ofNat' 2) * x (Fin2.ofNat' 5) =
        x (Fin2.ofNat' 2) * (x (Fin2.ofNat' 6) + x (Fin2.ofNat' 0))} :=
    Dioph.eq_dioph (Dioph.mul_dioph d2 d5)
      (Dioph.mul_dioph d2 (Dioph.add_dioph d6 d0))
  have hValue : Dioph {x : Vector3 ℕ 7 |
      x (Fin2.ofNat' 4) =
        x (Fin2.ofNat' 3) *
            (x (Fin2.ofNat' 6) * x (Fin2.ofNat' 6) + x (Fin2.ofNat' 5)) +
          x (Fin2.ofNat' 2) *
            (x (Fin2.ofNat' 5) * x (Fin2.ofNat' 5) +
              x (Fin2.ofNat' 5) + x (Fin2.ofNat' 6))} :=
    Dioph.eq_dioph d4
      (Dioph.add_dioph
        (Dioph.mul_dioph d3 (Dioph.add_dioph (Dioph.mul_dioph d6 d6) d5))
        (Dioph.mul_dioph d2
          (Dioph.add_dioph (Dioph.add_dioph (Dioph.mul_dioph d5 d5) d5) d6)))
  have hEquations : Dioph {x : Vector3 ℕ 7 |
      ((x (Fin2.ofNat' 3) + x (Fin2.ofNat' 2) = 1 ∧
        x (Fin2.ofNat' 3) * x (Fin2.ofNat' 6) =
          x (Fin2.ofNat' 3) * (x (Fin2.ofNat' 5) + x (Fin2.ofNat' 1) + 1)) ∧
        x (Fin2.ofNat' 2) * x (Fin2.ofNat' 5) =
          x (Fin2.ofNat' 2) * (x (Fin2.ofNat' 6) + x (Fin2.ofNat' 0))) ∧
        x (Fin2.ofNat' 4) =
          x (Fin2.ofNat' 3) *
              (x (Fin2.ofNat' 6) * x (Fin2.ofNat' 6) + x (Fin2.ofNat' 5)) +
            x (Fin2.ofNat' 2) *
              (x (Fin2.ofNat' 5) * x (Fin2.ofNat' 5) +
                x (Fin2.ofNat' 5) + x (Fin2.ofNat' 6))} := by
    exact ((hSelectors.inter hLeft).inter hRight).inter hValue
  -- Eliminate `v,u,f,e` in order and identify the remaining predicate with `pairRelation`.
  have hWithoutV := Dioph.vec_ex1_dioph 6 hEquations
  have hWithoutU := Dioph.vec_ex1_dioph 5 hWithoutV
  have hWithoutF := Dioph.vec_ex1_dioph 4 hWithoutU
  have hWithoutE := Dioph.vec_ex1_dioph 3 hWithoutF
  exact Dioph.ext hWithoutE (fun x ↦ by
    constructor
    · rintro ⟨e, f, u, v, hEquations⟩
      refine ⟨e, f, u, v, ?_⟩
      simpa only [Set.mem_setOf_eq, Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs,
        and_assoc] using hEquations
    · rintro ⟨e, f, u, v, hEquations⟩
      refine ⟨e, f, u, v, ?_⟩
      simpa only [Set.mem_setOf_eq, Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs,
        and_assoc] using hEquations)

/-- Helper for Theorem 1.4: the standard pairing function is Diophantine as a binary natural
function. -/
lemma natPair_diophFn :
    Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦
      Nat.pair (x (Fin2.ofNat' 0)) (x (Fin2.ofNat' 1))) := by
  -- Reorient the selector relation to the graph convention where the output is the head.
  apply (Dioph.diophFn_vec _).2
  exact Dioph.ext pairRelation_dioph (fun x ↦ by
    simpa only [Set.mem_setOf_eq, Function.comp_apply, Fin2.ofNat', eq_comm] using
      pairRelation_iff (x (Fin2.ofNat' 0)) (x (Fin2.ofNat' 1)) (x (Fin2.ofNat' 2)))

/-- Helper for Theorem 1.4: the left projection of `Nat.unpair` is a Diophantine unary natural
function. -/
lemma natUnpairLeft_diophFn :
    Dioph.DiophFn (fun x : Vector3 ℕ 1 ↦ (x (Fin2.ofNat' 0)).unpair.1) := by
  -- Reverse the graph coordinates, eliminate the unobserved right projection, and use
  -- `Nat.pair_unpair` for the converse witness.
  have hReversed : Dioph {x : Vector3 ℕ 3 |
      pairRelation (x (Fin2.ofNat' 2)) (x (Fin2.ofNat' 1)) (x (Fin2.ofNat' 0))} := by
    exact Dioph.ext
      (pairRelation_dioph.reindex_dioph (Fin2 3) Fin2.rev) (fun x ↦ by
        rfl)
  have hExistsRight := Dioph.vec_ex1_dioph 2 hReversed
  apply (Dioph.diophFn_vec _).2
  exact Dioph.ext hExistsRight (fun x ↦ by
    constructor
    · rintro ⟨right, hPair⟩
      have hPair' :
          pairRelation (x (Fin2.ofNat' 1)) (x (Fin2.ofNat' 0)) right := by
        simpa only [Set.mem_setOf_eq, Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs] using hPair
      have hCode : x (Fin2.ofNat' 1) = Nat.pair (x (Fin2.ofNat' 0)) right :=
        (pairRelation_iff _ _ _).1 hPair'
      simpa only [Set.mem_setOf_eq, Function.comp_apply, Fin2.ofNat', Nat.unpair_pair] using
        congrArg (fun value : ℕ ↦ value.unpair.1) hCode
    · intro hLeft
      have hLeft' : (x (Fin2.ofNat' 1)).unpair.1 = x (Fin2.ofNat' 0) := by
        simpa only [Set.mem_setOf_eq, Function.comp_apply, Fin2.ofNat'] using hLeft
      have hCode :
          x (Fin2.ofNat' 1) =
            Nat.pair (x (Fin2.ofNat' 0)) (x (Fin2.ofNat' 1)).unpair.2 := by
        rw [← hLeft']
        exact (Nat.pair_unpair _).symm
      have hPair :
          pairRelation (x (Fin2.ofNat' 1)) (x (Fin2.ofNat' 0))
            (x (Fin2.ofNat' 1)).unpair.2 :=
        (pairRelation_iff _ _ _).2 hCode
      refine ⟨(x (Fin2.ofNat' 1)).unpair.2, ?_⟩
      simpa only [Set.mem_setOf_eq, Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs] using hPair)

/-- Helper for Theorem 1.4: the right projection of `Nat.unpair` is a Diophantine unary natural
function. -/
lemma natUnpairRight_diophFn :
    Dioph.DiophFn (fun x : Vector3 ℕ 1 ↦ (x (Fin2.ofNat' 0)).unpair.2) := by
  -- Rotate the graph coordinates, eliminate the unobserved left projection, and use
  -- `Nat.pair_unpair` for the converse witness.
  have hRotated : Dioph {x : Vector3 ℕ 3 |
      pairRelation (x (Fin2.ofNat' 2)) (x (Fin2.ofNat' 0)) (x (Fin2.ofNat' 1))} := by
    exact Dioph.ext
      (pairRelation_dioph.reindex_dioph (Fin2 3)
        (Vector3.cons (Fin2.ofNat' 2)
          (Vector3.cons (Fin2.ofNat' 0)
            (Vector3.cons (Fin2.ofNat' 1) Vector3.nil)))) (fun x ↦ by
        rfl)
  have hExistsLeft := Dioph.vec_ex1_dioph 2 hRotated
  apply (Dioph.diophFn_vec _).2
  exact Dioph.ext hExistsLeft (fun x ↦ by
    constructor
    · rintro ⟨left, hPair⟩
      have hPair' :
          pairRelation (x (Fin2.ofNat' 1)) left (x (Fin2.ofNat' 0)) := by
        simpa only [Set.mem_setOf_eq, Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs] using hPair
      have hCode : x (Fin2.ofNat' 1) = Nat.pair left (x (Fin2.ofNat' 0)) :=
        (pairRelation_iff _ _ _).1 hPair'
      simpa only [Set.mem_setOf_eq, Function.comp_apply, Fin2.ofNat', Nat.unpair_pair] using
        congrArg (fun value : ℕ ↦ value.unpair.2) hCode
    · intro hRight
      have hRight' : (x (Fin2.ofNat' 1)).unpair.2 = x (Fin2.ofNat' 0) := by
        simpa only [Set.mem_setOf_eq, Function.comp_apply, Fin2.ofNat'] using hRight
      have hCode :
          x (Fin2.ofNat' 1) =
            Nat.pair (x (Fin2.ofNat' 1)).unpair.1 (x (Fin2.ofNat' 0)) := by
        rw [← hRight']
        exact (Nat.pair_unpair _).symm
      have hPair :
          pairRelation (x (Fin2.ofNat' 1)) (x (Fin2.ofNat' 1)).unpair.1
            (x (Fin2.ofNat' 0)) :=
        (pairRelation_iff _ _ _).2 hCode
      refine ⟨(x (Fin2.ofNat' 1)).unpair.1, ?_⟩
      simpa only [Set.mem_setOf_eq, Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs] using hPair)

/-- Helper for Theorem 1.4: composition of a unary Diophantine function with a Diophantine
function is Diophantine. -/
lemma diophFn_compUnary {α : Type} {f : Vector3 ℕ 1 → ℕ} {g : (α → ℕ) → ℕ}
    (hf : Dioph.DiophFn f) (hg : Dioph.DiophFn g) :
    Dioph.DiophFn (fun x ↦ f (Vector3.cons (g x) Vector3.nil)) := by
  -- Supply the singleton vector of inner functions to the general finite composition theorem.
  have hAll : VectorAllP Dioph.DiophFn (Vector3.cons g Vector3.nil) := by
    exact hg
  have hComposition :=
    Dioph.diophFn_comp hf (Vector3.cons g Vector3.nil) hAll
  have hVector (x : α → ℕ) :
      (fun i ↦ Vector3.cons g Vector3.nil i x) = Vector3.cons (g x) Vector3.nil := by
    funext i
    exact Fin2.cases' rfl Fin2.elim0 i
  simpa only [hVector] using hComposition

/-- Helper for Theorem 1.4: Gödel's beta lookup function is Diophantine in its code and index. -/
lemma natBeta_diophFn :
    Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦
      Nat.beta (x (Fin2.ofNat' 0)) (x (Fin2.ofNat' 1))) := by
  -- Build both decoded components from the certified unpairing graphs.
  have dCode : Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦ x (Fin2.ofNat' 0)) :=
    Dioph.proj_dioph _
  have dIndex : Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦ x (Fin2.ofNat' 1)) :=
    Dioph.proj_dioph _
  have dLeft : Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦ (x (Fin2.ofNat' 0)).unpair.1) := by
    simpa only [Fin2.ofNat', Vector3.cons_fz] using
      diophFn_compUnary natUnpairLeft_diophFn dCode
  have dRight : Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦ (x (Fin2.ofNat' 0)).unpair.2) := by
    simpa only [Fin2.ofNat', Vector3.cons_fz] using
      diophFn_compUnary natUnpairRight_diophFn dCode
  -- Assemble the beta denominator and use Diophantine closure under remainder.
  have dDenominator : Dioph.DiophFn (fun x : Vector3 ℕ 2 ↦
      (x (Fin2.ofNat' 1) + 1) * (x (Fin2.ofNat' 0)).unpair.2 + 1) :=
    Dioph.add_dioph
      (Dioph.mul_dioph (Dioph.add_dioph dIndex (Dioph.const_dioph 1)) dRight)
      (Dioph.const_dioph 1)
  simpa only [Nat.beta] using Dioph.mod_dioph dLeft dDenominator

/-- Helper for Theorem 1.4: applying Gödel's beta lookup to a Diophantine code and a
Diophantine index again gives a Diophantine function. -/
lemma natBeta_comp_diophFn {α : Type} {code index : (α → ℕ) → ℕ}
    (hCode : Dioph.DiophFn code) (hIndex : Dioph.DiophFn index) :
    Dioph.DiophFn (fun v ↦ Nat.beta (code v) (index v)) := by
  -- Present the two inner functions as the binary vector expected by `natBeta_diophFn`.
  have hAll :
      VectorAllP Dioph.DiophFn
        (Vector3.cons code (Vector3.cons index Vector3.nil)) := by
    exact ⟨hCode, hIndex⟩
  simpa only [Fin2.ofNat', Vector3.cons_fz, Vector3.cons_fs] using
    Dioph.diophFn_comp natBeta_diophFn
      (Vector3.cons code (Vector3.cons index Vector3.nil)) hAll

/-- Helper for Theorem 1.4: equality between a composed Gödel-beta lookup and a Diophantine
value is a Diophantine relation. -/
lemma natBeta_eq_dioph {α : Type} {code index value : (α → ℕ) → ℕ}
    (hCode : Dioph.DiophFn code) (hIndex : Dioph.DiophFn index)
    (hValue : Dioph.DiophFn value) :
    Dioph {v | Nat.beta (code v) (index v) = value v} := by
  -- Combine the reusable beta-composition theorem with closure under equality.
  exact Dioph.eq_dioph (natBeta_comp_diophFn hCode hIndex) hValue

/-- Helper for Theorem 1.4: every finite natural-number trace has one Gödel-beta code that
recovers all of its entries. -/
lemma exists_natBeta_code (values : List ℕ) :
    ∃ code : ℕ, ∀ i : Fin values.length, Nat.beta code i = values[i] := by
  -- The canonical `Nat.unbeta` code satisfies every in-range lookup simultaneously.
  exact ⟨Nat.unbeta values, Nat.beta_unbeta_coe values⟩

end QuadraticIntegerFeasibility
