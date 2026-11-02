module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.AcceptsDioph
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.SelectorRegsGlobal

/-!
# `Aggregation (k + 1)`

#49, phase 4, final layer. `SelectorRegsGlobal` reduced the bounded conjunction of encoded
steps, for an arbitrary `P : Program (k + 1)`, to `GlobalConditionsK`. Representing that
discharges `Aggregation` at every register count.

## What scales and what does not

Compared with `Spike/SelectorProgramDioph`, three witness families are indexed rather than
single: the lanes by `Fin (k + 2)`, and the two residual families by `Fin (k + 1)`. The selector
family is unchanged, and so is the number of *kinds* of condition. Everything that grows does so
as an `ExpDioph.fin_and` or an `ExpTerm.sumTerm` over an index type fixed by the program and its
register count — never by the run length `N`, which is the quantifier the obligation is about.

## Main results

* `RegisterMachine.expDioph_stepBundle_regs` — `StepBundle` for every `P : Program (k + 1)`
* `RegisterMachine.aggregation_succ` — `Aggregation (k + 1)`, for every `k`
* `RegisterMachine.dioph_accepts_regs` — acceptance by any register machine is Diophantine
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-- The witness block: the lanes, the branch selectors, the two residual families, and the
geometric sum. -/
abbrev RegsWitness (P : Program (k + 1)) :=
  Fin (k + 2) ⊕ (Fin P.length ⊕ Fin P.length) ⊕ Fin (k + 1) ⊕ Fin (k + 1) ⊕ Unit

namespace RegsWitness

/-- Lane `j`. -/
abbrev lane {P : Program (k + 1)} (j : Fin (k + 2)) : RegsWitness P := .inl j
/-- Branch selector `c`. -/
abbrev sel {P : Program (k + 1)} (c : Fin P.length ⊕ Fin P.length) : RegsWitness P :=
  .inr (.inl c)
/-- Register `r`'s positive residual. -/
abbrev pos {P : Program (k + 1)} (r : Fin (k + 1)) : RegsWitness P := .inr (.inr (.inl r))
/-- Register `r`'s zero residual. -/
abbrev zero {P : Program (k + 1)} (r : Fin (k + 1)) : RegsWitness P :=
  .inr (.inr (.inr (.inl r)))
/-- The geometric sum. -/
abbrev geo {P : Program (k + 1)} : RegsWitness P := .inr (.inr (.inr (.inr ())))

end RegsWitness

open RegsWitness in
/-- The body under the witnesses: the geometric sum is pinned, and the rest is
`GlobalConditionsK` verbatim. -/
def regsBody (P : Program (k + 1)) (N W R : ExpTerm α) :
    Set ((α ⊕ RegsWitness P) → ℕ) :=
  {u | u (.inr geo) * 2 ^ ((W.map Sum.inl).eval u * (k + 2) + 1) + 1
        = u (.inr geo)
          + (2 ^ ((W.map Sum.inl).eval u * (k + 2) + 1)) ^ (N.map Sum.inl).eval u ∧
      GlobalConditionsK P ((W.map Sum.inl).eval u) ((N.map Sum.inl).eval u)
        ((R.map Sum.inl).eval u) (fun j => u (.inr (lane j))) (fun c => u (.inr (sel c)))
        (fun r => u (.inr (pos r))) (fun r => u (.inr (zero r)))}

open RegsWitness in
theorem expDioph_regsBody (P : Program (k + 1)) (N W R : ExpTerm α) :
    ExpDioph (regsBody P N W R) := by
  set W' : ExpTerm (α ⊕ RegsWitness P) := W.map Sum.inl with hW'
  set N' : ExpTerm (α ⊕ RegsWitness P) := N.map Sum.inl with hN'
  set R' : ExpTerm (α ⊕ RegsWitness P) := R.map Sum.inl with hR'
  set pw : ExpTerm (α ⊕ RegsWitness P) := .pow (.const 2) W' with hpw
  set B : ExpTerm (α ⊕ RegsWitness P) :=
    .pow (.const 2) (.add (.mul W' (.const (k + 2))) (.const 1)) with hB
  set Bn : ExpTerm (α ⊕ RegsWitness P) := .pow B N' with hBn
  set vX : Fin (k + 2) → ExpTerm (α ⊕ RegsWitness P) :=
    fun j => .var (.inr (lane j)) with hvX
  set vS : Fin P.length ⊕ Fin P.length → ExpTerm (α ⊕ RegsWitness P) :=
    fun c => .var (.inr (sel c)) with hvS
  set vRes : Fin (k + 1) → ExpTerm (α ⊕ RegsWitness P) :=
    fun r => .var (.inr (pos r)) with hvRes
  set vZres : Fin (k + 1) → ExpTerm (α ⊕ RegsWitness P) :=
    fun r => .var (.inr (zero r)) with hvZres
  set vG : ExpTerm (α ⊕ RegsWitness P) := .var (.inr geo) with hvG
  set laneN : ExpTerm (α ⊕ RegsWitness P) := .mul (.sub pw (.const 1)) vG with hlaneN
  set laneS : ExpTerm (α ⊕ RegsWitness P) :=
    .mul (.sub pw (.const 1)) (.add (.const 1) (.mul B vG)) with hlaneS
  -- the conditions, assembled from the last one back
  have c14 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ c, u (.inr (sel c)) = 0 ∨ branchTgt P c < 2 ^ W'.eval u} :=
    ExpDioph.fin_and fun c =>
      ExpDioph.or (ExpDioph.of_eq (s := vS c) (t := .const 0))
        (ExpDioph.of_lt (s := .const (branchTgt P c)) (t := pw))
  have c13 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, Nat.IsBinarySubmask (u (.inr (pos r))) (laneN.eval u)} :=
    ExpDioph.fin_and fun r => ExpDioph.of_isBinarySubmask (vRes r) laneN
  have c12 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, (ExpTerm.mod (vX r.succ) Bn).eval u
        = (ExpTerm.add (vRes r) (ExpTerm.sumTerm fun p : Fin P.length =>
            .mul (.const ((P.get p).lossAt r)) (vS (.inl p)))).eval u} :=
    ExpDioph.fin_and fun r => ExpDioph.of_eq
      (s := .mod (vX r.succ) Bn)
      (t := .add (vRes r) (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const ((P.get p).lossAt r)) (vS (.inl p))))
  have c11 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, Nat.IsBinarySubmask (u (.inr (zero r))) (laneN.eval u)} :=
    ExpDioph.fin_and fun r => ExpDioph.of_isBinarySubmask (vZres r) laneN
  have c10 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, (ExpTerm.add (.add (.mod (vX r.succ) Bn)
          (.mul (ExpTerm.sumTerm fun p : Fin P.length =>
            .mul (.const ((P.get p).lossAt r)) (vS (.inr p))) (.sub pw (.const 1))))
        (vZres r)).eval u = laneN.eval u} :=
    ExpDioph.fin_and fun r => ExpDioph.of_eq
      (s := .add (.add (.mod (vX r.succ) Bn)
        (.mul (ExpTerm.sumTerm fun p : Fin P.length =>
          .mul (.const ((P.get p).lossAt r)) (vS (.inr p))) (.sub pw (.const 1)))) (vZres r))
      (t := laneN)
  have c9 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ p, (P.get p).branches = 0 → u (.inr (sel (.inr p))) = 0} :=
    ExpDioph.fin_and fun p => by
      by_cases hp : (P.get p).branches = 0
      · exact (ExpDioph.of_eq (s := vS (.inr p)) (t := .const 0)).congr fun u => by
          simp only [Set.mem_setOf_eq, hvS, ExpTerm.eval]
          exact ⟨fun h _ => h, fun h => h hp⟩
      · exact ExpDioph.of_true.congr fun u => by
          simp only [Set.mem_univ, true_iff]
          exact fun h => absurd h hp
  have c8 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, (ExpTerm.add (.div (vX r.succ) B) (ExpTerm.sumTerm fun p : Fin P.length =>
          .mul (.const ((P.get p).lossAt r)) (vS (.inl p)))).eval u
        = (ExpTerm.add (.mod (vX r.succ) Bn) (ExpTerm.sumTerm fun p : Fin P.length =>
          .mul (.const ((P.get p).gainAt r)) (vS (.inl p)))).eval u} :=
    ExpDioph.fin_and fun r => ExpDioph.of_eq
      (s := .add (.div (vX r.succ) B) (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const ((P.get p).lossAt r)) (vS (.inl p))))
      (t := .add (.mod (vX r.succ) Bn) (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const ((P.get p).gainAt r)) (vS (.inl p))))
  have c7 := ExpDioph.and (ExpDioph.of_eq (s := .div (vX 0) B)
    (t := ExpTerm.sumTerm fun c => .mul (.const (branchTgt P c)) (vS c)))
    (ExpDioph.and c8 (ExpDioph.and c9 (ExpDioph.and c10
      (ExpDioph.and c11 (ExpDioph.and c12 (ExpDioph.and c13 c14))))))
  have c6 := ExpDioph.and (ExpDioph.of_eq (s := .mod (vX 0) Bn)
    (t := ExpTerm.sumTerm fun c => .mul (.const (branchIdx P c)) (vS c))) c7
  have c5 := ExpDioph.and
    (ExpDioph.of_eq (s := ExpTerm.sumTerm fun c => vS c) (t := vG)) c6
  have c4 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ c, Nat.IsBinarySubmask (u (.inr (sel c))) (vG.eval u)} :=
    ExpDioph.fin_and fun c => ExpDioph.of_isBinarySubmask (vS c) vG
  have c3 := ExpDioph.and (ExpDioph.of_eq (s := R')
    (t := ExpTerm.sumTerm fun j : Fin (k + 2) =>
      .mul (.pow pw (.const (j : ℕ))) (vX j))) (ExpDioph.and c4 c5)
  have c2 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ j, Nat.IsBinarySubmask (u (.inr (lane j))) (laneS.eval u)} :=
    ExpDioph.fin_and fun j => ExpDioph.of_isBinarySubmask (vX j) laneS
  have c1 := ExpDioph.and (ExpDioph.of_lt (s := .const P.length) (t := pw))
    (ExpDioph.and c2 c3)
  have c0 := ExpDioph.and
    (ExpDioph.of_eq (s := .add (.mul vG B) (.const 1)) (t := .add vG Bn)) c1
  refine ExpDioph.congr c0 ?_
  intro u
  have hb : (2 : ℕ) ≤ 2 ^ (W'.eval u * (k + 2) + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (W'.eval u * (k + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, regsBody, GlobalConditionsK, laneMaskAt,
    bitMaskAt, geom_succ, hlaneN, hlaneS, hpw, hB, hBn, hvX, hvS, hvRes, hvZres, hvG,
    hW', hN', hR', ExpTerm.eval, ExpTerm.eval_sumTerm]
  constructor
  · rintro ⟨hpin, rest⟩
    have hG := geom_unique hb hpin
    refine ⟨hpin, ?_⟩
    rw [← hG]
    exact rest
  · rintro ⟨hpin, rest⟩
    have hG := geom_unique hb hpin
    refine ⟨hpin, ?_⟩
    rw [← hG] at rest
    exact rest

open RegsWitness in
/-- **The obligation, for every program on `k + 1` registers.** -/
theorem expDioph_stepBundle_regs (P : Program (k + 1)) (N W R : ExpTerm α) :
    ExpDioph (StepBundle P N W R) := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_regsBody P N W R)) fun v => ?_
  simp only [StepBundle, regsBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl,
    Sum.elim_inr, show k + 1 + 1 = k + 2 from rfl]
  rw [globalConditionsK_iff]
  constructor
  · rintro ⟨u, _, h⟩
    exact ⟨fun j => u (lane j), fun c => u (sel c), fun r => u (pos r), fun r => u (zero r), h⟩
  · rintro ⟨X, S, Res, Zres, h⟩
    refine ⟨Sum.elim X (Sum.elim S (Sum.elim Res (Sum.elim Zres
      (fun _ => geom (2 ^ (W.eval v * (k + 2) + 1)) (N.eval v))))), geom_spec _ _, h⟩

/-- **`Aggregation` at every register count.** -/
theorem aggregation_succ (k : ℕ) : Aggregation (k + 1) :=
  fun P N W R => expDioph_stepBundle_regs P N W R

/-- **Acceptance by any register machine is Diophantine**, unconditionally. -/
theorem expDioph_accepts_regs (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  expDioph_accepts (aggregation_succ k) P X Y

theorem dioph_accepts_regs (P : Program (k + 1)) (X Y : ExpTerm α) :
    Dioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  (expDioph_accepts_regs P X Y).dioph

end RegisterMachine

end Hilbert10
