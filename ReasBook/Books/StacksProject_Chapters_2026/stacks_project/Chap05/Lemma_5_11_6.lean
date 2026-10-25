module

public import stacks_project.Chap05.Definition_5_11_4
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Grade

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Lemma 5.11.6: strict containment of irreducible closed subsets gives positive
relative codimension. -/
private theorem codimBetween_pos_of_lt {T T' : IrreducibleCloseds X} (hTT' : T < T') :
    0 < codimBetween T T' hTT'.le := by
  -- Rewrite relative codimension as coheight of the bottom element in the interval `[T, T']`.
  let _ : Fact (T ≤ T') := ⟨hTT'.le⟩
  change 0 < coheight (⊥ : Set.Icc T T')
  exact coheight_pos_of_lt_top hTT'

/-- Helper for Lemma 5.11.6: a cover relation contributes exactly one unit of relative
codimension, once finiteness of codimension is known. -/
private theorem codimBetween_eq_one_of_covBy
    {T T' : IrreducibleCloseds X}
    (hfinite : ∀ ⦃A B : IrreducibleCloseds X⦄ (hAB : A ≤ B), codimBetween A B hAB < ⊤)
    (hTT' : T ⋖ T') :
    codimBetween T T' hTT'.le = 1 := by
  -- Route correction: exclude codimension `≥ 2` by producing an intermediate irreducible closed
  -- subset, which contradicts that `T ⋖ T'`.
  have hfin : codimBetween T T' hTT'.le < ⊤ := hfinite hTT'.le
  have hpos : 0 < codimBetween T T' hTT'.le := codimBetween_pos_of_lt hTT'.1
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin.ne
  have hone_lt : (1 : ℕ∞) < codimBetween T T' hTT'.le := by
    cases n with
    | zero =>
        exfalso
        rw [← hn] at hpos
        exact (lt_irrefl _ hpos).elim
    | succ n =>
        cases n with
        | zero =>
            exfalso
            have hone : codimBetween T T' hTT'.le = 1 := by simpa using hn.symm
            exact hne hone
        | succ n =>
            rw [← hn]
            exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
  let _ : Fact (T ≤ T') := ⟨hTT'.le⟩
  obtain ⟨U, hTU, hUcoh⟩ :=
    (coe_lt_coheight_iff hfin).1 <| by simpa using hone_lt
  have hU_ne_top : U ≠ (⊤ : Set.Icc T T') := by
    intro hU
    simp [hU] at hUcoh
  have hU_lt_top : U < (⊤ : Set.Icc T T') := lt_of_le_of_ne le_top hU_ne_top
  exact ((not_covBy_iff hTT'.1).2 ⟨U.1, by simpa using hTU, by simpa using hU_lt_top⟩) hTT'

/-- Helper for Lemma 5.11.6: the relative codimension of an irreducible closed subset inside
itself is zero. -/
private theorem codimBetween_eq_zero {T : IrreducibleCloseds X} :
    codimBetween T T le_rfl = 0 := by
  -- The interval `[T, T]` has a top element which is also bottom, so its coheight vanishes.
  let _ : Fact (T ≤ T) := ⟨le_rfl⟩
  change coheight (⊥ : Set.Icc T T) = 0
  exact IsMax.coheight_eq_zero isMax_top

/- Domain-style sampling for the catenary codimension criterion:
- primary domain: catenarity for the poset `IrreducibleCloseds X`, measured by the relative
  codimension `codimBetween`
- inspected owner declarations:
  `CatenarySpace`,
  `CatenarySpace.codimBetween_additive`,
  `catenarySpace_iff`,
  `Order.coheight_bot_eq_krullDim`
- best owner abstraction: the primitive owner is `CatenarySpace X`; `codimBetween` is the
  source-facing relative codimension bridge built on `Order.coheight`

Layer triage:
- `source-facing`: the finiteness-and-additivity criterion from Lemma 5.11.6
- `core/canonical`: `CatenarySpace X` and `Order.coheight`
- `bridge/view`: `codimBetween` together with the interval specialization of
  `Order.coheight_bot_eq_krullDim`

Primitive data belongs to the owner `CatenarySpace`: finite relative codimension and common
maximal-chain length in each interval. Additivity of `codimBetween` is derived API, so this file
should reuse the owner-derived theorem `CatenarySpace.codimBetween_additive` and state only the
source-facing bridge theorem using the chapter owner directly.
-/

-- Proof sketch: `Definition_5_11_4` already packages the owner-level data for catenarity.
-- Finiteness is the field `CatenarySpace.finite_codimBetween`, and additivity is the derived
-- owner theorem `CatenarySpace.codimBetween_additive`. Conversely, finiteness together with the
-- additivity relation forces every maximal chain in an interval to have the same length, which is
-- exactly the remaining owner data needed for `CatenarySpace`.
/-- Lemma 5.11.6: a topological space is catenary if and only if relative codimension between
comparable irreducible closed subsets is finite and additive along chains. -/
theorem catenarySpace_iff_finite_codimBetween_and_codimBetween_additive :
    CatenarySpace X ↔
      (∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T ≤ T'), codimBetween T T' hTT' < ⊤) ∧
      (∀ ⦃T T' T'' : IrreducibleCloseds X⦄
          (hTT' : T ≤ T') (hT'T'' : T' ≤ T''),
          codimBetween T T'' (hTT'.trans hT'T'') =
            codimBetween T T' hTT' + codimBetween T' T'' hT'T'') := by
  constructor
  · intro hX
    -- The forward implication is exactly the owner API already packaged by `CatenarySpace`.
    refine ⟨?_, ?_⟩
    · intro T T' hTT'
      exact hX.finite_codimBetween hTT'
    intro T T' T'' hTT' hT'T''
    exact @CatenarySpace.codimBetween_additive X _ hX _ _ _ hTT' hT'T''
  · rintro ⟨hfinite, hadditive⟩
    -- For the converse, grade a maximal chain in `[T, T']` by codimension from the bottom.
    refine ⟨fun hTT' ↦ hfinite hTT', ?_⟩
    intro T T' hTT' s hs
    classical
    let _ : Fact (T ≤ T') := ⟨hTT'⟩
    let flag : Flag (Set.Icc T T') := Flag.ofIsMaxChain s hs
    let N : ℕ := ENat.toNat (codimBetween T T' hTT')
    let gradeNat : flag → ℕ := fun x ↦
      ENat.toNat (codimBetween T (x : Set.Icc T T').1 (x : Set.Icc T T').2.1)
    -- Additivity and positivity make the codimension grading strictly increase along the flag.
    have hgrade_strict : StrictMono gradeNat := by
      intro x y hxy
      have hx : codimBetween T (x : Set.Icc T T').1 (x : Set.Icc T T').2.1 < ⊤ :=
        hfinite (x : Set.Icc T T').2.1
      have hy : codimBetween T (y : Set.Icc T T').1 (y : Set.Icc T T').2.1 < ⊤ :=
        hfinite (y : Set.Icc T T').2.1
      have hxy' : (x : Set.Icc T T') < y := hxy
      have hxyfin : codimBetween (x : Set.Icc T T').1 (y : Set.Icc T T').1 hxy'.le < ⊤ :=
        hfinite hxy'.le
      have hxypos :
          0 <
            codimBetween (x : Set.Icc T T').1 (y : Set.Icc T T').1 hxy'.le :=
        codimBetween_pos_of_lt hxy'
      have hxyadd :
          codimBetween T (y : Set.Icc T T').1 (y : Set.Icc T T').2.1 =
            codimBetween T (x : Set.Icc T T').1 (x : Set.Icc T T').2.1 +
              codimBetween (x : Set.Icc T T').1 (y : Set.Icc T T').1 hxy'.le := by
        simpa using hadditive (x : Set.Icc T T').2.1 hxy'.le
      have hxy_nat_ne_zero :
          ENat.toNat (codimBetween (x : Set.Icc T T').1 (y : Set.Icc T T').1 hxy'.le) ≠ 0 := by
        intro hzero
        exact hxypos.ne' <| by rw [← ENat.coe_toNat hxyfin.ne, hzero]; rfl
      dsimp [gradeNat]
      rw [hxyadd, ENat.toNat_add hx.ne hxyfin.ne]
      exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hxy_nat_ne_zero)
    -- Every graded value lies in `{0, ..., N}`, so the flag injects into `Fin (N + 1)`.
    have hgrade_le : ∀ x : flag, gradeNat x ≤ N := by
      intro x
      have hxadd :
          codimBetween T T' hTT' =
            codimBetween T (x : Set.Icc T T').1 (x : Set.Icc T T').2.1 +
              codimBetween (x : Set.Icc T T').1 T' (x : Set.Icc T T').2.2 := by
        simpa using hadditive (x : Set.Icc T T').2.1 (x : Set.Icc T T').2.2
      have hxle :
          codimBetween T (x : Set.Icc T T').1 (x : Set.Icc T T').2.1 ≤
            codimBetween T T' hTT' := by
        rw [hxadd]
        exact le_add_of_nonneg_right bot_le
      exact ENat.toNat_le_toNat hxle (hfinite hTT').ne
    let grade : flag → Fin (N + 1) := fun x ↦
      ⟨gradeNat x, Nat.lt_succ_of_le (hgrade_le x)⟩
    have hgrade_injective : Function.Injective grade := by
      intro x y hxy
      exact hgrade_strict.injective (congrArg Fin.val hxy)
    letI : Finite flag := Finite.of_injective grade hgrade_injective
    letI : Fintype flag := Fintype.ofFinite flag
    have hcard_pos : 0 < Fintype.card flag := Fintype.card_pos_iff.mpr ⟨⊥⟩
    let m : ℕ := Fintype.card flag - 1
    have hm_card : Fintype.card flag = m + 1 := by
      dsimp [m]
      exact (Nat.succ_pred_eq_of_pos hcard_pos).symm
    have huniv : (Finset.univ : Finset flag).card = m + 1 := by
      simpa using hm_card
    let e₀ : Fin (m + 1) ≃o { x : flag // x ∈ (Finset.univ : Finset flag) } :=
      (Finset.univ : Finset flag).orderIsoOfFin huniv
    let e₁ : { x : flag // x ∈ (Finset.univ : Finset flag) } ≃o flag := by
      refine
        { toFun := fun x ↦ x.1
          invFun := fun x ↦ ⟨x, by simp⟩
          left_inv := ?_
          right_inv := ?_
          map_rel_iff' := ?_ }
      · intro x
        cases x
        rfl
      · intro x
        rfl
      · intro a b
        rfl
    let e : Fin (m + 1) ≃o flag := e₀.trans e₁
    have hbot : e 0 = ⊥ := by
      exact e.map_bot
    have htop : e (Fin.last m) = ⊤ := by
      exact e.map_top
    -- Consecutive points in the enumeration are covers, so the grading jumps by exactly one.
    have hstep :
        ∀ i : Fin m, gradeNat (e (Fin.succ i)) = gradeNat (e (Fin.castSucc i)) + 1 := by
      intro i
      have hcov_fin : (Fin.castSucc i : Fin (m + 1)) ⋖ Fin.succ i := by
        have hnat : ((i : ℕ) ⋖ i + 1) := by
          simp
        exact (Fin.covBy_iff).2 hnat
      have hcov_flag : e (Fin.castSucc i) ⋖ e (Fin.succ i) :=
        (apply_covBy_apply_iff e).2 hcov_fin
      have hcov :
          ((e (Fin.castSucc i) : flag) : Set.Icc T T').1 ⋖
            ((e (Fin.succ i) : flag) : Set.Icc T T').1 := by
        have hcov' :
            ((e (Fin.castSucc i) : flag) : Set.Icc T T') ⋖
              ((e (Fin.succ i) : flag) : Set.Icc T T') :=
          (Flag.coe_covBy_coe).2 hcov_flag
        let emb : Set.Icc T T' ↪o IrreducibleCloseds X := OrderEmbedding.subtype (Set.Icc T T')
        have hemb : (Set.range emb).OrdConnected := by
          have hrange : Set.range emb = Set.Icc T T' := by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              exact y.2
            · intro hx
              exact ⟨⟨x, hx⟩, rfl⟩
          rw [hrange]
          infer_instance
        exact hcov'.image emb hemb
      have hedge :
          codimBetween
              (((e (Fin.castSucc i) : flag) : Set.Icc T T').1)
              (((e (Fin.succ i) : flag) : Set.Icc T T').1)
              hcov.le = 1 :=
        codimBetween_eq_one_of_covBy hfinite hcov
      have hleft :
          codimBetween T (((e (Fin.castSucc i) : flag) : Set.Icc T T').1)
              (((e (Fin.castSucc i) : flag) : Set.Icc T T').2.1) < ⊤ :=
        hfinite (((e (Fin.castSucc i) : flag) : Set.Icc T T').2.1)
      have hright :
          codimBetween
              (((e (Fin.castSucc i) : flag) : Set.Icc T T').1)
              (((e (Fin.succ i) : flag) : Set.Icc T T').1)
              hcov.le < ⊤ :=
        hfinite hcov.le
      have haddstep :
          codimBetween T (((e (Fin.succ i) : flag) : Set.Icc T T').1)
              (((e (Fin.succ i) : flag) : Set.Icc T T').2.1) =
            codimBetween T (((e (Fin.castSucc i) : flag) : Set.Icc T T').1)
                (((e (Fin.castSucc i) : flag) : Set.Icc T T').2.1) +
              codimBetween
                (((e (Fin.castSucc i) : flag) : Set.Icc T T').1)
                (((e (Fin.succ i) : flag) : Set.Icc T T').1)
                hcov.le := by
        simpa using hadditive (((e (Fin.castSucc i) : flag) : Set.Icc T T').2.1) hcov.le
      dsimp [gradeNat]
      rw [haddstep, ENat.toNat_add hleft.ne hright.ne, hedge]
      simp
    -- Starting from grade `0` at the bottom, the previous step forces the `n`-th point to have
    -- grade exactly `n`.
    have hindex : ∀ n (hn : n ≤ m), gradeNat (e ⟨n, Nat.lt_succ_of_le hn⟩) = n := by
      intro n hn
      induction n with
      | zero =>
          have hzero : gradeNat (e 0) = 0 := by
            have hbot' : ((e 0 : flag) : Set.Icc T T') = ⊥ := by
              exact congrArg (fun z : flag ↦ (z : Set.Icc T T')) hbot
            dsimp [gradeNat]
            rw [hbot']
            exact congrArg ENat.toNat (codimBetween_eq_zero : codimBetween T T le_rfl = 0)
          simpa using hzero
      | succ n ih =>
          have hn' : n ≤ m := Nat.le_of_succ_le hn
          have hstep' := hstep ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
          simpa [ih hn'] using hstep'
    -- Evaluating the grading at the top identifies the chain length with `codimBetween T T'`.
    have htop_grade : gradeNat (e (Fin.last m)) = N := by
      dsimp [gradeNat, N]
      simp [htop]
    have hm_eq_N : m = N := by
      calc
        m = gradeNat (e (Fin.last m)) := by simpa using (hindex m le_rfl).symm
        _ = N := htop_grade
    have hflag_card : Fintype.card flag = N + 1 := by
      simpa [hm_eq_N] using hm_card
    calc
      s.encard = (Fintype.card flag : ℕ∞) := by
        have hflag_encard : (flag : Set (Set.Icc T T')).encard = Fintype.card flag := by
          exact (Set.coe_fintypeCard (flag : Set (Set.Icc T T'))).symm
        simpa [flag] using hflag_encard
      _ = N + 1 := by simpa [Nat.cast_add] using congrArg (fun n : ℕ ↦ (n : ℕ∞)) hflag_card
