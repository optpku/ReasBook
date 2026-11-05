module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsSyncFamily

@[expose] public section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}
variable [K.HasPullbacks] [K.IsStableUnderBaseChange]
variable [HasWeakSheafify K.toCoverage.toGrothendieck (Type (max u v))]

local notation "J" => K.toCoverage.toGrothendieck

section

variable (β : Ordinal.{max u v}) (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

include F

include hcover

omit hcover in
/-- Explicit witness package for the source-faithful fixed-target overlap synchronization step. This
is an abbreviation for the dependent existential used downstream; naming it keeps the main theorem
header small without introducing a custom inductive wrapper. -/
abbrev refined_target_overlap_sync_witnesses
    {U : C} {R : Presieve U} {d : Set.Iio β}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1) : Prop :=
    ∃ Cbase : ∀ p : targeted_secondary_owner_index (T := T) B, Presieve p.1.2.1.1,
    ∃ hCbase : ∀ p, Cbase p ∈ K p.1.2.1.1,
    ∃ baseRight :
      (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry) → R.uncurry,
    ∃ baseGr :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        s.2.1.1 ⟶ (baseRight s).1.1,
    ∃ hbaseComp : (
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2)),
    ∃ e : Set.Iio β,
    ∃ hde : d.1 ≤ e.1,
    ∃ w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1),
    ∃ hw_def : (
      ∀ i, w i = ((F.map (homOfLE hde)).1.app (op i.1.1)) (v' i)),
    ∃ hw_image : (
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := e) (U := i.1.1) (w i) =
          x i),
    ∃ hbase_e : (
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (baseGr s).op) (w (baseRight s))),
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj))

/-- Helper for Lemma 7.17.10: the source-faithful synchronization step should range over actual
fixed-target overlap witnesses. This wrapper keeps the already-proved anonymous base-cover
equalities and isolates the remaining global fixed-target synchronization as one explicit output
hypothesis. -/
lemma presheafColimit_common_stage_of_refined_target_overlap_equalities
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i.1.1) (v' i) =
          x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (hκsmall :
      Cardinal.lift (Cardinal.mk (targeted_secondary_owner_index (T := T) B)) < β.cof) :
    refined_target_overlap_sync_witnesses
      (β := β)
      (F := F)
      (U := U)
      (R := R)
      (d := d)
      x
      v'
      T
      right
      gr
      B := by
  classical
  -- The explicit targeted-owner smallness hypothesis is retained for the downstream API shape.
  let _ := hκsmall
  choose Cbase hCbase hCbasefac using
    fun p : targeted_secondary_owner_index (T := T) B ↦
      K.toCoverage.pullback
        (p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2)
        R
        hR
  have hCbasesmall :
      Cardinal.lift
          (Cardinal.mk
            (Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry)) <
        β.cof := by
    exact
      small_sigma_of_small_family
        (C := C)
        (K := K)
        (β := β)
        (hcover := hcover)
        (ι := targeted_secondary_owner_index (T := T) B)
        (X := fun p : targeted_secondary_owner_index (T := T) B ↦ (Cbase p).uncurry)
        (hι := hκsmall)
        (by
          intro p
          exact hcover p.1.2.1.1 (Cbase p) (hCbase p))
  let κbase : Type (max u v) :=
    Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry
  choose baseObj baseGr baseMap hbaseMem hbaseEq using
    fun s : κbase ↦ hCbasefac s.1 s.2.2
  let baseRight : κbase → R.uncurry := fun s ↦ ⟨⟨baseObj s, baseMap s⟩, hbaseMem s⟩
  have hbaseComp :
      ∀ s : κbase,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        baseGr s ≫ (baseRight s).1.2 =
          ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
    intro s
    change
      baseGr s ≫ baseMap s =
        ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ (s.1.1.1).2.1.2) ≫ (s.1.1.1).1.1.2)
    simpa [Category.assoc] using hbaseEq s
  have hκbase : Cardinal.lift (Cardinal.mk κbase) < β.cof := by
    simpa [κbase] using hCbasesmall
  have hbase_stage_witness :
      ∀ s : κbase,
        ∃ e : Set.Iio β, ∃ f : d ⟶ e,
          ((F.map f).1.app (op s.2.1.1))
              (((F.obj d).1.map
                    (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr (s.1.1.1)).op)
                  (v' (right s.1.1.1))) =
            ((F.map f).1.app (op s.2.1.1))
              (((F.obj d).1.map (baseGr s).op) (v' (baseRight s))) := by
    intro s
    let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
    have hpath :
        (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q) ≫ (right q).1.2 =
          baseGr s ≫ (baseRight s).1.2 := by
      calc
        (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q) ≫ (right q).1.2 =
            (s.2.1.2 ≫ s.1.1.2.1.2) ≫ (gr q ≫ (right q).1.2) := by
              simp only [Category.assoc]
        _ = (s.2.1.2 ≫ s.1.1.2.1.2) ≫ (q.2.1.2 ≫ q.1.1.2) := by
              exact congrArg
                (fun t ↦ (s.2.1.2 ≫ s.1.1.2.1.2) ≫ t)
                (hcomm q).symm
        _ = ((s.2.1.2 ≫ s.1.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
              simp only [Category.assoc]
        _ = baseGr s ≫ (baseRight s).1.2 := by
              exact (hbaseComp s).symm
    change
      ∃ e : Set.Iio β, ∃ f : d ⟶ e,
        ((F.map f).1.app (op s.2.1.1))
            (((F.obj d).1.map
                  (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op)
                (v' (right q))) =
          ((F.map f).1.app (op s.2.1.1))
            (((F.obj d).1.map (baseGr s).op) (v' (baseRight s)))
    exact
      presheafColimit_overlap_eq_at_later_stage
        (β := β)
        (F := F)
        (hcover := hcover)
        (x := x)
        (hx := hx)
        (v' := v')
        (hv_image := hv_image)
        (i := right q)
        (j := baseRight s)
        (Z := s.2.1.1)
        (gi := s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q)
        (gj := baseGr s)
        hpath
  obtain ⟨e, hde, w, hw_def, hw_image, hbase_e⟩ :=
    presheafColimit_common_stage_of_targeted_secondary_branch_equalities
      (K := K)
      (β := β)
      (F := F)
      (hcover := hcover)
      (U := U)
      (R := R)
      (ι := κbase)
      (left := fun s : κbase ↦ right s.1.1.1)
      (right := baseRight)
      (Z := fun s : κbase ↦ s.2.1.1)
      (gl := fun s : κbase ↦ s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr s.1.1.1)
      (gr := baseGr)
      (c := d)
      (x := x)
      (v := v')
      (hv_image := hv_image)
      (hιsmall := hκbase)
      (hstage_witness := hbase_stage_witness)
  let ι : Type (max u v) := Σ s : κbase, (T s.1.2).uncurry
  let targetQ : ι → Σ i : R.uncurry, (T i).uncurry := fun u ↦ ⟨u.1.1.2, u.2⟩
  let overlap := fun u : ι ↦
    siteLocalTargetOverlapData.ofPullbacks
      (K := K)
      (hR := hR)
      (T := T)
      (hT := hT)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (baseRight := baseRight u.1)
      (baseGr := baseGr u.1)
      (j := u.1.1.2)
      (qj := u.2)
  let Z : ι → C := fun u ↦ (overlap u).Z
  let gl : ∀ u : ι, Z u ⟶ (baseRight u.1).1.1 := fun u ↦ (overlap u).gl
  let gt : ∀ u : ι, Z u ⟶ (right (targetQ u)).1.1 := fun u ↦ (overlap u).gt
  have hιsmall : Cardinal.lift (Cardinal.mk ι) < β.cof := by
    have hfiber :
        ∀ s : κbase, Cardinal.lift (Cardinal.mk ((T s.1.2).uncurry)) < β.cof := by
      intro s
      simpa using hcover s.1.2.1.1 (T s.1.2) (hT s.1.2)
    have htotal :
        Cardinal.lift (Cardinal.mk (Σ s : κbase, (T s.1.2).uncurry)) < β.cof :=
      small_sigma_of_small_family
        (C := C)
        (K := K)
        (β := β)
        (hcover := hcover)
        (ι := κbase)
        (X := fun s : κbase ↦ (T s.1.2).uncurry)
        (hι := hκbase)
        hfiber
    change Cardinal.lift (Cardinal.mk (Σ s : κbase, (T s.1.2).uncurry)) < β.cof
    exact htotal
  have hover :
      ∀ u : ι, (gl u) ≫ (baseRight u.1).1.2 = (gt u) ≫ (right (targetQ u)).1.2 := by
    intro u
    exact (overlap u).hover
  have hstage_witness :
      ∀ u : ι,
        ∃ e' : Set.Iio β, ∃ f : e ⟶ e',
          ((F.map f).1.app (op (Z u)))
              (((F.obj e).1.map (gl u).op) (w (baseRight u.1))) =
            ((F.map f).1.app (op (Z u)))
              (((F.obj e).1.map (gt u).op) (w (right (targetQ u)))) := by
    exact
      presheafColimit_overlap_family_stage_witness
        (β := β)
        (F := F)
        (hcover := hcover)
        (left := fun u : ι ↦ baseRight u.1)
        (right := fun u : ι ↦ right (targetQ u))
        (Z := Z)
        (gl := gl)
        (gt := gt)
        (hover := hover)
        (x := x)
        (hx := hx)
        (w := w)
        (hw_image := hw_image)
  obtain ⟨e', hee', w', hw'_def, hw'_image, hcanon⟩ :=
    presheafColimit_common_stage_of_targeted_secondary_branch_equalities
      (K := K)
      (β := β)
      (F := F)
      (hcover := hcover)
      (U := U)
      (R := R)
      (ι := ι)
      (left := fun u : ι ↦ baseRight u.1)
      (right := fun u : ι ↦ right (targetQ u))
      (Z := Z)
      (gl := gl)
      (gr := gt)
      (c := e)
      (x := x)
      (v := w)
      (hv_image := hw_image)
      (hιsmall := hιsmall)
      (hstage_witness := hstage_witness)
  have hbase_e' :
      ∀ s : Σ p : targeted_secondary_owner_index (T := T) B, (Cbase p).uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
        ((F.obj e').1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w' (right q)) =
          ((F.obj e').1.map (baseGr s).op) (w' (baseRight s)) := by
    intro s
    let q : Σ i : R.uncurry, (T i).uncurry := s.1.1.1
    let leftMap : s.2.1.1 ⟶ (right q).1.1 := s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q
    let rightMap : s.2.1.1 ⟶ (baseRight s).1.1 := baseGr s
    change
      ((F.obj e').1.map leftMap.op) (w' (right q)) =
        ((F.obj e').1.map rightMap.op) (w' (baseRight s))
    have hbase_s :
        ((F.obj e).1.map leftMap.op) (w (right q)) =
          ((F.obj e).1.map rightMap.op) (w (baseRight s)) := by
      change
        ((F.obj e).1.map (s.2.1.2 ≫ s.1.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (baseGr s).op) (w (baseRight s))
      exact hbase_e s
    have hleft_def :
        ((F.obj e').1.map leftMap.op) (w' (right q)) =
          ((F.obj e').1.map leftMap.op)
            (((F.map (homOfLE hee')).1.app (op (right q).1.1)) (w (right q))) := by
      exact congrArg (fun t ↦ ((F.obj e').1.map leftMap.op) t) (hw'_def (right q))
    have hright_def :
        ((F.obj e').1.map rightMap.op) (w' (baseRight s)) =
          ((F.obj e').1.map rightMap.op)
            (((F.map (homOfLE hee')).1.app (op (baseRight s).1.1)) (w (baseRight s))) := by
      exact congrArg (fun t ↦ ((F.obj e').1.map rightMap.op) t) (hw'_def (baseRight s))
    have htransport :
        ((F.obj e').1.map leftMap.op)
            (((F.map (homOfLE hee')).1.app (op (right q).1.1)) (w (right q))) =
          ((F.obj e').1.map rightMap.op)
            (((F.map (homOfLE hee')).1.app (op (baseRight s).1.1)) (w (baseRight s))) :=
      stage_family_two_restriction_eq_at_later_stage
        (β := β)
        (F := F)
        (hde := hee')
        (X := s.2.1.1)
        (A := (right q).1.1)
        (B := (baseRight s).1.1)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (xA := w (right q))
        (xB := w (baseRight s))
        (h := hbase_s)
    exact hleft_def.trans (htransport.trans hright_def.symm)
  have htarget_e' :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e').1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
            ((F.obj e').1.map (z.2.2.2.1 ≫ gr qj).op) (w' (right qj)) := by
    intro p z
    let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
    let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
    have hpullback :
        ∃ D : Presieve z.1, D ∈ K z.1 ∧ D.FactorsThruAlong (Cbase p) z.2.1 :=
      by
        exact K.toCoverage.pullback z.2.1 (Cbase p) (hCbase p)
    obtain ⟨D, hD, hDfac⟩ := hpullback
    refine
      (stage_family_target_overlap_eq_of_cover_branch_equalities
        (β := β)
        (F := F)
        (K := K)
        (hcover := hcover)
        (T := T)
        (right := right)
        (gr := gr)
        (w := w')
        (B := B)
        (p := p)
        (z := z)
        (D := D)
        (hD := hD)
        ?_)
    intro n
    have hDfac_n :
        ∃ (A₁ : C) (i₁ : n.1.1 ⟶ A₁) (e₁ : A₁ ⟶ p.1.2.1.1),
          Cbase p e₁ ∧ i₁ ≫ e₁ = n.1.2 ≫ z.2.1 :=
      by
        exact hDfac n.2
    obtain ⟨A₁, i₁, e₁, he₁, hi₁⟩ := hDfac_n
    let s : (Cbase p).uncurry := ⟨⟨A₁, e₁⟩, he₁⟩
    have hbase_to_target :
        ((i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2) =
          ((n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2) ≫ p.2.1.2) := by
      have hcomp_reassoc :
          ((i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2) =
            i₁ ≫ ((s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
        have hcomp_raw :
            baseGr ⟨p, s⟩ ≫ (baseRight ⟨p, s⟩).1.2 =
              ((s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
          exact hbaseComp ⟨p, s⟩
        calc
          ((i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2) =
              i₁ ≫ (baseGr ⟨p, s⟩ ≫ (baseRight ⟨p, s⟩).1.2) := by
                exact Category.assoc _ _ _
          _ = i₁ ≫ ((s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) := by
                exact congrArg (fun f ↦ i₁ ≫ f) hcomp_raw
      have hi₁_reassoc :
          i₁ ≫ s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2 =
            n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2 := by
        simpa [Category.assoc] using
          congrArg (fun f ↦ f ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2) hi₁
      have hz_reassoc :
          n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2 =
            n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2 ≫ p.2.1.2 := by
        have hz :
            z.2.1 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2 =
              z.2.2.2.1 ≫ z.2.2.1.1.2 ≫ p.2.1.2 := by
          change
            z.2.1 ≫ p.1.2.1.2 ≫ p.1.1.2.1.2 ≫ p.1.1.1.1.2 =
              z.2.2.2.1 ≫ z.2.2.1.1.2 ≫ p.2.1.2
          exact z.2.2.2.2
        simpa [Category.assoc] using congrArg (fun f ↦ n.1.2 ≫ f) hz
      calc
        ((i₁ ≫ baseGr ⟨p, s⟩) ≫ (baseRight ⟨p, s⟩).1.2) =
            i₁ ≫ ((s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2) ≫ q.1.1.2) :=
          hcomp_reassoc
        _ = i₁ ≫ s.1.2 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2 := by
              simp only [Category.assoc]
        _ = n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ q.2.1.2 ≫ q.1.1.2 :=
          hi₁_reassoc
        _ = n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2 ≫ p.2.1.2 :=
          hz_reassoc
        _ = ((n.1.2 ≫ z.2.2.2.1 ≫ z.2.2.1.1.2) ≫ p.2.1.2) := by
              simpa only [Category.assoc]
    let sκ : κbase := ⟨p, s⟩
    let u : ι := ⟨sκ, z.2.2.1⟩
    have hlift_comm :
        i₁ ≫ baseGr ⟨p, s⟩ ≫ (baseRight ⟨p, s⟩).1.2 =
          (n.1.2 ≫ z.2.2.2.1) ≫ z.2.2.1.1.2 ≫ p.2.1.2 := by
      simpa [Category.assoc] using hbase_to_target
    let l : n.1.1 ⟶ Z u :=
      (overlap u).lift i₁ (n.1.2 ≫ z.2.2.2.1) hlift_comm
    have hcanon_branch :
        ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) =
          ((F.obj e').1.map (n.1.2 ≫ z.2.2.2.1 ≫ gr qj).op) (w' (right qj)) := by
      have hpre :
          ((F.obj e').1.map (l ≫ gl u).op) (w' (baseRight u.1)) =
            ((F.obj e').1.map (l ≫ gt u).op) (w' (right (targetQ u))) :=
        stage_family_precompose_restriction_eq
          (β := β)
          (F := F)
          (k := l)
          (hcanon u)
      have hgl_comp : l ≫ gl u = i₁ ≫ baseGr ⟨p, s⟩ := by
        exact (overlap u).lift_gl i₁ (n.1.2 ≫ z.2.2.2.1) hlift_comm
      have hgt_comp : l ≫ gt u = n.1.2 ≫ z.2.2.2.1 ≫ gr qj := by
        dsimp only [qj]
        simpa only [Category.assoc] using
          (overlap u).lift_gt i₁ (n.1.2 ≫ z.2.2.2.1) hlift_comm
      have hleft :
          ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) =
            ((F.obj e').1.map (l ≫ gl u).op) (w' (baseRight u.1)) := by
        exact
          congrArg
            (fun f ↦ ((F.obj e').1.map f.op) (w' (baseRight ⟨p, s⟩)))
            hgl_comp.symm
      have hright :
          ((F.obj e').1.map (l ≫ gt u).op) (w' (right (targetQ u))) =
            ((F.obj e').1.map (n.1.2 ≫ z.2.2.2.1 ≫ gr qj).op) (w' (right qj)) := by
        exact
          congrArg
            (fun f ↦ ((F.obj e').1.map f.op) (w' (right qj)))
            hgt_comp
      exact hleft.trans (hpre.trans hright)
    have hbase_branch :
        ((F.obj e').1.map (n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
          ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) := by
      have hbase_core :
          ((F.obj e').1.map (e₁ ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
            ((F.obj e').1.map (baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) := by
        change
          ((F.obj e').1.map (s.1.2 ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
            ((F.obj e').1.map (baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩))
        exact hbase_e' ⟨p, s⟩
      have hs :
          ((F.obj e').1.map (i₁ ≫ (e₁ ≫ p.1.2.1.2 ≫ gr q)).op) (w' (right q)) =
            ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) :=
        stage_family_precompose_restriction_eq
          (β := β)
          (F := F)
          (k := i₁)
          hbase_core
      have hs_assoc :
          ((F.obj e').1.map (i₁ ≫ e₁ ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
            ((F.obj e').1.map (i₁ ≫ baseGr ⟨p, s⟩).op) (w' (baseRight ⟨p, s⟩)) := by
        simpa [Category.assoc] using hs
      have hpath :
          n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ gr q =
            i₁ ≫ e₁ ≫ p.1.2.1.2 ≫ gr q := by
        simpa [Category.assoc] using
          congrArg (fun f ↦ f ≫ p.1.2.1.2 ≫ gr q) hi₁.symm
      have hleft :
          ((F.obj e').1.map (n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) =
            ((F.obj e').1.map (i₁ ≫ e₁ ≫ p.1.2.1.2 ≫ gr q).op) (w' (right q)) := by
        exact congrArg (fun f ↦ ((F.obj e').1.map f.op) (w' (right q))) hpath
      exact hleft.trans hs_assoc
    exact hbase_branch.trans hcanon_branch
  have hw'_from_d :
      ∀ i : R.uncurry,
        w' i = ((F.map (homOfLE (le_trans hde hee'))).1.app (op i.1.1)) (v' i) := by
    intro i
    have hcomp : homOfLE (le_trans hde hee') = homOfLE hde ≫ homOfLE hee' := by
      exact Subsingleton.elim _ _
    let fde : d ⟶ e := homOfLE hde
    let fee : e ⟶ e' := homOfLE hee'
    calc
      w' i = ((F.map (homOfLE hee')).1.app (op i.1.1)) (w i) := hw'_def i
      _ = ((F.map (homOfLE hee')).1.app (op i.1.1))
            (((F.map (homOfLE hde)).1.app (op i.1.1)) (v' i)) := by
              rw [hw_def i]
      _ = ((F.map (fde ≫ fee)).1.app (op i.1.1)) (v' i) := by
              symm
              change
                ((F.map (fde ≫ fee)).1.app (op i.1.1)) (v' i) =
                  ((F.map fee).1.app (op i.1.1))
                    (((F.map fde).1.app (op i.1.1)) (v' i))
              simp [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
                NatTrans.comp_app, Function.comp]
      _ = ((F.map (homOfLE (le_trans hde hee'))).1.app (op i.1.1)) (v' i) := by
              exact
                congrArg
                  (fun f : d ⟶ e' ↦ ((F.map f).1.app (op i.1.1)) (v' i))
                  (Subsingleton.elim _ _)
  exact
    ⟨Cbase, hCbase, baseRight, baseGr, hbaseComp, e', le_trans hde hee', w',
      hw'_from_d, hw'_image, hbase_e', htarget_e'⟩


end

end CategoryTheory
