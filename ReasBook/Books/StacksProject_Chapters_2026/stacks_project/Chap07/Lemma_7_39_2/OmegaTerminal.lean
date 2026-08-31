module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionLimit

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

/-- Helper for Lemma 7.39.2: the omega comparison map is independent of the particular proof of
the comparison in the direct-union preorder. -/
theorem omegaRefinementSystemMap_proof_irrel
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (X Y : (omegaRefinementIndex (J := J) A)ᵒᵖ)
    (h h' : omegaRefinementIndexLE (J := J) A step (Opposite.unop Y) (Opposite.unop X)) :
    omegaRefinementSystemMap (J := J) A step X Y h =
      omegaRefinementSystemMap (J := J) A step X Y h' := by
  have hh : h = h' := Subsingleton.elim _ _
  subst h'
  rfl

/-- Helper for Lemma 7.39.2: the raw omega direct-union comparison map for an identity
comparison is the identity morphism in `C`. -/
theorem omegaRefinementSystemMap_id
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1))) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    ∀ X : (omegaRefinementIndex (J := J) A)ᵒᵖ,
      omegaRefinementSystemMap (J := J) A step X X (leOfHom (𝟙 (Opposite.unop X))) =
        𝟙 ((A (Opposite.unop X).1.down).T.obj (Opposite.op (Opposite.unop X).2)) := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  intro X
  simp only [omegaRefinementSystemMap]
  split
  · rename_i hstage
    exact refinement_stage_hom_self_comparison_map_id (J := J)
      (A := A (Opposite.unop X).1.down)
      (H := omegaStageHomLE (J := J) A step hstage)
      (omegaStageHomLE_self_eq (J := J) A step hstage) (Opposite.unop X).2 _
  · rename_i hfalse
    exact False.elim (hfalse le_rfl)

/-- Helper for Lemma 7.39.2: on two objects coming from the same finite stage, the omega
direct-union comparison map is the original inverse-system transition map of that stage. -/
theorem omegaRefinementSystemMap_same_stage
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) {i j : (A n).I} (hij : j ≤ i) :
    omegaRefinementSystemMap (J := J) A step
        (Opposite.op (⟨ULift.up n, i⟩ : omegaRefinementIndex (J := J) A))
        (Opposite.op (⟨ULift.up n, j⟩ : omegaRefinementIndex (J := J) A))
        (by simpa [omegaRefinementIndexLE] using hij) =
      (A n).T.map (homOfLE hij).op := by
  simp only [omegaRefinementSystemMap]
  split
  · rename_i hstage
    exact refinement_stage_hom_self_comparison_map (J := J)
      (A := A n)
      (H := omegaStageHomLE (J := J) A step hstage)
      (omegaStageHomLE_self_eq (J := J) A step hstage) i j hij _
  · rename_i hfalse
    exact False.elim (hfalse le_rfl)

/-- Helper for Lemma 7.39.2: an omega comparison into a successor stage factors through the
previous finite stage and the successor morphism. -/
theorem omegaRefinementSystemMap_succ
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) (i : (A (m + 1)).I) (j : (A n).I)
    (hji : (omegaStageHomLE (J := J) A step (Nat.le_succ_of_le hnm)).k j ≤ i)
    (hstep :
      (step m).k ((omegaStageHomLE (J := J) A step hnm).k j) ≤ i) :
    omegaRefinementSystemMap (J := J) A step
        (Opposite.op (⟨ULift.up (m + 1), i⟩ : omegaRefinementIndex (J := J) A))
        (Opposite.op (⟨ULift.up n, j⟩ : omegaRefinementIndex (J := J) A))
        (by simpa [omegaRefinementIndexLE, Nat.le_succ_of_le hnm] using hji) =
      ((A (m + 1)).T.map (homOfLE hstep).op ≫
          (step m).hT.inv.app
            (Opposite.op ((omegaStageHomLE (J := J) A step hnm).k j))) ≫
        omegaRefinementSystemMap (J := J) A step
          (Opposite.op
            (⟨ULift.up m, (omegaStageHomLE (J := J) A step hnm).k j⟩ :
              omegaRefinementIndex (J := J) A))
          (Opposite.op (⟨ULift.up n, j⟩ : omegaRefinementIndex (J := J) A))
          (by simpa [omegaRefinementIndexLE, hnm]) := by
  simp only [omegaRefinementSystemMap]
  split
  · rename_i hstage_direct
    have hstage_direct_eq : hstage_direct = Nat.le_succ_of_le hnm := Subsingleton.elim _ _
    subst hstage_direct
    have hcomp := refinement_stage_hom_comparison_map_comp (J := J)
      (hAB := omegaStageHomLE (J := J) A step hnm)
      (hBD := step m)
      (hAD := omegaStageHomLE (J := J) A step (Nat.le_succ_of_le hnm))
      (omegaStageHomLE_succ_eq_comp (J := J) A step hnm)
      (i := j) (j := (omegaStageHomLE (J := J) A step hnm).k j) (k := i)
      (hij := le_rfl) (hjk := hstep) (hik := hji)
    simpa [Category.assoc] using hcomp
  · rename_i hfalse
    exact False.elim (hfalse (Nat.le_succ_of_le hnm))

/-- Helper for Lemma 7.39.2: the omega comparison from the image of an index in the successor
stage back to that index is exactly the successor refinement map. -/
theorem omegaRefinementSystemMap_succ_self
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) (i : (A n).I) :
    omegaRefinementSystemMap (J := J) A step
        (Opposite.op (⟨ULift.up (n + 1), (step n).k i⟩ : omegaRefinementIndex (J := J) A))
        (Opposite.op (⟨ULift.up n, i⟩ : omegaRefinementIndex (J := J) A))
        (by
          dsimp [omegaRefinementIndexLE]
          rw [dif_pos (Nat.le_succ n)]
          rw [omegaStageHomLE_succ_self_eq (J := J) A step n]
          ) =
      (step n).hT.inv.app (Opposite.op i) := by
  simp only [omegaRefinementSystemMap]
  split
  · rename_i hstage
    exact refinement_stage_hom_comparison_map_self_of_eq (J := J)
      (H := omegaStageHomLE (J := J) A step hstage) (K := step n)
      (omegaStageHomLE_succ_self_eq_of_le (J := J) A step hstage) i
  · rename_i hfalse
    exact False.elim (hfalse (Nat.le_succ n))

/-- Helper for Lemma 7.39.2: omega direct-union comparison maps compose functorially. -/
theorem omegaRefinementSystemMap_comp
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (X Y Z : (omegaRefinementIndex (J := J) A)ᵒᵖ)
    (hYX : omegaRefinementIndexLE (J := J) A step (Opposite.unop Y) (Opposite.unop X))
    (hZY : omegaRefinementIndexLE (J := J) A step (Opposite.unop Z) (Opposite.unop Y))
    (hZX : omegaRefinementIndexLE (J := J) A step (Opposite.unop Z) (Opposite.unop X)) :
    omegaRefinementSystemMap (J := J) A step X Z hZX =
      omegaRefinementSystemMap (J := J) A step X Y hYX ≫
        omegaRefinementSystemMap (J := J) A step Y Z hZY := by
  let hYXn := omegaRefinementIndexLE_stageLe (J := J) A step hYX
  let hZYn := omegaRefinementIndexLE_stageLe (J := J) A step hZY
  let hYXi := omegaRefinementIndexLE_rel (J := J) A step hYX
  let hZYi := omegaRefinementIndexLE_rel (J := J) A step hZY
  have hZXi :
      (omegaStageHomLE (J := J) A step (le_trans hZYn hYXn)).k
          (Opposite.unop Z).2 ≤ (Opposite.unop X).2 := by
    rw [omegaStageHomLE_k_trans_apply (J := J) A step hZYn hYXn (Opposite.unop Z).2]
    exact le_trans
      ((omegaStageHomLE (J := J) A step hYXn).k.map_rel_iff.mpr hZYi) hYXi
  have hZXcanon :
      omegaRefinementIndexLE (J := J) A step (Opposite.unop Z) (Opposite.unop X) := by
    simpa [omegaRefinementIndexLE, le_trans hZYn hYXn] using hZXi
  rw [omegaRefinementSystemMap_proof_irrel (J := J) A step X Z hZX hZXcanon]
  simp only [omegaRefinementSystemMap]
  split
  · rename_i hstageZX
    have hstageZX_eq : hstageZX = le_trans hZYn hYXn := Subsingleton.elim _ _
    subst hstageZX
    have hcomp := refinement_stage_hom_comparison_map_comp (J := J)
      (hAB := omegaStageHomLE (J := J) A step hZYn)
      (hBD := omegaStageHomLE (J := J) A step hYXn)
      (hAD := omegaStageHomLE (J := J) A step (le_trans hZYn hYXn))
      (omegaStageHomLE_eq_comp (J := J) A step hZYn hYXn)
      (i := (Opposite.unop Z).2) (j := (Opposite.unop Y).2)
      (k := (Opposite.unop X).2)
      (hij := hZYi) (hjk := hYXi) (hik := hZXi)
    simpa [Category.assoc] using hcomp
  · rename_i hfalse
    exact False.elim (hfalse (le_trans hZYn hYXn))

/-- Helper for Lemma 7.39.2: the inverse system over the omega direct-union index associated to
an omega tower of packaged refinement stages. -/
noncomputable def omegaRefinementSystem
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1))) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    (omegaRefinementIndex (J := J) A)ᵒᵖ ⥤ C := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  exact {
    obj := fun X =>
      (A (Opposite.unop X).1.down).T.obj (Opposite.op (Opposite.unop X).2)
    map := fun {X Y} f =>
      omegaRefinementSystemMap (J := J) A step X Y (leOfHom f.unop)
    map_id := by
      intro X
      simpa using omegaRefinementSystemMap_id (J := J) A step X
    map_comp := by
      intro X Y Z f g
      exact omegaRefinementSystemMap_comp (J := J) A step X Y Z
        (leOfHom f.unop) (leOfHom g.unop) (leOfHom (f ≫ g).unop)
  }

/-- Helper for Lemma 7.39.2: restricting the omega direct-union system to a finite stage recovers
the inverse system of that stage. -/
noncomputable def omegaRefinementSystemInclusionIso
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    (A n).T ≅ ((omegaRefinementIndexInclusion (J := J) A step n).toOrderHom.toFunctor).op ⋙
      omegaRefinementSystem (J := J) A step := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro X Y f
  have hmap :=
    omegaRefinementSystemMap_same_stage (J := J) A step n
      (i := (Opposite.unop X)) (j := (Opposite.unop Y)) (leOfHom f.unop)
  simpa [omegaRefinementSystem, omegaRefinementIndexInclusion,
    homOfLE_leOfHom f.unop] using hmap.symm

/-- Helper for Lemma 7.39.2: the original refinement embedding of a finite stage, followed by
the canonical inclusion of that stage into the omega direct-union index. -/
noncomputable def omegaRefinementSystemOriginalEmbedding
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    ι ↪o omegaRefinementIndex (J := J) A := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  exact compose_refinement_embedding (A n).j
    (omegaRefinementIndexInclusion (J := J) A step n)

/-- Helper for Lemma 7.39.2: restricting the omega direct-union system along the composed
original embedding recovers the original inverse system. This packages the `j/e` part needed when
the omega system is later turned into a `refinement_stage`. -/
noncomputable def omegaRefinementSystemOriginalIso
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    S' ≅
      (((omegaRefinementSystemOriginalEmbedding (J := J) A step n).toOrderHom.toFunctor).op ⋙
        omegaRefinementSystem (J := J) A step) := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  exact compose_refinement_iso (A n).j
    (omegaRefinementIndexInclusion (J := J) A step n)
    (A n).e (omegaRefinementSystemInclusionIso (J := J) A step n)

/-- Helper for Lemma 7.39.2: the map on inverse-system fibers from a finite stage into the omega
direct union factors through the next finite stage. -/
theorem omegaRefinementSystemInclusion_refinementFiber_succ
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    refinementFiber (omegaRefinementIndexInclusion (J := J) A step n)
        (omegaRefinementSystem (J := J) A step)
        (omegaRefinementSystemInclusionIso (J := J) A step n) =
      refinementFiber (step n).k (A (n + 1)).T (step n).hT ≫
        refinementFiber (omegaRefinementIndexInclusion (J := J) A step (n + 1))
          (omegaRefinementSystem (J := J) A step)
          (omegaRefinementSystemInclusionIso (J := J) A step (n + 1)) := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  ext W x
  rcases fiberMk_jointly_surjective x with ⟨U, f, rfl⟩
  simp [refinementFiber_app_fiberMk, omegaRefinementSystemInclusionIso]
  let i : (A n).I := Opposite.unop U
  let Xn : omegaRefinementIndex (J := J) A := ⟨ULift.up n, i⟩
  let Xs : omegaRefinementIndex (J := J) A := ⟨ULift.up (n + 1), (step n).k i⟩
  have hle : omegaRefinementIndexLE (J := J) A step Xn Xs := by
    dsimp [Xn, Xs, omegaRefinementIndexLE]
    rw [dif_pos (Nat.le_succ n)]
    rw [omegaStageHomLE_succ_k_apply (J := J) A step (le_rfl : n ≤ n) i]
    rw [omegaStageHomLE_self_eq (J := J) A step (le_rfl : n ≤ n)]
    rfl
  have hmap :
      (omegaRefinementSystem (J := J) A step).map ((homOfLE hle).op) =
        (step n).hT.inv.app U := by
    have hcanonical :
        omegaRefinementIndexLE (J := J) A step Xn Xs := by
      simpa [Xn, Xs, i] using hle
    have hself :
        omegaRefinementSystemMap (J := J) A step
            (Opposite.op Xs) (Opposite.op Xn) hcanonical =
          (step n).hT.inv.app U := by
      simp only [omegaRefinementSystemMap, Xn, Xs, i]
      split
      · rename_i hstage
        have hcomp
            (H : refinement_stage_hom (J := J) (A n) (A (n + 1)))
            (hH : H = step n)
            (hrel : H.k i ≤ (step n).k i) :
            (A (n + 1)).T.map (homOfLE hrel).op ≫
                H.hT.inv.app (Opposite.op i) =
              (step n).hT.inv.app (Opposite.op i) := by
          subst H
          simp
        have hH : omegaStageHomLE (J := J) A step hstage = step n := by
          rw [show hstage = Nat.le_succ_of_le (le_rfl : n ≤ n) by
            exact Subsingleton.elim _ _]
          rw [omegaStageHomLE_succ_eq_comp (J := J) A step (le_rfl : n ≤ n)]
          rw [omegaStageHomLE_self_eq (J := J) A step (le_rfl : n ≤ n)]
          exact refinement_stage_hom.refl_comp (J := J) (step n)
        exact hcomp (omegaStageHomLE (J := J) A step hstage) hH _
      · rename_i hfalse
        exact False.elim (hfalse (Nat.le_succ n))
    simpa [omegaRefinementSystem, Xn, Xs, i] using hself
  let fΩ : (omegaRefinementSystem (J := J) A step).obj (Opposite.op Xn) ⟶ W := f
  have hfiber :
      fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step)
          ((omegaRefinementSystem (J := J) A step).map ((homOfLE hle).op) ≫ fΩ) =
        fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step) fΩ :=
    fiberMk_map_comp.{max u v w}
      (p := omegaRefinementSystem (J := J) A step) ((homOfLE hle).op) fΩ
  rw [← hmap]
  calc
    fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step)
        (𝟙 ((A n).T.obj U) ≫ f) =
      fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step) fΩ := by
        simpa only [fΩ, omegaRefinementSystem, Xn, i] using
          congrArg
            (fun q =>
              fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step) q)
            (Category.id_comp fΩ)
    _ = fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step)
        ((omegaRefinementSystem (J := J) A step).map ((homOfLE hle).op) ≫ fΩ) :=
      hfiber.symm
    _ = fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step)
        (𝟙 ((A (n + 1)).T.obj (Opposite.op ((step n).k i))) ≫
          (omegaRefinementSystem (J := J) A step).map ((homOfLE hle).op) ≫ f) := by
        simpa only [fΩ, omegaRefinementSystem, Xs, i, Category.assoc] using
          (congrArg
            (fun q =>
              fiberMk.{max u v w} (p := omegaRefinementSystem (J := J) A step) q)
            (Category.id_comp
              ((omegaRefinementSystem (J := J) A step).map ((homOfLE hle).op) ≫
                fΩ)).symm)

/-- Helper for Lemma 7.39.2: transporting a request from stage `n` to the omega direct union is
the same as first transporting it to stage `n + 1` and then to the omega direct union. -/
theorem omegaRefinementSystem_transport_request_succ
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) (r : finite_cover_lift_request J (A n).T) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    transport_request (J := J) (omegaRefinementIndexInclusion (J := J) A step n)
        (omegaRefinementSystem (J := J) A step)
        (omegaRefinementSystemInclusionIso (J := J) A step n) r =
      transport_request (J := J) (omegaRefinementIndexInclusion (J := J) A step (n + 1))
        (omegaRefinementSystem (J := J) A step)
        (omegaRefinementSystemInclusionIso (J := J) A step (n + 1))
        ((step n).map_request r) := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  -- After unpacking the request, the only field to compare is the transported fiber element.
  cases r
  simp [transport_request, refinement_stage_hom.map_request,
    omegaRefinementSystemInclusion_refinementFiber_succ (J := J) A step n]

/-- Helper for Lemma 7.39.2: every finite-cover request on the omega direct-union system is
transported from a request on one finite stage of the tower. -/
theorem omegaRefinementSystem_request_descends
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1))) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    ∀ r : finite_cover_lift_request J (omegaRefinementSystem (J := J) A step),
      ∃ n, ∃ r0 : finite_cover_lift_request J (A n).T,
        transport_request (J := J) (omegaRefinementIndexInclusion (J := J) A step n)
          (omegaRefinementSystem (J := J) A step)
          (omegaRefinementSystemInclusionIso (J := J) A step n) r0 = r := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  intro r
  rcases fiberMk_jointly_surjective r.f with ⟨X, f, hf⟩
  let n : ℕ := (Opposite.unop X).1.down
  let i : (A n).I := (Opposite.unop X).2
  let f0 : (A n).T.obj (Opposite.op i) ⟶ r.W := by
    simpa [n, i, omegaRefinementSystem] using f
  let r0 : finite_cover_lift_request J (A n).T := {
    W := r.W
    n := r.n
    obj := r.obj
    h𝒰 := r.h𝒰
    f := fiberMk f0
  }
  refine ⟨n, r0, ?_⟩
  cases r
  simp [r0, transport_request, f0, n, i, omegaRefinementSystemInclusionIso,
    refinementFiber_app_fiberMk] at hf ⊢
  have hmap :
      ((omegaRefinementSystem (J := J) A step).map (𝟙 X)) =
        𝟙 ((A (Opposite.unop X).1.down).T.obj (Opposite.op (Opposite.unop X).2)) := by
    simpa [omegaRefinementSystem] using omegaRefinementSystemMap_id (J := J) A step X
  rw [← hmap]
  exact (fiberMk_map_comp.{max u v w}
    (p := omegaRefinementSystem (J := J) A step) (g := 𝟙 X) (f := f)).trans hf

/-- Helper for Lemma 7.39.2: if the successor `n + 1` realizes the transport of a request from
stage `n`, then the omega direct-union system realizes the request transported directly from
stage `n`. -/
theorem omegaRefinementSystem_realizes_transported_request
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (step_realizes :
      ∀ n (r : finite_cover_lift_request J (A n).T),
        request_realized (J := J) ((step n).map_request r)) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    ∀ n (r : finite_cover_lift_request J (A n).T),
      request_realized (J := J)
        (transport_request (J := J) (omegaRefinementIndexInclusion (J := J) A step n)
          (omegaRefinementSystem (J := J) A step)
          (omegaRefinementSystemInclusionIso (J := J) A step n) r) := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  intro n r
  have hsucc :
      request_realized (J := J)
        (transport_request (J := J)
          (omegaRefinementIndexInclusion (J := J) A step (n + 1))
          (omegaRefinementSystem (J := J) A step)
          (omegaRefinementSystemInclusionIso (J := J) A step (n + 1))
          ((step n).map_request r)) :=
    request_realized_transport (J := J)
      (omegaRefinementIndexInclusion (J := J) A step (n + 1))
      (omegaRefinementSystem (J := J) A step)
      (omegaRefinementSystemInclusionIso (J := J) A step (n + 1))
      ((step n).map_request r) (step_realizes n r)
  rwa [← omegaRefinementSystem_transport_request_succ (J := J) A step n r] at hsucc

/-- Helper for Lemma 7.39.2: an omega tower whose successor maps realize every request from the
previous finite stage has an omega direct-union system realizing every one of its own
finite-cover requests. -/
theorem omegaRefinementSystem_realizes_all_requests
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (step_realizes :
      ∀ n (r : finite_cover_lift_request J (A n).T),
        request_realized (J := J) ((step n).map_request r)) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    ∀ r : finite_cover_lift_request J (omegaRefinementSystem (J := J) A step),
      request_realized (J := J) r := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  intro r
  rcases omegaRefinementSystem_request_descends (J := J) A step r with ⟨n, r0, hr0⟩
  have hreal :=
    omegaRefinementSystem_realizes_transported_request (J := J) A step step_realizes n r0
  rwa [hr0] at hreal

/-- Helper for Lemma 7.39.2: package an omega direct-union system as a terminal refinement stage,
once separation of the original two sections and realization of all omega-stage requests have been
proved. This isolates the remaining mathematical obligations from the purely structural
`refinement_stage` fields. -/
noncomputable def omegaTerminalRefinementStage
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (hsep :
      letI : Preorder (omegaRefinementIndex (J := J) A) :=
        omegaRefinementIndexPreorder (J := J) A step
      let TΩ := omegaRefinementSystem (J := J) A step
      let jΩ := omegaRefinementSystemOriginalEmbedding (J := J) A step 0
      let eΩ := omegaRefinementSystemOriginalIso (J := J) A step 0
      ((refinementFiber jΩ TΩ eΩ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΩ TΩ eΩ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (hreal :
      letI : Preorder (omegaRefinementIndex (J := J) A) :=
        omegaRefinementIndexPreorder (J := J) A step
      ∀ r : finite_cover_lift_request J (omegaRefinementSystem (J := J) A step),
        request_realized (J := J) r) :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  exact {
    I := omegaRefinementIndex (J := J) A
    instPreorder := omegaRefinementIndexPreorder (J := J) A step
    instDirected := omegaRefinementIndexDirected (J := J) A step
    T := omegaRefinementSystem (J := J) A step
    j := omegaRefinementSystemOriginalEmbedding (J := J) A step 0
    e := omegaRefinementSystemOriginalIso (J := J) A step 0
    separated := hsep
    solved := Set.univ
    solved_realized := by
      intro r _hr
      exact hreal r
  }

/-- Helper for Lemma 7.39.2: an omega tower whose direct union still separates the two original
sections and whose successor maps realize every previous-stage request yields a packaged terminal
stage realizing all of its own finite-cover requests. -/
theorem exists_omega_terminal_refinement_stage_realizing_all_requests
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (hsep :
      letI : Preorder (omegaRefinementIndex (J := J) A) :=
        omegaRefinementIndexPreorder (J := J) A step
      let TΩ := omegaRefinementSystem (J := J) A step
      let jΩ := omegaRefinementSystemOriginalEmbedding (J := J) A step 0
      let eΩ := omegaRefinementSystemOriginalIso (J := J) A step 0
      ((refinementFiber jΩ TΩ eΩ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΩ TΩ eΩ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (step_realizes :
      ∀ n (r : finite_cover_lift_request J (A n).T),
        request_realized (J := J) ((step n).map_request r)) :
    ∃ L : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J L.T, request_realized (J := J) r := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  let hreal :
      ∀ r : finite_cover_lift_request J (omegaRefinementSystem (J := J) A step),
        request_realized (J := J) r :=
    omegaRefinementSystem_realizes_all_requests (J := J) A step step_realizes
  let L : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    omegaTerminalRefinementStage (J := J) A step hsep hreal
  refine ⟨L, ?_⟩
  intro r
  exact L.solved_realized (Set.mem_univ r)

/-- Helper for Lemma 7.39.2: the omega tower obtained by repeatedly applying a stagewise
advance procedure. -/
noncomputable def omegaTowerFromStagewiseAdvance
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (advance :
      ∀ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
          ∃ h : refinement_stage_hom (J := J) A B,
            ∀ r : finite_cover_lift_request J A.T,
              request_realized (J := J) (h.map_request r)) :
    ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  Nat.rec A₀ (fun _ A => Classical.choose (advance A))

/-- Helper for Lemma 7.39.2: the successor morphisms in the omega tower obtained from a stagewise
advance procedure. -/
noncomputable def omegaStepFromStagewiseAdvance
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (advance :
      ∀ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
          ∃ h : refinement_stage_hom (J := J) A B,
            ∀ r : finite_cover_lift_request J A.T,
              request_realized (J := J) (h.map_request r)) :
    ∀ n, refinement_stage_hom (J := J)
      ((omegaTowerFromStagewiseAdvance (J := J) A₀ advance) n)
      ((omegaTowerFromStagewiseAdvance (J := J) A₀ advance) (n + 1)) :=
  fun n =>
    Classical.choose
      (Classical.choose_spec
        (advance ((omegaTowerFromStagewiseAdvance (J := J) A₀ advance) n)))

/-- Helper for Lemma 7.39.2: given a one-step procedure that realizes every request on the current
stage, build an omega tower and return its terminal packaged stage. The remaining mathematical
content is isolated in `advance`, which is the transfinite/Zorn construction for one fixed stage
in the source proof. -/
theorem exists_terminal_stage_from_stagewise_advance
    [IsDirected ι (· ≤ ·)]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (advance :
      ∀ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
          ∃ h : refinement_stage_hom (J := J) A B,
            ∀ r : finite_cover_lift_request J A.T,
              request_realized (J := J) (h.map_request r))
    (hsep :
      let A := omegaTowerFromStagewiseAdvance (J := J) A₀ advance
      let step := omegaStepFromStagewiseAdvance (J := J) A₀ advance
      letI : Preorder (omegaRefinementIndex (J := J) A) :=
        omegaRefinementIndexPreorder (J := J) A step
      let TΩ := omegaRefinementSystem (J := J) A step
      let jΩ := omegaRefinementSystemOriginalEmbedding (J := J) A step 0
      let eΩ := omegaRefinementSystemOriginalIso (J := J) A step 0
      ((refinementFiber jΩ TΩ eΩ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΩ TΩ eΩ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s') :
    ∃ L : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J L.T, request_realized (J := J) r := by
  let A := omegaTowerFromStagewiseAdvance (J := J) A₀ advance
  let step := omegaStepFromStagewiseAdvance (J := J) A₀ advance
  have step_realizes :
      ∀ n (r : finite_cover_lift_request J (A n).T),
        request_realized (J := J) ((step n).map_request r) := by
    intro n r
    exact (Classical.choose_spec (Classical.choose_spec (advance (A n)))) r
  exact exists_omega_terminal_refinement_stage_realizing_all_requests
    (J := J) A step hsep step_realizes


end

end CategoryTheory
