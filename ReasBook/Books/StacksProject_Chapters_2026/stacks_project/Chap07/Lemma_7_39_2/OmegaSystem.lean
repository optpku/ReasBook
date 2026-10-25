module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.FiniteFrontier

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

/-- Helper for Lemma 7.39.2: compose the successor morphisms in an omega tower from stage `n`
to any later stage `m`. -/
noncomputable def omegaStageHomLE
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n m : ℕ} (h : n ≤ m) :
    refinement_stage_hom (J := J) (A n) (A m) :=
  Nat.leRecOn (C := fun m => refinement_stage_hom (J := J) (A n) (A m)) h
    (fun {k} hk =>
      refinement_stage_hom.comp (J := J) hk (by simpa [Nat.add_comm] using step k))
    (refinement_stage_hom_refl (J := J) (A n))

/-- Helper for Lemma 7.39.2: the zero-length omega composite acts as the identity on indices. -/
@[simp] theorem omegaStageHomLE_refl_k_apply
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n : ℕ} (i : (A n).I) :
    (omegaStageHomLE (J := J) A step (show n ≤ n from le_rfl)).k i = i := by
  rw [omegaStageHomLE, Nat.leRecOn_self]
  rfl

/-- Helper for Lemma 7.39.2: the zero-length omega composite is the identity stage morphism. -/
@[simp] theorem omegaStageHomLE_self_eq
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n : ℕ} (h : n ≤ n) :
    omegaStageHomLE (J := J) A step h = refinement_stage_hom_refl (J := J) (A n) := by
  rw [show h = (le_rfl : n ≤ n) by exact Subsingleton.elim _ _]
  unfold omegaStageHomLE
  rw [Nat.leRecOn_self]

/-- Helper for Lemma 7.39.2: proof-irrelevant form of the zero-length omega composite on
indices. -/
@[simp] theorem omegaStageHomLE_self_k_apply
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n : ℕ} (h : n ≤ n) (i : (A n).I) :
    (omegaStageHomLE (J := J) A step h).k i = i := by
  rw [omegaStageHomLE_self_eq (J := J) A step h]
  rfl

/-- Helper for Lemma 7.39.2: the omega composite to a successor stage is the previous omega
composite followed by the corresponding successor morphism. -/
theorem omegaStageHomLE_succ_eq_comp
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) :
    omegaStageHomLE (J := J) A step (Nat.le_succ_of_le hnm) =
      refinement_stage_hom.comp (J := J)
        (omegaStageHomLE (J := J) A step hnm) (step m) := by
  rw [show Nat.le_succ_of_le hnm = le_trans hnm (Nat.le_succ m) by
    exact Subsingleton.elim _ _]
  unfold omegaStageHomLE
  erw [Nat.leRecOn_succ]

/-- Helper for Lemma 7.39.2: the omega composite from a stage to its successor is the corresponding
successor morphism. -/
@[simp] theorem omegaStageHomLE_succ_self_eq
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) :
    omegaStageHomLE (J := J) A step (Nat.le_succ n) = step n := by
  rw [show (Nat.le_succ n) = Nat.le_succ_of_le (le_rfl : n ≤ n) by
    exact Subsingleton.elim _ _]
  rw [omegaStageHomLE_succ_eq_comp (J := J) A step (le_rfl : n ≤ n)]
  rw [omegaStageHomLE_self_eq (J := J) A step (le_rfl : n ≤ n)]
  exact refinement_stage_hom.refl_comp (J := J) (step n)

/-- Helper for Lemma 7.39.2: proof-irrelevant form of the one-step omega composite. -/
@[simp] theorem omegaStageHomLE_succ_self_eq_of_le
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n : ℕ} (h : n ≤ n + 1) :
    omegaStageHomLE (J := J) A step h = step n := by
  rw [show h = Nat.le_succ n by exact Subsingleton.elim _ _]
  exact omegaStageHomLE_succ_self_eq (J := J) A step n

/-- Helper for Lemma 7.39.2: on indices, the omega composite to a successor stage is obtained by
applying the previous omega composite and then the successor embedding. -/
theorem omegaStageHomLE_succ_k_apply
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) (i : (A n).I) :
    (omegaStageHomLE (J := J) A step (Nat.le_succ_of_le hnm)).k i =
      (step m).k ((omegaStageHomLE (J := J) A step hnm).k i) := by
  have h :=
    congrArg (fun H : refinement_stage_hom (J := J) (A n) (A (m + 1)) => H.k i)
      (omegaStageHomLE_succ_eq_comp (J := J) A step hnm)
  simpa [refinement_stage_hom.comp, compose_refinement_embedding] using h

/-- Helper for Lemma 7.39.2: omega composites of successor morphisms associate as packaged
stage morphisms. -/
theorem omegaStageHomLE_eq_comp
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n m p : ℕ} (hnm : n ≤ m) (hmp : m ≤ p) :
    omegaStageHomLE (J := J) A step (le_trans hnm hmp) =
      refinement_stage_hom.comp (J := J)
        (omegaStageHomLE (J := J) A step hnm)
        (omegaStageHomLE (J := J) A step hmp) := by
  induction hmp using Nat.leRec with
  | refl =>
      rw [show le_trans hnm (le_rfl : m ≤ m) = hnm by exact Subsingleton.elim _ _]
      rw [omegaStageHomLE_self_eq]
      exact (refinement_stage_hom.comp_refl (J := J)
        (omegaStageHomLE (J := J) A step hnm)).symm
  | @le_succ_of_le p hmp ih =>
      rw [show le_trans hnm (Nat.le_succ_of_le hmp) =
          Nat.le_succ_of_le (le_trans hnm hmp) by
        exact Subsingleton.elim _ _]
      rw [omegaStageHomLE_succ_eq_comp (J := J) A step (le_trans hnm hmp)]
      rw [omegaStageHomLE_succ_eq_comp (J := J) A step hmp]
      rw [ih]
      rw [refinement_stage_hom.comp_assoc]

/-- Helper for Lemma 7.39.2: index maps in the omega composite associate on the nose. -/
theorem omegaStageHomLE_k_trans_apply
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {n m p : ℕ} (hnm : n ≤ m) (hmp : m ≤ p) (i : (A n).I) :
    (omegaStageHomLE (J := J) A step (le_trans hnm hmp)).k i =
      (omegaStageHomLE (J := J) A step hmp).k
        ((omegaStageHomLE (J := J) A step hnm).k i) := by
  induction hmp using Nat.leRec with
  | refl =>
      rw [show le_trans hnm (le_rfl : m ≤ m) = hnm by exact Subsingleton.elim _ _]
      change (omegaStageHomLE (J := J) A step hnm).k i =
        (omegaStageHomLE (J := J) A step (show m ≤ m from le_rfl)).k
          ((omegaStageHomLE (J := J) A step hnm).k i)
      conv_rhs => rw [omegaStageHomLE, Nat.leRecOn_self]
      rfl
  | @le_succ_of_le p hmp ih =>
      change (omegaStageHomLE (J := J) A step (le_trans hnm (Nat.le_succ_of_le hmp))).k i =
        (omegaStageHomLE (J := J) A step (Nat.le_succ_of_le hmp)).k
          ((omegaStageHomLE (J := J) A step hnm).k i)
      erw [omegaStageHomLE,
        Nat.leRecOn_succ (C := fun q => refinement_stage_hom (J := J) (A n) (A q))
          (h1 := le_trans hnm hmp)]
      erw [omegaStageHomLE,
        Nat.leRecOn_succ (C := fun q => refinement_stage_hom (J := J) (A m) (A q))
          (h1 := hmp)]
      exact congrArg (fun t => (step p).k t) ih

/-- Helper for Lemma 7.39.2: the index type of the omega direct union. The natural-number
coordinate is universe-lifted so this sigma type remains in the stage-index universe `w`.

This is a type synonym rather than an abbreviation so the omega preorder below, not Mathlib's
generic `Sigma` order/category instances, controls the order-category structure. -/
def omegaRefinementIndex
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s') :=
  Σ n : ULift.{w} ℕ, (A n.down).I

/-- Helper for Lemma 7.39.2: order on the omega direct-union index. A point at stage `n` is
below a point at a later stage `m` when its image under the composed step embedding is below that
later point. -/
def omegaRefinementIndexLE
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (x y : omegaRefinementIndex (J := J) A) : Prop :=
  if h : x.1.down ≤ y.1.down then
    (omegaStageHomLE (J := J) A step h).k x.2 ≤ y.2
  else
    False

/-- Helper for Lemma 7.39.2: extract the stage comparison from an omega-index comparison. -/
def omegaRefinementIndexLE_stageLe
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {x y : omegaRefinementIndex (J := J) A}
    (hxy : omegaRefinementIndexLE (J := J) A step x y) : x.1.down ≤ y.1.down :=
  by
    by_cases h : x.1.down ≤ y.1.down
    · exact h
    · exact False.elim (by simpa [omegaRefinementIndexLE, h] using hxy)

/-- Helper for Lemma 7.39.2: the object comparison attached to an omega-index comparison. -/
theorem omegaRefinementIndexLE_rel
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    {x y : omegaRefinementIndex (J := J) A}
    (hxy : omegaRefinementIndexLE (J := J) A step x y) :
    (omegaStageHomLE (J := J) A step
      (omegaRefinementIndexLE_stageLe (J := J) A step hxy)).k x.2 ≤ y.2 :=
  by
    unfold omegaRefinementIndexLE_stageLe
    by_cases h : x.1.down ≤ y.1.down
    · have hxy' :
          (omegaStageHomLE (J := J) A step h).k x.2 ≤ y.2 := by
        simpa [omegaRefinementIndexLE, h] using hxy
      simpa [h] using hxy'
    · exact False.elim (by simpa [omegaRefinementIndexLE, h] using hxy)

/-- Helper for Lemma 7.39.2: the omega direct-union index is a preorder. -/
@[reducible] def omegaRefinementIndexPreorder
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1))) :
    Preorder (omegaRefinementIndex (J := J) A) where
  le := omegaRefinementIndexLE (J := J) A step
  lt := fun x y =>
    omegaRefinementIndexLE (J := J) A step x y ∧
      ¬ omegaRefinementIndexLE (J := J) A step y x
  le_refl x := by
    simp [omegaRefinementIndexLE, refinement_stage_hom_refl]
  le_trans x y z hxy hyz := by
    let hxy_n := omegaRefinementIndexLE_stageLe (J := J) A step hxy
    let hyz_n := omegaRefinementIndexLE_stageLe (J := J) A step hyz
    let hxy_i := omegaRefinementIndexLE_rel (J := J) A step hxy
    let hyz_i := omegaRefinementIndexLE_rel (J := J) A step hyz
    have hxz_i :
        (omegaStageHomLE (J := J) A step (le_trans hxy_n hyz_n)).k x.2 ≤ z.2 := by
      rw [omegaStageHomLE_k_trans_apply (J := J) A step hxy_n hyz_n x.2]
      exact le_trans ((omegaStageHomLE (J := J) A step hyz_n).k.map_rel_iff.mpr hxy_i) hyz_i
    simpa [omegaRefinementIndexLE, le_trans hxy_n hyz_n] using hxz_i
  lt_iff_le_not_ge := by
    intro a b
    rfl

/-- Helper for Lemma 7.39.2: the omega direct-union index is directed. -/
@[reducible] def omegaRefinementIndexDirected
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1))) :
    IsDirected (omegaRefinementIndex (J := J) A)
      (omegaRefinementIndexLE (J := J) A step) where
  directed x y := by
    let N := max x.1.down y.1.down
    let hxN : x.1.down ≤ N := Nat.le_max_left _ _
    let hyN : y.1.down ≤ N := Nat.le_max_right _ _
    let xN := (omegaStageHomLE (J := J) A step hxN).k x.2
    let yN := (omegaStageHomLE (J := J) A step hyN).k y.2
    letI : Preorder (A N).I := (A N).instPreorder
    letI : IsDirected (A N).I (· ≤ ·) := (A N).instDirected
    rcases IsDirected.directed (r := (· ≤ ·)) xN yN with ⟨z, hxz, hyz⟩
    refine ⟨⟨ULift.up N, z⟩, ?_, ?_⟩
    · simpa [omegaRefinementIndexLE, hxN, xN] using hxz
    · simpa [omegaRefinementIndexLE, hyN, yN] using hyz

/-- Helper for Lemma 7.39.2: the canonical order embedding of a finite stage into the omega
direct-union index. -/
noncomputable def omegaRefinementIndexInclusion
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (n : ℕ) :
    letI : Preorder (omegaRefinementIndex (J := J) A) :=
      omegaRefinementIndexPreorder (J := J) A step
    (A n).I ↪o omegaRefinementIndex (J := J) A := by
  letI : Preorder (omegaRefinementIndex (J := J) A) :=
    omegaRefinementIndexPreorder (J := J) A step
  exact {
    toFun := fun i => ⟨ULift.up n, i⟩
    inj' := by
      intro i j h
      cases h
      rfl
    map_rel_iff' := by
      intro i j
      constructor
      · intro hij
        let hnn := omegaRefinementIndexLE_stageLe (J := J) A step hij
        have hij' := omegaRefinementIndexLE_rel (J := J) A step hij
        have hnn_eq : hnn = (le_rfl : n ≤ n) := Subsingleton.elim _ _
        simpa [hnn, hnn_eq] using hij'
      · intro hij
        change omegaRefinementIndexLE (J := J) A step ⟨ULift.up n, i⟩ ⟨ULift.up n, j⟩
        simpa [omegaRefinementIndexLE] using hij
  }

/-- Helper for Lemma 7.39.2: the morphism in `C` attached to one comparison in the omega
direct-union index. -/
noncomputable def omegaRefinementSystemMap
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (X Y : (omegaRefinementIndex (J := J) A)ᵒᵖ)
    (hYX : omegaRefinementIndexLE (J := J) A step (Opposite.unop Y) (Opposite.unop X)) :
    (A (Opposite.unop X).1.down).T.obj (Opposite.op (Opposite.unop X).2) ⟶
      (A (Opposite.unop Y).1.down).T.obj (Opposite.op (Opposite.unop Y).2) := by
  by_cases hYXn : (Opposite.unop Y).1.down ≤ (Opposite.unop X).1.down
  · have hYXi :
        (omegaStageHomLE (J := J) A step hYXn).k (Opposite.unop Y).2 ≤
          (Opposite.unop X).2 := by
      simpa [omegaRefinementIndexLE, hYXn] using hYX
    exact
      (A (Opposite.unop X).1.down).T.map (homOfLE hYXi).op ≫
        (omegaStageHomLE (J := J) A step hYXn).hT.inv.app
          (Opposite.op (Opposite.unop Y).2)
  · exact False.elim (by simpa [omegaRefinementIndexLE, hYXn] using hYX)

/-- Helper for Lemma 7.39.2: a self-comparison stage morphism equal to the identity gives the
identity map on the corresponding object of the inverse system. This isolates the dependent
normalization needed for the identity maps in the omega direct-union system. -/
theorem refinement_stage_hom_self_comparison_map_id
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (H : refinement_stage_hom (J := J) A A)
    (hH : H = refinement_stage_hom_refl (J := J) A)
    (i : A.I) (hii : H.k i ≤ i) :
    A.T.map (homOfLE hii).op ≫ H.hT.inv.app (Opposite.op i) =
      𝟙 (A.T.obj (Opposite.op i)) := by
  subst H
  simp [refinement_stage_hom_refl, identity_refinement_iso]

/-- Helper for Lemma 7.39.2: a self-comparison stage morphism equal to the identity gives the
ordinary inverse-system transition map between two objects of the same stage. -/
theorem refinement_stage_hom_self_comparison_map
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (H : refinement_stage_hom (J := J) A A)
    (hH : H = refinement_stage_hom_refl (J := J) A)
    (i j : A.I) (hij : j ≤ i) (hHji : H.k j ≤ i) :
    A.T.map (homOfLE hHji).op ≫ H.hT.inv.app (Opposite.op j) =
      A.T.map (homOfLE hij).op := by
  subst H
  simp [refinement_stage_hom_refl, identity_refinement_iso]

/-- Helper for Lemma 7.39.2: if two stage morphisms are equal, the comparison map attached to
one, evaluated at the image under the other, is the second morphism's structure map. -/
theorem refinement_stage_hom_comparison_map_self_of_eq
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (H K : refinement_stage_hom (J := J) A B) (hHK : H = K) (i : A.I)
    {hHii : H.k i ≤ K.k i} :
    B.T.map (homOfLE hHii).op ≫ H.hT.inv.app (Opposite.op i) =
      K.hT.inv.app (Opposite.op i) := by
  subst H
  simp

/-- Helper for Lemma 7.39.2: comparison maps attached to a composite stage morphism compose as
expected. This is the local functoriality calculation behind the omega direct-union system. -/
theorem refinement_stage_hom_comparison_map_comp
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B D : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hAB : refinement_stage_hom (J := J) A B)
    (hBD : refinement_stage_hom (J := J) B D)
    (hAD : refinement_stage_hom (J := J) A D)
    (hAD_eq : hAD = refinement_stage_hom.comp (J := J) hAB hBD)
    (i : A.I) (j : B.I) (k : D.I)
    (hij : hAB.k i ≤ j) (hjk : hBD.k j ≤ k) (hik : hAD.k i ≤ k) :
    D.T.map (homOfLE hik).op ≫ hAD.hT.inv.app (Opposite.op i) =
      (D.T.map (homOfLE hjk).op ≫ hBD.hT.inv.app (Opposite.op j)) ≫
        (B.T.map (homOfLE hij).op ≫ hAB.hT.inv.app (Opposite.op i)) := by
  subst hAD
  simp [refinement_stage_hom.comp, compose_refinement_iso, compose_refinement_embedding,
    Category.assoc]
  let Fmap := ((hBD.k.toOrderHom.toFunctor).op ⋙ D.T).map (homOfLE hij).op
  have hmap :
      D.T.map (homOfLE hik).op =
        D.T.map (homOfLE hjk).op ≫ Fmap := by
    dsimp [Fmap]
    rw [← D.T.map_comp]
    congr 1
  have hnat :
      Fmap ≫ hBD.hT.inv.app (Opposite.op (hAB.k i)) =
        hBD.hT.inv.app (Opposite.op j) ≫ B.T.map (homOfLE hij).op := by
    dsimp [Fmap]
    exact hBD.hT.inv.naturality (homOfLE hij).op
  calc
    D.T.map (homOfLE hik).op ≫ hBD.hT.inv.app (Opposite.op (hAB.k i)) ≫
        hAB.hT.inv.app (Opposite.op i)
        = (D.T.map (homOfLE hjk).op ≫ Fmap) ≫
            hBD.hT.inv.app (Opposite.op (hAB.k i)) ≫
              hAB.hT.inv.app (Opposite.op i) := by
              simpa [Category.assoc] using
                congrArg (fun q => q ≫ hBD.hT.inv.app (Opposite.op (hAB.k i)) ≫
                  hAB.hT.inv.app (Opposite.op i)) hmap
    _ = D.T.map (homOfLE hjk).op ≫
          (hBD.hT.inv.app (Opposite.op j) ≫ B.T.map (homOfLE hij).op) ≫
            hAB.hT.inv.app (Opposite.op i) := by
              simpa [Category.assoc] using
                congrArg (fun q => D.T.map (homOfLE hjk).op ≫ q ≫
                  hAB.hT.inv.app (Opposite.op i)) hnat
    _ = D.T.map (homOfLE hjk).op ≫ hBD.hT.inv.app (Opposite.op j) ≫
          B.T.map (homOfLE hij).op ≫ hAB.hT.inv.app (Opposite.op i) := by
              simp [Category.assoc]


end

end CategoryTheory
