/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Path.Homotopic.Quotient
open scoped unitInterval

section HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Helper for Problem 1.8.3: pointwise loop multiplication on homotopy classes induced by the
ambient `HSpace` structure. -/
def loop_hmul_class
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    Path.Homotopic.Quotient (HSpace.e : X) HSpace.e :=
  ((Path.Homotopic.prod p q).map HSpace.hmul).cast
    HSpace.hmul_e_e.symm
    HSpace.hmul_e_e.symm

/-- Helper for Problem 1.8.3: the left-unit homotopy coming from `HSpace.eHmul`. -/
lemma loop_hmul_refl_left_homotopic (γ : Path (HSpace.e : X) HSpace.e) :
    ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).Homotopic γ := by
  -- Track the homotopy `(t, s) ↦ e ⋀ γ s` directly on the square.
  refine ⟨{
    toFun := fun p => HSpace.eHmul (p.1, γ p.2)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro s
      simp [Path.cast]
    map_one_left := by
      intro s
      simp
    prop' := by
      intro t s hs
      rcases hs with rfl | rfl
      · calc
          ({ toFun := fun x ↦ HSpace.eHmul ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 0 = HSpace.eHmul (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.eHmul (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.eHmul.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 0 := by
              simp [Path.cast, HSpace.hmul_e_e]
      · calc
          ({ toFun := fun x ↦ HSpace.eHmul ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 1 = HSpace.eHmul (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.eHmul (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.eHmul.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 1 := by
              simp [Path.cast, HSpace.hmul_e_e] }⟩

/-- Helper for Problem 1.8.3: the right-unit homotopy coming from `HSpace.hmulE`. -/
lemma loop_hmul_refl_right_homotopic (γ : Path (HSpace.e : X) HSpace.e) :
    (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).Homotopic γ := by
  -- Track the homotopy `(t, s) ↦ γ s ⋀ e` directly on the square.
  refine ⟨{
    toFun := fun p => HSpace.hmulE (p.1, γ p.2)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro s
      simp [Path.cast]
    map_one_left := by
      intro s
      simp
    prop' := by
      intro t s hs
      rcases hs with rfl | rfl
      · calc
          ({ toFun := fun x ↦ HSpace.hmulE ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 0 = HSpace.hmulE (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.hmulE (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.hmulE.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 0 := by
              simp [Path.cast, HSpace.hmul_e_e]
      · calc
          ({ toFun := fun x ↦ HSpace.hmulE ((t, x).1, γ (t, x).2), continuous_toFun := by
                fun_prop } : C(I, X)) 1 = HSpace.hmulE (t, (HSpace.e : X)) := by
              simp
          _ = HSpace.e := by
            calc
              HSpace.hmulE (t, (HSpace.e : X)) = HSpace.hmul (HSpace.e, HSpace.e) := by
                simpa using HSpace.hmulE.2 t (HSpace.e : X) (by simp)
              _ = HSpace.e := HSpace.hmul_e_e
          _ = (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
                HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).toContinuousMap 1 := by
              simp [Path.cast, HSpace.hmul_e_e] }⟩

/-- Helper for Problem 1.8.3: path composition commutes with endpoint casts on loop classes. -/
lemma loop_class_cast_trans {a₂ b₂ c₂ a₁ b₁ c₁ : X}
    (p : Path.Homotopic.Quotient a₂ b₂) (q : Path.Homotopic.Quotient b₂ c₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (p.cast ha hb).trans (q.cast hb hc) = (p.trans q).cast ha hc := by
  induction p using Quotient.ind
  rename_i p
  induction q using Quotient.ind
  rename_i q
  rfl

/-- Helper for Problem 1.8.3: loop multiplication by `HSpace.hmul` has the constant loop as a left
unit on homotopy classes. -/
lemma loop_hmul_class_refl_left (q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (X := X) (Path.Homotopic.Quotient.refl HSpace.e) q = q := by
  induction q using Quotient.ind
  rename_i γ
  -- Reduce to the explicit left-unit homotopy on representatives.
  change Path.Homotopic.Quotient.mk
      ((((Path.refl HSpace.e).prod γ).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) = Path.Homotopic.Quotient.mk γ
  rw [Path.Homotopic.Quotient.eq]
  exact loop_hmul_refl_left_homotopic (X := X) γ

/-- Helper for Problem 1.8.3: loop multiplication by `HSpace.hmul` has the constant loop as a right
unit on homotopy classes. -/
lemma loop_hmul_class_refl_right (q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (X := X) q (Path.Homotopic.Quotient.refl HSpace.e) = q := by
  induction q using Quotient.ind
  rename_i γ
  -- Reduce to the explicit right-unit homotopy on representatives.
  change Path.Homotopic.Quotient.mk
      (((γ.prod (Path.refl HSpace.e)).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) = Path.Homotopic.Quotient.mk γ
  rw [Path.Homotopic.Quotient.eq]
  exact loop_hmul_refl_right_homotopic (X := X) γ

/-- Helper for Problem 1.8.3: pointwise loop multiplication distributes over path composition on
homotopy classes. -/
lemma loop_hmul_class_interchange
    (p₁ q₁ p₂ q₂ : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    (loop_hmul_class (X := X) p₁ q₁).trans (loop_hmul_class (X := X) p₂ q₂) =
      loop_hmul_class (X := X) (p₁.trans p₂) (q₁.trans q₂) := by
  induction p₁, q₁ using Path.Homotopic.Quotient.ind₂
  rename_i a c
  induction p₂, q₂ using Path.Homotopic.Quotient.ind₂
  rename_i b d
  -- On representatives this is the interchange between product paths and composition.
  change Path.Homotopic.Quotient.mk
      ((((a.prod c).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).trans
        (((b.prod d).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)) =
    Path.Homotopic.Quotient.mk
      ((((a.trans b).prod (c.trans d)).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)
  congr 1
  calc
    ((((a.prod c).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).trans
        (((b.prod d).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)) =
        ((((a.prod c).map HSpace.hmul.continuous).trans ((b.prod d).map HSpace.hmul.continuous)).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) := by
            simpa using (Path.cast_trans
              ((a.prod c).map HSpace.hmul.continuous)
              ((b.prod d).map HSpace.hmul.continuous)
              HSpace.hmul_e_e.symm
              HSpace.hmul_e_e.symm
              HSpace.hmul_e_e.symm).symm
    _ = ((((a.prod c).trans (b.prod d)).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) := by
            rw [← Path.map_trans]
    _ = ((((a.trans b).prod (c.trans d)).map HSpace.hmul.continuous).cast
          HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm) := by
            simp [Path.trans_prod_eq_prod_trans]

/-- Helper for Problem 1.8.3: the `HSpace` loop product agrees with path composition on homotopy
classes. -/
lemma loop_hmul_class_eq_trans
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    loop_hmul_class (X := X) p q = p.trans q := by
  let htrans :
      EckmannHilton.IsUnital
        (Path.Homotopic.Quotient.trans :
          Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
            Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
              Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
        (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := Path.Homotopic.Quotient.refl_trans
      right_id := Path.Homotopic.Quotient.trans_refl }
  let hhmul :
      EckmannHilton.IsUnital (loop_hmul_class (X := X)) (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := loop_hmul_class_refl_left (X := X)
      right_id := loop_hmul_class_refl_right (X := X) }
  -- Apply the abstract Eckmann-Hilton argument to the two loop operations.
  exact
    (congr_fun₂ (EckmannHilton.mul htrans hhmul (loop_hmul_class_interchange (X := X))) p q).symm

/-- Helper for Problem 1.8.3: path composition is commutative on loop classes at the `HSpace`
unit. -/
lemma loop_trans_comm
    (p q : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) :
    p.trans q = q.trans p := by
  let htrans :
      EckmannHilton.IsUnital
        (Path.Homotopic.Quotient.trans :
          Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
            Path.Homotopic.Quotient (HSpace.e : X) HSpace.e →
              Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
        (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := Path.Homotopic.Quotient.refl_trans
      right_id := Path.Homotopic.Quotient.trans_refl }
  let hhmul :
      EckmannHilton.IsUnital (loop_hmul_class (X := X)) (Path.Homotopic.Quotient.refl HSpace.e) :=
    { left_id := loop_hmul_class_refl_left (X := X)
      right_id := loop_hmul_class_refl_right (X := X) }
  -- Compare path composition to the `HSpace` loop product, then use its commutativity.
  calc
    p.trans q = loop_hmul_class (X := X) p q := (loop_hmul_class_eq_trans (X := X) p q).symm
    _ = loop_hmul_class (X := X) q p :=
      (EckmannHilton.mul_comm htrans hhmul (loop_hmul_class_interchange (X := X))).comm p q
    _ = q.trans p := loop_hmul_class_eq_trans (X := X) q p

/-- Problem 1.8.3: multiplication on the fundamental group at the unit of an `HSpace` is
commutative. In particular, the fundamental group at the identity of a topological group is
commutative via `IsTopologicalGroup.hSpace`. -/
-- Proof sketch: use the `HSpace` multiplication on loops based at `HSpace.e`, compare it with path
-- composition at the level of homotopy classes, and conclude by the Eckmann-Hilton argument.
theorem fundamentalGroup_mul_comm (a b : FundamentalGroup X HSpace.e) :
    a * b = b * a := by
  -- Translate the group law into path composition of loop classes and use commutativity there.
  change (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e).trans
      (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e) =
    (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e).trans
      (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
  exact
    loop_trans_comm (X := X)
      (b : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)
      (a : Path.Homotopic.Quotient (HSpace.e : X) HSpace.e)

/-- The fundamental group at the unit of an `HSpace` is abelian. In particular, the fundamental
group of a topological group at the identity is abelian via `IsTopologicalGroup.hSpace`. -/
instance fundamentalGroup_commGroup : CommGroup (FundamentalGroup X HSpace.e) :=
  { (inferInstance : Group (FundamentalGroup X HSpace.e)) with
      mul_comm := fundamentalGroup_mul_comm }

end HSpace

section ContinuousMul

variable {G : Type u} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Problem 1.8.3: for loops based at the unit of a topological space with continuous
multiplication, pointwise multiplication is homotopic to path composition. In particular, this
applies to topological groups via `IsTopologicalGroup.hSpace`. -/
-- Proof sketch: consider the square `(s, t) ↦ γ s * δ t`; its diagonal recovers the identity-loop
-- specialization of `Path.mul`, while its boundary yields a reparametrization of `γ.trans δ`.
theorem loop_pointwise_mul_homotopic_trans (γ δ : Path (1 : G) 1) :
    ((γ.mul δ).cast (one_mul (1 : G)).symm (one_mul (1 : G)).symm).Homotopic (γ.trans δ) := by
  letI : HSpace G := IsTopologicalGroup.toHSpace G
  -- Route correction: specialize the abstract `HSpace` comparison instead of building a second
  -- square homotopy directly in the concrete multiplication case.
  rw [← Path.Homotopic.Quotient.eq]
  simpa [loop_hmul_class, Path.mul, IsTopologicalGroup.toHSpace,
    Path.Homotopic.Quotient.mk''_eq_mk, Path.Homotopic.prod_lift,
    Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.mk_cast] using
    loop_hmul_class_eq_trans (X := G) ⟦γ⟧ ⟦δ⟧

/-- Specialization of `fundamentalGroup_mul_comm` to a topological space with continuous
multiplication and unit, using the canonical `HSpace` structure `IsTopologicalGroup.toHSpace`. -/
theorem fundamentalGroup_mul_comm_of_continuousMul (a b : FundamentalGroup G (1 : G)) :
    a * b = b * a := by
  letI : HSpace G := IsTopologicalGroup.toHSpace G
  simpa using fundamentalGroup_mul_comm a b

end ContinuousMul
