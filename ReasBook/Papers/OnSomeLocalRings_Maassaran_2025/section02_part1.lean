/-
Authors: Liang Xiao, Haochen Ju, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/README.md (Contributors).
-/

import Mathlib

namespace SomeLocalRings

variable {𝕜 : Type*} [Field 𝕜]
variable {A B : Type*} [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]

/--
Definition 2.1.
For `A` and `B` two `𝕜`-algebras, we say that a ring morphism `f : A →+* B` stabilizes `𝕜` if
there exists a field automorphism `σ_f : 𝕜 ≃+* 𝕜` such that for all `a : 𝕜`,
`f (algebraMap 𝕜 A a) = algebraMap 𝕜 B (σ_f a)`.
-/
def RingHom.StabilizesBaseField (f : A →+* B) : Prop :=
  ∃ σ_f : 𝕜 ≃+* 𝕜, ∀ a : 𝕜, f (algebraMap 𝕜 A a) = algebraMap 𝕜 B (σ_f a)

/-- A ring morphism `f : A →+* B` stabilizes `𝕜` with respect to a given automorphism `σ_f`. -/
def RingHom.StabilizesBaseFieldWith (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜) : Prop :=
  ∀ a : 𝕜, f (algebraMap 𝕜 A a) = algebraMap 𝕜 B (σ_f a)

/--
Given `f : A →+* B` stabilizing `𝕜` with respect to `σ_f`, the range of `f` is a `𝕜`-submodule
of `B`.

This corresponds to the statement that `Im(f)` is a `𝕜`-vector subspace of `B`.
-/
noncomputable def RingHom.rangeSubmodule (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜)
    (hf : RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) f σ_f) :
    Submodule 𝕜 B := by
  classical
  refine
    { carrier := Set.range f
      add_mem' := ?_
      zero_mem' := ?_
      smul_mem' := ?_ }
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    refine ⟨x' + y', by simp⟩
  · exact ⟨0, by simp⟩
  · intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨(algebraMap 𝕜 A (σ_f.symm a)) * x, ?_⟩
    -- `f` is `σ_f`-semilinear on `𝕜`-scalars.
    calc
      f ((algebraMap 𝕜 A (σ_f.symm a)) * x) =
          f (algebraMap 𝕜 A (σ_f.symm a)) * f x := by
            simp [map_mul]
      _ = (algebraMap 𝕜 B a) * f x := by
            have : f (algebraMap 𝕜 A (σ_f.symm a)) = algebraMap 𝕜 B a := by
              simpa using (hf (σ_f.symm a))
            simp [this]
      _ = a • f x := by
            simp [Algebra.smul_def]

/--
Proposition 2.2.
Let `𝕜` be a field. Let `A` and `B` be finite dimensional algebras over `𝕜` and let `f : A →+* B`
be a ring morphism stabilizing `𝕜` with respect to `σ_f : 𝕜 ≃+* 𝕜`.

1. `Im(f)` is a `𝕜`-vector subspace of `B`.
2. If `f` is injective then `dim(Im(f)) = dim(A)`.
3. If `f` is injective and `dim(A) = dim(B)` then `f` is an isomorphism.
4. If `f` is an isomorphism then `f⁻¹` stabilizes `𝕜` and `σ_{f⁻¹} = σ_f⁻¹`.
5. If `f` is an isomorphism then `dim(A) = dim(B)`.
6. Let `I` be a proper ideal of `B`, and let `π : B →+* B ⧸ I` be the projection. Then `π ∘ f`
   stabilizes `𝕜` and `σ_{π ∘ f} = σ_f`.
7. Let `J` be an ideal of `A` lying in the kernel of `f`. Then the induced morphism
   `f̄ : A ⧸ J →+* B` factorising `f` stabilizes `𝕜` and `σ_{f̄} = σ_f`.
-/
theorem exists_submodule_range_eq_of_stabilizesBaseFieldWith
    (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜)
    (hf : RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) f σ_f) :
    ∃ V : Submodule 𝕜 B, (V : Set B) = Set.range f := by
  classical
  refine ⟨RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf, ?_⟩
  rfl

/-- Twisting scalar multiplication by a field automorphism preserves `Module.finrank`. -/
theorem finrank_compHom_symm
    [FiniteDimensional 𝕜 A] (σ : 𝕜 ≃+* 𝕜) :
    @Module.finrank 𝕜 A _ _ (Module.compHom A (σ.symm.toRingHom)) = Module.finrank 𝕜 A := by
  classical
  let inst0 : Module 𝕜 A := inferInstance
  let inst1 : Module 𝕜 A := by
    letI : Module 𝕜 A := inst0
    exact Module.compHom A (σ.symm.toRingHom)
  have hrank : @Module.rank 𝕜 A _ _ inst1 = @Module.rank 𝕜 A _ _ inst0 := by
    -- Compare ranks using the identity additive equivalence and the scalar automorphism `σ`.
    have hrank' :
        @Module.rank 𝕜 A _ _ inst0 = @Module.rank 𝕜 A _ _ inst1 := by
      simpa using
        (@rank_eq_of_equiv_equiv (R := 𝕜) (R' := 𝕜) (M := A) (M₁ := A)
          _ _ inst0 _ _ inst1 (i := σ) (j := AddEquiv.refl A) σ.bijective (by
            intro r m
            -- Unfold the scalar action for `inst1` (a `Module.compHom`).
            change @SMul.smul 𝕜 A inst0.toSMul r m =
                @SMul.smul 𝕜 A inst1.toSMul (σ r) m
            change @SMul.smul 𝕜 A inst0.toSMul r m =
                @SMul.smul 𝕜 A inst0.toSMul (σ.symm (σ r)) m
            simp))
    simpa using hrank'.symm
  -- Convert rank equality into `finrank` equality.
  simpa [Module.finrank, inst1, inst0] using congrArg Cardinal.toNat hrank

theorem finrank_rangeSubmodule_eq_finrank_of_injective
    [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜)
    (hf : RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) f σ_f)
    (hinj : Function.Injective f) :
    Module.finrank 𝕜
        (RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf) =
      Module.finrank 𝕜 A := by
  classical
  -- Use the twisted `𝕜`-module structure on `A` (via `σ_f.symm`) so that `f` becomes `𝕜`-linear.
  let inst0 : Module 𝕜 A := inferInstance
  let instAσ : Module 𝕜 A := Module.compHom A (σ_f.symm.toRingHom)
  have hfin_twist :
      @Module.finrank 𝕜 A _ _ instAσ = @Module.finrank 𝕜 A _ _ inst0 := by
    -- `inst0` is definitionally the ambient `𝕜`-module structure on `A`.
    simpa [instAσ, inst0] using (finrank_compHom_symm (𝕜 := 𝕜) (A := A) σ_f)
  have hfin :
      Module.finrank 𝕜
          (RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf) =
        @Module.finrank 𝕜 A _ _ instAσ := by
    letI : Module 𝕜 A := instAσ
    let fL : A →ₗ[𝕜] B :=
      { toFun := f
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro a x
          -- Unfold the scalar action for `instAσ` (a `Module.compHom`).
          change f ((letI : Module 𝕜 A := inst0; (σ_f.symm a) • x)) = a • f x
          -- Use the defining relation `hf` and multiplicativity of `f`.
          simp [Algebra.smul_def, map_mul, hf (σ_f.symm a)] }
    have hrange :
        RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf = LinearMap.range fL := by
      ext y
      rfl
    have hfinrange : Module.finrank 𝕜 (LinearMap.range fL) = Module.finrank 𝕜 A := by
      simpa using (LinearMap.finrank_range_of_inj (f := fL) (by simpa using hinj))
    calc
      Module.finrank 𝕜
          (RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf) =
          Module.finrank 𝕜 (LinearMap.range fL) := by
            simpa using congrArg (fun (S : Submodule 𝕜 B) => Module.finrank 𝕜 S) hrange
      _ = Module.finrank 𝕜 A := hfinrange
      _ = @Module.finrank 𝕜 A _ _ instAσ := by rfl
  -- Convert from the twisted module structure back to the original one.
  exact hfin.trans hfin_twist

theorem exists_ringEquiv_of_injective_of_finrank_eq
    [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜)
    (hf : RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) f σ_f)
    (hinj : Function.Injective f)
    (hfinrank : Module.finrank 𝕜 A = Module.finrank 𝕜 B) :
    ∃ e : A ≃+* B, e.toRingHom = f := by
  classical
  let V := RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf
  have hV :
      Module.finrank 𝕜 V = Module.finrank 𝕜 B := by
    calc
      Module.finrank 𝕜 V = Module.finrank 𝕜 A := by
        simpa [V] using
          (finrank_rangeSubmodule_eq_finrank_of_injective (𝕜 := 𝕜) (A := A) (B := B) f σ_f hf
            hinj)
      _ = Module.finrank 𝕜 B := hfinrank
  have hVtop : (V : Submodule 𝕜 B) = ⊤ := by
    -- A submodule of the same `finrank` as the ambient space is `⊤`.
    exact Submodule.eq_top_of_finrank_eq (S := V) (by simpa using hV)
  have hsurj : Function.Surjective f := by
    intro y
    have : y ∈ (V : Submodule 𝕜 B) := by
      simp [hVtop]
    rcases this with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  refine ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  rfl

theorem stabilizesBaseFieldWith_inv_of_ringEquiv
    (e : A ≃+* B) (σ_e : 𝕜 ≃+* 𝕜)
    (he :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e) :
    RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := B) (B := A) e.symm.toRingHom σ_e.symm := by
  intro a
  have h := he (σ_e.symm a)
  -- Apply `e.symm` to the defining relation for `e`.
  have h' := congrArg (fun b => e.symm b) h
  -- Simplify.
  simpa using h'.symm

theorem finrank_eq_of_ringEquiv
    [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    (e : A ≃+* B) (σ_e : 𝕜 ≃+* 𝕜)
    (he :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e) :
    Module.finrank 𝕜 A = Module.finrank 𝕜 B := by
  classical
  -- Apply Prop. 2.2.(2) to `e.toRingHom`, and use that its range is `⊤`.
  have hinj : Function.Injective e.toRingHom := e.injective
  have h1 :
      Module.finrank 𝕜
          (RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e he) =
        Module.finrank 𝕜 A := by
    simpa using
      (finrank_rangeSubmodule_eq_finrank_of_injective (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e
        he hinj)
  have hrange :
      (RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e he : Submodule 𝕜 B)
        = ⊤ := by
    ext y
    constructor
    · intro _; simp
    · intro _
      rcases e.surjective y with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have htop :
      Module.finrank 𝕜
          (RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e he) =
        Module.finrank 𝕜 B := by
    -- Use that `rangeSubmodule = ⊤`, hence it is linearly equivalent to `B`.
    let S : Submodule 𝕜 B :=
      RingHom.rangeSubmodule (𝕜 := 𝕜) (A := A) (B := B) e.toRingHom σ_e he
    have eSTop : (↥S) ≃ₗ[𝕜] (↥(⊤ : Submodule 𝕜 B)) :=
      LinearEquiv.ofEq S ⊤ (by simpa [S] using hrange)
    have eSB : (↥S) ≃ₗ[𝕜] B := eSTop.trans Submodule.topEquiv
    simpa [S] using eSB.finrank_eq
  -- Combine the two equalities.
  exact (h1.symm.trans htop)

theorem stabilizesBaseFieldWith_comp_quotient_mk
    (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜)
    (hf : RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) f σ_f)
    (I : Ideal B) [I.IsTwoSided] (hI : I ≠ ⊤) :
    RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B ⧸ I) ((Ideal.Quotient.mk I).comp f)
      σ_f := by
  have _ : I ≠ ⊤ := hI
  intro a
  -- Push the relation through the quotient map.
  simpa [RingHom.StabilizesBaseFieldWith] using congrArg (Ideal.Quotient.mk I) (hf a)

theorem stabilizesBaseFieldWith_quotientLift
    (f : A →+* B) (σ_f : 𝕜 ≃+* 𝕜)
    (hf : RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A) (B := B) f σ_f)
    (J : Ideal A) [J.IsTwoSided] (hJ : ∀ a ∈ J, f a = 0) :
    RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := A ⧸ J) (B := B)
      (Ideal.Quotient.lift J f hJ) σ_f := by
  intro a
  -- Use the quotient algebra map and the defining property of `Ideal.Quotient.lift`.
  simpa [RingHom.StabilizesBaseFieldWith] using (by
    -- `algebraMap` into a quotient is `Ideal.Quotient.mk` on `algebraMap` into the ring.
    simpa using
      (by
        -- Reduce to the statement for `f` using `Ideal.Quotient.lift_mk`.
        simpa [Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := A) J a] using
          (by
            -- `lift` agrees with `f` on representatives.
            simpa [Ideal.Quotient.lift_mk] using hf a)))

/-- `Polynomial.mapEquiv` fixes the variable `X`. -/
lemma polynomial_mapEquiv_fix_X (σ : 𝕜 ≃+* 𝕜) :
    (Polynomial.mapEquiv σ) Polynomial.X = Polynomial.X := by
  simp [Polynomial.mapEquiv_apply]

/-- `Polynomial.mapEquiv` stabilizes the base field with the given automorphism. -/
lemma polynomial_mapEquiv_stabilizesBaseFieldWith (σ : 𝕜 ≃+* 𝕜) :
    RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
      (Polynomial.mapEquiv σ).toRingHom σ := by
  intro a
  simp [Polynomial.mapEquiv_apply, Polynomial.algebraMap_eq]

/--
If a ring automorphism of `𝕜[X]` fixes `X` and acts on the base field `𝕜` by `σ`, then it is
`Polynomial.mapEquiv σ`.
-/
lemma polynomialRingEquiv_eq_mapEquiv_of_fix_X_of_stabilizesBaseFieldWith
    (σ : 𝕜 ≃+* 𝕜) (e : Polynomial 𝕜 ≃+* Polynomial 𝕜)
    (hX : e Polynomial.X = Polynomial.X)
    (he :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
        e.toRingHom σ) :
    e = Polynomial.mapEquiv σ := by
  -- First prove equality of the underlying ring homomorphisms.
  have hRingHom :
      e.toRingHom = (Polynomial.mapEquiv σ).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      have hCe : e.toRingHom (Polynomial.C a) = Polynomial.C (σ a) := by
        simpa [Polynomial.algebraMap_eq] using he a
      have hCmap :
          (Polynomial.mapEquiv σ).toRingHom (Polynomial.C a) = Polynomial.C (σ a) := by
        simp [Polynomial.mapEquiv_apply]
      exact hCe.trans hCmap.symm
    · have hXe : e.toRingHom Polynomial.X = Polynomial.X := by
        simpa using hX
      have hXmap :
          (Polynomial.mapEquiv σ).toRingHom Polynomial.X = Polynomial.X := by
        simp [RingEquiv.toRingHom_eq_coe, polynomial_mapEquiv_fix_X (𝕜 := 𝕜) σ]
      exact hXe.trans hXmap.symm
  -- Lift to an equality of ring equivalences.
  apply RingEquiv.ext
  intro p
  simpa using congrArg (fun f : Polynomial 𝕜 →+* Polynomial 𝕜 => f p) hRingHom

/--
Proposition 2.3.
Let `𝕜` be a field and let `σ : 𝕜 ≃+* 𝕜` be a field automorphism.
Then there is a unique ring automorphism `σX : Polynomial 𝕜 ≃+* Polynomial 𝕜` stabilizing `𝕜`
with respect to
`σ` such that `σX(X) = X`.
-/
theorem existsUnique_polynomialRingEquiv_stabilizesBaseFieldWith_fixing_X (σ : 𝕜 ≃+* 𝕜) :
    ∃! σX : Polynomial 𝕜 ≃+* Polynomial 𝕜,
      σX Polynomial.X = Polynomial.X ∧
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
          σX.toRingHom σ := by
  refine ⟨Polynomial.mapEquiv σ, ?_, ?_⟩
  · refine ⟨polynomial_mapEquiv_fix_X (𝕜 := 𝕜) σ, ?_⟩
    exact polynomial_mapEquiv_stabilizesBaseFieldWith (𝕜 := 𝕜) σ
  · intro e he
    rcases he with ⟨hX, hstab⟩
    exact
      polynomialRingEquiv_eq_mapEquiv_of_fix_X_of_stabilizesBaseFieldWith (𝕜 := 𝕜) σ e hX hstab

/-- A ring isomorphism `𝕜[X]/(P₁) ≃+* 𝕜[X]/(P₂)` stabilizing `𝕜` forces equal `natDegree`. -/
lemma prop2_4_natDegree_eq
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂) (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (σ_f : 𝕜 ≃+* 𝕜)
    (hf :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f) :
    P₁.natDegree = P₂.natDegree := by
  classical
  -- Equip the quotients with `FiniteDimensional` instances, using a monic associate.
  have hP₁0 : P₁ ≠ 0 := hP₁.ne_zero
  have hP₂0 : P₂ ≠ 0 := hP₂.ne_zero
  let P₁m : Polynomial 𝕜 := P₁ * Polynomial.C (P₁.leadingCoeff)⁻¹
  let P₂m : Polynomial 𝕜 := P₂ * Polynomial.C (P₂.leadingCoeff)⁻¹
  have hP₁m_monic : P₁m.Monic := by
    simpa [P₁m] using (Polynomial.monic_mul_leadingCoeff_inv (p := P₁) hP₁0)
  have hP₂m_monic : P₂m.Monic := by
    simpa [P₂m] using (Polynomial.monic_mul_leadingCoeff_inv (p := P₂) hP₂0)
  have hP₁m_isUnit : IsUnit (Polynomial.C (P₁.leadingCoeff)⁻¹) := by
    have hne : (P₁.leadingCoeff)⁻¹ ≠ 0 := by
      exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hP₁0)
    exact (Polynomial.isUnit_C).2 ((isUnit_iff_ne_zero).2 hne)
  have hP₂m_isUnit : IsUnit (Polynomial.C (P₂.leadingCoeff)⁻¹) := by
    have hne : (P₂.leadingCoeff)⁻¹ ≠ 0 := by
      exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hP₂0)
    exact (Polynomial.isUnit_C).2 ((isUnit_iff_ne_zero).2 hne)
  have hI₁ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
        Ideal.span ({P₁m} : Set (Polynomial 𝕜)) := by
    -- The generators are associated via multiplication by a unit constant.
    have hassoc : Associated P₁ P₁m := by
      refine ⟨hP₁m_isUnit.unit, ?_⟩
      simp [P₁m]
    exact (Ideal.span_singleton_eq_span_singleton).2 hassoc
  have hI₂ :
      (Ideal.span ({P₂} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
        Ideal.span ({P₂m} : Set (Polynomial 𝕜)) := by
    have hassoc : Associated P₂ P₂m := by
      refine ⟨hP₂m_isUnit.unit, ?_⟩
      simp [P₂m]
    exact (Ideal.span_singleton_eq_span_singleton).2 hassoc
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁m} : Set (Polynomial 𝕜))) :=
    (Polynomial.Monic.finite_quotient (R := 𝕜) (g := P₁m) hP₁m_monic)
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂m} : Set (Polynomial 𝕜))) :=
    (Polynomial.Monic.finite_quotient (R := 𝕜) (g := P₂m) hP₂m_monic)
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) := by
    let e :
        (Polynomial 𝕜 ⧸ Ideal.span ({P₁m} : Set (Polynomial 𝕜))) ≃ₐ[𝕜]
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) :=
      Ideal.quotientEquivAlgOfEq (R₁ := 𝕜) (A := Polynomial 𝕜)
        (I := Ideal.span ({P₁m} : Set (Polynomial 𝕜)))
        (J := Ideal.span ({P₁} : Set (Polynomial 𝕜))) hI₁.symm
    exact Module.Finite.equiv (R := 𝕜)
      (M := Polynomial 𝕜 ⧸ Ideal.span ({P₁m} : Set (Polynomial 𝕜)))
      (N := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) e.toLinearEquiv
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) := by
    let e :
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂m} : Set (Polynomial 𝕜))) ≃ₐ[𝕜]
          (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
      Ideal.quotientEquivAlgOfEq (R₁ := 𝕜) (A := Polynomial 𝕜)
        (I := Ideal.span ({P₂m} : Set (Polynomial 𝕜)))
        (J := Ideal.span ({P₂} : Set (Polynomial 𝕜))) hI₂.symm
    exact Module.Finite.equiv (R := 𝕜)
      (M := Polynomial 𝕜 ⧸ Ideal.span ({P₂m} : Set (Polynomial 𝕜)))
      (N := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) e.toLinearEquiv
  have hfin :
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) =
        Module.finrank 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
    finrank_eq_of_ringEquiv (𝕜 := 𝕜)
      (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
      (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f σ_f hf
  simpa [finrank_quotient_span_eq_natDegree] using hfin

/-- In the quotient by the principal ideal `(P)`,
a polynomial and its remainder modulo `P` agree. -/
lemma quotient_mk_mod_eq_mk (P p : Polynomial 𝕜) :
    Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial 𝕜))) (p % P) =
      Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial 𝕜))) p := by
  classical
  apply (Ideal.Quotient.eq).2
  -- `p % P - p` is a multiple of `P`.
  refine (Ideal.mem_span_singleton).2 ?_
  refine ⟨-(p / P), ?_⟩
  have hrem : p % P = p - P * (p / P) := by
    exact eq_sub_of_add_eq (EuclideanDomain.mod_add_div p P)
  calc
    p % P - p = (p - P * (p / P)) - p := by simp [hrem]
    _ = -(P * (p / P)) := by simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = P * (-(p / P)) := by simp [mul_neg]

/-- Every element of `𝕜[X]⧸(P)` has a representative of `natDegree < natDegree(P)`. -/
lemma prop2_4_exists_reduced_poly_rep (P : Polynomial 𝕜) (hP : P.natDegree ≠ 0)
    (z : Polynomial 𝕜 ⧸ Ideal.span ({P} : Set (Polynomial 𝕜))) :
    ∃ Q : Polynomial 𝕜, Q.natDegree < P.natDegree ∧ Ideal.Quotient.mk _ Q = z := by
  classical
  rcases (Ideal.Quotient.mk_surjective (I := Ideal.span ({P} : Set (Polynomial 𝕜))) z) with ⟨R, rfl⟩
  refine ⟨R % P, ?_, ?_⟩
  · simpa using Polynomial.natDegree_mod_lt R hP
  · simpa using (quotient_mk_mod_eq_mk (𝕜 := 𝕜) P R)

/--
If two polynomials of `natDegree < natDegree(P)` represent the same element in `𝕜[X]⧸(P)`, then
they are equal.
-/
lemma prop2_4_unique_reduced_poly_rep {P : Polynomial 𝕜}
    {Q Q' : Polynomial 𝕜} (hQ : Q.natDegree < P.natDegree) (hQ' : Q'.natDegree < P.natDegree)
    (h :
      Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial 𝕜))) Q =
        Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial 𝕜))) Q') :
    Q = Q' := by
  classical
  have hmem : Q - Q' ∈ Ideal.span ({P} : Set (Polynomial 𝕜)) := (Ideal.Quotient.eq).1 h
  have hdvd : P ∣ Q - Q' := (Ideal.mem_span_singleton).1 hmem
  by_contra hne
  have hneq0 : Q - Q' ≠ 0 := sub_ne_zero.2 hne
  have hdeg :
      (Q - Q').natDegree < P.natDegree := by
    have hle : (Q - Q').natDegree ≤ max Q.natDegree Q'.natDegree := Polynomial.natDegree_sub_le Q Q'
    have hmax : max Q.natDegree Q'.natDegree < P.natDegree := max_lt_iff.2 ⟨hQ, hQ'⟩
    exact lt_of_le_of_lt hle hmax
  exact (Polynomial.not_dvd_of_natDegree_lt (p := P) hneq0 hdeg) hdvd

/--
Proposition 2.4.
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. Let
`f : 𝕜[X]/(P₁) ≃+* 𝕜[X]/(P₂)` be a ring isomorphism stabilizing `𝕜` with respect to `σ_f`.

1. `deg(P₁) = deg(P₂)`.
2. There exists a unique polynomial `Q_f ∈ 𝕜[X]` with `1 ≤ deg(Q_f) < deg(P₁)` such that `f` is
   induced by a ring morphism `f_X : 𝕜[X] →+* 𝕜[X]` stabilizing `𝕜` with respect to `σ_f` and
   given by `P ↦ σ_f^X(P) ∘ Q_f`, where `σ_f^X` is as in Proposition 2.3.
3. `σ_f^X(P₁) ∘ Q_f = S_f * P₂` for some polynomial `S_f`.
4. If `σ_f^X(P) ∘ Q_f = S * P₂` then `P = R * P₁`.
5. The morphism `f_X` maps `(P₁^n)` into `(P₂^n)` and hence induces
   `f_{X,n} : 𝕜[X]/(P₁^n) →+* 𝕜[X]/(P₂^n)` stabilizing `𝕜`.
-/
theorem proposition_2_4
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (σ_f : 𝕜 ≃+* 𝕜)
    (hf :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f) :
    P₁.natDegree = P₂.natDegree ∧
      (let σX :=
        Classical.choose
          (ExistsUnique.exists
            (existsUnique_polynomialRingEquiv_stabilizesBaseFieldWith_fixing_X (𝕜 := 𝕜) σ_f))
        ∃! Qf : Polynomial 𝕜,
          Qf.natDegree < P₁.natDegree ∧
            ∃ fX : Polynomial 𝕜 →+* Polynomial 𝕜,
              fX Polynomial.X = Qf ∧
                RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
                  fX σ_f ∧
                  (∀ P : Polynomial 𝕜, fX P = (σX P).comp Qf) ∧
                    (∃ hIJ :
                        (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
                          Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))),
                      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
                          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
                        f.toRingHom) ∧
                      (∃ Sf : Polynomial 𝕜, (σX P₁).comp Qf = Sf * P₂) ∧
                        (∀ P : Polynomial 𝕜,
                            (∃ S : Polynomial 𝕜, (σX P).comp Qf = S * P₂) →
                              ∃ R : Polynomial 𝕜, P = R * P₁) ∧
                          ∀ n : ℕ,
                            ∃ hIJn :
                              (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
                                Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
                              RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
                                (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
                                (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))
                                (Ideal.quotientMap (I :=
                                  Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
                                  (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn)
                                σ_f) := by
  classical
  have hdeg : P₁.natDegree = P₂.natDegree :=
    prop2_4_natDegree_eq (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf
  refine ⟨hdeg, ?_⟩
  -- Unfold the chosen lift `σ_f^X`.
  simp (config := { zeta := false }) only
  let σX :=
    Classical.choose
      (ExistsUnique.exists
        (existsUnique_polynomialRingEquiv_stabilizesBaseFieldWith_fixing_X (𝕜 := 𝕜) σ_f))
  have hσX :
      σX Polynomial.X = Polynomial.X ∧
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
          σX.toRingHom σ_f :=
    Classical.choose_spec
      (ExistsUnique.exists
        (existsUnique_polynomialRingEquiv_stabilizesBaseFieldWith_fixing_X (𝕜 := 𝕜) σ_f))
  let mk₁ :
      Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) :=
    Ideal.Quotient.mk _
  let mk₂ :
      Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
    Ideal.Quotient.mk _
  -- Choose `Qf` as the reduced representative of `f(X₁)`.
  let z : Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜)) := f (mk₁ Polynomial.X)
  have hP₂deg0 : P₂.natDegree ≠ 0 := ne_of_gt (hP₂.natDegree_pos)
  rcases prop2_4_exists_reduced_poly_rep (𝕜 := 𝕜) P₂ hP₂deg0 z with ⟨Qf, hQf_deg₂, hQf_mk⟩
  have hQf_deg₁ : Qf.natDegree < P₁.natDegree := by
    simpa [hdeg] using hQf_deg₂
  -- Define `fX(P) = (σX P).comp Qf`.
  let fX : Polynomial 𝕜 →+* Polynomial 𝕜 := (Polynomial.compRingHom Qf).comp σX.toRingHom
  have hfX_def : ∀ P : Polynomial 𝕜, fX P = (σX P).comp Qf := by
    intro P
    rfl
  have hfX_X : fX Polynomial.X = Qf := by
    -- `σX` fixes `X`, and `X.comp Qf = Qf`.
    simp [fX, hσX.1]
  have hfX :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜) fX σ_f := by
    intro a
    -- Constants are handled by the stabilization property of `σX`.
    have hCσ : σX (Polynomial.C a) = Polynomial.C (σ_f a) := by
      simpa [Polynomial.algebraMap_eq] using (hσX.2 a)
    simp [fX, hCσ]
  -- Core identity: `f` agrees with the induced map from `fX` on polynomial representatives.
  have hmk : ∀ P : Polynomial 𝕜, f (mk₁ P) = mk₂ (fX P) := by
    have hRingHom :
        f.toRingHom.comp mk₁ = mk₂.comp fX := by
      apply Polynomial.ringHom_ext
      · intro a
        -- Compare on constants using the stabilization of `f` and `σX`.
        have hfC :
            f (mk₁ (Polynomial.C a)) =
              algebraMap 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) (σ_f a) := by
          simpa [mk₁, Polynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap] using (hf a)
        have hCσ : σX (Polynomial.C a) = Polynomial.C (σ_f a) := by
          simpa [Polynomial.algebraMap_eq] using (hσX.2 a)
        have hfXC : fX (Polynomial.C a) = Polynomial.C (σ_f a) := by
          simp [hfX_def, hCσ]
        have halg :
            algebraMap 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) (σ_f a) =
              mk₂ (Polynomial.C (σ_f a)) := by
          simpa [mk₂, Polynomial.algebraMap_eq] using
            (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜)
              (Ideal.span ({P₂} : Set (Polynomial 𝕜))) (σ_f a)).symm
        -- Finish by rewriting both sides through `algebraMap`.
        simp [RingHom.comp_apply, hfC, hfXC, halg]
      · -- Compare on `X` by definition of `Qf`.
        have : mk₂ Qf = f (mk₁ Polynomial.X) := by
          simpa [z] using hQf_mk
        simpa [RingHom.comp_apply, hfX_X] using this.symm
    intro P
    simpa [mk₁, mk₂] using congrArg (fun g : Polynomial 𝕜 →+* _ => g P) hRingHom
  -- Show the ideal compatibility needed to form `quotientMap`.
  have hmk₁_P₁ : mk₁ P₁ = 0 := by
    refine (Ideal.Quotient.eq_zero_iff_mem).2 ?_
    exact Ideal.subset_span (by simp)
  have hmk₂_fXP₁ : mk₂ (fX P₁) = 0 := by
    calc
      mk₂ (fX P₁) = f (mk₁ P₁) := (hmk P₁).symm
      _ = f 0 := by simp [hmk₁_P₁]
      _ = 0 := by simp
  have hmem₂ : fX P₁ ∈ (Ideal.span ({P₂} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) :=
    (Ideal.Quotient.eq_zero_iff_mem).1 hmk₂_fXP₁
  have hIJ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))) := by
    -- Principal ideal: it suffices to check the generator.
    refine (Ideal.span_singleton_le_iff_mem
      (I := Ideal.comap fX (Ideal.span ({P₂} : Set _))) (x := P₁)).2 ?_
    exact hmem₂
  have hf_ind :
      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
        f.toRingHom := by
    apply RingHom.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro P
    -- Reduce to the defining equation on representatives.
    simpa [Ideal.quotientMap_mk, mk₁, mk₂] using (hmk P).symm
  -- Point (3): divisibility by `P₂`.
  have hSf : ∃ Sf : Polynomial 𝕜, (σX P₁).comp Qf = Sf * P₂ := by
    rcases (Ideal.mem_span_singleton).1 hmem₂ with ⟨Sf, hSf⟩
    refine ⟨Sf, ?_⟩
    have : (σX P₁).comp Qf = P₂ * Sf := by
      simpa [hfX_def P₁, fX] using hSf
    simpa [mul_comm] using this
  -- Point (4): kernel characterization via injectivity of `f`.
  have hker :
      ∀ P : Polynomial 𝕜,
        (∃ S : Polynomial 𝕜, (σX P).comp Qf = S * P₂) → ∃ R : Polynomial 𝕜, P = R * P₁ := by
    intro P hdiv
    rcases hdiv with ⟨S, hS⟩
    have hmk₂_zero : mk₂ (fX P) = 0 := by
      -- In the quotient by `(P₂)`, multiples of `P₂` are zero.
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      refine (Ideal.mem_span_singleton).2 ?_
      refine ⟨S, ?_⟩
      -- Convert `S * P₂` into `P₂ * S` for divisibility.
      simpa [hfX_def P, mul_comm, mul_left_comm, mul_assoc] using hS
    have hmk₁_zero : mk₁ P = 0 := by
      apply f.injective
      have hfP : f (mk₁ P) = 0 := by simpa [hmk P] using hmk₂_zero
      calc
        f (mk₁ P) = 0 := hfP
        _ = f 0 := by simp
    have hmem₁ : P ∈ (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) :=
      (Ideal.Quotient.eq_zero_iff_mem).1 hmk₁_zero
    rcases (Ideal.mem_span_singleton).1 hmem₁ with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    -- Convert the divisibility statement into the desired multiplicative form.
    simpa [mul_comm] using hR
  -- Point (5): ideal power compatibility.
  have hpow :
      ∀ n : ℕ,
        ∃ hIJn :
          (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
            Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
          RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
            (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))
            (Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
              (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn)
            σ_f := by
    intro n
    rcases hSf with ⟨Sf, hSf⟩
    have hmem_pow :
        fX (P₁ ^ n) ∈ (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) := by
      -- `fX(P₁^n) = (Sf*P₂)^n = Sf^n * P₂^n`.
      refine (Ideal.mem_span_singleton).2 ?_
      refine ⟨Sf ^ n, ?_⟩
      calc
        fX (P₁ ^ n) = (fX P₁) ^ n := by simp [map_pow]
        _ = ((σX P₁).comp Qf) ^ n := by simp [hfX_def P₁]
        _ = (Sf * P₂) ^ n := by simp [hSf]
        _ = (Sf ^ n) * (P₂ ^ n) := by simp [mul_pow]
        _ = (P₂ ^ n) * (Sf ^ n) := by simp [mul_comm]
    have hIJn :
        (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
          Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) := by
      refine (Ideal.span_singleton_le_iff_mem
        (I := Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set _))) (x := P₁ ^ n)).2 ?_
      exact hmem_pow
    refine ⟨hIJn, ?_⟩
    intro a
    -- Stabilization is inherited from `fX`.
    simpa [RingHom.StabilizesBaseFieldWith, Ideal.quotientMap_mk,
      Ideal.Quotient.mk_algebraMap] using
      congrArg (Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) (hfX a)
  -- Assemble existence.
  refine ⟨Qf, ⟨hQf_deg₁, ?_⟩, ?_⟩
  · refine ⟨fX, ⟨hfX_X, hfX, hfX_def, ?_, hSf, hker, ?_⟩⟩
    · refine ⟨hIJ, ?_⟩
      exact hf_ind
    · intro n
      simpa using (hpow n)
  -- Uniqueness of `Qf`: any solution must represent `f(X₁)` and satisfy the degree bound.
  intro Qg hQg
  rcases hQg with ⟨hQg_deg₁, fXg, hfXg_X, hfXg, hfXg_def, hrest⟩
  rcases hrest with ⟨hIJg, hrest⟩
  rcases hIJg with ⟨hIJg, hf_indg⟩
  -- Evaluate the induced equality on `X`.
  have hmkQg :
      mk₂ Qg = f (mk₁ Polynomial.X) := by
    have hq :
        Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
            (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fXg hIJg (mk₁ Polynomial.X) =
          f.toRingHom (mk₁ Polynomial.X) := by
        simpa using congrArg (fun g => g (mk₁ Polynomial.X)) hf_indg
    simpa [Ideal.quotientMap_mk, mk₁, mk₂, hfXg_X] using hq
  have hmkQf : mk₂ Qf = f (mk₁ Polynomial.X) := by
    simpa [z] using hQf_mk
  have hmk_eq : mk₂ Qf = mk₂ Qg := by simp [hmkQf, hmkQg]
  have hQg_deg₂ : Qg.natDegree < P₂.natDegree := by
    simpa [hdeg] using hQg_deg₁
  -- Apply uniqueness of reduced representatives modulo `P₂`.
  have : Qf = Qg :=
    prop2_4_unique_reduced_poly_rep (𝕜 := 𝕜) (P := P₂) hQf_deg₂ hQg_deg₂ (by
      simpa [mk₂] using hmk_eq)
  simp [this]

/-- If `P₂ ∣ fX P`, then `P₁ ∣ P` (using injectivity of the induced map on `(P₁)`-quotients). -/
lemma prop2_5_dvd_P1_of_dvd_P2_fX
    (P₁ P₂ : Polynomial 𝕜) (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (fX : Polynomial 𝕜 →+* Polynomial 𝕜)
    (hIJ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (hf_ind :
      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
        f.toRingHom) :
    ∀ P : Polynomial 𝕜, P₂ ∣ fX P → P₁ ∣ P := by
  intro P hP
  classical
  let mk₁ :
      Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) :=
    Ideal.Quotient.mk _
  let mk₂ :
      Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
    Ideal.Quotient.mk _
  have hmk₂ : mk₂ (fX P) = 0 := by
    refine (Ideal.Quotient.eq_zero_iff_mem).2 ?_
    exact (Ideal.mem_span_singleton).2 hP
  have hEq : mk₂ (fX P) = f (mk₁ P) := by
    simpa [Ideal.quotientMap_mk, mk₁, mk₂] using
      congrArg (fun g => g (mk₁ P)) hf_ind
  have hmk₁ : mk₁ P = 0 := by
    apply f.injective
    have : f (mk₁ P) = f 0 := by simpa [hEq] using hmk₂
    simpa using this
  have hmem : P ∈ (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) := by
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hmk₁
  exact (Ideal.mem_span_singleton).1 hmem

/--
If `S_f` is coprime to `P₂`, then divisibility of `fX(P)` by `P₂^k` forces divisibility of `P`
by `P₁^k`.
-/
lemma prop2_5_pow_dvd_P1_of_pow_dvd_P2_fX
    (P₁ P₂ : Polynomial 𝕜) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (fX : Polynomial 𝕜 →+* Polynomial 𝕜)
    (hIJ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (hf_ind :
      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
        f.toRingHom)
    (Sf : Polynomial 𝕜) (hSf : fX P₁ = Sf * P₂) :
    IsCoprime Sf P₂ → ∀ k : ℕ, ∀ P : Polynomial 𝕜, (P₂ ^ k ∣ fX P) → (P₁ ^ k ∣ P) := by
  intro hcop
  refine Nat.rec ?_ ?_
  · intro P _; simp
  · intro k IH P hdiv
    have hP₂0 : P₂ ≠ 0 := hP₂.ne_zero
    have hP₂_dvd : P₂ ∣ fX P := by
      exact dvd_trans (dvd_pow_self P₂ (Nat.succ_ne_zero k)) hdiv
    have hP₁_dvd : P₁ ∣ P :=
      prop2_5_dvd_P1_of_dvd_P2_fX (𝕜 := 𝕜) P₁ P₂ f fX hIJ hf_ind P hP₂_dvd
    rcases hP₁_dvd with ⟨P', rfl⟩
    have hdiv' : P₂ ^ (k + 1) ∣ fX P₁ * fX P' := by
      simpa [map_mul] using hdiv
    have hdiv'' : P₂ ^ k * P₂ ∣ (Sf * fX P') * P₂ := by
      simpa [pow_succ, hSf, mul_assoc, mul_left_comm, mul_comm] using hdiv'
    have hdivSf : P₂ ^ k ∣ Sf * fX P' := by
      exact (mul_dvd_mul_iff_right hP₂0).1 hdiv''
    have hcop' : IsCoprime (P₂ ^ k) Sf := by
      exact (isCoprime_comm).1 (hcop.pow_right (n := k))
    have hdivP' : P₂ ^ k ∣ fX P' := by
      exact IsCoprime.dvd_of_dvd_mul_left hcop' hdivSf
    have hIH : P₁ ^ k ∣ P' := IH P' hdivP'
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using (mul_dvd_mul_left P₁ hIH)

/-- Injectivity of the induced map `f_{X,n}` under the coprimality hypothesis. -/
lemma prop2_5_injective_quotientMap_pow
    (P₁ P₂ : Polynomial 𝕜) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (fX : Polynomial 𝕜 →+* Polynomial 𝕜)
    (hIJ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (hf_ind :
      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
        f.toRingHom)
    (Sf : Polynomial 𝕜) (hSf : fX P₁ = Sf * P₂)
    (n : ℕ)
    (hIJn :
      (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) :
    IsCoprime Sf P₂ →
      Function.Injective
        (Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn) := by
  intro hcop
  classical
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro p q hxy
  apply (Ideal.Quotient.eq).2
  have hEq :
      Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) (fX p) =
        Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) (fX q) := by
    simpa [Ideal.quotientMap_mk] using hxy
  have hmem₂ :
      fX p - fX q ∈ (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) :=
    (Ideal.Quotient.eq).1 hEq
  have hdiv₂ : P₂ ^ n ∣ fX (p - q) := by
    simpa [map_sub] using (Ideal.mem_span_singleton).1 hmem₂
  have hdiv₁ :
      P₁ ^ n ∣ p - q :=
    prop2_5_pow_dvd_P1_of_pow_dvd_P2_fX (𝕜 := 𝕜) P₁ P₂ hP₂ f fX hIJ hf_ind Sf hSf hcop n
      (p - q) hdiv₂
  exact (Ideal.mem_span_singleton).2 hdiv₁

/--
If `S_f` is coprime to `P₂`, then the induced map `f_{X,n} : 𝕜[X]/(P₁^n) → 𝕜[X]/(P₂^n)` is an
isomorphism.
-/
lemma prop2_5_exists_ringEquiv_of_isCoprime
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (σ_f : 𝕜 ≃+* 𝕜)
    (hf :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f)
    (fX : Polynomial 𝕜 →+* Polynomial 𝕜)
    (hfX :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜) fX σ_f)
    (hIJ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (hf_ind :
      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
        f.toRingHom)
    (Sf : Polynomial 𝕜) (hSf : fX P₁ = Sf * P₂)
    (n : ℕ)
    (hIJn :
      (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) :
    IsCoprime Sf P₂ →
      ∃ e :
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) ≃+*
            (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
        e.toRingHom =
          Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn := by
  intro hcop
  classical
  -- Finite-dimensionality of the quotients, by reducing to a monic associate.
  have hP₁0 : P₁ ≠ 0 := hP₁.ne_zero
  have hP₂0 : P₂ ≠ 0 := hP₂.ne_zero
  have hP₁n0 : P₁ ^ n ≠ 0 := pow_ne_zero n hP₁0
  have hP₂n0 : P₂ ^ n ≠ 0 := pow_ne_zero n hP₂0
  let P₁m : Polynomial 𝕜 := (P₁ ^ n) * Polynomial.C ((P₁ ^ n).leadingCoeff)⁻¹
  let P₂m : Polynomial 𝕜 := (P₂ ^ n) * Polynomial.C ((P₂ ^ n).leadingCoeff)⁻¹
  have hP₁m_monic : P₁m.Monic := by
    simpa [P₁m] using (Polynomial.monic_mul_leadingCoeff_inv (p := P₁ ^ n) hP₁n0)
  have hP₂m_monic : P₂m.Monic := by
    simpa [P₂m] using (Polynomial.monic_mul_leadingCoeff_inv (p := P₂ ^ n) hP₂n0)
  have hP₁m_isUnit : IsUnit (Polynomial.C ((P₁ ^ n).leadingCoeff)⁻¹) := by
    have hne : ((P₁ ^ n).leadingCoeff)⁻¹ ≠ 0 := by
      exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hP₁n0)
    exact (Polynomial.isUnit_C).2 ((isUnit_iff_ne_zero).2 hne)
  have hP₂m_isUnit : IsUnit (Polynomial.C ((P₂ ^ n).leadingCoeff)⁻¹) := by
    have hne : ((P₂ ^ n).leadingCoeff)⁻¹ ≠ 0 := by
      exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hP₂n0)
    exact (Polynomial.isUnit_C).2 ((isUnit_iff_ne_zero).2 hne)
  have hI₁ :
      (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
        Ideal.span ({P₁m} : Set (Polynomial 𝕜)) := by
    have hassoc : Associated (P₁ ^ n) P₁m := by
      refine ⟨hP₁m_isUnit.unit, ?_⟩
      simp [P₁m]
    exact (Ideal.span_singleton_eq_span_singleton).2 hassoc
  have hI₂ :
      (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
        Ideal.span ({P₂m} : Set (Polynomial 𝕜)) := by
    have hassoc : Associated (P₂ ^ n) P₂m := by
      refine ⟨hP₂m_isUnit.unit, ?_⟩
      simp [P₂m]
    exact (Ideal.span_singleton_eq_span_singleton).2 hassoc
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁m} : Set (Polynomial 𝕜))) :=
    (Polynomial.Monic.finite_quotient (R := 𝕜) (g := P₁m) hP₁m_monic)
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂m} : Set (Polynomial 𝕜))) :=
    (Polynomial.Monic.finite_quotient (R := 𝕜) (g := P₂m) hP₂m_monic)
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) := by
    let e :
        (Polynomial 𝕜 ⧸ Ideal.span ({P₁m} : Set (Polynomial 𝕜))) ≃ₐ[𝕜]
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) :=
      Ideal.quotientEquivAlgOfEq (R₁ := 𝕜) (A := Polynomial 𝕜)
        (I := Ideal.span ({P₁m} : Set (Polynomial 𝕜)))
        (J := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) hI₁.symm
    exact Module.Finite.equiv (R := 𝕜)
      (M := Polynomial 𝕜 ⧸ Ideal.span ({P₁m} : Set (Polynomial 𝕜)))
      (N := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) e.toLinearEquiv
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) := by
    let e :
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂m} : Set (Polynomial 𝕜))) ≃ₐ[𝕜]
          (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) :=
      Ideal.quotientEquivAlgOfEq (R₁ := 𝕜) (A := Polynomial 𝕜)
        (I := Ideal.span ({P₂m} : Set (Polynomial 𝕜)))
        (J := Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) hI₂.symm
    exact Module.Finite.equiv (R := 𝕜)
      (M := Polynomial 𝕜 ⧸ Ideal.span ({P₂m} : Set (Polynomial 𝕜)))
      (N := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) e.toLinearEquiv
  let fXn :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) →+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) :=
    Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
      (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn
  have hfXn :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fXn σ_f := by
    intro a
    simpa [RingHom.StabilizesBaseFieldWith, fXn, Ideal.quotientMap_mk,
      Ideal.Quotient.mk_algebraMap] using
        congrArg (Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) (hfX a)
  have hinj : Function.Injective fXn := by
    simpa [fXn] using
      prop2_5_injective_quotientMap_pow (𝕜 := 𝕜) P₁ P₂ hP₂ f fX hIJ hf_ind Sf hSf n hIJn hcop
  have hdeg : P₁.natDegree = P₂.natDegree :=
    prop2_4_natDegree_eq (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf
  have hfinrank :
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) =
        Module.finrank 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) := by
    calc
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) =
          (P₁ ^ n).natDegree := by simp [finrank_quotient_span_eq_natDegree]
      _ = n * P₁.natDegree := by simp [Polynomial.natDegree_pow]
      _ = n * P₂.natDegree := by simp [hdeg]
      _ = (P₂ ^ n).natDegree := by simp [Polynomial.natDegree_pow]
      _ = Module.finrank 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) := by
          simp [finrank_quotient_span_eq_natDegree]
  rcases
    exists_ringEquiv_of_injective_of_finrank_eq (𝕜 := 𝕜)
      (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
      (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fXn σ_f hfXn hinj
      hfinrank with
    ⟨e, he⟩
  refine ⟨e, ?_⟩
  simpa [fXn] using he


end SomeLocalRings
