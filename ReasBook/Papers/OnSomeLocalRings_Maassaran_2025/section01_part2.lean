/-
Authors: Liang Xiao, Haochen Ju, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/README.md (Contributors).
-/

import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Papers.OnSomeLocalRings_Maassaran_2025.section01_part1

namespace SomeLocalRings

open Polynomial
open scoped BigOperators

variable {𝕜 : Type*} [Field 𝕜]

/-- The `AdjoinRoot P`-dimension of `AdjoinRoot (P^k)` is `k` under the scalar tower hypothesis. -/
lemma finrank_target_over_adjoinRoot_eq_k
    (P : Polynomial 𝕜) (hP : Irreducible P) (k : ℕ)
    [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))]
    [IsScalarTower 𝕜 (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    Module.finrank (AdjoinRoot P) (AdjoinRoot (P ^ k)) = k := by
  classical
  haveI : Fact (Irreducible P) := ⟨hP⟩
  have hPk0 : (P ^ k) ≠ 0 := pow_ne_zero k hP.ne_zero
  have hP0 : P ≠ 0 := hP.ne_zero
  haveI : Module.Finite 𝕜 (AdjoinRoot P) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (K := 𝕜) hP0).basis
  haveI : Module.Finite 𝕜 (AdjoinRoot (P ^ k)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis (K := 𝕜) hPk0).basis
  -- Ensure the finrank over `AdjoinRoot P` is defined, using finiteness over `𝕜`.
  haveI : Module.Finite (AdjoinRoot P) (AdjoinRoot (P ^ k)) :=
    Module.Finite.right 𝕜 (AdjoinRoot P) (AdjoinRoot (P ^ k))
  have hdegPpos : 0 < P.natDegree := by
    -- An irreducible polynomial over a field has positive degree.
    exact (Polynomial.natDegree_pos_iff_degree_pos).2 (Polynomial.degree_pos_of_irreducible hP)
  have finrank_base :
      Module.finrank 𝕜 (AdjoinRoot P) = P.natDegree := by
    simpa [AdjoinRoot.powerBasis_dim (K := 𝕜) (f := P) hP0] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis (K := 𝕜) hP0))
  have finrank_target :
      Module.finrank 𝕜 (AdjoinRoot (P ^ k)) = (P ^ k).natDegree := by
    simpa [AdjoinRoot.powerBasis_dim (K := 𝕜) (f := P ^ k) hPk0] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis (K := 𝕜) hPk0))
  -- Apply the tower finrank formula and cancel `P.natDegree`.
  have hmul :
      Module.finrank 𝕜 (AdjoinRoot P) *
          Module.finrank (AdjoinRoot P) (AdjoinRoot (P ^ k)) =
        Module.finrank 𝕜 (AdjoinRoot (P ^ k)) := by
    simpa [Nat.mul_comm] using
      (Module.finrank_mul_finrank 𝕜 (AdjoinRoot P) (AdjoinRoot (P ^ k)))
  -- Rewrite the finranks in terms of `natDegree`.
  have hmul' :
      P.natDegree * Module.finrank (AdjoinRoot P) (AdjoinRoot (P ^ k)) =
        (P ^ k).natDegree := by
    simpa [finrank_base, finrank_target, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  -- `natDegree (P^k) = k * natDegree P`.
  have hdegpow : (P ^ k).natDegree = k * P.natDegree := by
    simp [Polynomial.natDegree_pow]
  -- Cancel `P.natDegree`.
  have :
      P.natDegree * Module.finrank (AdjoinRoot P) (AdjoinRoot (P ^ k)) =
        P.natDegree * k := by
    simpa [hdegpow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul'
  exact mul_left_cancel₀ (Nat.ne_of_gt hdegPpos) this

/--
Theorem 1.7.
Let `𝕜` be a field and `P` be an irreducible polynomial over `𝕜`. If `P' ≠ 0`, then `𝕜[X]⧸(P ^ k)`
is isomorphic, as an `𝕜[X]⧸(P)`-algebra (and hence as a `𝕜`-algebra), to `(𝕜[X]⧸(P))[Y]⧸(Y ^ k)`.
The isomorphism is given by `Y ↦ P`.
-/
theorem exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow
    (P : Polynomial 𝕜) (hP : Irreducible P) (hP' : P.derivative ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    [Algebra (AdjoinRoot P) (AdjoinRoot (P ^ k))]
    [IsScalarTower 𝕜 (AdjoinRoot P) (AdjoinRoot (P ^ k))] :
    ∃ e :
        AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k) ≃ₐ[AdjoinRoot P]
          AdjoinRoot (P ^ k),
      e (AdjoinRoot.root ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) =
        AdjoinRoot.mk (P ^ k) P := by
  classical
  haveI : Fact (Irreducible P) := ⟨hP⟩
  let ψ : AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k) →ₐ[AdjoinRoot P]
      AdjoinRoot (P ^ k) :=
    psiK (P := P) (k := k)
  have hψroot :
      ψ (AdjoinRoot.root ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) =
        AdjoinRoot.mk (P ^ k) P := by
    simpa [ψ] using (psiK_def_and_root (P := P) (k := k))
  have hψ_inj : Function.Injective ψ := by
    simpa [ψ] using
      (psiK_injective (P := P) (hP := hP) (hP' := hP') (k := k) (hk := hk))
  -- Compare finranks over `AdjoinRoot P` to deduce surjectivity.
  have finrank_dom :
      Module.finrank (AdjoinRoot P)
          (AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) =
        k := by
    simpa using (finrank_domain_over_adjoinRoot_eq_k (P := P) (hP := hP) (k := k))
  have finrank_cod :
      Module.finrank (AdjoinRoot P) (AdjoinRoot (P ^ k)) = k := by
    simpa using (finrank_target_over_adjoinRoot_eq_k (P := P) (hP := hP) (k := k))
  have hfin :
      Module.finrank (AdjoinRoot P)
          (AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) =
        Module.finrank (AdjoinRoot P) (AdjoinRoot (P ^ k)) := by
    simp [finrank_dom, finrank_cod]
  have hψ_surj : Function.Surjective ψ := by
    -- Use the finite-dimensional linear algebra lemma over the field `AdjoinRoot P`.
    haveI : Module.Finite 𝕜 (AdjoinRoot P) :=
      Module.Finite.of_basis (AdjoinRoot.powerBasis (K := 𝕜) hP.ne_zero).basis
    haveI : Module.Finite 𝕜 (AdjoinRoot (P ^ k)) :=
      Module.Finite.of_basis (AdjoinRoot.powerBasis (K := 𝕜) (pow_ne_zero k hP.ne_zero)).basis
    haveI : Module.Finite (AdjoinRoot P) (AdjoinRoot (P ^ k)) :=
      Module.Finite.right 𝕜 (AdjoinRoot P) (AdjoinRoot (P ^ k))
    haveI :
        FiniteDimensional (AdjoinRoot P)
          (AdjoinRoot ((Polynomial.X : Polynomial (AdjoinRoot P)) ^ k)) := by
      classical
      let g : Polynomial (AdjoinRoot P) := (Polynomial.X : Polynomial (AdjoinRoot P)) ^ k
      have hg : g ≠ 0 := by
        simp [g]
      exact
        Module.Basis.finiteDimensional_of_finite
          (AdjoinRoot.powerBasis (K := AdjoinRoot P) hg).basis
    haveI : FiniteDimensional (AdjoinRoot P) (AdjoinRoot (P ^ k)) := by
      classical
      exact
        Module.Basis.finiteDimensional_of_finite
          (Module.finBasis (AdjoinRoot P) (AdjoinRoot (P ^ k)))
    have hsurj_lin :
        Function.Surjective (ψ.toLinearMap : _ →ₗ[AdjoinRoot P] _) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1
        (by
          -- `ψ.toLinearMap` has the same underlying function as `ψ`.
          simpa using hψ_inj)
    simpa using hsurj_lin
  refine ⟨AlgEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩, ?_⟩
  simp [AlgEquiv.ofBijective_apply, hψroot]

/-- A ring equivalence preserves the nilradical ideal. -/
lemma nilradical_map_eq_of_ringEquiv {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R ≃+* S) : (nilradical R).map (e : R →+* S) = nilradical S := by
  ext y
  constructor
  · intro hy
    rcases
        (Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective).1 hy with
      ⟨x, hx, rfl⟩
    exact (mem_nilradical).2 (((mem_nilradical).1 hx).map (e : R →+* S))
  · intro hy
    refine (Ideal.mem_map_iff_of_surjective (e : R →+* S) e.surjective).2 ?_
    refine ⟨e.symm y, ?_, by simp⟩
    exact (mem_nilradical).2 (((mem_nilradical).1 hy).map (e.symm : S →+* R))

/--
The quotient of `A[Y]/(Y^k)` by the ideal `(Y)` is canonically isomorphic to `A`.

We present `A[Y]/(Y^k)` as `AdjoinRoot (X^k)` and the ideal `(Y)` as the span of the adjoined
root.
-/
noncomputable def quotient_span_root_adjoinRoot_X_pow_ringEquiv_base
    (A : Type*) [CommRing A] (k : ℕ) (hk : 1 ≤ k) :
    (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
        Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _)) ≃+* A := by
  classical
  -- Work in the polynomial ring and apply the third isomorphism theorem.
  let I : Ideal (Polynomial A) := Ideal.span ({(X : Polynomial A) ^ k} : Set (Polynomial A))
  let J : Ideal (Polynomial A) := Ideal.span ({(X : Polynomial A)} : Set (Polynomial A))
  have hIJ : I ≤ J := by
    -- Since `k ≥ 1`, we have `X^k ∈ (X)`.
    cases k with
    | zero =>
        cases (Nat.not_succ_le_zero 0 hk)
    | succ k =>
        refine Ideal.span_le.2 ?_
        intro y hy
        have hX : (X : Polynomial A) ∈ J := by
          simpa [J] using (Ideal.subset_span (by simp : (X : Polynomial A) ∈ ({X} : Set _)))
        -- `X^(k+1) = X^k * X`.
        have hXpow : (X : Polynomial A) ^ (Nat.succ k) ∈ J := by
          simpa [pow_succ] using (J.mul_mem_left ((X : Polynomial A) ^ k) hX)
        have : y = (X : Polynomial A) ^ (Nat.succ k) := by simpa [I] using hy
        simpa [this] using hXpow
  -- Identify the ideal generated by the class of `X` in the quotient.
  have hJmap :
      J.map (Ideal.Quotient.mk I) =
        Ideal.span ({(Ideal.Quotient.mk I) (X : Polynomial A)} : Set (Polynomial A ⧸ I)) := by
    simp [J, Ideal.map_span]
  -- Rewrite the ideal generated by the adjoined root as the image of `(X)`.
  have hIdeal :
      Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)}
        : Set (AdjoinRoot ((X : Polynomial A) ^ k))) =
        J.map (Ideal.Quotient.mk I) := by
    -- `J.map (mk I)` is the ideal generated by the class of `X` in `A[X]/I`.
    simpa [AdjoinRoot, AdjoinRoot.root, AdjoinRoot.mk, I] using hJmap.symm
  -- Apply the third isomorphism theorem, then identify `A[X]/(X)` with `A` via evaluation at `0`.
  refine (Ideal.quotEquivOfEq hIdeal).trans ?_
  have e₃ :
      (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ J.map (Ideal.Quotient.mk I)) ≃+* Polynomial A ⧸ J := by
    simpa [AdjoinRoot, I] using
      (DoubleQuot.quotQuotEquivQuotOfLE (R := Polynomial A) (I := I) (J := J) hIJ)
  refine e₃.trans ?_
  have hJ0 : J = Ideal.span ({(X : Polynomial A) - C (0 : A)} : Set (Polynomial A)) := by
    simp [J]
  exact
    (Ideal.quotEquivOfEq hJ0).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (R := A) (x := (0 : A))).toRingEquiv

/-- The isomorphism `A[Y]/(Y^k)/(Y) ≃ A` sends scalars to scalars. -/
lemma quotient_span_root_adjoinRoot_X_pow_ringEquiv_base_algebraMap
    (A : Type*) [CommRing A] (k : ℕ) (hk : 1 ≤ k) (a : A) :
    quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
        ((algebraMap A
              (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))) a) =
      a := by
  classical
  -- Rewrite the scalar into the quotient using the `A`-scalar tower.
  have ha :
      (algebraMap A
            (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
              Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))) a =
          Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))
            ((algebraMap A (AdjoinRoot ((X : Polynomial A) ^ k))) a) := by
    -- `algebraMap (AdjoinRoot ..) (quotient)` is the quotient map.
    simpa [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
      using congrArg (fun f => f a)
        (IsScalarTower.algebraMap_eq A (AdjoinRoot ((X : Polynomial A) ^ k))
          (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
            Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _)))
  -- Reduce to the explicit normal form used in the definition, then evaluate at `0`.
  rw [ha]
  -- Replace `algebraMap` into `AdjoinRoot` by `AdjoinRoot.of`.
  simp [AdjoinRoot.algebraMap_eq]
  -- Unfold the ring equivalence and compute it on this scalar.
  -- The remaining goal is an evaluation statement in a polynomial quotient.
  simp [quotient_span_root_adjoinRoot_X_pow_ringEquiv_base, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, AdjoinRoot.of.eq_1, AdjoinRoot.mk, -AdjoinRoot.mk_C]
  -- Finish by reducing to evaluation at `0` of a constant polynomial.
  change
      (quotientSpanXSubCAlgEquiv 0)
          ((Ideal.quotEquivOfEq _)
            ((DoubleQuot.quotQuotEquivQuotOfLE _)
              (DoubleQuot.quotQuotMk (Ideal.span ({(X : Polynomial A) ^ k} : Set (Polynomial A)))
                  (Ideal.span ({(X : Polynomial A)} : Set (Polynomial A))) (C a)))) =
        a
  simp [Ideal.quotEquivOfEq_mk, Polynomial.quotientSpanXSubCAlgEquiv_mk]

/--
For a field `A`, the nilradical of `A[Y]/(Y^k)` (presented as `AdjoinRoot (X^k)`) is the ideal
generated by `Y`, i.e. the span of the adjoined root.
-/
lemma nilradical_adjoinRoot_X_pow_eq_span_root
    (A : Type*) [Field A] (k : ℕ) (hk : 1 ≤ k) :
    nilradical (AdjoinRoot ((X : Polynomial A) ^ k)) =
      Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _) := by
  classical
  let T := AdjoinRoot ((X : Polynomial A) ^ k)
  -- The adjoined root is nilpotent of index `k`.
  have hrootk : (AdjoinRoot.root ((X : Polynomial A) ^ k) : T) ^ k = 0 := by
    -- Evaluate `(X^k)` at the root.
    simpa [Polynomial.eval₂_pow] using (AdjoinRoot.eval₂_root ((X : Polynomial A) ^ k))
  -- First inclusion: `(root) ≤ nilradical`.
  have hspan_le : Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T)
    ≤ nilradical T := by
    intro x hx
    -- Elements in a principal ideal are multiples of the generator.
    rcases Ideal.mem_span_singleton.mp (by simpa using hx) with ⟨a, rfl⟩
    refine (mem_nilradical).2 ?_
    refine ⟨k, ?_⟩
    simp [mul_pow, hrootk]
  -- Second inclusion: `nilradical ≤ (root)` since `(root)` is a prime ideal.
  have hprime :
      (Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T)).IsPrime := by
    -- The quotient by `(root)` is isomorphic to the field `A`, hence a domain.
    let e :=
      quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
    haveI : IsDomain
        (T ⧸ Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T)) :=
      e.toMulEquiv.isDomain A
    exact
      (Ideal.Quotient.isDomain_iff_prime
          (I := Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T))).1
        (by infer_instance)
  have hnil_le :
      nilradical T ≤ Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T) := by
    haveI :
        (Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T)).IsPrime :=
      hprime
    exact nilradical_le_prime (J := Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set T))
  exact le_antisymm hnil_le hspan_le

/--
For fields `A` and `B`, the truncated polynomial rings `A[Y]/(Y^k)` and `B[Y]/(Y^k)` (presented
as `AdjoinRoot (X^k)`) are isomorphic if and only if `A` and `B` are isomorphic.
-/
lemma nonempty_ringEquiv_adjoinRoot_X_pow_iff_nonempty_ringEquiv_base
    (A B : Type*) [Field A] [Field B] (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (AdjoinRoot ((X : Polynomial A) ^ k) ≃+* AdjoinRoot ((X : Polynomial B) ^ k)) ↔
      Nonempty (A ≃+* B) := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Pass to quotients by nilradicals to recover the base fields.
    have hmap :
        nilradical (AdjoinRoot ((X : Polynomial B) ^ k)) =
          (nilradical (AdjoinRoot ((X : Polynomial A) ^ k))).map (e : _ →+* _) := by
      simpa using (nilradical_map_eq_of_ringEquiv e).symm
    let eQuot :
        (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))) ≃+*
        (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) :=
      Ideal.quotientEquiv (I := nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))
        (J := nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) e hmap
    have hnilA :
        nilradical (AdjoinRoot ((X : Polynomial A) ^ k)) =
          Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _) :=
      nilradical_adjoinRoot_X_pow_eq_span_root (A := A) (k := k) (hk := hk)
    have hnilB :
        nilradical (AdjoinRoot ((X : Polynomial B) ^ k)) =
          Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _) :=
      nilradical_adjoinRoot_X_pow_eq_span_root (A := B) (k := k) (hk := hk)
    let eA :
        (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))) ≃+*
          A :=
      (Ideal.quotEquivOfEq hnilA).trans
        (quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk))
    let eB :
        (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) ≃+*
          B :=
      (Ideal.quotEquivOfEq hnilB).trans
        (quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk))
    refine ⟨eA.symm.trans (eQuot.trans eB)⟩
  · rintro ⟨e⟩
    refine ⟨AdjoinRoot.mapRingEquiv e ((X : Polynomial A) ^ k) ((X : Polynomial B) ^ k) ?_⟩
    exact Associated.of_eq (by simp)

/--
For `𝕜`-algebra fields `A` and `B`, the truncated polynomial rings `A[Y]/(Y^k)` and `B[Y]/(Y^k)`
(presented as `AdjoinRoot (X^k)`) are isomorphic as `𝕜`-algebras if and only if `A` and `B` are
isomorphic as `𝕜`-algebras.
-/
lemma nonempty_algEquiv_adjoinRoot_X_pow_iff_nonempty_algEquiv_base
    (A B : Type*) [Field A] [Field B] [Algebra 𝕜 A] [Algebra 𝕜 B] (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (AdjoinRoot ((X : Polynomial A) ^ k) ≃ₐ[𝕜] AdjoinRoot ((X : Polynomial B) ^ k)) ↔
      Nonempty (A ≃ₐ[𝕜] B) := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Pass to quotients by nilradicals to recover the base fields.
    have hmap :
        nilradical (AdjoinRoot ((X : Polynomial B) ^ k)) =
          (nilradical (AdjoinRoot ((X : Polynomial A) ^ k))).map (e.toRingEquiv : _ →+* _) := by
      simpa using (nilradical_map_eq_of_ringEquiv e.toRingEquiv).symm
    let eQuotRing :
        (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))) ≃+*
        (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) :=
      Ideal.quotientEquiv
        (I := nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))
        (J := nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))
        e.toRingEquiv hmap
    have hcommQuot :
        ∀ x : 𝕜,
          eQuotRing ((algebraMap 𝕜 (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) x) =
            (algebraMap 𝕜 (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) x := by
      intro x
      have hxA :
          (algebraMap 𝕜
                (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                  nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) x =
              Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))
                ((algebraMap 𝕜 (AdjoinRoot ((X : Polynomial A) ^ k))) x) := by
        -- Use the scalar tower `𝕜 → AdjoinRoot → quotient`.
        simp
      have hxB :
          (algebraMap 𝕜
                (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                  nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) x =
              Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))
                ((algebraMap 𝕜 (AdjoinRoot ((X : Polynomial B) ^ k))) x) := by
        simp
      -- Reduce to the formula for `Ideal.quotientEquiv` on quotient maps.
      -- Then use `e.commutes` to pass through scalars.
      calc
        eQuotRing
              ((algebraMap 𝕜
                    (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                      nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) x) =
        eQuotRing
              (Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))
                ((algebraMap 𝕜 (AdjoinRoot ((X : Polynomial A) ^ k))) x)) := by
          rw [hxA]
        _ =
            Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))
              (e.toRingEquiv ((algebraMap 𝕜 (AdjoinRoot ((X : Polynomial A) ^ k))) x)) := by
          simp [eQuotRing]
        _ =
            Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))
              ((algebraMap 𝕜 (AdjoinRoot ((X : Polynomial B) ^ k))) x) := by
          exact
            congrArg
              (Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial B) ^ k))))
              (e.commutes x)
        _ =
            (algebraMap 𝕜
                  (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                    nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) x := by
          rw [hxB]
    let eQuot :
      (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))) ≃ₐ[𝕜]
      (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) :=
      AlgEquiv.ofRingEquiv (f := eQuotRing) hcommQuot
    have hnilA :
        nilradical (AdjoinRoot ((X : Polynomial A) ^ k)) =
          Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _) :=
      nilradical_adjoinRoot_X_pow_eq_span_root (A := A) (k := k) (hk := hk)
    have hnilB :
        nilradical (AdjoinRoot ((X : Polynomial B) ^ k)) =
          Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _) :=
      nilradical_adjoinRoot_X_pow_eq_span_root (A := B) (k := k) (hk := hk)
    let eA_ring :
        (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))) ≃+*
          A :=
      (Ideal.quotEquivOfEq hnilA).trans
        (quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk))
    let eB_ring :
        (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) ≃+*
          B :=
      (Ideal.quotEquivOfEq hnilB).trans
        (quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk))
    have hcommA_overA :
        ∀ a : A, eA_ring ((algebraMap A _) a) = a := by
      intro a
      have haNil :
          (algebraMap A
                (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                  nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) a =
              Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))
                ((algebraMap A (AdjoinRoot ((X : Polynomial A) ^ k))) a) := by
        simpa [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
          using congrArg (fun f => f a)
          (IsScalarTower.algebraMap_eq A (AdjoinRoot ((X : Polynomial A) ^ k))
          (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))))
      have haSpan :
          (algebraMap A
                (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                  Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))) a =
              Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))
                ((algebraMap A (AdjoinRoot ((X : Polynomial A) ^ k))) a) := by
        simpa [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
          using congrArg (fun f => f a)
            (IsScalarTower.algebraMap_eq A (AdjoinRoot ((X : Polynomial A) ^ k))
              (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _)))
      have hstep :
          quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
              ((Ideal.quotEquivOfEq hnilA)
                ((algebraMap A
                      (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                        nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) a)) =
            a := by
        -- Move from the nilradical quotient to the quotient by `(Y)`.
        have haSpan' :
            (algebraMap A
                  (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                    Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))) a =
                Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))
                  ((AdjoinRoot.of ((X : Polynomial A) ^ k)) a) := by
          simpa [AdjoinRoot.algebraMap_eq] using haSpan
        calc
          quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
                ((Ideal.quotEquivOfEq hnilA)
                  ((algebraMap A
                        (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                          nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) a)) =
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
                ((Ideal.quotEquivOfEq hnilA)
                  (Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))
                    ((algebraMap A (AdjoinRoot ((X : Polynomial A) ^ k))) a))) := by
                simp [haNil]
          _ =
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
                (Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))
                  ((algebraMap A (AdjoinRoot ((X : Polynomial A) ^ k))) a)) := by
                simp [Ideal.quotEquivOfEq_mk]
          _ =
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
                ((algebraMap A
                    (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                      Ideal.span ({AdjoinRoot.root ((X : Polynomial A) ^ k)} : Set _))) a) := by
                simp [haSpan']
          _ = a :=
            quotient_span_root_adjoinRoot_X_pow_ringEquiv_base_algebraMap (A := A) (k := k) (hk := hk) a
      -- `eA_ring` is the composition of the two maps above.
      change
          quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := A) (k := k) (hk := hk)
              ((Ideal.quotEquivOfEq hnilA)
                ((algebraMap A
                      (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                        nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) a)) =
            a
      exact hstep
    have hcommB_overB :
        ∀ b : B, eB_ring ((algebraMap B _) b) = b := by
      intro b
      have hbNil :
          (algebraMap B
                (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                  nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) b =
              Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))
                ((algebraMap B (AdjoinRoot ((X : Polynomial B) ^ k))) b) := by
        simpa [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
          using congrArg (fun f => f b)
            (IsScalarTower.algebraMap_eq B (AdjoinRoot ((X : Polynomial B) ^ k))
              (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))))
      have hbSpan :
          (algebraMap B
                (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                  Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _))) b =
              Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _))
                ((algebraMap B (AdjoinRoot ((X : Polynomial B) ^ k))) b) := by
        simpa [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
          using congrArg (fun f => f b)
            (IsScalarTower.algebraMap_eq B (AdjoinRoot ((X : Polynomial B) ^ k))
              (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _)))
      have hstep :
          quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk)
              ((Ideal.quotEquivOfEq hnilB)
                ((algebraMap B
                      (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                        nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) b)) =
            b := by
        have hbSpan' :
            (algebraMap B
                  (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                    Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _))) b =
                Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _))
                  ((AdjoinRoot.of ((X : Polynomial B) ^ k)) b) := by
          simpa [AdjoinRoot.algebraMap_eq] using hbSpan
        calc
          quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk)
                ((Ideal.quotEquivOfEq hnilB)
                  ((algebraMap B
                        (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                          nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) b)) =
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk)
                ((Ideal.quotEquivOfEq hnilB)
                  (Ideal.Quotient.mk (nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))
                    ((algebraMap B (AdjoinRoot ((X : Polynomial B) ^ k))) b))) := by
                simp [hbNil]
          _ =
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk)
                (Ideal.Quotient.mk (Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _))
                  ((algebraMap B (AdjoinRoot ((X : Polynomial B) ^ k))) b)) := by
                simp [Ideal.quotEquivOfEq_mk]
          _ =
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk)
                ((algebraMap B
                    (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                      Ideal.span ({AdjoinRoot.root ((X : Polynomial B) ^ k)} : Set _))) b) := by
                simp [hbSpan']
          _ = b :=
              quotient_span_root_adjoinRoot_X_pow_ringEquiv_base_algebraMap (A := B) (k := k) (hk := hk) b
      change
          quotient_span_root_adjoinRoot_X_pow_ringEquiv_base (A := B) (k := k) (hk := hk)
              ((Ideal.quotEquivOfEq hnilB)
                ((algebraMap B
                      (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                        nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) b)) =
            b
      exact hstep
    have hcommA :
        ∀ x : 𝕜, eA_ring ((algebraMap 𝕜 _) x) = (algebraMap 𝕜 A) x := by
      intro x
      -- Use the scalar tower `𝕜 → A → ...`.
      have hx :
          (algebraMap 𝕜
                (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                  nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) x =
              (algebraMap A
                  (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                    nilradical (AdjoinRoot ((X : Polynomial A) ^ k)))) ((algebraMap 𝕜 A) x) := by
        simpa [RingHom.comp_apply]
          using congrArg (fun f => f x)
            (IsScalarTower.algebraMap_eq 𝕜 A
              (AdjoinRoot ((X : Polynomial A) ^ k) ⧸
                nilradical (AdjoinRoot ((X : Polynomial A) ^ k))))
      -- Now apply the `A`-compatibility proved above.
      simpa [hx] using hcommA_overA ((algebraMap 𝕜 A) x)
    have hcommB :
        ∀ x : 𝕜, eB_ring ((algebraMap 𝕜 _) x) = (algebraMap 𝕜 B) x := by
      intro x
      have hx :
          (algebraMap 𝕜
                (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                  nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) x =
              (algebraMap B
                  (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                    nilradical (AdjoinRoot ((X : Polynomial B) ^ k)))) ((algebraMap 𝕜 B) x) := by
        simpa [RingHom.comp_apply]
          using congrArg (fun f => f x)
            (IsScalarTower.algebraMap_eq 𝕜 B
              (AdjoinRoot ((X : Polynomial B) ^ k) ⧸
                nilradical (AdjoinRoot ((X : Polynomial B) ^ k))))
      simpa [hx] using hcommB_overB ((algebraMap 𝕜 B) x)
    let eA :
        (AdjoinRoot ((X : Polynomial A) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial A) ^ k))) ≃ₐ[𝕜]
          A :=
      AlgEquiv.ofRingEquiv (f := eA_ring) hcommA
    let eB :
        (AdjoinRoot ((X : Polynomial B) ^ k) ⧸ nilradical (AdjoinRoot ((X : Polynomial B) ^ k))) ≃ₐ[𝕜]
          B :=
      AlgEquiv.ofRingEquiv (f := eB_ring) hcommB
    exact ⟨eA.symm.trans (eQuot.trans eB)⟩
  · rintro ⟨e⟩
    refine ⟨AdjoinRoot.mapAlgEquiv e ((X : Polynomial A) ^ k) ((X : Polynomial B) ^ k) ?_⟩
    exact Associated.of_eq (by simp)

/--
Theorem 1.8.
Let `𝕜` be a field. Let `P₁` and `P₂` be irreducible polynomials over `𝕜` and let `k` be a
positive integer. If `P₁` and `P₂` are separable (i.e. `Pᵢ' ≠ 0`), then the local rings
`𝕜[X]⧸(P₁ ^ k)` and `𝕜[X]⧸(P₂ ^ k)` are isomorphic if and only if their residue fields `𝕜[X]⧸(P₁)`
and `𝕜[X]⧸(P₂)` are isomorphic.
-/
theorem nonempty_ringEquiv_adjoinRoot_pow_iff_nonempty_ringEquiv_adjoinRoot
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (hP₁' : P₁.derivative ≠ 0) (hP₂' : P₂.derivative ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (AdjoinRoot (P₁ ^ k) ≃+* AdjoinRoot (P₂ ^ k)) ↔
      Nonempty (AdjoinRoot P₁ ≃+* AdjoinRoot P₂) := by
  classical
  haveI : Fact (Irreducible P₁) := ⟨hP₁⟩
  haveI : Fact (Irreducible P₂) := ⟨hP₂⟩
  constructor
  · rintro ⟨ePow⟩
    -- Use Corollary 1.4 to put a `𝕜`-compatible algebra tower structure on each `AdjoinRoot (Pᵢ^k)`.
    obtain ⟨S₁, hS₁⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk
    obtain ⟨S₂, hS₂⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk
    rcases hS₁ with ⟨eS₁⟩
    rcases hS₂ with ⟨eS₂⟩
    let f₁ : AdjoinRoot P₁ →ₐ[𝕜] AdjoinRoot (P₁ ^ k) := S₁.val.comp eS₁.toAlgHom
    let f₂ : AdjoinRoot P₂ →ₐ[𝕜] AdjoinRoot (P₂ ^ k) := S₂.val.comp eS₂.toAlgHom
    letI : Algebra (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) := (f₁.toRingHom).toAlgebra
    letI : Algebra (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) := (f₂.toRingHom).toAlgebra
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₁.commutes x).symm
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₂.commutes x).symm
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk with
      ⟨e₁, -⟩
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk with
      ⟨e₂, -⟩
    let r₁ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃+* AdjoinRoot (P₁ ^ k) :=
      e₁.toRingEquiv
    let r₂ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k) ≃+* AdjoinRoot (P₂ ^ k) :=
      e₂.toRingEquiv
    let eTrunc :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃+*
          AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k) :=
      r₁.trans (ePow.trans r₂.symm)
    -- Recover the residue fields from the truncated models.
    exact
      (nonempty_ringEquiv_adjoinRoot_X_pow_iff_nonempty_ringEquiv_base
            (A := AdjoinRoot P₁) (B := AdjoinRoot P₂) (k := k) hk).1
        ⟨eTrunc⟩
  · rintro ⟨eBase⟩
    obtain ⟨S₁, hS₁⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk
    obtain ⟨S₂, hS₂⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk
    rcases hS₁ with ⟨eS₁⟩
    rcases hS₂ with ⟨eS₂⟩
    let f₁ : AdjoinRoot P₁ →ₐ[𝕜] AdjoinRoot (P₁ ^ k) := S₁.val.comp eS₁.toAlgHom
    let f₂ : AdjoinRoot P₂ →ₐ[𝕜] AdjoinRoot (P₂ ^ k) := S₂.val.comp eS₂.toAlgHom
    letI : Algebra (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) := (f₁.toRingHom).toAlgebra
    letI : Algebra (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) := (f₂.toRingHom).toAlgebra
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₁.commutes x).symm
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₂.commutes x).symm
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk with
      ⟨e₁, -⟩
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk with
      ⟨e₂, -⟩
    let r₁ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃+* AdjoinRoot (P₁ ^ k) :=
      e₁.toRingEquiv
    let r₂ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k) ≃+* AdjoinRoot (P₂ ^ k) :=
      e₂.toRingEquiv
    have hTrunc :
        Nonempty
          (AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃+*
            AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k)) :=
      (nonempty_ringEquiv_adjoinRoot_X_pow_iff_nonempty_ringEquiv_base
            (A := AdjoinRoot P₁) (B := AdjoinRoot P₂) (k := k) hk).2
        ⟨eBase⟩
    rcases hTrunc with ⟨eTrunc⟩
    exact ⟨r₁.symm.trans (eTrunc.trans r₂)⟩

/--
Proposition 1.10.
Let `P₁` and `P₂` be two irreducible polynomials over `𝕜` and `k` a positive integer. If `P₁` and
`P₂` are separable (i.e. `Pᵢ' ≠ 0`), then the local rings `𝕜[X]⧸(P₁ ^ k)` and `𝕜[X]⧸(P₂ ^ k)` are
isomorphic as `𝕜`-algebras if and only if their residue fields `𝕜[X]⧸(P₁)` and `𝕜[X]⧸(P₂)` are
isomorphic as `𝕜`-algebras.
-/
theorem nonempty_algEquiv_adjoinRoot_pow_iff_nonempty_algEquiv_adjoinRoot
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (hP₁' : P₁.derivative ≠ 0) (hP₂' : P₂.derivative ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (AdjoinRoot (P₁ ^ k) ≃ₐ[𝕜] AdjoinRoot (P₂ ^ k)) ↔
      Nonempty (AdjoinRoot P₁ ≃ₐ[𝕜] AdjoinRoot P₂) := by
  classical
  haveI : Fact (Irreducible P₁) := ⟨hP₁⟩
  haveI : Fact (Irreducible P₂) := ⟨hP₂⟩
  constructor
  · rintro ⟨ePow⟩
    -- Use Corollary 1.4 to put a `𝕜`-compatible algebra tower structure on each `AdjoinRoot (Pᵢ^k)`.
    obtain ⟨S₁, hS₁⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk
    obtain ⟨S₂, hS₂⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk
    rcases hS₁ with ⟨eS₁⟩
    rcases hS₂ with ⟨eS₂⟩
    let f₁ : AdjoinRoot P₁ →ₐ[𝕜] AdjoinRoot (P₁ ^ k) := S₁.val.comp eS₁.toAlgHom
    let f₂ : AdjoinRoot P₂ →ₐ[𝕜] AdjoinRoot (P₂ ^ k) := S₂.val.comp eS₂.toAlgHom
    letI : Algebra (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) := (f₁.toRingHom).toAlgebra
    letI : Algebra (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) := (f₂.toRingHom).toAlgebra
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₁.commutes x).symm
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₂.commutes x).symm
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk with
      ⟨e₁, -⟩
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk with
      ⟨e₂, -⟩
    let r₁ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃ₐ[𝕜] AdjoinRoot (P₁ ^ k) :=
      AlgEquiv.restrictScalars 𝕜 e₁
    let r₂ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k) ≃ₐ[𝕜] AdjoinRoot (P₂ ^ k) :=
      AlgEquiv.restrictScalars 𝕜 e₂
    let eTrunc :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃ₐ[𝕜]
          AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k) :=
      r₁.trans (ePow.trans r₂.symm)
    exact
      (nonempty_algEquiv_adjoinRoot_X_pow_iff_nonempty_algEquiv_base
            (𝕜 := 𝕜) (A := AdjoinRoot P₁) (B := AdjoinRoot P₂) (k := k) hk).1
        ⟨eTrunc⟩
  · rintro ⟨eBase⟩
    obtain ⟨S₁, hS₁⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk
    obtain ⟨S₂, hS₂⟩ :=
      exists_residueField_algEquiv_subalgebra_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk
    rcases hS₁ with ⟨eS₁⟩
    rcases hS₂ with ⟨eS₂⟩
    let f₁ : AdjoinRoot P₁ →ₐ[𝕜] AdjoinRoot (P₁ ^ k) := S₁.val.comp eS₁.toAlgHom
    let f₂ : AdjoinRoot P₂ →ₐ[𝕜] AdjoinRoot (P₂ ^ k) := S₂.val.comp eS₂.toAlgHom
    letI : Algebra (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) := (f₁.toRingHom).toAlgebra
    letI : Algebra (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) := (f₂.toRingHom).toAlgebra
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₁) (AdjoinRoot (P₁ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₁.commutes x).symm
    haveI : IsScalarTower 𝕜 (AdjoinRoot P₂) (AdjoinRoot (P₂ ^ k)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using (f₂.commutes x).symm
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₁) hP₁ hP₁' k hk with
      ⟨e₁, -⟩
    rcases
        exists_algEquiv_adjoinRoot_X_pow_to_adjoinRoot_pow (𝕜 := 𝕜) (P := P₂) hP₂ hP₂' k hk with
      ⟨e₂, -⟩
    let r₁ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃ₐ[𝕜] AdjoinRoot (P₁ ^ k) :=
      AlgEquiv.restrictScalars 𝕜 e₁
    let r₂ :
        AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k) ≃ₐ[𝕜] AdjoinRoot (P₂ ^ k) :=
      AlgEquiv.restrictScalars 𝕜 e₂
    have hTrunc :
        Nonempty
          (AdjoinRoot ((X : Polynomial (AdjoinRoot P₁)) ^ k) ≃ₐ[𝕜]
            AdjoinRoot ((X : Polynomial (AdjoinRoot P₂)) ^ k)) :=
      (nonempty_algEquiv_adjoinRoot_X_pow_iff_nonempty_algEquiv_base
            (𝕜 := 𝕜) (A := AdjoinRoot P₁) (B := AdjoinRoot P₂) (k := k) hk).2
        ⟨eBase⟩
    rcases hTrunc with ⟨eTrunc⟩
    exact ⟨r₁.symm.trans (eTrunc.trans r₂)⟩

end SomeLocalRings
