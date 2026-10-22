/-
Authors: Liang Xiao, Haochen Ju, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/README.md (Contributors).
-/

import Mathlib
import OnSomeLocalRings_Maassaran_2025.section02_part1

namespace SomeLocalRings

variable {𝕜 : Type*} [Field 𝕜]
variable {A B : Type*} [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]

/--
If `p.comp q = r * s`, then every root of `s` maps to a root of `p` by evaluation of `q`.

This is the basic “root mapping” step used in Proposition 2.6.
-/
lemma isRoot_aeval_of_comp_eq_mul
    {K : Type*} [Field K] [Algebra 𝕜 K]
    {p q r s : Polynomial 𝕜} (h : p.comp q = r * s) {α : K}
    (hs : (s.map (algebraMap 𝕜 K)).IsRoot α) :
    ((p.map (algebraMap 𝕜 K)).IsRoot ((Polynomial.aeval α) q)) := by
  have hs0 : (Polynomial.aeval α) s = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hs
  have h' :
      (Polynomial.aeval ((Polynomial.aeval α) q)) p =
        (Polynomial.aeval α) r * (Polynomial.aeval α) s := by
    simpa [Polynomial.aeval_comp, map_mul] using
      congrArg (fun t : Polynomial 𝕜 => (Polynomial.aeval α) t) h
  have hp0 : (Polynomial.aeval ((Polynomial.aeval α) q)) p = 0 := by
    simpa [hs0] using h'.trans rfl
  have hp0' :
      Polynomial.eval₂ (algebraMap 𝕜 K) ((Polynomial.aeval α) q) p = 0 := by
    simpa [Polynomial.aeval_def] using hp0
  have hp0'' :
      Polynomial.eval ((Polynomial.aeval α) q) (p.map (algebraMap 𝕜 K)) = 0 := by
    simpa [Polynomial.eval_map] using hp0'
  simpa [Polynomial.IsRoot] using hp0''

/--
`𝕜[X]⧸(P)` is finite-dimensional over `𝕜`, using the monic associate of `P`.

This is a local helper for Proposition 2.6.
-/
lemma finiteDimensional_quotient_span_of_ne_zero (P : Polynomial 𝕜) (hP0 : P ≠ 0) :
    FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P} : Set (Polynomial 𝕜))) := by
  classical
  let Pm : Polynomial 𝕜 := P * Polynomial.C (P.leadingCoeff)⁻¹
  have hPm_monic : Pm.Monic := by
    simpa [Pm] using (Polynomial.monic_mul_leadingCoeff_inv (p := P) hP0)
  have hPm_isUnit : IsUnit (Polynomial.C (P.leadingCoeff)⁻¹) := by
    have hne : (P.leadingCoeff)⁻¹ ≠ 0 := by
      exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hP0)
    exact (Polynomial.isUnit_C).2 ((isUnit_iff_ne_zero).2 hne)
  have hI :
      (Ideal.span ({P} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
        Ideal.span ({Pm} : Set (Polynomial 𝕜)) := by
    have hassoc : Associated P Pm := by
      refine ⟨hPm_isUnit.unit, ?_⟩
      simp [Pm]
    exact (Ideal.span_singleton_eq_span_singleton).2 hassoc
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({Pm} : Set (Polynomial 𝕜))) :=
    (Polynomial.Monic.finite_quotient (R := 𝕜) (g := Pm) hPm_monic)
  let e :
      (Polynomial 𝕜 ⧸ Ideal.span ({Pm} : Set (Polynomial 𝕜))) ≃ₐ[𝕜]
        (Polynomial 𝕜 ⧸ Ideal.span ({P} : Set (Polynomial 𝕜))) :=
    Ideal.quotientEquivAlgOfEq (R₁ := 𝕜) (A := Polynomial 𝕜)
      (I := Ideal.span ({Pm} : Set (Polynomial 𝕜)))
      (J := Ideal.span ({P} : Set (Polynomial 𝕜))) hI.symm
  exact Module.Finite.equiv (R := 𝕜)
    (M := Polynomial 𝕜 ⧸ Ideal.span ({Pm} : Set (Polynomial 𝕜)))
    (N := Polynomial 𝕜 ⧸ Ideal.span ({P} : Set (Polynomial 𝕜))) e.toLinearEquiv

/--
Conversely, if `f_{X,n}` is an isomorphism and `n > 1`, then `S_f` is coprime to `P₂`.
-/
lemma prop2_5_coprime_of_exists_ringEquiv
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (fX : Polynomial 𝕜 →+* Polynomial 𝕜)
    (Sf : Polynomial 𝕜) (hSf : fX P₁ = Sf * P₂)
    (n : ℕ) (hn : 1 < n)
    (hIJn :
      (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) :
    (∃ e :
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) ≃+*
            (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
        e.toRingHom =
          Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn) →
      IsCoprime Sf P₂ := by
  intro hexists
  classical
  rcases hexists with ⟨e, he⟩
  let fXn :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) →+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) :=
    Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
      (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn
  have hinj : Function.Injective fXn := by
    have hxe : fXn = e.toRingHom := by
      simpa [fXn] using he.symm
    intro x y hxy
    apply e.injective
    have : e.toRingHom x = e.toRingHom y := by
      simpa [hxe] using hxy
    simpa using this
  by_contra hcop
  have hP₂_dvd : P₂ ∣ Sf := by
    have hnot : ¬ IsCoprime P₂ Sf := by
      intro h'
      exact hcop ((isCoprime_comm).1 h')
    exact (hP₂.dvd_iff_not_isCoprime).2 hnot
  rcases hP₂_dvd with ⟨S0, rfl⟩
  -- Construct a nonzero element in the kernel using the extra `P₂`-divisibility of `fX(P₁)`.
  have hP₂sq : P₂ ^ 2 ∣ fX P₁ := by
    refine ⟨S0, ?_⟩
    simp [hSf, pow_two, mul_left_comm, mul_comm]
  have hle : n ≤ 2 * (n - 1) := by
    omega
  have hP₂n : P₂ ^ n ∣ fX (P₁ ^ (n - 1)) := by
    have hpow : P₂ ^ (2 * (n - 1)) ∣ fX (P₁ ^ (n - 1)) := by
      have hpow' : (P₂ ^ 2) ^ (n - 1) ∣ (fX P₁) ^ (n - 1) :=
        pow_dvd_pow_of_dvd hP₂sq (n - 1)
      simpa [pow_mul, map_pow] using hpow'
    exact dvd_trans (pow_dvd_pow P₂ hle) hpow
  have hker :
      fXn (Ideal.Quotient.mk (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (P₁ ^ (n - 1))) =
        0 := by
    have hmem :
        fX (P₁ ^ (n - 1)) ∈ (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) :=
      (Ideal.mem_span_singleton).2 hP₂n
    -- Reduce to ideal membership.
    have :
        Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) (fX (P₁ ^ (n - 1))) =
          0 := (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    have hf :
        fXn (Ideal.Quotient.mk (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) (P₁ ^ (n - 1))) =
          Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) (fX (P₁ ^ (n - 1))) := by
      simp [fXn]
    exact hf.trans this
  have hnonzero :
      Ideal.Quotient.mk (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) (P₁ ^ (n - 1)) ≠ 0 := by
    intro hz
    have hmem :
        P₁ ^ (n - 1) ∈ (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) :=
      (Ideal.Quotient.eq_zero_iff_mem).1 hz
    have hdvd : P₁ ^ n ∣ P₁ ^ (n - 1) := (Ideal.mem_span_singleton).1 hmem
    have hne : ¬ n ≤ n - 1 := by omega
    have : n ≤ n - 1 := (pow_dvd_pow_iff hP₁.ne_zero hP₁.not_isUnit).1 hdvd
    exact hne this
  have : Ideal.Quotient.mk (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) (P₁ ^ (n - 1)) = 0 := by
    have hx :
        fXn (Ideal.Quotient.mk (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) (P₁ ^ (n - 1))) =
          fXn 0 := by
      calc
        fXn (Ideal.Quotient.mk (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) (P₁ ^ (n - 1))) = 0 :=
          hker
        _ = fXn 0 := by simp
    exact hinj hx
  exact hnonzero this

/--
Proposition 2.5.
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. Let
`f : 𝕜[X]/(P₁) → 𝕜[X]/(P₂)` be a ring isomorphism stabilizing `𝕜`, and let `S_f` and `f_{X,n}`
be as in Proposition 2.4. For `n > 1`, `S_f` is prime to `P₂` if and only if
`f_{X,n} : 𝕜[X]/(P₁^n) → 𝕜[X]/(P₂^n)` is an isomorphism.
-/
theorem proposition_2_5
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (σ_f : 𝕜 ≃+* 𝕜)
    (hf :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f)
    (σX : Polynomial 𝕜 ≃+* Polynomial 𝕜)
    (hσX :
      σX Polynomial.X = Polynomial.X ∧
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
          σX.toRingHom σ_f)
    (Qf : Polynomial 𝕜) (hQf : Qf.natDegree < P₁.natDegree ∧ 1 ≤ Qf.natDegree)
    (fX : Polynomial 𝕜 →+* Polynomial 𝕜) (hfX_X : fX Polynomial.X = Qf)
    (hfX :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜) fX σ_f)
    (hfX_def : ∀ P : Polynomial 𝕜, fX P = (σX P).comp Qf)
    (hIJ :
      (Ideal.span ({P₁} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (hf_ind :
      Ideal.quotientMap (I := Ideal.span ({P₁} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂} : Set (Polynomial 𝕜))) fX hIJ =
        f.toRingHom)
    (Sf : Polynomial 𝕜) (hSf : (σX P₁).comp Qf = Sf * P₂)
    (n : ℕ) (hn : 1 < n)
    (hIJn :
      (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) :
    IsCoprime Sf P₂ ↔
      ∃ e :
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) ≃+*
            (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
        e.toRingHom =
          Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn := by
  have _ := hσX
  have _ := hQf
  have _ := hfX_X
  constructor
  · intro hcop
    have hfXP₁ : fX P₁ = Sf * P₂ := by
      calc
        fX P₁ = (σX P₁).comp Qf := hfX_def P₁
        _ = Sf * P₂ := by simpa [mul_comm] using hSf
    exact
      prop2_5_exists_ringEquiv_of_isCoprime (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf fX hfX hIJ
        hf_ind Sf hfXP₁ n hIJn hcop
  · intro hexists
    have hfXP₁ : fX P₁ = Sf * P₂ := by
      calc
        fX P₁ = (σX P₁).comp Qf := hfX_def P₁
        _ = Sf * P₂ := by simpa [mul_comm] using hSf
    exact
      prop2_5_coprime_of_exists_ringEquiv (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ fX Sf hfXP₁ n hn hIJn
        hexists

/--
Proposition 2.6.
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. Let
`f : 𝕜[X]/(P₁) ≃+* 𝕜[X]/(P₂)` be a ring isomorphism stabilizing `𝕜`, and let `σ_f^X` and `Q_f`
be as in Proposition 2.4.

1. If `α` is a root of `P₂`, then `Q_f(α)` is a root of `σ_f^X(P₁)`.
2. The map `α ↦ Q_f(α)` gives a bijection between the roots of `P₂` and the roots of
   `σ_f^X(P₁)`.
-/
theorem proposition_2_6
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (σ_f : 𝕜 ≃+* 𝕜)
    (hf :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f)
    (σX : Polynomial 𝕜 ≃+* Polynomial 𝕜)
    (hσX :
      σX Polynomial.X = Polynomial.X ∧
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
          σX.toRingHom σ_f)
    (Qf Sf : Polynomial 𝕜) (hSf : (σX P₁).comp Qf = Sf * P₂) :
    (∀ {K : Type*} [Field K] [Algebra 𝕜 K] {α : K},
        (P₂.map (algebraMap 𝕜 K)).IsRoot α →
          ((σX P₁).map (algebraMap 𝕜 K)).IsRoot ((Polynomial.aeval α) Qf)) ∧
      ∃ e :
          {α : AlgebraicClosure 𝕜 // (P₂.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot α} ≃
            {β : AlgebraicClosure 𝕜 //
                ((σX P₁).map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot β},
        ∀ a, (e a).1 = ((Polynomial.aeval a.1) Qf) := by
  classical
  refine ⟨?_, ?_⟩
  · intro K _ _ α hα
    exact isRoot_aeval_of_comp_eq_mul (𝕜 := 𝕜) (p := σX P₁) (q := Qf) (r := Sf) (s := P₂) hSf hα
  · classical
    -- Work with the quotient rings `𝕜[X]/(σX P₁)`
    -- and `𝕜[X]/(P₂)` and the substitution map `X ↦ Qf`.
    let I1 : Ideal (Polynomial 𝕜) := Ideal.span ({σX P₁} : Set (Polynomial 𝕜))
    let I2 : Ideal (Polynomial 𝕜) := Ideal.span ({P₂} : Set (Polynomial 𝕜))
    let compQ : Polynomial 𝕜 →+* Polynomial 𝕜 := Polynomial.compRingHom Qf
    have hIJ : (I1 : Ideal (Polynomial 𝕜)) ≤ Ideal.comap compQ I2 := by
      refine (Ideal.span_singleton_le_iff_mem (I := Ideal.comap compQ I2) (x := σX P₁)).2 ?_
      refine (Ideal.mem_span_singleton).2 ?_
      refine ⟨Sf, ?_⟩
      simpa [I1, I2, compQ, mul_comm] using hSf
    have hP₁σ : Irreducible (σX P₁) := hP₁.map σX
    haveI : I1.IsMaximal := by
      letI : Fact (Irreducible (σX P₁)) := ⟨hP₁σ⟩
      simpa [I1] using (AdjoinRoot.span_maximal_of_irreducible (K := 𝕜) (f := σX P₁))
    haveI : I2.IsMaximal := by
      letI : Fact (Irreducible P₂) := ⟨hP₂⟩
      simpa [I2] using (AdjoinRoot.span_maximal_of_irreducible (K := 𝕜) (f := P₂))
    -- Use the induced field structures on the quotient rings.
    letI : Field (Polynomial 𝕜 ⧸ I1) := Ideal.Quotient.field (I := I1)
    letI : Field (Polynomial 𝕜 ⧸ I2) := Ideal.Quotient.field (I := I2)
    let mk₁ : Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ I1) := Ideal.Quotient.mk I1
    let mk₂ : Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ I2) := Ideal.Quotient.mk I2
    let ψ : (Polynomial 𝕜 ⧸ I1) →+* (Polynomial 𝕜 ⧸ I2) :=
      Ideal.quotientMap (I := I1) I2 compQ hIJ
    have hψ :
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜 ⧸ I1) (B := Polynomial 𝕜 ⧸ I2)
          ψ (RingEquiv.refl 𝕜) := by
      intro a
      -- `ψ` fixes constants since `compQ` does.
      have hmk₁ : mk₁ (Polynomial.C a) = algebraMap 𝕜 (Polynomial 𝕜 ⧸ I1) a := by
        simpa [mk₁, Polynomial.algebraMap_eq] using
          (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜) (I := I1) a)
      have hmk₂ : mk₂ (Polynomial.C a) = algebraMap 𝕜 (Polynomial 𝕜 ⧸ I2) a := by
        simpa [mk₂, Polynomial.algebraMap_eq] using
          (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜) (I := I2) a)
      have hcalc : ψ (mk₁ (Polynomial.C a)) = mk₂ (Polynomial.C a) := by
        have :
            ψ (mk₁ (Polynomial.C a)) = mk₂ (compQ (Polynomial.C a)) := by
          simp [ψ, mk₁, mk₂]
        simpa [compQ] using this
      -- Translate back to the `algebraMap` form.
      simpa [RingHom.StabilizesBaseFieldWith, hmk₁, hmk₂] using hcalc
    have hinj : Function.Injective ψ := by
      exact RingHom.injective ψ
    haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ I1) := by
      simpa [I1] using
        (finiteDimensional_quotient_span_of_ne_zero (𝕜 := 𝕜) (P := σX P₁) hP₁σ.ne_zero)
    haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ I2) := by
      simpa [I2] using
        (finiteDimensional_quotient_span_of_ne_zero (𝕜 := 𝕜) (P := P₂) hP₂.ne_zero)
    have hσX_eq : σX = Polynomial.mapEquiv σ_f :=
      polynomialRingEquiv_eq_mapEquiv_of_fix_X_of_stabilizesBaseFieldWith (𝕜 := 𝕜) σ_f σX
        hσX.1 hσX.2
    have hdeg₁₂ : P₁.natDegree = P₂.natDegree :=
      prop2_4_natDegree_eq (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf
    have hdegσ : (σX P₁).natDegree = P₁.natDegree := by
      simp [hσX_eq, Polynomial.mapEquiv_apply]
    have hfinrank : Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I1) =
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I2) := by
      have hdeg : (σX P₁).natDegree = P₂.natDegree := hdegσ.trans hdeg₁₂
      simp [I1, I2, finrank_quotient_span_eq_natDegree, hdeg]
    rcases
        exists_ringEquiv_of_injective_of_finrank_eq (𝕜 := 𝕜)
          (A := Polynomial 𝕜 ⧸ I1) (B := Polynomial 𝕜 ⧸ I2) ψ
          (RingEquiv.refl 𝕜) hψ hinj hfinrank with
      ⟨eQ, heQ⟩
    -- Choose a polynomial representative for the inverse image of `X`.
    rcases Ideal.Quotient.mk_surjective (I := I1) (eQ.symm (mk₂ Polynomial.X)) with ⟨R, hR⟩
    have heQ_mk (P : Polynomial 𝕜) : eQ (mk₁ P) = mk₂ (P.comp Qf) := by
      have : eQ.toRingHom (mk₁ P) = ψ (mk₁ P) := by
        simpa using congrArg (fun g => g (mk₁ P)) heQ
      simpa [ψ, mk₁, mk₂, compQ] using this
    have hsymm_mk (P : Polynomial 𝕜) : eQ.symm (mk₂ P) = mk₁ (P.comp R) := by
      have hconst : ∀ a : 𝕜, eQ.symm (mk₂ (Polynomial.C a)) = mk₁ (Polynomial.C a) := by
        intro a
        have hx : eQ (mk₁ (Polynomial.C a)) = mk₂ (Polynomial.C a) := by
          simpa using heQ_mk (P := Polynomial.C a)
        have hx' := congrArg (fun x => eQ.symm x) hx
        simpa using hx'.symm
      have hX : eQ.symm (mk₂ Polynomial.X) = mk₁ R := by
        simpa [mk₁, mk₂] using hR.symm
      have hRingHom :
          eQ.symm.toRingHom.comp mk₂ = (mk₁.comp (Polynomial.compRingHom R)) := by
        apply Polynomial.ringHom_ext
        · intro a
          simpa [RingHom.comp_apply] using hconst a
        · simpa [RingHom.comp_apply] using hX
      have := congrArg (fun g : Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ I1) => g P) hRingHom
      simpa [RingHom.comp_apply, mk₁, mk₂, Polynomial.compRingHom] using this
    -- Polynomial congruences expressing that `Qf` and `R` are inverses modulo `(P₂)` and `(σX P₁)`.
    have hRcomp_mk : mk₂ (R.comp Qf) = mk₂ Polynomial.X := by
      have : eQ (mk₁ R) = mk₂ Polynomial.X := by
        simpa using congrArg (fun x => eQ x) hR
      simpa [heQ_mk (P := R)] using this
    rcases (Ideal.mem_span_singleton).1 ((Ideal.Quotient.eq).1 hRcomp_mk) with ⟨S₂, hS₂⟩
    have hRcomp : R.comp Qf = Polynomial.X + P₂ * S₂ := eq_add_of_sub_eq' hS₂
    have hQfcomp_mk : mk₁ (Qf.comp R) = mk₁ Polynomial.X := by
      have hmkX : eQ (mk₁ Polynomial.X) = mk₂ Qf := by
        simpa [hσX.1] using heQ_mk (P := Polynomial.X)
      have hmkX' := congrArg (fun x => eQ.symm x) hmkX
      have htmp : mk₁ Polynomial.X = mk₁ (Qf.comp R) := by
        simpa [hsymm_mk (P := Qf)] using hmkX'
      exact htmp.symm
    rcases (Ideal.mem_span_singleton).1 ((Ideal.Quotient.eq).1 hQfcomp_mk) with ⟨S₁, hS₁⟩
    have hQfcomp : Qf.comp R = Polynomial.X + (σX P₁) * S₁ := eq_add_of_sub_eq' hS₁
    have hP₂comp : ∃ T : Polynomial 𝕜, P₂.comp R = T * (σX P₁) := by
      have hmk0 : mk₁ (P₂.comp R) = 0 := by
        have hmk₂0 : mk₂ P₂ = 0 := by
          apply (Ideal.Quotient.eq_zero_iff_mem).2
          simpa [I2] using (Ideal.subset_span (by simp : P₂ ∈ ({P₂} : Set (Polynomial 𝕜))))
        have : eQ.symm (mk₂ P₂) = mk₁ (P₂.comp R) := by
          simpa using hsymm_mk (P := P₂)
        simpa [hmk₂0] using this.symm
      have hmem : P₂.comp R ∈ (I1 : Ideal (Polynomial 𝕜)) :=
        (Ideal.Quotient.eq_zero_iff_mem).1 hmk0
      rcases (Ideal.mem_span_singleton).1 hmem with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      simpa [I1, mul_comm, mul_left_comm, mul_assoc] using hT
    let g :
        {α : AlgebraicClosure 𝕜 //
            (P₂.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot α} →
          {β : AlgebraicClosure 𝕜 //
              ((σX P₁).map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot β} :=
      fun a =>
        ⟨(Polynomial.aeval a.1) Qf,
          isRoot_aeval_of_comp_eq_mul (𝕜 := 𝕜) (p := σX P₁) (q := Qf) (r := Sf) (s := P₂) hSf
            (K := AlgebraicClosure 𝕜) (α := a.1) a.2⟩
    let h :
        {β : AlgebraicClosure 𝕜 //
            ((σX P₁).map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot β} →
          {α : AlgebraicClosure 𝕜 //
              (P₂.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot α} :=
      fun b =>
        ⟨(Polynomial.aeval b.1) R,
          by
            rcases hP₂comp with ⟨T, hT⟩
            simpa [mul_assoc] using
              (isRoot_aeval_of_comp_eq_mul (𝕜 := 𝕜) (p := P₂) (q := R) (r := T) (s := σX P₁) hT
                (K := AlgebraicClosure 𝕜) (α := b.1) b.2)⟩
    have h_left : Function.LeftInverse h g := by
      intro a
      ext
      have hP₂a : (Polynomial.aeval a.1) P₂ = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using a.2
      have hEval : (Polynomial.aeval a.1) (R.comp Qf) = a.1 := by
        simp [hRcomp, hP₂a, map_add, map_mul]
      have : (Polynomial.aeval ((Polynomial.aeval a.1) Qf)) R = a.1 := by
        simpa [Polynomial.aeval_comp] using hEval
      simpa [g, h] using this
    have h_right : Function.RightInverse h g := by
      intro b
      ext
      have hσa : (Polynomial.aeval b.1) (σX P₁) = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using b.2
      have hEval : (Polynomial.aeval b.1) (Qf.comp R) = b.1 := by
        simp [hQfcomp, hσa, map_add, map_mul]
      have : (Polynomial.aeval ((Polynomial.aeval b.1) R)) Qf = b.1 := by
        simpa [Polynomial.aeval_comp] using hEval
      simpa [g, h] using this
    refine ⟨Equiv.mk g h h_left h_right, ?_⟩
    intro a
    rfl

/--
Root multiplicity for a composition over an algebraically closed field.

If `b = q.eval a`, then the multiplicity of `a` as a root of `p.comp q` is the multiplicity of `b`
as a root of `p`, times the multiplicity of `a` as a root of `q - C b`.
-/
lemma rootMultiplicity_comp_eq_mul
    {K : Type*} [Field K] [IsAlgClosed K] (p q : Polynomial K) (a : K) (hp : p ≠ 0) :
    Polynomial.rootMultiplicity a (p.comp q) =
      Polynomial.rootMultiplicity (Polynomial.eval a q) p *
        Polynomial.rootMultiplicity a (q - Polynomial.C (Polynomial.eval a q)) := by
  classical
  by_cases hq0 : q = Polynomial.C (Polynomial.eval a q)
  · -- Here `q` is constant, so `p.comp q` is constant and the inner factor is zero.
    rw [hq0]
    simp [Polynomial.comp_C]
  · set b : K := Polynomial.eval a q
    have hq : q ≠ Polynomial.C b := by
      simpa [b] using hq0
    have hq_sub_ne_zero : ∀ c : K, q - Polynomial.C c ≠ 0 := by
      intro c hc
      have hqc : q = Polynomial.C c := sub_eq_zero.mp hc
      have hb : b = c := by
        -- Evaluate at `a` to compare constants.
        simp [b, hqc]
      exact hq (by simp [hqc, hb] : q = Polynomial.C b)
    have h0not : (0 : Polynomial K) ∉ p.roots.map (fun c : K => q - Polynomial.C c) := by
      intro hmem
      rcases (Multiset.mem_map.1 hmem) with ⟨c, hc, hc0⟩
      exact hq_sub_ne_zero c (by simpa using hc0)
    have hprod_ne_zero :
        (p.roots.map (fun c : K => q - Polynomial.C c)).prod ≠ 0 :=
      Multiset.prod_ne_zero h0not
    have hleading : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp
    have hC_ne : (Polynomial.C p.leadingCoeff : Polynomial K) ≠ 0 := by
      simpa [Polynomial.C_eq_zero] using hleading
    have hroots : p.roots.card = p.natDegree :=
      IsAlgClosed.card_roots_eq_natDegree (p := p)
    have hp_fac :
        Polynomial.C p.leadingCoeff *
            (p.roots.map fun c : K => Polynomial.X - Polynomial.C c).prod =
          p :=
      Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) hroots
    have hcomp :
        p.comp q =
          Polynomial.C p.leadingCoeff * (p.roots.map fun c : K => q - Polynomial.C c).prod := by
      -- Compose the factorization of `p` with `q`.
      calc
        p.comp q = q.compRingHom p := rfl
        _ = q.compRingHom
              (Polynomial.C p.leadingCoeff *
                (p.roots.map fun c : K => Polynomial.X - Polynomial.C c).prod) := by
              simp [hp_fac]
        _ = Polynomial.C p.leadingCoeff * (p.roots.map fun c : K => q - Polynomial.C c).prod := by
              simp [map_mul, map_multiset_prod, Polynomial.compRingHom]
    have hmul_ne :
        (Polynomial.C p.leadingCoeff * (p.roots.map fun c : K => q - Polynomial.C c).prod) ≠ 0 :=
      mul_ne_zero hC_ne hprod_ne_zero
    have hrootC : Polynomial.rootMultiplicity a
      (Polynomial.C p.leadingCoeff : Polynomial K) = 0 := by
      refine Polynomial.rootMultiplicity_eq_zero ?_
      intro hroot
      have : Polynomial.eval a (Polynomial.C p.leadingCoeff : Polynomial K) = 0 := by
        simpa [Polynomial.IsRoot] using hroot
      rw [Polynomial.eval_C] at this
      exact hleading this
    have hRM_prod :
        Polynomial.rootMultiplicity a (p.roots.map fun c : K => q - Polynomial.C c).prod =
          Multiset.count b p.roots * Polynomial.rootMultiplicity a (q - Polynomial.C b) := by
      -- Induct on the multiset `p.roots`.
      induction p.roots using Multiset.induction_on with
      | empty =>
          simp [b]
      | cons c s ih =>
          have h0not_s : (0 : Polynomial K) ∉ s.map (fun c : K => q - Polynomial.C c) := by
            intro hmem
            rcases (Multiset.mem_map.1 hmem) with ⟨c', hc', hc0⟩
            exact hq_sub_ne_zero c' (by simpa using hc0)
          have hprod_s :
              (s.map (fun c : K => q - Polynomial.C c)).prod ≠ 0 :=
            Multiset.prod_ne_zero h0not_s
          have hmul :
              (q - Polynomial.C c) * (s.map (fun c : K => q - Polynomial.C c)).prod ≠ 0 :=
            mul_ne_zero (hq_sub_ne_zero c) hprod_s
          by_cases hcb : c = b
          · subst hcb
            have hRM_mul :=
              (Polynomial.rootMultiplicity_mul (x := a) (p := q - Polynomial.C b)
                    (q := (s.map (fun c : K => q - Polynomial.C c)).prod) (hpq := hmul))
            -- Only the head factor contributes at `b`.
            have hcount : Multiset.count b (b ::ₘ s) = Multiset.count b s + 1 := by
              simp
            -- Rearrange.
            calc
              Polynomial.rootMultiplicity a ((b ::ₘ s).map (fun c : K => q - Polynomial.C c)).prod
                  = Polynomial.rootMultiplicity a ((q - Polynomial.C b) *
                      (s.map (fun c : K => q - Polynomial.C c)).prod) := by
                        simp
              _ = Polynomial.rootMultiplicity a (q - Polynomial.C b) +
                    Polynomial.rootMultiplicity a
                    (s.map (fun c : K => q - Polynomial.C c)).prod := by
                        simpa using hRM_mul
              _ = (Multiset.count b s + 1) * Polynomial.rootMultiplicity a
                (q - Polynomial.C b) := by
                    -- Use the induction hypothesis and arithmetic.
                    -- `m + n*m = (n+1)*m`.
                    simp [ih, Nat.add_mul, Nat.add_comm]
              _ = Multiset.count b (b ::ₘ s) * Polynomial.rootMultiplicity a
                (q - Polynomial.C b) := by
                    simp [hcount]
          · have hbcn : b ≠ c := by
              simpa [ne_comm] using hcb
            have hnotroot : ¬ (q - Polynomial.C c).IsRoot a := by
              intro hroot
              have : Polynomial.eval a (q - Polynomial.C c) = 0 := by
                simpa [Polynomial.IsRoot] using hroot
              have : b - c = 0 := by
                simpa [b, Polynomial.eval_sub, Polynomial.eval_C] using this
              exact hcb (sub_eq_zero.mp this).symm
            have hRM_head : Polynomial.rootMultiplicity a (q - Polynomial.C c) = 0 :=
              Polynomial.rootMultiplicity_eq_zero hnotroot
            have hRM_mul :=
              (Polynomial.rootMultiplicity_mul (x := a) (p := q - Polynomial.C c)
                    (q := (s.map (fun c : K => q - Polynomial.C c)).prod) (hpq := hmul))
            calc
              Polynomial.rootMultiplicity a ((c ::ₘ s).map (fun c : K => q - Polynomial.C c)).prod
                  = Polynomial.rootMultiplicity a ((q - Polynomial.C c) *
                      (s.map (fun c : K => q - Polynomial.C c)).prod) := by
                        simp
              _ = Polynomial.rootMultiplicity a (q - Polynomial.C c) +
                    Polynomial.rootMultiplicity a
                    (s.map (fun c : K => q - Polynomial.C c)).prod := by
                        simpa using hRM_mul
              _ = Multiset.count b (c ::ₘ s) *
                Polynomial.rootMultiplicity a (q - Polynomial.C b) := by
                    simp [hRM_head, ih, hbcn]
    have hcount : Multiset.count b p.roots = Polynomial.rootMultiplicity b p := by
      simp
    calc
      Polynomial.rootMultiplicity a (p.comp q)
          = Polynomial.rootMultiplicity a
              (Polynomial.C p.leadingCoeff *
                (p.roots.map fun c : K => q - Polynomial.C c).prod) := by
              simp [hcomp]
      _ = Polynomial.rootMultiplicity a (Polynomial.C p.leadingCoeff : Polynomial K) +
            Polynomial.rootMultiplicity a (p.roots.map fun c : K => q - Polynomial.C c).prod := by
            simpa using (Polynomial.rootMultiplicity_mul (x := a) hmul_ne)
      _ = Multiset.count b p.roots * Polynomial.rootMultiplicity a (q - Polynomial.C b) := by
            simp [hrootC, hRM_prod]
      _ = Polynomial.rootMultiplicity b p * Polynomial.rootMultiplicity a (q - Polynomial.C b) := by
            simp [hcount]

/--
For `q : K[X]`, the multiplicity of `a` as a root of `q - C (q.eval a)` is `1` iff the derivative
does not vanish at `a`.
-/
lemma rootMultiplicity_sub_C_eval_eq_one_iff
    {K : Type*} [Field K] (q : Polynomial K) (a : K) :
    Polynomial.rootMultiplicity a (q - Polynomial.C (Polynomial.eval a q)) = 1 ↔
      ¬ (q.derivative.IsRoot a) := by
  classical
  set r : Polynomial K := q - Polynomial.C (Polynomial.eval a q)
  by_cases hr0 : r = 0
  · have hqconst : q = Polynomial.C (Polynomial.eval a q) := by
      have : q - Polynomial.C (Polynomial.eval a q) = 0 := by simpa [r] using hr0
      exact sub_eq_zero.mp this
    have hqder : q.derivative = 0 := by
      rw [hqconst]
      simp
    constructor
    · intro h _
      have hrm : Polynomial.rootMultiplicity a r = 0 := by
        simp [r, hr0]
      rw [hrm] at h
      exact Nat.zero_ne_one h
    · intro h
      have : q.derivative.IsRoot a := by
        simp [hqder, Polynomial.IsRoot]
      exact False.elim (h this)
  · have hr_root : r.IsRoot a := by
      simp [r, Polynomial.IsRoot]
    have hpos : 0 < Polynomial.rootMultiplicity a r :=
      (Polynomial.rootMultiplicity_pos hr0).2 hr_root
    have hge : 1 ≤ Polynomial.rootMultiplicity a r := Nat.succ_le_iff.2 hpos
    have hlt : (1 < Polynomial.rootMultiplicity a r) ↔ r.derivative.IsRoot a := by
      constructor
      · intro h
        exact (Polynomial.one_lt_rootMultiplicity_iff_isRoot (p := r) (t := a) hr0).1 h |>.2
      · intro h
        exact (Polynomial.one_lt_rootMultiplicity_iff_isRoot (p := r) (t := a) hr0).2 ⟨hr_root, h⟩
    have hEq : Polynomial.rootMultiplicity a r = 1 ↔ ¬ r.derivative.IsRoot a := by
      constructor
      · intro h hdr
        have : ¬ 1 < Polynomial.rootMultiplicity a r := by simp [h]
        exact this (hlt.2 hdr)
      · intro hdr
        rcases Nat.lt_or_eq_of_le hge with hlt' | heq
        · exact (hdr (hlt.1 hlt')).elim
        · simpa using heq.symm
    have hderiv : r.derivative = q.derivative := by
      simp [r]
    simpa [r, hderiv] using hEq

end SomeLocalRings
