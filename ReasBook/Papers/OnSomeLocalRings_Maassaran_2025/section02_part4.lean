/-
Authors: Liang Xiao, Haochen Ju, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/README.md (Contributors).
-/

import Mathlib
import Papers.OnSomeLocalRings_Maassaran_2025.section02_part3

namespace SomeLocalRings

set_option maxHeartbeats 800000

variable {𝕜 : Type*} [Field 𝕜]
variable {A B : Type*} [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]

/--
Theorem 2.8.
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. Take `n > 1`.
If `f : 𝕜[X]/(P₁) → 𝕜[X]/(P₂)` is a ring isomorphism stabilizing `𝕜`, then the induced map
`f_{X,n} : 𝕜[X]/(P₁^n) → 𝕜[X]/(P₂^n)` from Proposition 2.4 is a ring isomorphism stabilizing
`𝕜` if and only if the formal derivative `Q_f'` is nonzero.
-/
theorem theorem_2_8
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
    ((∃ e :
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) ≃+*
            (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
        e.toRingHom =
          Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn) ∧
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
          (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
          (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))
          (Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn)
          σ_f) ↔
      Qf.derivative ≠ 0 := by
  have hfXn :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))
        (Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
          (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn)
        σ_f :=
    stabilizesBaseFieldWith_quotientMap_pow (𝕜 := 𝕜) (P₁ := P₁) (P₂ := P₂) (n := n)
      (fX := fX) (σ_f := σ_f) hfX hIJn
  constructor
  · rintro ⟨hex, -⟩
    have hcop : IsCoprime Sf P₂ :=
      (proposition_2_5 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf hQf fX hfX_X hfX hfX_def hIJ
          hf_ind Sf hSf n hn hIJn).2 hex
    exact
      (proposition_2_7 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf Sf hQf.1 hSf).1 hcop
  · intro hQ'
    have hcop : IsCoprime Sf P₂ :=
      (proposition_2_7 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf Sf hQf.1 hSf).2 hQ'
    refine ⟨?_, hfXn⟩
    exact
      (proposition_2_5 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf hQf fX hfX_X hfX hfX_def hIJ
          hf_ind Sf hSf n hn hIJn).1 hcop

/--
Corollary 2.9.
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. If
`f : 𝕜[X]/(P₁) ≃+* 𝕜[X]/(P₂)` is a ring isomorphism stabilizing `𝕜` such that the formal
derivative `Q_f'` (associated to `f` as in Proposition 2.4) is nonzero, then for all `n ≥ 1`
the quotient rings `𝕜[X]/(P₁^n)` and `𝕜[X]/(P₂^n)` are isomorphic.
-/
theorem corollary_2_9
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
    (hQf' : Qf.derivative ≠ 0) :
    ∀ n : ℕ,
      1 ≤ n →
        ∃ e :
          (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) ≃+*
            (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
          RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
            (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
            (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) e.toRingHom σ_f := by
  classical
  have hP₁mem : P₁ ∈ Ideal.span ({P₁} : Set (Polynomial 𝕜)) :=
    Ideal.subset_span (by simp)
  have hcomap : P₁ ∈ Ideal.comap fX (Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
    hIJ hP₁mem
  have hfX_P₁_mem : fX P₁ ∈ Ideal.span ({P₂} : Set (Polynomial 𝕜)) :=
    hcomap
  have hcomp_mem : (σX P₁).comp Qf ∈ Ideal.span ({P₂} : Set (Polynomial 𝕜)) := by
    simpa [hfX_def] using hfX_P₁_mem
  rcases (Ideal.mem_span_singleton.mp hcomp_mem) with ⟨Sf, hSf'⟩
  have hSf : (σX P₁).comp Qf = Sf * P₂ := by
    simpa [mul_comm] using hSf'
  have hfX_P₁ : fX P₁ = Sf * P₂ := by
    calc
      fX P₁ = (σX P₁).comp Qf := hfX_def P₁
      _ = Sf * P₂ := hSf
  have hfX_P₁' : fX P₁ = P₂ * Sf := by
    calc
      fX P₁ = (σX P₁).comp Qf := hfX_def P₁
      _ = P₂ * Sf := hSf'

  intro n hn
  cases n with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hn)
  | succ n =>
      cases n with
      | zero =>
          have hI₁ :
              (Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
                Ideal.span ({P₁} : Set (Polynomial 𝕜)) := by
            simp
          have hI₂ :
              (Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) =
                Ideal.span ({P₂} : Set (Polynomial 𝕜)) := by
            simp
          let e₁ :
              (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜))) ≃+*
                (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) :=
            Ideal.quotEquivOfEq (R := Polynomial 𝕜)
              (I := Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜)))
              (J := Ideal.span ({P₁} : Set (Polynomial 𝕜))) hI₁
          let e₂ :
              (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜))) ≃+*
                (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
            Ideal.quotEquivOfEq (R := Polynomial 𝕜)
              (I := Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜)))
              (J := Ideal.span ({P₂} : Set (Polynomial 𝕜))) hI₂
          refine ⟨(e₁.trans f).trans e₂.symm, ?_⟩
          intro a
          have hmk₁ :
              algebraMap 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜))) a =
                Ideal.Quotient.mk (Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜)))
                  (Polynomial.C a) := by
            simpa [Polynomial.algebraMap_eq] using
              (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜)
                  (I := Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜))) a).symm
          have hmk₂ :
              algebraMap 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜)))
                  (σ_f a) =
                Ideal.Quotient.mk (Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜)))
                  (Polynomial.C (σ_f a)) := by
            simpa [Polynomial.algebraMap_eq] using
              (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜)
                  (I := Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜))) (σ_f a)).symm
          have hf_mk :
              f (Ideal.Quotient.mk (Ideal.span ({P₁} : Set (Polynomial 𝕜))) (Polynomial.C a)) =
                Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) (Polynomial.C (σ_f a)) := by
            have hmk₁' :
                algebraMap 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) a =
                  Ideal.Quotient.mk (Ideal.span ({P₁} : Set (Polynomial 𝕜))) (Polynomial.C a) := by
              simpa [Polynomial.algebraMap_eq] using
                (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜)
                    (I := Ideal.span ({P₁} : Set (Polynomial 𝕜))) a).symm
            have hmk₂' :
                algebraMap 𝕜 (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) (σ_f a) =
                  Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜)))
                    (Polynomial.C (σ_f a)) := by
              simpa [Polynomial.algebraMap_eq] using
                (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜)
                    (I := Ideal.span ({P₂} : Set (Polynomial 𝕜))) (σ_f a)).symm
            simpa [hmk₁', hmk₂'] using hf a
          rw [hmk₁, hmk₂]
          simp [e₁, e₂, Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk, hf_mk]
      | succ n =>
          have hn' : 1 < Nat.succ (Nat.succ n) :=
            Nat.succ_lt_succ (Nat.succ_pos n)
          have hIJn :
              (Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)) :
                  Ideal (Polynomial 𝕜)) ≤
                Ideal.comap fX
                  (Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))) := by
            refine
              (Ideal.span_singleton_le_iff_mem
                    (I := Ideal.comap fX
                      (Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))))
                    (x := P₁ ^ Nat.succ (Nat.succ n))).2 ?_
            show fX (P₁ ^ Nat.succ (Nat.succ n)) ∈
                Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))
            refine (Ideal.mem_span_singleton).2 ?_
            refine ⟨Sf ^ Nat.succ (Nat.succ n), ?_⟩
            calc
              fX (P₁ ^ Nat.succ (Nat.succ n)) = (fX P₁) ^ Nat.succ (Nat.succ n) := by simp
              _ = (P₂ * Sf) ^ Nat.succ (Nat.succ n) := by simp [hfX_P₁']
              _ = P₂ ^ Nat.succ (Nat.succ n) * Sf ^ Nat.succ (Nat.succ n) := by
                simpa using (mul_pow P₂ Sf (Nat.succ (Nat.succ n)))

          rcases
              (theorem_2_8 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf hQf fX hfX_X hfX
                    hfX_def hIJ hf_ind Sf hSf (Nat.succ (Nat.succ n)) hn' hIJn).2 hQf' with
            ⟨⟨e, he⟩, hstab⟩
          refine ⟨e, ?_⟩
          have he_coe :
              (↑e :
                    (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))) →+*
                      (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)))) =
                  Ideal.quotientMap (I := Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)))
                    (Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))) fX hIJn := by
            simpa [RingEquiv.toRingHom_eq_coe] using he
          simpa [RingEquiv.toRingHom_eq_coe, he_coe] using hstab

/-- The ideal generated by `P ^ m` is contained in the ideal generated by `P` when `1 ≤ m`. -/
lemma span_pow_le_span (P : Polynomial 𝕜) (m : ℕ) (hm : 1 ≤ m) :
    Ideal.span ({P ^ m} : Set (Polynomial 𝕜)) ≤ Ideal.span ({P} : Set (Polynomial 𝕜)) := by
  classical
  refine
    (Ideal.span_singleton_le_iff_mem (I := Ideal.span ({P} : Set (Polynomial 𝕜))) (x := P ^ m)).2
      ?_
  refine (Ideal.mem_span_singleton).2 ?_
  refine ⟨P ^ (m - 1), ?_⟩
  calc
    P ^ m = P ^ ((m - 1) + 1) := by simp [Nat.sub_add_cancel hm]
    _ = P ^ (m - 1) * P := by simp [pow_succ]
    _ = P * P ^ (m - 1) := by simp [mul_comm]

/--
Theorem 2.10.
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. Let
`f_m : 𝕜[X]/(P₁^m) ≃+* 𝕜[X]/(P₂^m)` be a ring isomorphism stabilizing `𝕜`, for some `m ≥ 1`.
Assume that `f_m` maps the class of `X` to the class of some polynomial `R : 𝕜[X]`, and let
`Q` be the remainder of dividing `R` by `P₂` (this `Q` does not depend on the choice of `R`).
If the formal derivative `Q'` is nonzero, then the rings `𝕜[X]/(P₁^n)` and `𝕜[X]/(P₂^n)` are
isomorphic for all `n ≥ 1`.
-/
theorem theorem_2_10
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (m : ℕ) (hm : 1 ≤ m)
    (f_m :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ m} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ m} : Set (Polynomial 𝕜))))
    (hf_m :
      RingHom.StabilizesBaseField (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ m} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ m} : Set (Polynomial 𝕜))) f_m.toRingHom)
    (hX :
      ∃ R : Polynomial 𝕜,
        f_m
            ((Ideal.Quotient.mk (Ideal.span ({P₁ ^ m} : Set (Polynomial 𝕜)))) Polynomial.X) =
          (Ideal.Quotient.mk (Ideal.span ({P₂ ^ m} : Set (Polynomial 𝕜)))) R ∧
          ((R % P₂).derivative ≠ 0)) :
    ∀ n : ℕ,
      1 ≤ n →
        Nonempty
          ((Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜))) ≃+*
            (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) := by
  classical
  rcases hf_m with ⟨σ_f, hf_m_with⟩
  rcases hX with ⟨R, hR, hR'⟩

  -- Ideals for the various quotients.
  let I₁m : Ideal (Polynomial 𝕜) := Ideal.span ({P₁ ^ m} : Set (Polynomial 𝕜))
  let I₂m : Ideal (Polynomial 𝕜) := Ideal.span ({P₂ ^ m} : Set (Polynomial 𝕜))
  let I₁ : Ideal (Polynomial 𝕜) := Ideal.span ({P₁} : Set (Polynomial 𝕜))
  let I₂ : Ideal (Polynomial 𝕜) := Ideal.span ({P₂} : Set (Polynomial 𝕜))

  have hI₂m_le : I₂m ≤ I₂ := span_pow_le_span (𝕜 := 𝕜) (P := P₂) m hm
  have hI₁m_le : I₁m ≤ I₁ := span_pow_le_span (𝕜 := 𝕜) (P := P₁) m hm

  -- The residue quotient `𝕜[X]/(P₂)` is a field, so nilpotent elements are zero.
  haveI : I₂.IsMaximal := by
    letI : Fact (Irreducible P₂) := ⟨hP₂⟩
    simpa [I₂] using (AdjoinRoot.span_maximal_of_irreducible (K := 𝕜) (f := P₂))
  letI : Field (Polynomial 𝕜 ⧸ I₂) := Ideal.Quotient.field (I := I₂)

  -- The canonical projection `𝕜[X]/(P₂^m) → 𝕜[X]/(P₂)`.
  let π₂ : (Polynomial 𝕜 ⧸ I₂m) →+* (Polynomial 𝕜 ⧸ I₂) := Ideal.Quotient.factor hI₂m_le

  -- Compose `f_m` with `π₂` to get a map `𝕜[X] → 𝕜[X]/(P₂)`.
  let g : Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ I₂) :=
    (π₂.comp f_m.toRingHom).comp (Ideal.Quotient.mk I₁m)

  have hgP₁ : g P₁ = 0 := by
    let xq : Polynomial 𝕜 ⧸ I₁m := (Ideal.Quotient.mk I₁m) P₁
    have hxq : xq ^ m = 0 := by
      have hx : (Ideal.Quotient.mk I₁m) (P₁ ^ m) = 0 := by
        apply (Ideal.Quotient.eq_zero_iff_mem).2
        exact Ideal.subset_span (by simp)
      calc
        xq ^ m = (Ideal.Quotient.mk I₁m) (P₁ ^ m) := by simp [xq]
        _ = 0 := hx
    have hnil : (g P₁) ^ m = 0 := by
      have hpow : (f_m.toRingHom xq) ^ m = f_m.toRingHom (xq ^ m) := by
        simp
      calc
        (g P₁) ^ m = (π₂ (f_m.toRingHom xq)) ^ m := by rfl
        _ = π₂ ((f_m.toRingHom xq) ^ m) := by simp
        _ = π₂ (f_m.toRingHom (xq ^ m)) := by rw [hpow]
        _ = 0 := by simp [hxq]
    exact eq_zero_of_pow_eq_zero hnil

  have hker : ∀ a ∈ I₁, g a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span ({P₁} : Set (Polynomial 𝕜)) := by simpa [I₁] using ha
    rcases (Ideal.mem_span_singleton.mp ha') with ⟨b, rfl⟩
    simp [map_mul, hgP₁]

  -- Induced map on residue fields.
  let φ : (Polynomial 𝕜 ⧸ I₁) →+* (Polynomial 𝕜 ⧸ I₂) := Ideal.Quotient.lift I₁ g hker

  have hφ_stab :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ I₁) (B := Polynomial 𝕜 ⧸ I₂) φ σ_f := by
    intro a
    have hmk₁ :
        algebraMap 𝕜 (Polynomial 𝕜 ⧸ I₁) a =
          Ideal.Quotient.mk I₁ (Polynomial.C a) := by
      simpa [Polynomial.algebraMap_eq] using
        (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜) (I := I₁) a).symm
    have hmk₁m :
        algebraMap 𝕜 (Polynomial 𝕜 ⧸ I₁m) a =
          Ideal.Quotient.mk I₁m (Polynomial.C a) := by
      simpa [Polynomial.algebraMap_eq] using
        (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜) (I := I₁m) a).symm
    have hmk₂ :
        algebraMap 𝕜 (Polynomial 𝕜 ⧸ I₂) (σ_f a) =
          Ideal.Quotient.mk I₂ (Polynomial.C (σ_f a)) := by
      simpa [Polynomial.algebraMap_eq] using
        (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜) (I := I₂) (σ_f a)).symm
    have hmk₂m :
        algebraMap 𝕜 (Polynomial 𝕜 ⧸ I₂m) (σ_f a) =
          Ideal.Quotient.mk I₂m (Polynomial.C (σ_f a)) := by
      simpa [Polynomial.algebraMap_eq] using
        (Ideal.Quotient.mk_algebraMap (R₁ := 𝕜) (A := Polynomial 𝕜) (I := I₂m) (σ_f a)).symm
    have hf_m_mk :
        f_m.toRingHom (Ideal.Quotient.mk I₁m (Polynomial.C a)) =
          Ideal.Quotient.mk I₂m (Polynomial.C (σ_f a)) := by
      -- Rewrite the stabilization property of `f_m` in terms of quotient representatives.
      simpa [hmk₁m, hmk₂m] using hf_m_with a
    calc
      φ (algebraMap 𝕜 (Polynomial 𝕜 ⧸ I₁) a) =
          φ (Ideal.Quotient.mk I₁ (Polynomial.C a)) := by simp [hmk₁]
      _ = g (Polynomial.C a) := by simp [φ]
      _ = π₂ (f_m.toRingHom (Ideal.Quotient.mk I₁m (Polynomial.C a))) := by rfl
      _ = π₂ (Ideal.Quotient.mk I₂m (Polynomial.C (σ_f a))) := by
          simpa using congrArg (fun x => π₂ x) hf_m_mk
      _ = Ideal.Quotient.mk I₂ (Polynomial.C (σ_f a)) := by simp [π₂]
      _ = algebraMap 𝕜 (Polynomial 𝕜 ⧸ I₂) (σ_f a) := by simp [hmk₂]

  -- Build a ring isomorphism of residue fields from `φ` using finite-dimensionality.
  haveI : I₁.IsMaximal := by
    letI : Fact (Irreducible P₁) := ⟨hP₁⟩
    simpa [I₁] using (AdjoinRoot.span_maximal_of_irreducible (K := 𝕜) (f := P₁))
  letI : Field (Polynomial 𝕜 ⧸ I₁) := Ideal.Quotient.field (I := I₁)

  have hinjφ : Function.Injective φ := by
    exact RingHom.injective φ

  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ I₁m) := by
    have hP : P₁ ^ m ≠ 0 := pow_ne_zero m hP₁.ne_zero
    simpa [I₁m] using finiteDimensional_quotient_span_of_ne_zero (𝕜 := 𝕜) (P := P₁ ^ m) hP
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ I₂m) := by
    have hP : P₂ ^ m ≠ 0 := pow_ne_zero m hP₂.ne_zero
    simpa [I₂m] using finiteDimensional_quotient_span_of_ne_zero (𝕜 := 𝕜) (P := P₂ ^ m) hP
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ I₁) := by
    simpa [I₁] using
      finiteDimensional_quotient_span_of_ne_zero (𝕜 := 𝕜) (P := P₁) hP₁.ne_zero
  haveI : FiniteDimensional 𝕜 (Polynomial 𝕜 ⧸ I₂) := by
    simpa [I₂] using
      finiteDimensional_quotient_span_of_ne_zero (𝕜 := 𝕜) (P := P₂) hP₂.ne_zero

  have hfinrank_pow :
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I₁m) =
        Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I₂m) :=
    finrank_eq_of_ringEquiv (𝕜 := 𝕜)
      (A := Polynomial 𝕜 ⧸ I₁m) (B := Polynomial 𝕜 ⧸ I₂m) f_m σ_f hf_m_with

  have hdeg₁₂ : P₁.natDegree = P₂.natDegree := by
    have hndpow : (P₁ ^ m).natDegree = (P₂ ^ m).natDegree := by
      simpa [I₁m, I₂m, finrank_quotient_span_eq_natDegree] using hfinrank_pow
    have hmpos : 0 < m := (Nat.succ_le_iff).1 hm
    have hmul : m * P₁.natDegree = m * P₂.natDegree := by
      simpa [Polynomial.natDegree_pow] using hndpow
    exact Nat.mul_left_cancel hmpos hmul

  have hfinrank :
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I₁) =
        Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I₂) := by
    calc
      Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I₁) = P₁.natDegree := by
        simp [I₁, finrank_quotient_span_eq_natDegree]
      _ = P₂.natDegree := by simp [hdeg₁₂]
      _ = Module.finrank 𝕜 (Polynomial 𝕜 ⧸ I₂) := by
        simp [I₂, finrank_quotient_span_eq_natDegree]

  rcases
      exists_ringEquiv_of_injective_of_finrank_eq (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ I₁) (B := Polynomial 𝕜 ⧸ I₂) φ σ_f hφ_stab hinjφ hfinrank with
    ⟨f, hf_indφ⟩

  have hf_stab :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f := by
    -- `f.toRingHom` is `φ`, so transfer stabilization.
    have hf_coe :
        (↑f : (Polynomial 𝕜 ⧸ I₁) →+* (Polynomial 𝕜 ⧸ I₂)) = φ := by
      simpa [RingEquiv.toRingHom_eq_coe] using hf_indφ
    have hf_stab_coe :
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
          (A := Polynomial 𝕜 ⧸ I₁) (B := Polynomial 𝕜 ⧸ I₂) (↑f) σ_f := by
      simpa [hf_coe] using hφ_stab
    have hf_stab' :
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
          (A := Polynomial 𝕜 ⧸ I₁) (B := Polynomial 𝕜 ⧸ I₂) f.toRingHom σ_f := by
      simpa [RingEquiv.toRingHom_eq_coe] using hf_stab_coe
    simpa [I₁, I₂] using hf_stab'

  -- Set up Proposition 2.4 for the residue-field isomorphism `f`.
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

  have hprop := proposition_2_4 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf_stab
  have hdeg' : P₁.natDegree = P₂.natDegree := hprop.1

  have hQf_exists :
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
                            (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) :
                                Ideal (Polynomial 𝕜)) ≤
                              Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))),
                            RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
                              (A :=
                                Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
                              (B :=
                                Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))
                              (Ideal.quotientMap (I :=
                                Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
                                (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn)
                              σ_f := by
    simpa [σX] using hprop.2

  rcases hQf_exists with ⟨Qf, hQf, hQf_unique⟩
  rcases hQf with ⟨hQfdeg, ⟨fX, hfX_X, hfX, hfX_def, hrest⟩⟩
  rcases hrest with ⟨⟨hIJ, hf_ind⟩, hSf, hPdiv, hIJn_all⟩
  rcases hSf with ⟨Sf, hSf⟩

  -- Identify Proposition 2.4's polynomial `Qf` with the remainder `R % P₂`.
  have hf_X_eq :
      f (Ideal.Quotient.mk (Ideal.span ({P₁} : Set (Polynomial 𝕜))) Polynomial.X) =
        Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) (R % P₂) := by
    -- First compute the same identity for `φ`, then transfer it to `f` using `hf_indφ`.
    have hφ_X :
        φ (Ideal.Quotient.mk I₁ Polynomial.X) =
          Ideal.Quotient.mk I₂ (R % P₂) := by
      calc
        φ (Ideal.Quotient.mk I₁ Polynomial.X) = g Polynomial.X := by simp [φ]
        _ = π₂ (f_m.toRingHom
              (Ideal.Quotient.mk I₁m Polynomial.X)) := by rfl
        _ = π₂ (Ideal.Quotient.mk I₂m R) := by
            have hR_to :
                f_m.toRingHom (Ideal.Quotient.mk I₁m Polynomial.X) =
                  Ideal.Quotient.mk I₂m R := by
              simpa [I₁m, I₂m] using hR
            rw [hR_to]
        _ = Ideal.Quotient.mk I₂ R := by
          simp [π₂]
        _ = Ideal.Quotient.mk I₂ (R % P₂) := by
          symm
          simpa [I₂] using quotient_mk_mod_eq_mk (𝕜 := 𝕜) P₂ R
    have hf_to :
        f.toRingHom (Ideal.Quotient.mk I₁ Polynomial.X) =
          Ideal.Quotient.mk I₂ (R % P₂) := by
      have hcomp :=
        congrArg (fun h => h (Ideal.Quotient.mk I₁ Polynomial.X)) hf_indφ
      exact hcomp.trans hφ_X
    simpa [I₁, I₂] using hf_to

  have hf_mkX_Qf :
      f (Ideal.Quotient.mk (Ideal.span ({P₁} : Set (Polynomial 𝕜))) Polynomial.X) =
        Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) Qf := by
    let mk₁ :
        Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) :=
      Ideal.Quotient.mk _
    let mk₂ :
        Polynomial 𝕜 →+* (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) :=
      Ideal.Quotient.mk _
    have h := congrArg (fun g =>
        g (mk₁ Polynomial.X)) hf_ind
    -- `hf_ind` says the quotient map induced by `fX` agrees with `f`.
    have h' :
        mk₂ (fX Polynomial.X) =
          f.toRingHom (mk₁ Polynomial.X) := by
      simpa [mk₁, mk₂, Ideal.quotientMap_mk] using h
    -- Use the defining property `fX X = Qf`.
    simpa [mk₁, mk₂, hfX_X] using h'.symm

  have hmk_eq :
      Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) Qf =
        Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) (R % P₂) := by
    -- Compare the two expressions for `f(X)`.
    calc
      Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) Qf =
          f (Ideal.Quotient.mk (Ideal.span ({P₁} : Set (Polynomial 𝕜))) Polynomial.X) := by
            simpa using hf_mkX_Qf.symm
      _ = Ideal.Quotient.mk (Ideal.span ({P₂} : Set (Polynomial 𝕜))) (R % P₂) := hf_X_eq

  have hQfdeg₂ : Qf.natDegree < P₂.natDegree := by
    simpa [hdeg'] using hQfdeg
  have hRdeg₂ : (R % P₂).natDegree < P₂.natDegree := by
    have hP₂deg0 : P₂.natDegree ≠ 0 := by
      exact ne_of_gt hP₂.natDegree_pos
    simpa using Polynomial.natDegree_mod_lt R hP₂deg0

  have hQf_eq_mod : Qf = R % P₂ :=
    prop2_4_unique_reduced_poly_rep (𝕜 := 𝕜) (P := P₂) hQfdeg₂ hRdeg₂ (by simpa using hmk_eq)

  have hQf' : Qf.derivative ≠ 0 := by
    simpa [hQf_eq_mod] using hR'

  have hQf_pos : 1 ≤ Qf.natDegree := by
    have hQf0 : Qf.natDegree ≠ 0 := by
      intro h0
      have hconst : Qf = Polynomial.C (Qf.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have : Qf.derivative = 0 := by
        rw [hconst]
        simp
      exact hQf' this
    exact (Nat.succ_le_iff).2 (Nat.pos_of_ne_zero hQf0)

  -- Finally, apply Theorem 2.8 for all `n > 1`.
  intro n hn
  cases n with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hn)
  | succ n =>
      cases n with
      | zero =>
          -- `n = 1`
          refine ⟨?_⟩
          have f₁ :
              (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
                (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) := by
            simpa [I₁, I₂] using f
          have hI₁ :
              (Ideal.span ({P₁ ^ (1 : ℕ)} : Set (Polynomial 𝕜)) :
                  Ideal (Polynomial 𝕜)) =
                Ideal.span ({P₁} : Set (Polynomial 𝕜)) := by
            simp
          have hI₂ :
              (Ideal.span ({P₂ ^ (1 : ℕ)} : Set (Polynomial 𝕜)) :
                  Ideal (Polynomial 𝕜)) =
                Ideal.span ({P₂} : Set (Polynomial 𝕜)) := by
            simp
          -- Simplify the exponent and rewrite the ideals to match `f₁`.
          simp
          rw [hI₁, hI₂]
          exact f₁
      | succ n =>
          -- `n ≥ 2`
          have hn' : 1 < Nat.succ (Nat.succ n) :=
            Nat.succ_lt_succ (Nat.succ_pos n)
          rcases hIJn_all (Nat.succ (Nat.succ n)) with ⟨hIJn, -⟩
          have hex :
              (∃ e :
                    (Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))) ≃+*
                      (Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))),
                  e.toRingHom =
                    Ideal.quotientMap (I :=
                        Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)))
                      (Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))) fX hIJn) ∧
                RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
                  (A :=
                    Polynomial 𝕜 ⧸
                      Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)))
                  (B :=
                    Polynomial 𝕜 ⧸
                      Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)))
                  (Ideal.quotientMap (I :=
                      Ideal.span ({P₁ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜)))
                    (Ideal.span ({P₂ ^ Nat.succ (Nat.succ n)} : Set (Polynomial 𝕜))) fX hIJn)
                  σ_f := by
            exact
              (theorem_2_8 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf_stab σX hσX Qf
                    ⟨hQfdeg, hQf_pos⟩ fX hfX_X hfX hfX_def hIJ hf_ind Sf hSf
                    (Nat.succ (Nat.succ n)) hn' hIJn).2 hQf'
          rcases hex.1 with ⟨e, -⟩
          exact ⟨e⟩
end SomeLocalRings
