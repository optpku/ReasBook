/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {I : Type u} {Ω : Type v} {E : Type w}
variable {J : Type*}

variable [MeasurableSpace Ω] [MeasurableSpace E]

namespace IsExchangeable

variable {X : I → Ω → E} {μ : Measure Ω}

-- Proof sketch: this is exactly the defining permutation-invariance property of an exchangeable
-- family, applied to the chosen finite injective tuple `u` and permutation `σ`.
/-- Helper for Remark 12.2: an exchangeable family is invariant in law under every finite
permutation of an injective coordinate tuple. -/
theorem identDistrib_comp_perm (hX : IsExchangeable X μ) {n : ℕ} (u : Fin n ↪ I)
    (σ : Equiv.Perm (Fin n)) :
    IdentDistrib (fun ω i ↦ X (u (σ i)) ω) (fun ω i ↦ X (u i) ω) μ μ := by
  -- This is exactly the defining permutation-invariance clause of `IsExchangeable`.
  simpa [IsExchangeable] using hX u σ

-- Proof sketch: apply the characterization of exchangeability to the case `n = 1`, using the
-- unique embeddings `Fin 1 ↪ I` selecting the coordinates `i` and `j`.
/-- Helper for Remark 12.2: every pair of coordinates in an exchangeable family is identically
distributed. -/
theorem identDistrib (hX : IsExchangeable X μ) (i j : I) :
    IdentDistrib (X i) (X j) μ μ := by
  classical
  by_cases hij : i = j
  · let u : Fin 1 ↪ I :=
      ⟨fun _ ↦ i, fun a b _ ↦ by simpa using Subsingleton.elim a b⟩
    -- Restrict the one-point tuple law to recover the scalar marginal.
    have htuple :
        IdentDistrib (fun ω k ↦ X (u ((1 : Equiv.Perm (Fin 1)) k)) ω) (fun ω k ↦ X (u k) ω) μ μ :=
      hX.identDistrib_comp_perm u 1
    have hproj :
        IdentDistrib (fun ω ↦ X (u ((1 : Equiv.Perm (Fin 1)) 0)) ω) (fun ω ↦ X (u 0) ω) μ μ :=
      htuple.comp (measurable_pi_apply 0)
    simpa [u, hij] using hproj
  · let u : Fin 2 ↪ I := Function.Embedding.embFinTwo hij
    -- The swap on a two-point tuple exchanges the laws of `X i` and `X j`.
    have htuple :
        IdentDistrib (fun ω k ↦ X (u ((Equiv.swap 0 1) k)) ω) (fun ω k ↦ X (u k) ω) μ μ :=
      hX.identDistrib_comp_perm u (Equiv.swap 0 1)
    have hproj :
        IdentDistrib (fun ω ↦ X (u ((Equiv.swap 0 1) 0)) ω) (fun ω ↦ X (u 0) ω) μ μ :=
      htuple.comp (measurable_pi_apply 0)
    simpa [u, Function.Embedding.embFinTwo_apply_zero, Function.Embedding.embFinTwo_apply_one]
      using hproj.symm

-- Proof sketch: specialize exchangeability of `X` to the composite embedding `v.trans u`.
/-- Helper for Remark 12.2: composing an exchangeable family with an injective reindexing
preserves exchangeability. -/
theorem comp_embedding (hX : IsExchangeable X μ) (u : J ↪ I) :
    IsExchangeable (fun j ↦ X (u j)) μ := by
  intro n v σ
  -- Reindex the original exchangeable family along the composite embedding.
  simpa using hX (v.trans u) σ

end IsExchangeable

/-- Helper for Remark 12.2: permutations of `Fin m` act transitively on injective `Fin n`-tuples. -/
private theorem existsPermApplyEqOfEmbedding {m n : ℕ} (a b : Fin n ↪ Fin m) :
    ∃ ρ : Equiv.Perm (Fin m), ∀ i, ρ (b i) = a i := by
  classical
  let e : Set.range b ≃ Set.range a :=
    { toFun := fun x ↦ ⟨a (b.invOfMemRange x), Set.mem_range_self _⟩
      invFun := fun x ↦ ⟨b (a.invOfMemRange x), Set.mem_range_self _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp }
  -- Extend the permutation on the two finite ranges to all of `Fin m`.
  refine ⟨e.extendSubtype, ?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (b i) (Set.mem_range_self i)]
  simp [e]

/-- Helper for Remark 12.2: restricting identically distributed finite tuples along an embedding
preserves identical distribution. -/
private theorem identDistribRestrictTuple {μ : Measure Ω} {m n : ℕ} {F G : Ω → Fin m → E}
    (hFG : IdentDistrib F G μ μ) (a : Fin n ↪ Fin m) :
    IdentDistrib (fun ω i ↦ F ω (a i)) (fun ω i ↦ G ω (a i)) μ μ := by
  -- Compose the ambient tuple law with the measurable restriction map.
  have hrestrict : Measurable (fun z : Fin m → E ↦ fun i ↦ z (a i)) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply (a i)
  simpa [Function.comp] using hFG.comp hrestrict

-- Proof sketch: move the two injective tuples into a common finite `Fin` index set using a finite
-- embedding of their combined range, then apply exchangeability to the ambient finite tuple and
-- restrict back.
/-- Remark 12.2: a family is exchangeable if and only if for every `n` and every two injective
choices of `n` indices, the corresponding `n`-dimensional random vectors have the same law. -/
theorem isExchangeable_iff_identDistrib_of_pairwise_distinct (X : I → Ω → E)
    (μ : Measure Ω := by volume_tac) :
    IsExchangeable X μ ↔
      ∀ n, ∀ u v : Fin n ↪ I,
        IdentDistrib (fun ω i ↦ X (u i) ω) (fun ω i ↦ X (v i) ω) μ μ := by
  constructor
  · intro hX n u v
    classical
    let s : Set I := Set.range u ∪ Set.range v
    have hs : s.Finite := (Set.finite_range u).union (Set.finite_range v)
    obtain ⟨m, w, hw⟩ := hs.fin_embedding
    let aFun : Fin n → Fin m := fun i ↦
      w.invOfMemRange ⟨u i, by
        rw [hw]
        exact Or.inl (Set.mem_range_self i)⟩
    have haFun_injective : Function.Injective aFun := by
      intro i j hij
      apply u.injective
      simpa [aFun] using congrArg w hij
    let a : Fin n ↪ Fin m := ⟨aFun, haFun_injective⟩
    let bFun : Fin n → Fin m := fun i ↦
      w.invOfMemRange ⟨v i, by
        rw [hw]
        exact Or.inr (Set.mem_range_self i)⟩
    have hbFun_injective : Function.Injective bFun := by
      intro i j hij
      apply v.injective
      simpa [bFun] using congrArg w hij
    let b : Fin n ↪ Fin m := ⟨bFun, hbFun_injective⟩
    have ha_apply : ∀ i, w (a i) = u i := by
      intro i
      simp [a, aFun]
    have hb_apply : ∀ i, w (b i) = v i := by
      intro i
      simp [b, bFun]
    obtain ⟨ρ, hρ⟩ := existsPermApplyEqOfEmbedding a b
    -- Reorder the ambient tuple indexed by `w`, then restrict back to the chosen coordinates.
    have hambient : IdentDistrib (fun ω i ↦ X (w (ρ i)) ω) (fun ω i ↦ X (w i) ω) μ μ :=
      hX.identDistrib_comp_perm w ρ
    have hrestricted :
        IdentDistrib (fun ω i ↦ X (w (ρ (b i))) ω) (fun ω i ↦ X (w (b i)) ω) μ μ :=
      identDistribRestrictTuple hambient b
    simpa [hρ, ha_apply, hb_apply] using hrestricted
  · intro h n u σ
    -- Specialize the injective-index criterion to the tuple `u` and its permuted version.
    simpa using h n (σ.toEmbedding.trans u) u
