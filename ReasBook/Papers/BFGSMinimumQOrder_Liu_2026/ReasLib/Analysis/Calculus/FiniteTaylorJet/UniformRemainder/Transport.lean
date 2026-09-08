module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder

public section

universe u v w x

namespace FiniteTaylorJet

variable {Θ : Type u} {E : Type v} {F : Type w} {G : Type x}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcompose every coefficient of a finite Taylor jet with a continuous
linear map. -/
def postcompContinuousLinearMap {m : ℕ} (L : F →L[ℝ] G)
    (J : FiniteTaylorJet ℝ E F m) : FiniteTaylorJet ℝ E G m where
  coeff n := L.compContinuousMultilinearMap (J.coeff n)

/-- Coefficients of a continuously linear postcomposition are obtained by
postcomposing the original coefficient maps. -/
theorem coeff_postcompContinuousLinearMap {m : ℕ} (L : F →L[ℝ] G)
    (J : FiniteTaylorJet ℝ E F m) (n : Fin (m + 1)) :
    (postcompContinuousLinearMap L J).coeff n =
      L.compContinuousMultilinearMap (J.coeff n) := by
  rfl

/-- Evaluating a continuously linear postcomposition commutes with the map. -/
theorem eval_postcompContinuousLinearMap {m : ℕ} (L : F →L[ℝ] G)
    (J : FiniteTaylorJet ℝ E F m) (h : E) :
    (postcompContinuousLinearMap L J).eval h = L (J.eval h) := by
  rw [eval_eq_sum, eval_eq_sum, map_sum]
  simp only [coeff_postcompContinuousLinearMap,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]

/-- The remainder of a continuously linear postcomposition is the image of
the original remainder. -/
theorem remainder_postcompContinuousLinearMap {m : ℕ} (L : F →L[ℝ] G)
    (J : FiniteTaylorJet ℝ E F m) (f : E → F) (a h : E) :
    (postcompContinuousLinearMap L J).remainder (fun z => L (f z)) a h =
      L (J.remainder f a h) := by
  rw [remainder_def, remainder_def, eval_postcompContinuousLinearMap, map_sub]

/-- Evaluation of a product jet is the pair of the two evaluations. -/
theorem eval_prod {m : ℕ} (P : FiniteTaylorJet ℝ E F m)
    (Q : FiniteTaylorJet ℝ E G m) (h : E) :
    (prod P Q).eval h = (P.eval h, Q.eval h) := by
  simp only [eval_eq_sum, coeff_prod, ContinuousMultilinearMap.prod_apply]
  apply Prod.ext
  · change (ContinuousLinearMap.fst ℝ F G)
      (∑ n, ((P.coeff n) (fun _ => h), (Q.coeff n) (fun _ => h))) =
        ∑ n, (P.coeff n) (fun _ => h)
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_fst']
  · change (ContinuousLinearMap.snd ℝ F G)
      (∑ n, ((P.coeff n) (fun _ => h), (Q.coeff n) (fun _ => h))) =
        ∑ n, (Q.coeff n) (fun _ => h)
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_snd']

/-- The remainder of a product jet is the pair of the two component remainders. -/
theorem remainder_prod {m : ℕ} (P : FiniteTaylorJet ℝ E F m)
    (Q : FiniteTaylorJet ℝ E G m) (f : E → F) (g : E → G) (a h : E) :
    (prod P Q).remainder (fun z => (f z, g z)) a h =
      (P.remainder f a h, Q.remainder g a h) := by
  rw [remainder_def, remainder_def, remainder_def, eval_prod]
  rfl

namespace IsUniformRemainderOn

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- A uniform finite-jet remainder remains uniform after restricting the
parameter set. -/
theorem mono {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K L : Set Θ} {C q : ℝ}
    (hJ : FiniteTaylorJet.IsUniformRemainderOn f J a K C q)
    (hLK : L ⊆ K) :
    FiniteTaylorJet.IsUniformRemainderOn f J a L C q := by
  obtain ⟨δ, hδ, hbound⟩ := bound hJ
  exact (spec f J a L C q).mpr
    ⟨δ, hδ, fun θ hθ h hh => hbound θ (hLK hθ) h hh⟩

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- Uniform finite-jet remainders are invariant under pointwise replacement
of the function and jet families on the parameter set. -/
theorem congr {m : ℕ} {f g : Θ → E → F}
    {P Q : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ} {C q : ℝ}
    (hP : FiniteTaylorJet.IsUniformRemainderOn f P a K C q)
    (hfun : ∀ θ ∈ K, f θ = g θ) (hjet : ∀ θ ∈ K, P θ = Q θ) :
    FiniteTaylorJet.IsUniformRemainderOn g Q a K C q := by
  obtain ⟨δ, hδ, hbound⟩ := bound hP
  refine (spec g Q a K C q).mpr ⟨δ, hδ, ?_⟩
  intro θ hθ h hh
  rw [← hfun θ hθ, ← hjet θ hθ]
  exact hbound θ hθ h hh

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- Postcomposition by a continuous linear map preserves a uniform remainder,
with the coefficient scaled by the operator norm. -/
theorem postcompContinuousLinearMap {m : ℕ} {f : Θ → E → F}
    {J : Θ → FiniteTaylorJet ℝ E F m} {a : E} {K : Set Θ} {C q : ℝ}
    (hJ : FiniteTaylorJet.IsUniformRemainderOn f J a K C q)
    (L : F →L[ℝ] G) :
    FiniteTaylorJet.IsUniformRemainderOn
      (fun θ z => L (f θ z))
      (fun θ => FiniteTaylorJet.postcompContinuousLinearMap L (J θ))
      a K (‖L‖ * C) q := by
  obtain ⟨δ, hδ, hbound⟩ := bound hJ
  refine (spec
    (fun θ z => L (f θ z))
    (fun θ => FiniteTaylorJet.postcompContinuousLinearMap L (J θ))
    a K (‖L‖ * C) q).mpr ⟨δ, hδ, ?_⟩
  intro θ hθ h hh
  rw [remainder_postcompContinuousLinearMap]
  calc
    ‖L ((J θ).remainder (f θ) a h)‖ ≤
        ‖L‖ * ‖(J θ).remainder (f θ) a h‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (C * ‖h‖ ^ q) :=
      mul_le_mul_of_nonneg_left (hbound θ hθ h hh) (norm_nonneg L)
    _ = (‖L‖ * C) * ‖h‖ ^ q := by ring

omit [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] in
/-- Pairing two uniform finite-jet remainders of the same order gives a
uniform product-valued remainder. -/
theorem prod {m : ℕ} {f : Θ → E → F} {g : Θ → E → G}
    {P : Θ → FiniteTaylorJet ℝ E F m}
    {Q : Θ → FiniteTaylorJet ℝ E G m}
    {a : E} {K : Set Θ} {C D q : ℝ}
    (hP : FiniteTaylorJet.IsUniformRemainderOn f P a K C q)
    (hQ : FiniteTaylorJet.IsUniformRemainderOn g Q a K D q) :
    FiniteTaylorJet.IsUniformRemainderOn
      (fun θ z => (f θ z, g θ z))
      (fun θ => FiniteTaylorJet.prod (P θ) (Q θ))
      a K (C + D) q := by
  obtain ⟨δP, hδP, hPbound⟩ := bound hP
  obtain ⟨δQ, hδQ, hQbound⟩ := bound hQ
  refine (spec
    (fun θ z => (f θ z, g θ z))
    (fun θ => FiniteTaylorJet.prod (P θ) (Q θ))
    a K (C + D) q).mpr
      ⟨min δP δQ, lt_min hδP hδQ, ?_⟩
  intro θ hθ h hh
  rw [remainder_prod, Prod.norm_mk]
  calc
    max ‖(P θ).remainder (f θ) a h‖ ‖(Q θ).remainder (g θ) a h‖ ≤
        ‖(P θ).remainder (f θ) a h‖ + ‖(Q θ).remainder (g θ) a h‖ :=
      max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
    _ ≤ C * ‖h‖ ^ q + D * ‖h‖ ^ q :=
      add_le_add
        (hPbound θ hθ h (hh.trans_le (min_le_left _ _)))
        (hQbound θ hθ h (hh.trans_le (min_le_right _ _)))
    _ = (C + D) * ‖h‖ ^ q := by ring

end IsUniformRemainderOn

end FiniteTaylorJet
