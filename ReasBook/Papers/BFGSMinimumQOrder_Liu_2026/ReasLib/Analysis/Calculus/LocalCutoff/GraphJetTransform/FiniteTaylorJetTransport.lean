module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.ScalarComposition
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds

public section

universe u v

namespace FiniteTaylorJet

variable {F : Type u} {G : Type v}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Helper for Infrastructure I.16a: evaluating an `ofFunction` coefficient on the
all-ones source vector exposes its factorial-normalized iterated derivative. -/
theorem ofFunction_coeff_apply_one
    {m : ℕ} {f : ℝ → F} {x : ℝ} (n : Fin (m + 1)) :
    (ofFunction ℝ m f x).coeff n (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) =
      ((n : ℕ).factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ (n : ℕ) f x (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) := by
  exact coeff_ofFunction_apply m f x n (fun _ : Fin (n : ℕ) ↦ (1 : ℝ))

/-- Helper for Infrastructure I.16a: a scalar-source finite jet composition
transports its all-ones coefficient to the normalized iterated derivative of
the composite function. -/
theorem comp_ofFunction_coeff_apply_one
    {m : ℕ} {f : ℝ → F} {g : F → G} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x))
    (n : Fin (m + 1)) :
    (comp (ofFunction ℝ m g (f x)) (ofFunction ℝ m f x)).coeff n
        (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) =
      ((n : ℕ).factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ (n : ℕ) (g ∘ f) x
          (fun _ : Fin (n : ℕ) ↦ (1 : ℝ)) := by
  rw [comp_ofFunction_scalar hf hg]
  exact ofFunction_coeff_apply_one n

/- A compact-support branch is often represented by a derivative-constructed jet.
   Keep the support transport at coefficient level so callers need not unfold
   the jet constructor or its factorial normalization. -/

/-- Helper for Infrastructure I.16a: outside the topological support of its source map, every
    coefficient of a derivative-constructed finite Taylor jet is zero. -/
theorem ofFunction_coeff_eq_zero_of_notMem_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (f : E → F) (x : E) (n : Fin (m + 1))
    (hx : x ∉ tsupport f) :
    (ofFunction ℝ m f x).coeff n = 0 := by
  rw [coeff_ofFunction,
    iteratedFDeriv_eq_zero_of_notMem_tsupport f (n : ℕ) hx, smul_zero]

/-- Helper for Infrastructure I.16a: evaluating an outside-support finite Taylor coefficient on
    any repeated or non-repeated direction also gives zero. -/
theorem ofFunction_coeff_apply_eq_zero_of_notMem_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (f : E → F) (x : E) (n : Fin (m + 1))
    (v : Fin (n : ℕ) → E) (hx : x ∉ tsupport f) :
    (ofFunction ℝ m f x).coeff n v = 0 := by
  rw [coeff_ofFunction_apply,
    iteratedFDeriv_eq_zero_of_notMem_tsupport f (n : ℕ) hx]
  simp only [zero_apply, smul_zero]

/- A single vanishing inner block is enough to remove an entire formal branch.
   Keeping this fact at the series level lets support arguments avoid unfolding
   finite-jet truncation or the composition sum. -/

/-- Helper for Infrastructure I.16a: a zero inner block coefficient annihilates the
corresponding formal-multilinear composition branch. -/
theorem branch_eq_zero_of_inner_coeff_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (c : Composition n)
    (i : Fin c.length) (h : p (c.blocksFun i) = 0) :
    q.compAlongComposition p c = 0 := by
  ext v
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  apply ContinuousMultilinearMap.map_coord_zero _ i
  dsimp [FormalMultilinearSeries.applyComposition]
  rw [h, _root_.zero_apply]

/-- Helper for Infrastructure I.16a: a derivative-constructed inner jet outside its
source support annihilates every positive-degree formal composition branch. -/
theorem ofFunction_branch_eq_zero_of_notMem_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (q : FormalMultilinearSeries ℝ F G)
    (f : E → F) (x : E) (c : Composition n)
    (hn : 0 < n) (hx : x ∉ tsupport f) :
    q.compAlongComposition
        (ofFunction ℝ m f x).toFormalMultilinearSeries c = 0 := by
  have hlength_pos : 0 < c.length := c.length_pos_of_pos hn
  let i : Fin c.length := ⟨0, hlength_pos⟩
  have hblock_pos : 0 < c.blocksFun i :=
    lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun i)
  have hinner :
      (ofFunction ℝ m f x).toFormalMultilinearSeries (c.blocksFun i) = 0 := by
    by_cases hle : c.blocksFun i ≤ m
    · rw [toFormalMultilinearSeries_coeff_of_le
        (ofFunction ℝ m f x) hle]
      exact ofFunction_coeff_eq_zero_of_notMem_tsupport f x
        ⟨c.blocksFun i, Nat.lt_succ_of_le hle⟩ hx
    · rw [toFormalMultilinearSeries_coeff_of_lt _ (Nat.lt_of_not_ge hle)]
  exact branch_eq_zero_of_inner_coeff_eq_zero q
    (ofFunction ℝ m f x).toFormalMultilinearSeries c i hinner

/-- Helper for Infrastructure I.16a: outside the support of a scalar-source map,
every positive retained coefficient of its finite-jet composition vanishes. -/
theorem comp_ofFunction_coeff_eq_zero_of_notMem_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (f : E → F) (x : E) (hn : 0 < n) (hnm : n ≤ m)
    (hx : x ∉ tsupport f) :
    (FiniteTaylorJet.comp Q (FiniteTaylorJet.ofFunction ℝ m f x)).coeff
        ⟨n, Nat.lt_succ_of_le hnm⟩ = 0 := by
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  apply Finset.sum_eq_zero
  intro c _hc
  exact ofFunction_branch_eq_zero_of_notMem_tsupport
    Q.toFormalMultilinearSeries f x c hn hx

/-- Helper for Infrastructure I.16a: a zero outer coefficient annihilates the
corresponding formal-multilinear composition branch. -/
theorem branch_eq_zero_of_outer_coeff_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (c : Composition n)
    (h : q c.length = 0) :
    q.compAlongComposition p c = 0 := by
  rw [FormalMultilinearSeries.compAlongComposition]
  rw [h]
  rfl

/-- Helper for Infrastructure I.16a: outside the support of an outer scalar-source map,
every positive retained coefficient of its composition with an arbitrary inner jet vanishes. -/
theorem comp_ofFunction_outer_coeff_eq_zero_of_notMem_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (f : F → G) (x : F)
    (P : FiniteTaylorJet ℝ E F m) (hn : 0 < n) (hnm : n ≤ m)
    (hx : x ∉ tsupport f) :
    (FiniteTaylorJet.comp (FiniteTaylorJet.ofFunction ℝ m f x) P).coeff
        ⟨n, Nat.lt_succ_of_le hnm⟩ = 0 := by
  rw [FiniteTaylorJet.coeff_comp, FormalMultilinearSeries.comp]
  apply Finset.sum_eq_zero
  intro c _hc
  have hlength_pos : 0 < c.length := c.length_pos_of_pos hn
  have hlength_le_n : c.length ≤ n := c.length_le
  have hlength_le_m : c.length ≤ m := hlength_le_n.trans hnm
  have houter :
      (FiniteTaylorJet.ofFunction ℝ m f x).toFormalMultilinearSeries c.length = 0 := by
    rw [toFormalMultilinearSeries_coeff_of_le
      (FiniteTaylorJet.ofFunction ℝ m f x) hlength_le_m]
    exact ofFunction_coeff_eq_zero_of_notMem_tsupport f x
      ⟨c.length, Nat.lt_succ_of_le hlength_le_m⟩ hx
  exact branch_eq_zero_of_outer_coeff_eq_zero
    (FiniteTaylorJet.ofFunction ℝ m f x).toFormalMultilinearSeries
    P.toFormalMultilinearSeries c houter

end FiniteTaylorJet
