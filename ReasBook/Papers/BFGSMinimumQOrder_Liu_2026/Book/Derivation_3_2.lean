module

public import Book.Derivation_3_1
public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.StepBounds

public section

universe u

/- Derivation 3.2 (1): a nonzero affine expression can be made arbitrarily small by
choosing its target value first and then solving for the perturbation. -/
#check (PlanarGradient.exists_nearCancellation :
  ∀ (P D ε : ℝ) (hP : P ≠ 0) (hD : D ≠ 0) (hε : 0 < ε),
    ∃ τ δ : ℝ, 0 < |τ| ∧ |τ| < min ε (|P| / 2) ∧
      δ = (τ - P) / D ∧ P + D * δ = τ)

/- Derivation 3.2 (2): solving for a near-cancelling perturbation places its size
between one half and three halves of the cancellation scale. -/
#check (PlanarGradient.nearCancellation_abs_mem_Icc :
  ∀ (P D τ : ℝ) (hP : P ≠ 0) (hD : D ≠ 0) (hτ : |τ| ≤ |P| / 2),
    |(τ - P) / D| ∈
      Set.Icc ((1 / 2 : ℝ) * |P / D|) ((3 / 2 : ℝ) * |P / D|))

/- Derivation 3.2 (3): a nonzero preceding perturbation and positive angular
separation make the next parallel coefficient nonzero. -/
#check (PlanarGradient.parallelCoefficient_ne_zero_of_perturbation :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
      (gPrev g : E) (δPrev : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
      (hDistinct : g ≠ gPrev)
      (hPre : inner ℝ (g - gPrev) g =
        inner ℝ g (PlanarGradient.perturbation o gPrev δPrev))
      (hSeparation : 0 < PlanarGradient.angularSeparation o gPrev g)
      (hδPrev : δPrev ≠ 0),
      PlanarGradient.parallelCoefficient gPrev g ≠ 0)

/- Derivation 3.2 (4): a nonzero affine leading term admits an arbitrarily small
nonzero perturbation whose correction cannot cancel more than half of it. -/
#check (PlanarGradient.exists_retainingPerturbation :
  ∀ (P D ε : ℝ) (hP : P ≠ 0) (hε : 0 < ε),
    ∃ δ : ℝ, 0 < |δ| ∧ |δ| < ε ∧ |D * δ| ≤ |P| / 2)

/- Derivation 3.2 (5): a correction bounded by half of the leading term retains
between one half and three halves of its magnitude. -/
#check (PlanarGradient.retainingPerturbation_abs_mem_Icc :
  ∀ (P D δ : ℝ) (hP : P ≠ 0) (hδ : |D * δ| ≤ |P| / 2),
    |P + D * δ| ∈ Set.Icc (|P| / 2) ((3 / 2 : ℝ) * |P|))

/- Derivation 3.2 (6): the odd-step perturbation and coefficient bounds propagate
the cancellation-scale invariant to the next even index. -/
#check (PlanarGradient.nextCancellationScale_le_min :
  ∀ (j : ℕ) (η c T rCurrent rNext δ : ℝ)
      (hCurrent : 0 < rCurrent) (hNext : 0 < rNext) (hTnonneg : 0 ≤ T)
      (hTnext : T ≤ 2 * rNext) (hTlt : T < 1)
      (hδ : |δ| ≤ c * rCurrent * T ^ (j + 3)) (hc : 0 ≤ c)
      (hcBound : c ≤ min (((2 : ℝ) ^ (j + 3))⁻¹) ((4 / 9 : ℝ) * η)),
    |δ| * rNext / rCurrent ≤
      min (rNext ^ (j + 4)) ((4 / 9 : ℝ) * η * rNext))
