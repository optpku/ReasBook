module

public import ReasLib.Analysis.Asymptotics.PositiveProduct

public section

open Filter
open scoped Asymptotics Topology

/- Infrastructure I.21 (Positive infinite product with first-order tail asymptotic) (1) -/
#check (PositiveProduct.existsLimit :
  ∀ {u a : ℕ → ℝ} {c : ℝ},
    (∀ j, 0 ≤ u j) → Summable u → (∀ j, 0 < a j) →
      (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u →
        ∃ aLim : ℝ, 0 < aLim ∧ Tendsto a atTop (𝓝 aLim))

/- Infrastructure I.21 (Positive infinite product with first-order tail asymptotic) (2) -/
#check (PositiveProduct.subLimitIsLittleO :
  ∀ {u a v : ℕ → ℝ} {c aLim : ℝ},
    (∀ j, 0 ≤ u j) → Summable u → (∀ j, 0 < a j) →
      (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u →
        Tendsto a atTop (𝓝 aLim) →
          (fun j ↦ ∑' k : ℕ, u (j + k)) ~[atTop] v →
            (fun j ↦ a j - aLim - c * aLim * v j) =o[atTop] v)

#check (PositiveProduct.subLimitIsEquivalent :
  ∀ {u a v : ℕ → ℝ} {c aLim : ℝ},
    (∀ j, 0 ≤ u j) → Summable u → (∀ j, 0 < a j) →
      (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u →
        Tendsto a atTop (𝓝 aLim) →
          (fun j ↦ ∑' k : ℕ, u (j + k)) ~[atTop] v → c ≠ 0 →
            (fun j ↦ a j - aLim) ~[atTop] (fun j ↦ c * aLim * v j))
