/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_21_Positive_infinite_product_with_first_order_tail_asymptotic.lean
-/

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
