module

public import ReasLib.Analysis.PSeries

public section

open Filter
open scoped Asymptotics

/- Infrastructure I.20 (Tail sums at a parabolic scale) (1): The general
p-series convergence and divergence criterion. -/
#check (Asymptotics.IsEquivalent.summable_rpow_iff :
  ∀ {ε : ℕ → ℝ} {C p q : ℝ},
    ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p)) → 0 < C → 0 < p →
      (Summable (fun j ↦ ε j ^ q) ↔ p < q))

/- Infrastructure I.20 (Tail sums at a parabolic scale) (2): The sharp
asymptotic formula for shifted power tails. -/
#check (Asymptotics.IsEquivalent.tail_rpow_isEquivalent :
  ∀ {ε : ℕ → ℝ} {C p q : ℝ},
    ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p)) → 0 < C → 0 < p → p < q →
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) ~[atTop]
        (fun j : ℕ ↦ C ^ q * (p / (q - p)) * (j : ℝ) ^ (1 - q / p)))

/- Infrastructure I.20 (Tail sums at a parabolic scale) (3): The index-scale
Big-O estimate for shifted power tails. -/
#check (Asymptotics.IsEquivalent.tail_rpow_isBigO :
  ∀ {ε : ℕ → ℝ} {C p q : ℝ},
    ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p)) → 0 < C → 0 < p → p < q →
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) =O[atTop]
        (fun j : ℕ ↦ (j : ℝ) ^ (1 - q / p)))

/- Infrastructure I.20 (Tail sums at a parabolic scale) (4): The intrinsic-scale
Big-O estimate for shifted power tails. -/
#check (Asymptotics.IsEquivalent.tail_rpow_isBigO_self :
  ∀ {ε : ℕ → ℝ} {C p q : ℝ},
    ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p)) → 0 < C → 0 < p → p < q →
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) =O[atTop]
        (fun j : ℕ ↦ ε j ^ (q - p)))
