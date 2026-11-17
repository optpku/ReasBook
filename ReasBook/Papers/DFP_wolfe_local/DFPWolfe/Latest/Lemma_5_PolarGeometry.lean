module

public import ReasLib.Optimization.DFP.Polar.General.ActualGeometry

/-!
# Lemma 8 — polar geometry and uniform separation

Source label: `lem:polar-geometry` in the manuscript `20251117-DFP/arXiv.tex`.
The actual tail-product radius excesses above one have principal term
`((1+β)/(1-β)) (rE+rO) τ^(1-β)` and error `O(τ^(2(1-β)))`.
Radial decrements are comparable to `τ²`, physical steps to `τ`, and all
distinct point pairs are separated by a fixed multiple of their maximum
scale. The complete cluster set is the unit circle. Constants are chosen
before the final starting index.
-/

#check DFP.Polar.General.ActualGeometry.existsSourceGeometry
