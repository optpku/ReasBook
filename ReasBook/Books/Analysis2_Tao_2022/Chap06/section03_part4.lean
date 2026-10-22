/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap06.section03_part3

section Chap06
section Section03

open scoped Topology

/-- Helper for Theorem 6.2: specialize Theorem 6.1 to `E = F` and `F = U` to package the
within-`F` Fréchet derivative at `x₀` together with its coordinate-sum evaluation formula. -/
lemma helperForTheorem_6_2_fderiv_data_from_6_1
    {n m : ℕ}
    {F U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀U : x₀ ∈ interior U)
    (hUF : U ⊆ F)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hpartial : ∀ j : Fin n, ∀ x, x ∈ U → HasPartialDerivWithinAt F f x j (g j x))
    (hcont : ∀ j : Fin n, ContinuousWithinAt (g j) U x₀) :
    ∃ f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt f f' F x₀ ∧
        ∀ w : EuclideanSpace ℝ (Fin n),
          f' w = ∑ j : Fin n, w j • g j x₀ := by
  exact hasFDerivAt_of_continuous_partialDerivWithinAt
    (E := F)
    (F := U)
    (hFE := hUF)
    (hx₀ := hx₀U)
    (g := g)
    hpartial
    hcont

/-- Helper for Theorem 6.2: a within-`F` Fréchet derivative and its coordinate-sum evaluation
formula imply the punctured directional limit with target `∑ j, v j • g j x₀`. -/
lemma helperForTheorem_6_2_directional_limit_to_sum
    {n m : ℕ}
    {F : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hx₀F : x₀ ∈ interior F)
    (hfd : HasFDerivWithinAt f f' F x₀)
    (hf' : ∀ w : EuclideanSpace ℝ (Fin n), f' w = ∑ j : Fin n, w j • g j x₀) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ F})
      (𝓝 (∑ j : Fin n, v j • g j x₀)) := by
  have hlim :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ F})
        (𝓝 (f' v)) :=
    helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀F
      hfd
  simpa [hf' v] using hlim

/-- Helper for Theorem 6.2: project a vector-valued limit in Euclidean space to any coordinate. -/
lemma helperForTheorem_6_2_component_limit_from_vector_limit
    {m : ℕ}
    {L : Filter ℝ}
    {φ : ℝ → EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin m)}
    (hφ : Filter.Tendsto φ L (𝓝 y))
    (i : Fin m) :
    Filter.Tendsto (fun t : ℝ => (φ t) i) L (𝓝 (y i)) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  have hφe : Filter.Tendsto (fun t : ℝ => e (φ t)) L (𝓝 (e y)) :=
    (e.continuous.tendsto y).comp hφ
  have hcoord : Filter.Tendsto (fun t : ℝ => (e (φ t)) i) L (𝓝 ((e y) i)) :=
    tendsto_pi_nhds.1 hφe i
  simpa [e] using hcoord

/-- Helper for Theorem 6.2: the `i`-th coordinate of `∑ j, v j • g j x₀` is the dot-product
`dotProduct v (fun j => (g j x₀) i)`. -/
lemma helperForTheorem_6_2_sum_component_eq_dotProduct
    {n m : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n))
    (i : Fin m) :
    ((∑ j : Fin n, v j • g j x₀) i)
      = dotProduct v (fun j : Fin n => (g j x₀) i) := by
  simp [dotProduct]

/-- Theorem 6.2: Let `F ⊆ ℝⁿ` and `f : ℝⁿ → ℝᵐ`, and let `x₀ ∈ interior F`.
Assume there is a neighborhood `U` of `x₀` with `U ⊆ F` such that for each coordinate
`j : Fin n`, the partial derivative of `f` with respect to `xⱼ` exists at every `x ∈ U`
within `F` and is represented by `g j x`, and the map `g j` is continuous at `x₀`
within `U`. Then for every direction `v`, the directional difference quotient of `f`
at `x₀` along `v` (equation 6.u93) converges to `∑ⱼ vⱼ • gⱼ(x₀)` (equation 6.u94).
In the scalar-valued case `m = 1`, the `0`-th coordinate form is
`Dᵥ f(x₀) = v • ∇f(x₀)` in dot-product form (equation 6.u95). -/
theorem directionalDerivWithinAt_eq_sum_partialDeriv_of_continuousAt
    {n m : ℕ}
    {F U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀F : x₀ ∈ interior F)
    (hx₀U : x₀ ∈ interior U)
    (hUF : U ⊆ F)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hpartial : ∀ j : Fin n, ∀ x, x ∈ U → HasPartialDerivWithinAt F f x j (g j x))
    (hcont : ∀ j : Fin n, ContinuousWithinAt (g j) U x₀)
    (v : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ F})
      (𝓝 (∑ j : Fin n, v j • g j x₀)) ∧
      (m = 1 →
        ∀ i : Fin m,
          Filter.Tendsto
            (fun t : ℝ => (t⁻¹ • (f (x₀ + t • v) - f x₀)) i)
            (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ F})
            (𝓝 (dotProduct v (fun j : Fin n => (g j x₀) i)))) := by
  rcases helperForTheorem_6_2_fderiv_data_from_6_1
    (hx₀U := hx₀U)
    (hUF := hUF)
    (g := g)
    (hpartial := hpartial)
    (hcont := hcont) with ⟨f', hfd, hf'⟩
  have hvectorLimit :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ F})
        (𝓝 (∑ j : Fin n, v j • g j x₀)) :=
    helperForTheorem_6_2_directional_limit_to_sum
      (g := g)
      (hx₀F := hx₀F)
      (hfd := hfd)
      (hf' := hf')
  constructor
  · exact hvectorLimit
  · intro _ i
    have hcoordLimit :
        Filter.Tendsto
          (fun t : ℝ => (t⁻¹ • (f (x₀ + t • v) - f x₀)) i)
          (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ F})
          (𝓝 ((∑ j : Fin n, v j • g j x₀) i)) :=
      helperForTheorem_6_2_component_limit_from_vector_limit
        (hφ := hvectorLimit)
        i
    simpa [helperForTheorem_6_2_sum_component_eq_dotProduct (g := g) (x₀ := x₀) (v := v) i] using
      hcoordLimit


end Section03
end Chap06
