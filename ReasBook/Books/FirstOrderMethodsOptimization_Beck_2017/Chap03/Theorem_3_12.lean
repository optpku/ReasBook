/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → EReal} {x : E}

/- Theorem 3.12 is `source-facing`: its public content is the Chapter 3 identification of the
custom directional derivative with evaluation of the owner Fréchet derivative. The supporting
`bridge/view` step factors first through the owner line-derivative predicate `HasLineDerivAt` for
the real-valued restriction `y ↦ (f y).toReal`; the Fréchet-derivative input is stronger derived
API. The primitive data for the directional-limit statement are therefore the interior
finite-domain hypothesis, the direction `d`, and a line-derivative witness in that direction. -/

-- Proof sketch: a line derivative in direction `d` gives the right-hand real slope limit with
-- value `ℓ`. Converting this limit to `EReal` along `𝓝[>] 0` and using that points sufficiently
-- close to `x` along the ray remain in the finite domain lets us replace `toReal` by the original
-- extended-real values, yielding the chapter directional derivative.
/-- If `x` lies in the interior of the finite domain and the real-valued restriction of `f` has
line derivative `ℓ` at `x` in the direction `d`, then the chapter directional derivative exists
with value `ℓ`. -/
theorem has_directional_derivative_at_of_mem_interior_of_hasLineDerivAt
    (hx : x ∈ interior (finite_domain f))
    {d : E} {ℓ : ℝ}
    (hd : HasLineDerivAt ℝ (fun y ↦ (f y).toReal) ℓ x d) :
    has_directional_derivative_at f x d (ℓ : EReal) := by
  rw [has_directional_derivative_at]
  have hxfd : x ∈ finite_domain f := interior_subset hx
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ finite_domain f := by
    have hcont : Tendsto (fun t : ℝ ↦ x + t • d) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa using
        tendsto_const_nhds.add
          (((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).smul_const d))
    have hinterior :
        ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ interior (finite_domain f) := by
      exact (hcont.eventually <| isOpen_interior.mem_nhds hx).filter_mono nhdsWithin_le_nhds
    exact hinterior.mono fun t ht ↦ interior_subset ht
  let fReal : E → ℝ := fun y ↦ (f y).toReal
  have hslope :
      Tendsto
        (fun t : ℝ ↦ (((fReal (x + t • d) - fReal x) / t : ℝ) : EReal))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((ℓ : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 <| by
      simpa [fReal, div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        hd.tendsto_slope_zero_right
  refine hslope.congr' ?_
  filter_upwards [hdom] with t ht
  have hxt : ((f (x + t • d)).toReal : EReal) = f (x + t • d) := by
    exact EReal.coe_toReal (mem_effective_domain.mp ht.1).ne ht.2
  have hx0 : ((f x).toReal : EReal) = f x := by
    exact EReal.coe_toReal (mem_effective_domain.mp hxfd.1).ne hxfd.2
  simp [fReal, hxt, hx0, EReal.coe_sub, EReal.coe_div]

/-- Theorem 3.12: if `x` lies in the interior of the finite domain and the real-valued restriction
of `f` has Fréchet derivative `g` at `x`, then for every direction `d` the directional derivative
of `f` at `x` along `d` is the pairing `g d`. -/
theorem directional_derivative_eq_of_mem_interior_of_hasFDerivAt
    {g : StrongDual ℝ E}
    (hx : x ∈ interior (finite_domain f))
    (hg : HasFDerivAt (fun y ↦ (f y).toReal) g x) (d : E) :
    directional_derivative f x d = (g d : EReal) := by
  have hline : HasLineDerivAt ℝ (fun y ↦ (f y).toReal) (g d) x d := by
    simpa using hg.hasLineDerivAt d
  exact directional_derivative_eq_of_has_directional_derivative_at
    (has_directional_derivative_at_of_mem_interior_of_hasLineDerivAt hx hline)

end
