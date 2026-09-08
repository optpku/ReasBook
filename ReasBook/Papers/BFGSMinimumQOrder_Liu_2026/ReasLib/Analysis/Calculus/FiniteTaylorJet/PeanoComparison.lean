module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.CoefficientComparison
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder

public section

/-!
# Comparing finite Taylor jets by Peano remainders

This file turns little-o comparison of functions or jet evaluations into equality of their
finite Taylor jets.  It also packages the pointwise Peano remainder of `ofFunction`, avoiding
repeated singleton-family arguments at downstream call sites.
-/

open Filter
open scoped Topology

universe u

namespace FiniteTaylorJet

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two one-variable finite jets are equal when the difference of their evaluations is
little-o of the top retained monomial. -/
theorem eq_of_eval_sub_isLittleO {m : ℕ}
    (J K : FiniteTaylorJet ℝ ℝ F m)
    (hJK : (fun h : ℝ => J.eval h - K.eval h) =o[𝓝 0] fun h : ℝ => h ^ m) :
    J = K := by
  apply ext_coeff
  intro n
  apply ContinuousMultilinearMap.ext_ring
  simpa only [scalarCoeff_apply] using scalarCoeff_eq_of_eval_sub_isLittleO J K hJK n

/-- The derivative-constructed one-variable finite jet has Peano remainder
`o(h ^ m)` at its expansion point. -/
theorem remainder_ofFunction_isLittleO {m : ℕ} {f : ℝ → F} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) :
    (fun h : ℝ => (ofFunction ℝ m f x).remainder f x h) =o[𝓝 0]
      (fun h : ℝ => h ^ m) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hfamily :
      ∀ θ ∈ ({0} : Set ℝ),
        ContDiffAt ℝ m (Function.uncurry (fun _ : ℝ => f)) (θ, x) := by
    intro θ hθ
    change ContDiffAt ℝ m (f ∘ Prod.snd) (θ, x)
    exact hf.comp (θ, x) contDiffAt_snd
  have huniform := uniformRemainderOn_of_contDiffAt m
    (fun _ : ℝ => f) x ({0} : Set ℝ) isCompact_singleton hfamily c hc
  obtain ⟨δ, hδ, hbound⟩ := IsUniformRemainderOn.bound huniform
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hsmall : ‖h‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hb := hbound 0 (Set.mem_singleton 0) h hsmall
  simpa only [Real.rpow_natCast, norm_pow] using hb

/-- If two `C^m` one-variable functions, based at possibly different points, differ by
`o(h ^ m)` after translation to zero, then their order-`m` finite jets agree. -/
theorem ofFunction_eq_of_sub_isLittleO {m : ℕ} {f g : ℝ → F} {x y : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g y)
    (hfg : (fun h : ℝ => f (x + h) - g (y + h)) =o[𝓝 0]
      (fun h : ℝ => h ^ m)) :
    ofFunction ℝ m f x = ofFunction ℝ m g y := by
  let J := ofFunction ℝ m f x
  let K := ofFunction ℝ m g y
  apply eq_of_eval_sub_isLittleO J K
  have hfrem : (fun h : ℝ => J.remainder f x h) =o[𝓝 0]
      (fun h : ℝ => h ^ m) := by
    exact remainder_ofFunction_isLittleO hf
  have hgrem : (fun h : ℝ => K.remainder g y h) =o[𝓝 0]
      (fun h : ℝ => h ^ m) := by
    exact remainder_ofFunction_isLittleO hg
  refine ((hfg.sub hfrem).add hgrem).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards
  intro h
  simp only [J, K, remainder_def]
  abel

/-- A difference of order `O(h ^ (m + 1))` is invisible to the order-`m` finite jets. -/
theorem ofFunction_eq_of_sub_isBigO_succ {m : ℕ} {f g : ℝ → F} {x y : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g y)
    (hfg : (fun h : ℝ => f (x + h) - g (y + h)) =O[𝓝 0]
      (fun h : ℝ => h ^ (m + 1))) :
    ofFunction ℝ m f x = ofFunction ℝ m g y := by
  apply ofFunction_eq_of_sub_isLittleO hf hg
  exact hfg.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self m))

/-- Functions equal in a neighborhood of their common base have equal finite Taylor jets there. -/
theorem ofFunction_eq_of_eventuallyEq {m : ℕ} {f g : ℝ → F} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x)
    (hfg : f =ᶠ[𝓝 x] g) :
    ofFunction ℝ m f x = ofFunction ℝ m g x := by
  apply ofFunction_eq_of_sub_isLittleO hf hg
  have htranslate : Tendsto (fun h : ℝ => x + h) (𝓝 0) (𝓝 x) := by
    have hx : Tendsto (fun _ : ℝ => x) (𝓝 0) (𝓝 x) := tendsto_const_nhds
    have hid : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
    simpa using hx.add hid
  have heq :
      (fun h : ℝ => f (x + h) - g (x + h)) =ᶠ[𝓝 0]
        (fun _ : ℝ => (0 : F)) := by
    filter_upwards [hfg.comp_tendsto htranslate] with h heqh
    exact sub_eq_zero.mpr heqh
  exact (Asymptotics.isLittleO_zero (fun h : ℝ => h ^ m) (𝓝 0)).congr'
    heq.symm Filter.EventuallyEq.rfl

end FiniteTaylorJet
