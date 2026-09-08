module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform

public section

/-!
# Scalar composition of finite Taylor jets

For a one-dimensional source, the formal composition of derivative-constructed finite
Taylor jets agrees with the derivative-constructed jet of the composite.  The proof uses
the uniform Peano composition theorem, so it does not expose the combinatorial definition
of formal jet composition.
-/

open Filter
open scoped Topology

universe u v w

namespace FiniteTaylorJet

variable {Theta : Type u} {F : Type v}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Helper for Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable
contraction): a scalar member of a uniform jet family has a pointwise Peano remainder. -/
theorem IsUniformOn.scalarRemainder_isLittleO {m : ℕ} {f : Theta → ℝ → F}
    {J : Theta → FiniteTaylorJet ℝ ℝ F m} {x : ℝ} {K : Set Theta}
    (hJ : FiniteTaylorJet.IsUniformOn f J x K) {theta : Theta} (htheta : theta ∈ K) :
    (fun h : ℝ => (J theta).remainder (f theta) x h) =o[nhds 0]
      (fun h : ℝ => h ^ m) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨delta, hdelta, hbound⟩ :=
    IsUniformRemainderOn.bound (hJ.remainder c hc)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hdelta] with h hh
  have hsmall : ‖h‖ < delta := by
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hb := hbound theta htheta h hsmall
  simpa only [Real.rpow_natCast, norm_pow] using hb

/-- Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable contraction):
for a scalar source, derivative-constructed finite jets commute with composition in every
finite order. -/
theorem comp_ofFunction_scalar {m : ℕ} {f : ℝ → F} {G : Type w}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x)) :
    comp (ofFunction ℝ m g (f x)) (ofFunction ℝ m f x) =
      ofFunction ℝ m (g ∘ f) x := by
  have hfFamily :
      ∀ theta ∈ ({0} : Set ℝ),
        ContDiffAt ℝ m (Function.uncurry (fun _ : ℝ => f)) (theta, x) := by
    intro theta htheta
    change ContDiffAt ℝ m (f ∘ Prod.snd) (theta, x)
    exact hf.comp (theta, x) contDiffAt_snd
  have hgFamily :
      ∀ theta ∈ ({0} : Set ℝ),
        ContDiffAt ℝ m (Function.uncurry (fun _ : ℝ => g)) (theta, f x) := by
    intro theta htheta
    change ContDiffAt ℝ m (g ∘ Prod.snd) (theta, f x)
    exact hg.comp (theta, f x) contDiffAt_snd
  have hP := isUniformOn_of_contDiffAt m (fun _ : ℝ => f) x
    ({0} : Set ℝ) isCompact_singleton hfFamily
  have hQ := isUniformOn_of_contDiffAt m (fun _ : ℝ => g) (f x)
    ({0} : Set ℝ) isCompact_singleton hgFamily
  have hbase : ∀ theta ∈ ({0} : Set ℝ), (fun _ : ℝ => f) theta x = f x := by
    intro theta htheta
    rfl
  have hcomp := hP.comp hQ hbase
  let J := comp (ofFunction ℝ m g (f x)) (ofFunction ℝ m f x)
  let Kjet := ofFunction ℝ m (g ∘ f) x
  apply eq_of_eval_sub_isLittleO J Kjet
  have hJremRaw := hcomp.scalarRemainder_isLittleO (Set.mem_singleton 0)
  have hcomposite : (fun z : ℝ => g (f z)) = g ∘ f := rfl
  rw [hcomposite] at hJremRaw
  have hJrem :
      (fun h : ℝ => J.remainder (g ∘ f) x h) =o[nhds 0]
        (fun h : ℝ => h ^ m) := by
    simpa only [J] using hJremRaw
  have hgf : ContDiffAt ℝ m (g ∘ f) x := hg.comp x hf
  have hKrem :
      (fun h : ℝ => Kjet.remainder (g ∘ f) x h) =o[nhds 0]
        (fun h : ℝ => h ^ m) := by
    exact remainder_ofFunction_isLittleO hgf
  refine (hKrem.sub hJrem).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards
  intro h
  simp only [J, Kjet, remainder_def]
  abel

/-- Helper for Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable
contraction): every coefficient of a scalar formal jet composition is the corresponding
coefficient of the derivative-constructed composite jet. -/
theorem coeff_comp_ofFunction_scalar {m : ℕ} {f : ℝ → F} {G : Type w}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x))
    (n : Fin (m + 1)) :
    (comp (ofFunction ℝ m g (f x)) (ofFunction ℝ m f x)).coeff n =
      (ofFunction ℝ m (g ∘ f) x).coeff n := by
  rw [comp_ofFunction_scalar hf hg]

end FiniteTaylorJet
