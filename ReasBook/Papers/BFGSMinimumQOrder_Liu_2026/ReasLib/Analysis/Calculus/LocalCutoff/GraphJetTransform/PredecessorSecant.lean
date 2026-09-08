module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.ScalarComposition
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

public section

namespace FiniteTaylorJet

universe v w

variable {F : Type v} {G : Type w}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Infrastructure I.16 (finite-order graph-jet contraction): for a scalar source, the finite
jet of a composite function is obtained by composing the two derivative-constructed jets. -/
theorem comp_ofFunction {m : ℕ} {f : ℝ → F} {g : F → G} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g (f x)) :
    comp (ofFunction ℝ m g (f x)) (ofFunction ℝ m f x) =
      ofFunction ℝ m (g ∘ f) x := by
  exact comp_ofFunction_scalar hf hg

end FiniteTaylorJet
