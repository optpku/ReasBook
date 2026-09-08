module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.OfFunctionOperations
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison

public section

/-!
# Splitting finite Taylor jets modulo a higher-order remainder

This file packages the common pattern of splitting a function into two model pieces minus their
shared base piece, up to an error one order beyond the retained finite Taylor jet.
-/

open Filter
open scoped Topology

universe u

namespace FiniteTaylorJet

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `f = s + t - c + O(h^(m+1))` near the expansion point, then order-`m` jet
identities for the three pieces assemble into the corresponding identity for `f`. -/
theorem ofFunction_split_of_isBigO_succ {m : ℕ}
    {f s t c s' t' c' : ℝ → F} {a : ℝ}
    (hf : ContDiffAt ℝ m f a)
    (hs : ContDiffAt ℝ m s a) (ht : ContDiffAt ℝ m t a)
    (hc : ContDiffAt ℝ m c a)
    (hs' : ContDiffAt ℝ m s' a) (ht' : ContDiffAt ℝ m t' a)
    (hc' : ContDiffAt ℝ m c' a)
    (hrem : (fun h : ℝ =>
      f (a + h) - (s (a + h) + t (a + h) - c (a + h))) =O[𝓝 0]
        (fun h : ℝ => h ^ (m + 1)))
    (hsJet : ofFunction ℝ m s a = ofFunction ℝ m s' a)
    (htJet : ofFunction ℝ m t a = ofFunction ℝ m t' a)
    (hcJet : ofFunction ℝ m c a = ofFunction ℝ m c' a) :
    ofFunction ℝ m f a =
      ofFunction ℝ m (fun x => s' x + t' x - c' x) a := by
  have hsum :
      ofFunction ℝ m (fun x => s x + t x) a =
        ofFunction ℝ m (fun x => s' x + t' x) a :=
    ofFunction_add_congr hs hs' ht ht' hsJet htJet
  have hsplit :
      ofFunction ℝ m (fun x => s x + t x - c x) a =
        ofFunction ℝ m (fun x => s' x + t' x - c' x) a :=
    ofFunction_sub_congr (hs.add ht) (hs'.add ht') hc hc' hsum hcJet
  exact (ofFunction_eq_of_sub_isBigO_succ hf ((hs.add ht).sub hc) hrem).trans hsplit

end FiniteTaylorJet
