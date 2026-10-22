/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

variable {I : Type v}
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

section HilbertSum

variable [Finite I]

-- Proof sketch: unfold the finite Hilbert direct sum through the Chapter 8 owner `⨁ i, f i`, then
-- separate the defining supremum of the Fenchel conjugate into the independent coordinate suprema
-- that define the coordinate conjugates.
/-- Core owner form of Proposition 13.30: the Fenchel conjugate of a finite Hilbert direct sum is
the finite Hilbert direct sum of the coordinate Fenchel conjugates. -/
theorem conjugate_hilbertSumFunction_eq_hilbertSumFunction_conjugate
    (f : ∀ i, H i → EReal) :
    (⨁ i, f i)∗ = ⨁ i, (f i)∗ := sorry

end HilbertSum

section DirectSum

variable [Fintype I]

-- Proof sketch: rewrite the `Γ₀`-valued direct sum as the Chapter 8 owner `⨁ i, ...`, apply the
-- owner-level conjugate identity above, then specialize the resulting finite Hilbert sum back to
-- an ordinary coordinate sum.
/-- Proposition 13.30: after coercing a finite direct sum of `]-∞,+∞]`-valued functions to
`EReal`, its Fenchel conjugate is the finite sum of the coordinate Fenchel conjugates. -/
theorem conjugate_directSumFunction_eq_sum_conjugate
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) :
    (directSumFunction f).asEReal∗ =
      fun u : lp H 2 ↦ ∑ i, (f i).asEReal∗ (u i) := by
  calc
    (directSumFunction f).asEReal∗ = (⨁ i, (f i).asEReal)∗ := by
      congr 1
      ext x
      simpa using directSumFunction_coe_eq_hilbertSumFunction f x
    _ = ⨁ i, ((f i).asEReal)∗ :=
      conjugate_hilbertSumFunction_eq_hilbertSumFunction_conjugate
        (fun i ↦ (f i).asEReal)
    _ = fun u : lp H 2 ↦ ∑ i, (f i).asEReal∗ (u i) := by
      ext u
      have hI : Finite I := by infer_instance
      simp [hilbertSumFunction, hI]
      have hinst : (inferInstance : Fintype I) = Fintype.ofFinite I := Subsingleton.elim _ _
      have huniv :
          (Finset.univ : Finset I) = (@Finset.univ I (Fintype.ofFinite I)) := by
        cases hinst
        rfl
      simpa using
        congrArg (fun s : Finset I ↦ s.sum (fun i ↦ (f i).asEReal∗ (u i))) huniv.symm

section GammaZero

variable [∀ i, CompleteSpace (H i)]

-- Proof sketch: package the source-facing conjugate identity back into `]-∞,+∞]`-valued
-- functions using `gammaZeroConjugate_apply` and the `Γ₀` membership facts supplied by `hf`.
/-- Companion bridge: the `Γ₀`-packaged Fenchel conjugate of the finite direct sum agrees with the
finite direct sum of the packaged coordinate conjugates. -/
theorem gammaZeroConjugate_directSumFunction_eq_directSumFunction_gammaZeroConjugate
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal)) (hf : ∀ i, f i ∈ Γ₀(H i)) :
    gammaZeroConjugate (directSumFunction f)
        (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf) =
      directSumFunction (fun i ↦ gammaZeroConjugate (f i) (hf i)) := by
  ext u
  simpa [directSumFunction_apply, gammaZeroConjugate_apply] using
    congrFun (conjugate_directSumFunction_eq_sum_conjugate f) u

end GammaZero

end DirectSum

end

end ERealFunction
