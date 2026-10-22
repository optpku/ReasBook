/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Coefficients
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Growth

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {n : ℕ}

/-- Helper for Theorem 26.26: deterministic-start local-martingale existence is the source-facing
clause-(1) existence owner under the Stroock--Varadhan hypotheses. -/
theorem stroockVaradhan_diracLocalMartingaleSolutionDirect
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (ha_time : ∀ t x i j, a t x i j = a 0 x i j)
    (hb_time : ∀ t x i, b t x i = b 0 x i)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b) :
    ∀ x : StroockVaradhanState n,
      ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
        (P : ProbabilityMeasure Ω) (X : Ω → StroockVaradhanPathSpace n),
        IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X := by
  -- Route correction: the repeated clause-(1) blocker should live on the deterministic-start
  -- local-martingale surface. This support theorem is now a downstream corollary of the public
  -- well-posedness theorem already established in the main file, so it no longer carries a
  -- duplicate analytic construction.
  intro x
  have hWellPosed : LocalMartingaleProblemWellPosed.{u, u} a b :=
    stroockVaradhan_localMartingaleProblemWellPosed.{u, u}
      a
      b
      ha_time
      hb_time
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
  -- Proof comment: the public well-posedness theorem already packages deterministic-start
  -- existence and uniqueness in law; projecting the first component at the chosen start `x`
  -- yields the required local-martingale witness.
  exact ((localMartingaleProblemWellPosed_iff.mp hWellPosed) x).1

end ProbabilityTheory
