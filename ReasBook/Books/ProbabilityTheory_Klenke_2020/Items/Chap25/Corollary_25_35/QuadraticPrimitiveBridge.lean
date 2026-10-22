/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_33

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

namespace ProbabilityTheory

local notation "PathSpace" => C(NNReal, ℝ)

/-- Helper for Corollary 25.35: if the mixed quadratic-covariation primitive is given by an
interval integral against a density `aij`, then the corresponding weighted pathwise quadratic
covariation at a fixed horizon should reduce to the weighted interval integral against the same
density. This theorem-local owner isolates the repeatedly failing primitive-to-interval bridge
from the main corollary file. -/
theorem pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationDensity
    (H : NNReal → ℝ) {Yi Yj : PathSpace} {aii aij ajj : ℝ → ℝ}
    (hii :
      HasQuadraticCovariationAlong
        Yi
        Yi
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), aii s))
    (hjj :
      HasQuadraticCovariationAlong
        Yj
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ajj s))
    (hij :
      HasQuadraticCovariationAlong
        Yi
        Yj
        (fun T ↦ ∫ s in Set.Icc (0 : ℝ) (T : ℝ), aij s))
    (hiiNat :
      ∀ n : ℕ,
        IntegrableOn
          aii
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hijNat :
      ∀ n : ℕ,
        IntegrableOn
          aij
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hjjNat :
      ∀ n : ℕ,
        IntegrableOn
          ajj
          (Set.Icc (0 : ℝ) (n : ℝ)))
    (hH : Continuous H)
    (T : NNReal)
    (hInt :
      IntegrableOn
        aij
        (Set.Icc (0 : ℝ) (T : ℝ))) :
    pathwiseQuadraticCovariationIntegral H Yi Yj T =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), aij s * H s.toNNReal := by
  -- Route correction: the corollary repeatedly stalled while trying to normalize this bridge
  -- inline. Here we package the three scalar densities into the `d = 2` matrix-process surface
  -- already handled in Theorem 25.33, so the main corollary can reuse the existing primitive API.
  let a : NNReal → Unit → Fin 2 → Fin 2 → ℝ := fun t _ i j ↦
    if hi : i = 0 then
      if hj : j = 0 then aii (t : ℝ) else aij (t : ℝ)
    else if hj : j = 1 then
      ajj (t : ℝ)
    else
      0
  have h00_eq :
      ∀ ⦃b s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) b → a s.toNNReal () 0 0 = aii s := by
    intro b s hs
    simp [a, Real.toNNReal_of_nonneg hs.1]
  have h01_eq :
      ∀ ⦃b s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) b → a s.toNNReal () 0 1 = aij s := by
    intro b s hs
    simp [a, Real.toNNReal_of_nonneg hs.1]
  have h11_eq :
      ∀ ⦃b s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) b → a s.toNNReal () 1 1 = ajj s := by
    intro b s hs
    simp [a, Real.toNNReal_of_nonneg hs.1]
  have h00 :
      HasQuadraticCovariationAlong
        Yi
        Yi
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal () 0 0) := by
    intro S
    have hTarget :
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal () 0 0 =
          ∫ s in Set.Icc (0 : ℝ) (S : ℝ), aii s := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 <| Filter.Eventually.of_forall ?_
      intro s hs
      exact h00_eq hs
    simpa [hTarget] using hii S
  have h01 :
      HasQuadraticCovariationAlong
        Yi
        Yj
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal () 0 1) := by
    intro S
    have hTarget :
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal () 0 1 =
          ∫ s in Set.Icc (0 : ℝ) (S : ℝ), aij s := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 <| Filter.Eventually.of_forall ?_
      intro s hs
      exact h01_eq hs
    simpa [hTarget] using hij S
  have h11 :
      HasQuadraticCovariationAlong
        Yj
        Yj
        (fun S ↦ ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal () 1 1) := by
    intro S
    have hTarget :
        ∫ s in Set.Icc (0 : ℝ) (S : ℝ), a s.toNNReal () 1 1 =
          ∫ s in Set.Icc (0 : ℝ) (S : ℝ), ajj s := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 <| Filter.Eventually.of_forall ?_
      intro s hs
      exact h11_eq hs
    simpa [hTarget] using hjj S
  have h00Nat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal () 0 0)
          (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro n
    exact (integrableOn_congr_fun (fun s hs ↦ h00_eq hs) measurableSet_Icc).2 (hiiNat n)
  have h01Nat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal () 0 1)
          (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro n
    exact (integrableOn_congr_fun (fun s hs ↦ h01_eq hs) measurableSet_Icc).2 (hijNat n)
  have h11Nat :
      ∀ n : ℕ,
        IntegrableOn
          (fun s : ℝ ↦ a s.toNNReal () 1 1)
          (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro n
    exact (integrableOn_congr_fun (fun s hs ↦ h11_eq hs) measurableSet_Icc).2 (hjjNat n)
  have h01Int :
      IntegrableOn
        (fun s : ℝ ↦ a s.toNNReal () 0 1)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact (integrableOn_congr_fun (fun s hs ↦ h01_eq hs) measurableSet_Icc).2 hInt
  have hTarget :
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal () 0 1 * H s.toNNReal =
        ∫ s in Set.Icc (0 : ℝ) (T : ℝ), aij s * H s.toNNReal := by
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 <| Filter.Eventually.of_forall ?_
    intro s hs
    change a s.toNNReal () 0 1 * H s.toNNReal = aij s * H s.toNNReal
    rw [h01_eq hs]
  calc
    pathwiseQuadraticCovariationIntegral H Yi Yj T
        =
      ∫ s in Set.Icc (0 : ℝ) (T : ℝ), a s.toNNReal () 0 1 * H s.toNNReal := by
          exact
            pathwiseQuadraticCovariationIntegral_eq_intervalIntegral_of_covariationPrimitive
              (Ω := Unit)
              (a := a)
              (d := 2)
              (ω := ())
              (i := (0 : Fin 2))
              (j := (1 : Fin 2))
              (H := H)
              (Yi := Yi)
              (Yj := Yj)
              h00
              h11
              h01
              h00Nat
              h01Nat
              h11Nat
              hH
              T
              h01Int
    _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), aij s * H s.toNNReal := hTarget

end ProbabilityTheory
