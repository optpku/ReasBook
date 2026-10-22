/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1

namespace ProbabilityTheory

variable {n : ℕ}

/-- The Euclidean state space used in Theorem 26.26. -/
abbrev StroockVaradhanState (n : ℕ) :=
  Fin n → ℝ

/-- The canonical continuous-path space over the Stroock--Varadhan state space. -/
abbrev StroockVaradhanPathSpace (n : ℕ) :=
  EuclideanPathSpace n

/-- The diffusion-matrix coefficient type used in Theorem 26.26. -/
abbrev StroockVaradhanDiffusionMatrixCoeff (n : ℕ) :=
  NNReal → StroockVaradhanState n → Fin n → Fin n → ℝ

/-- The drift coefficient type used in Theorem 26.26. -/
abbrev StroockVaradhanDriftCoeff (n : ℕ) :=
  NNReal → StroockVaradhanState n → Fin n → ℝ

end ProbabilityTheory
