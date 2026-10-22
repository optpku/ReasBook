/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_8
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_8.HarmonicDiagonal

public section

namespace RealL2

/-- The weighted rescaling attached to Example 2.9. -/
def harmonicDiagonalRescaling (g : lp (fun _ : ℕ ↦ ℝ) 2) : ℕ → ℝ :=
  fun n ↦ ((n : ℝ) + 1) * g n

/-- The weighted rescaling multiplies the `n`th coordinate by `((n : ℝ) + 1)`. -/
theorem harmonicDiagonalRescaling_apply (g : lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    harmonicDiagonalRescaling g n = ((n : ℝ) + 1) * g n :=
  by simp [harmonicDiagonalRescaling]

/-- The canonical candidate solution of `harmonicDiagonal f = g` obtained by weighted
rescaling of `g`. -/
def harmonicDiagonalPreimage (g : lp (fun _ : ℕ ↦ ℝ) 2)
    (hg : Memℓp (harmonicDiagonalRescaling g) 2) : lp (fun _ : ℕ ↦ ℝ) 2 :=
  ⟨harmonicDiagonalRescaling g, hg⟩

/-- The preimage candidate has coordinates given by the weighted rescaling. -/
theorem harmonicDiagonalPreimage_apply (g : lp (fun _ : ℕ ↦ ℝ) 2)
    (hg : Memℓp (harmonicDiagonalRescaling g) 2) (n : ℕ) :
    harmonicDiagonalPreimage g hg n = harmonicDiagonalRescaling g n :=
  by simp [harmonicDiagonalPreimage]

/-- Rescaling the `n`th output coordinate of `harmonicDiagonal` recovers the `n`th input
coordinate. -/
theorem harmonicDiagonal_weighted_apply (f : lp (fun _ : ℕ ↦ ℝ) 2) (n : ℕ) :
    harmonicDiagonalRescaling (harmonicDiagonal f) n = f n := by
  -- Cancel the scalar factor in `ℝ` before reattaching the coordinate `f n`.
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcancel : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
    field_simp [hne]
  have hscaled := congrArg (fun x : ℝ ↦ x * f n) hcancel
  -- Re-expand the weighted coordinate and identify it with the scaled cancellation identity.
  simpa [harmonicDiagonalRescaling_apply, harmonicDiagonal_apply, mul_assoc] using hscaled

/-- The weighted-rescaling preimage solves `harmonicDiagonal f = g` whenever it lies in real
`ℓ²`. -/
theorem harmonicDiagonal_preimage_spec (g : lp (fun _ : ℕ ↦ ℝ) 2)
    (hg : Memℓp (harmonicDiagonalRescaling g) 2) :
    harmonicDiagonal (harmonicDiagonalPreimage g hg) = g := by
  ext n
  -- Cancel the scalar factor in `ℝ` before reattaching the coordinate `g n`.
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcancel : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 := by
    field_simp [hne]
  have hscaled := congrArg (fun x : ℝ ↦ x * g n) hcancel
  -- Re-expand the preimage coordinate and compare with the cancellation identity.
  simpa [harmonicDiagonal_apply, harmonicDiagonalPreimage_apply, harmonicDiagonalRescaling_apply,
    mul_assoc] using hscaled

/-- The equation `harmonicDiagonal f = g` is solvable exactly when the weighted rescaling of `g`
lies in real `ℓ²`. -/
theorem harmonicDiagonal_exists_iff (g : lp (fun _ : ℕ ↦ ℝ) 2) :
    (∃ f : lp (fun _ : ℕ ↦ ℝ) 2, harmonicDiagonal f = g) ↔
      Memℓp (harmonicDiagonalRescaling g) 2 := by
  constructor
  · intro h
    rcases h with ⟨f, hf⟩
    -- Rewrite the weighted datum back to the original `ℓ²` coordinates of the witness.
    have hrescale : harmonicDiagonalRescaling g = fun n ↦ f n := by
      ext n
      rw [← hf]
      exact harmonicDiagonal_weighted_apply f n
    simpa [hrescale] using (lp.memℓp f)
  · intro hg
    -- The canonical weighted-rescaling preimage is the required witness.
    exact ⟨harmonicDiagonalPreimage g hg, harmonicDiagonal_preimage_spec g hg⟩

/-- The weighted norm identity from Example 2.9 (1): the harmonic diagonal from Example 2.8
is an isometry from real
`ℓ²` to the weighted sequence norm `Real.sqrt (∑' n, ((((n : ℝ) + 1) * g n) ^ (2 : ℕ)))`. -/
theorem harmonicDiagonal_weightedNorm_eq (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    Real.sqrt (∑' n : ℕ, ((harmonicDiagonalRescaling (harmonicDiagonal f) n) ^ (2 : ℕ))) = ‖f‖ :=
  by
  -- Replace the weighted harmonic coordinates by the original coordinates of `f`.
  calc
    Real.sqrt (∑' n : ℕ, ((harmonicDiagonalRescaling (harmonicDiagonal f) n) ^ (2 : ℕ))) =
        Real.sqrt (∑' n : ℕ, (f n) ^ (2 : ℕ)) := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          rw [harmonicDiagonal_weighted_apply]
    -- Invoke the standard `ℓ²` norm formula from Example 2.3.
    _ = ‖f‖ := by
          simpa using (norm_eq_sqrt_tsum_sq f).symm

/-- Example 2.9 (2). The equation `harmonicDiagonal f = g` has a unique solution exactly for
those `g : lp (fun _ : ℕ ↦ ℝ) 2` whose weighted rescaling lies in real `ℓ²`. -/
theorem harmonicDiagonal_existsUnique_iff (g : lp (fun _ : ℕ ↦ ℝ) 2) :
    (∃! f : lp (fun _ : ℕ ↦ ℝ) 2, harmonicDiagonal f = g) ↔
      Memℓp (harmonicDiagonalRescaling g) 2 := by
  constructor
  · intro h
    -- Unique solvability implies solvability, so the range criterion applies.
    exact (harmonicDiagonal_exists_iff g).1 h.exists
  · intro hg
    rcases (harmonicDiagonal_exists_iff g).2 hg with ⟨f, hf⟩
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    -- Injectivity upgrades existence to uniqueness.
    exact harmonicDiagonal_injective (hf'.trans hf.symm)

end RealL2
