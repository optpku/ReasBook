module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap
import all ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
# Independent-radius mixed jets

This file records the proof interface needed before the paper-facing mixed expansion
theorems can be instantiated. It deliberately does not assert regularity of the raw
mixed evaluator: that analytic input belongs to a later cancellation proof.
-/

/-- Independent-radius mixed expansion prerequisite: the canonical state path used by the
mixed evaluator, with the radius kept independent of the signed control coordinate. -/
def independentRadiusPath (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ × ℝ × ℝ :=
  input θ r

/-- Independent-radius mixed expansion prerequisite: the exact output state evaluated on the
canonical independent-radius path. -/
def independentRadiusOutput (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ × ℝ × ℝ :=
  map θ.1 (independentRadiusPath θ r)

/-- Independent-radius mixed expansion prerequisite: the radius coordinate family of the
exact output on the canonical path. -/
def independentRadiusRadius (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusOutput θ r).1

/-- Independent-radius mixed expansion prerequisite: the recovered shape coordinate family
of the exact output on the canonical path. -/
def independentRadiusShape (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusOutput θ r).2.1

/-- Independent-radius mixed expansion prerequisite: the recovered high-scale coordinate
family of the exact output on the canonical path. -/
def independentRadiusScale (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusOutput θ r).2.2

/-- Independent-radius mixed expansion prerequisite: the bounded mixed parameter region is
compact whenever its radius parameters are finite. -/
theorem parameterSet_isCompact (β B : ℝ) :
    IsCompact (parameterSet β B) := by
  have hset : parameterSet β B = Set.Icc (-β) β ×ˢ Metric.closedBall
      (0 : ℝ × ℝ) B := by
    ext θ
    exact mem_parameterSet θ β B
  rw [hset]
  exact isCompact_Icc.prod (isCompact_closedBall (0 : ℝ × ℝ) B)

/-- Independent-radius mixed expansion prerequisite: a scalar family is jointly `C^m` on a
compact parameter fiber at the zero-radius base. The coefficient family is the intended
factorial-normalized Taylor polynomial. -/
structure IndependentRadiusCoefficientGerm
    (f : (ℝ × ℝ × ℝ) → ℝ → ℝ) (K : Set (ℝ × ℝ × ℝ)) (m : ℕ)
    (coeff : Fin (m + 1) → (ℝ × ℝ × ℝ) → ℝ) : Prop where
  regularity : ∀ θ, θ ∈ K →
    ContDiffAt ℝ m (Function.uncurry f) (θ, 0)
  coefficient_eq : ∀ (n : Fin (m + 1)) (θ : ℝ × ℝ × ℝ), θ ∈ K →
    (FiniteTaylorJet.ofFunction ℝ m (f θ) 0).scalarCoeff n = coeff n θ

/-- Independent-radius mixed expansion prerequisite: a coefficient germ identifies the
finite Taylor remainder with the explicit polynomial residual. -/
lemma scalarCoefficientGerm_residual_eq
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} {m : ℕ}
    {coeff : Fin (m + 1) → (ℝ × ℝ × ℝ) → ℝ}
    (hGerm : IndependentRadiusCoefficientGerm f K m coeff)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ K) (r : ℝ) :
    f θ r - ∑ n : Fin (m + 1), coeff n θ * r ^ (n : ℕ) =
      (FiniteTaylorJet.ofFunction ℝ m (f θ) 0).remainder (f θ) 0 r := by
  rw [FiniteTaylorJet.remainder_def]
  rw [FiniteTaylorJet.eval_eq_sum_smul_scalarCoeff]
  simp only [zero_add, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hGerm.coefficient_eq n θ hθ]
  ring

/-- Independent-radius mixed expansion prerequisite: a compactly uniform scalar coefficient
germ yields its explicit scalar remainder estimate. -/
theorem uniformRemainderOn_of_independentRadiusGerm
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} {m : ℕ}
    {coeff : Fin (m + 1) → (ℝ × ℝ × ℝ) → ℝ}
    (hK : IsCompact K)
    (hGerm : IndependentRadiusCoefficientGerm f K m coeff)
    (C : ℝ) (hC : 0 < C) :
    Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ f θ r - ∑ n : Fin (m + 1), coeff n θ * r ^ (n : ℕ))
      K C (m : ℝ) := by
  have hJet := FiniteTaylorJet.uniformRemainderOn_of_contDiffAt m f 0 K hK
    (fun θ hθ ↦ hGerm.regularity θ hθ) C hC
  obtain ⟨δ, hδ, hbound⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound hJet
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ r hr
  have hrnorm : ‖r‖ < δ := by
    simpa only [Real.norm_eq_abs] using hr
  have hbound' := hbound θ hθ r hrnorm
  dsimp only
  rw [scalarCoefficientGerm_residual_eq hGerm hθ r]
  simpa only [Real.norm_eq_abs] using hbound'

/-- Independent-radius mixed expansion prerequisite: the radius coefficient family has the
constant, linear, and displayed quadratic coefficients. -/
def radiusCoefficient (n : Fin 4) (θ : ℝ × ℝ × ℝ) : ℝ :=
  (![0, 1, θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18, 0] : Fin 4 → ℝ) n

/-- Independent-radius mixed expansion prerequisite: the shape coefficient family has the
displayed constant and linear coefficients and vanishing quadratic coefficient. -/
def shapeCoefficient (n : Fin 3) (θ : ℝ × ℝ × ℝ) : ℝ :=
  (![2, θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9, 0] : Fin 3 → ℝ) n

/-- Independent-radius mixed expansion prerequisite: the scale coefficient family has the
displayed constant and linear coefficients and vanishing quadratic coefficient. -/
def scaleCoefficient (n : Fin 3) (θ : ℝ × ℝ × ℝ) : ℝ :=
  (![1, 8 * θ.1, 0] : Fin 3 → ℝ) n

/-- Independent-radius mixed expansion prerequisite: the radius coefficient polynomial is the
displayed constant, linear, and quadratic expression. -/
lemma radiusCoefficient_polynomial (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    ∑ n : Fin 4, radiusCoefficient n θ * r ^ (n : ℕ) =
      r + (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2 := by
  simp [radiusCoefficient, Fin.sum_univ_succ]

/-- Independent-radius mixed expansion prerequisite: the shape coefficient polynomial is the
displayed constant and linear expression. -/
lemma shapeCoefficient_polynomial (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    ∑ n : Fin 3, shapeCoefficient n θ * r ^ (n : ℕ) =
      2 + (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r := by
  simp [shapeCoefficient, Fin.sum_univ_succ]

/-- Independent-radius mixed expansion prerequisite: the scale coefficient polynomial is the
displayed constant and linear expression. -/
lemma scaleCoefficient_polynomial (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    ∑ n : Fin 3, scaleCoefficient n θ * r ^ (n : ℕ) =
      1 + 8 * θ.1 * r := by
  simp [scaleCoefficient, Fin.sum_univ_succ]

/-- Independent-radius mixed expansion prerequisite: a radius coefficient germ supplies the
paper-facing order-three radius remainder for any positive coefficient. -/
theorem radiusRemainderOn_of_germ
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hGerm : IndependentRadiusCoefficientGerm independentRadiusRadius K 3
      radiusCoefficient) (C : ℝ) (hC : 0 < C) :
    Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ independentRadiusRadius θ r - r -
        (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2)
      K C 3 := by
  have hraw := uniformRemainderOn_of_independentRadiusGerm hK hGerm C hC
  unfold Asymptotics.IsUniformRemainderOn at hraw
  obtain ⟨δ, hδ, hbound⟩ := hraw
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ r hr
  have hbound' := hbound θ hθ r hr
  dsimp only at hbound' ⊢
  rw [radiusCoefficient_polynomial] at hbound'
  calc
    ‖independentRadiusRadius θ r - r -
        (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2‖ =
      ‖independentRadiusRadius θ r -
        (r + (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2)‖ := by
      congr 1
      ring
    _ ≤ C * |r| ^ (3 : ℝ) := hbound'

/-- Independent-radius mixed expansion prerequisite: a shape coefficient germ supplies the
paper-facing order-two shape remainder for any positive coefficient. -/
theorem shapeRemainderOn_of_germ
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hGerm : IndependentRadiusCoefficientGerm independentRadiusShape K 2
      shapeCoefficient) (C : ℝ) (hC : 0 < C) :
    Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ independentRadiusShape θ r - 2 -
        (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r)
      K C 2 := by
  have hraw := uniformRemainderOn_of_independentRadiusGerm hK hGerm C hC
  unfold Asymptotics.IsUniformRemainderOn at hraw
  obtain ⟨δ, hδ, hbound⟩ := hraw
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ r hr
  have hbound' := hbound θ hθ r hr
  dsimp only at hbound' ⊢
  rw [shapeCoefficient_polynomial] at hbound'
  calc
    ‖independentRadiusShape θ r - 2 -
        (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r‖ =
      ‖independentRadiusShape θ r -
        (2 + (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r)‖ := by
      congr 1
      ring
    _ ≤ C * |r| ^ (2 : ℝ) := hbound'

/-- Independent-radius mixed expansion prerequisite: a scale coefficient germ supplies the
paper-facing order-two high-scale remainder for any positive coefficient. -/
theorem scaleRemainderOn_of_germ
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hGerm : IndependentRadiusCoefficientGerm independentRadiusScale K 2
      scaleCoefficient) (C : ℝ) (hC : 0 < C) :
    Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ independentRadiusScale θ r - 1 - 8 * θ.1 * r)
      K C 2 := by
  have hraw := uniformRemainderOn_of_independentRadiusGerm hK hGerm C hC
  unfold Asymptotics.IsUniformRemainderOn at hraw
  obtain ⟨δ, hδ, hbound⟩ := hraw
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ r hr
  have hbound' := hbound θ hθ r hr
  dsimp only at hbound' ⊢
  rw [scaleCoefficient_polynomial] at hbound'
  calc
    ‖independentRadiusScale θ r - 1 - 8 * θ.1 * r‖ =
      ‖independentRadiusScale θ r - (1 + 8 * θ.1 * r)‖ := by
      congr 1
      ring
    _ ≤ C * |r| ^ (2 : ℝ) := hbound'

/-- Helper for Infrastructure I.16a: the three independent-radius coefficient germs and their
positive constants form one reusable certificate for the radius, shape, and scale remainders. -/
structure IndependentRadiusMixedRemainderCertificate
    (K : Set (ℝ × ℝ × ℝ))
    (radiusConstant shapeConstant scaleConstant : ℝ) : Prop where
  radius_germ :
    IndependentRadiusCoefficientGerm independentRadiusRadius K 3 radiusCoefficient
  shape_germ :
    IndependentRadiusCoefficientGerm independentRadiusShape K 2 shapeCoefficient
  scale_germ :
    IndependentRadiusCoefficientGerm independentRadiusScale K 2 scaleCoefficient
  radiusConstant_pos : 0 < radiusConstant
  shapeConstant_pos : 0 < shapeConstant
  scaleConstant_pos : 0 < scaleConstant

/-- Infrastructure I.16a: a mixed independent-radius remainder certificate exposes all three
uniform estimates consumed by the paper-facing expansion layer. -/
theorem IndependentRadiusMixedRemainderCertificate.uniformRemainders
    {K : Set (ℝ × ℝ × ℝ)}
    {radiusConstant shapeConstant scaleConstant : ℝ}
    (certificate : IndependentRadiusMixedRemainderCertificate
      K radiusConstant shapeConstant scaleConstant)
    (hK : IsCompact K) :
    Asymptotics.IsUniformRemainderOn
        (fun θ r ↦ independentRadiusRadius θ r - r -
          (θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18) * r ^ 2)
        K radiusConstant 3 ∧
      Asymptotics.IsUniformRemainderOn
        (fun θ r ↦ independentRadiusShape θ r - 2 -
          (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r)
        K shapeConstant 2 ∧
      Asymptotics.IsUniformRemainderOn
        (fun θ r ↦ independentRadiusScale θ r - 1 - 8 * θ.1 * r)
        K scaleConstant 2 := by
  have hradius := radiusRemainderOn_of_germ hK certificate.radius_germ
    radiusConstant certificate.radiusConstant_pos
  have hshape := shapeRemainderOn_of_germ hK certificate.shape_germ
    shapeConstant certificate.shapeConstant_pos
  have hscale := scaleRemainderOn_of_germ hK certificate.scale_germ
    scaleConstant certificate.scaleConstant_pos
  exact ⟨hradius, hshape, hscale⟩

end DFP.TwoLeg.Mixed
