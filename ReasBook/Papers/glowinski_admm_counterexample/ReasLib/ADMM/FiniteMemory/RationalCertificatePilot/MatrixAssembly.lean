/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalComputation

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.MatrixAssembly

universe u v

/-- Expand the two blocks before simplifying coordinate formulas. -/
theorem sum_block {α : Type v} [AddCommMonoid α] (f : Block → α) :
    (∑ b : Block, f b) = f .F + f .J := by
  change f .F + (f .J + 0) = _
  simp only [add_zero]

/-- A coordinate vector, in the orientation used by rational polarization. -/
def unitVector {ι : Type u} [DecidableEq ι] (i : ι) : ι → ℚ :=
  fun k ↦ if k = i then 1 else 0

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Polarization is additive, including for expressions not yet bundled as forms. -/
theorem polar_add (f g : (ι → ℚ) → ℚ) :
    matrixOfQuadratic (fun x ↦ f x + g x) = matrixOfQuadratic f + matrixOfQuadratic g := by
  ext i j
  simp only [matrixOfQuadratic, Matrix.add_apply]
  ring

/-- Subtraction distributes through rational polarization. -/
theorem polar_sub (f g : (ι → ℚ) → ℚ) :
    matrixOfQuadratic (fun x ↦ f x - g x) = matrixOfQuadratic f - matrixOfQuadratic g := by
  ext i j
  simp only [matrixOfQuadratic, Matrix.sub_apply]
  ring

/-- Rational scalar multiplication distributes through polarization. -/
theorem polar_smul (a : ℚ) (f : (ι → ℚ) → ℚ) :
    matrixOfQuadratic (fun x ↦ a * f x) = a • matrixOfQuadratic f := by
  ext i j
  simp only [matrixOfQuadratic, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Finite weighted quadratic sums can be polarized term by term. -/
theorem polar_sum {α : Type v} (s : Finset α) (f : α → (ι → ℚ) → ℚ) :
    matrixOfQuadratic (fun x ↦ ∑ a ∈ s, f a x) = ∑ a ∈ s, matrixOfQuadratic (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; simp [matrixOfQuadratic]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [polar_add, ih]

/-- A product of additive coordinate forms polarizes to a symmetric outer product. -/
theorem polar_mul (f g : (ι → ℚ) → ℚ)
    (hf : ∀ x y, f (x + y) = f x + f y)
    (hg : ∀ x y, g (x + y) = g x + g y) (i j : ι) :
    matrixOfQuadratic (fun x ↦ f x * g x) i j =
      (f (unitVector i) * g (unitVector j) +
        f (unitVector j) * g (unitVector i)) / 2 := by
  change (f (unitVector i + unitVector j) * g (unitVector i + unitVector j) -
    f (unitVector i) * g (unitVector i) - f (unitVector j) * g (unitVector j)) / 2 = _
  rw [hf, hg]
  ring

/-- The storage matrix is recovered by polarization up to its symmetric part. -/
theorem polar_storage {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (i j : Fin k × Fin 2) :
    matrixOfQuadratic (quadraticStorage P) i j = (P i j + P j i) / 2 := by
  simp [matrixOfQuadratic, quadraticStorage_apply, mul_add, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Interpolation positions are additive in the history. -/
theorem interpolationPosition_add {ℓ : ℕ} (b : Block) (i : Option (Fin ℓ))
    (x y : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    interpolationPosition b i (x + y) =
      interpolationPosition b i x + interpolationPosition b i y := by
  cases i with
  | none => simp [interpolationPosition]
  | some i => cases b <;> simp [interpolationPosition, Pi.add_apply] <;> ring

/-- Interpolation normals are additive in the history. -/
theorem interpolationNormal_add {ℓ : ℕ} (γ : ℚ) (b : Block) (i : Option (Fin ℓ))
    (x y : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    interpolationNormal γ b i (x + y) =
      interpolationNormal γ b i x + interpolationNormal γ b i y := by
  cases i with
  | none => simp [interpolationNormal]
  | some i => cases b <;> simp [interpolationNormal, interpolationPosition, Pi.add_apply] <;> ring

/-- One directed interpolation term has a sparse two-coordinate matrix formula. -/
theorem polar_interpolation {ℓ : ℕ} (γ : ℚ) (b : Block) (a d : Option (Fin ℓ))
    (i j : Fin (ℓ + 1) × Fin 2) :
    matrixOfQuadratic (fun x ↦ -interpolationNormal γ b d x *
      (interpolationPosition b a x - interpolationPosition b d x)) i j =
      -(interpolationNormal γ b d (unitVector i) *
          (interpolationPosition b a (unitVector j) - interpolationPosition b d (unitVector j)) +
        interpolationNormal γ b d (unitVector j) *
          (interpolationPosition b a (unitVector i) - interpolationPosition b d (unitVector i))) / 2 := by
  rw [polar_mul]
  · ring
  · intro x y
    rw [interpolationNormal_add]
    ring
  · intro x y
    rw [interpolationPosition_add, interpolationPosition_add]
    ring

/-- The matrix contribution of one directed interpolation inequality. -/
def interpolationEntry {ℓ : ℕ} (γ : ℚ) (b : Block) (a d : Option (Fin ℓ))
    (i j : Fin (ℓ + 1) × Fin 2) : ℚ :=
  -(interpolationNormal γ b d (unitVector i) *
      (interpolationPosition b a (unitVector j) - interpolationPosition b d (unitVector j)) +
    interpolationNormal γ b d (unitVector j) *
      (interpolationPosition b a (unitVector i) - interpolationPosition b d (unitVector i))) / 2

/-- A cheap coordinate matrix for the current-pair squared norm. -/
def currentPairMatrix (ℓ : ℕ) : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ :=
  matrixOfQuadratic (fun Z ↦ Z (0, 0) ^ 2 + Z (0, 1) ^ 2)

/-- The lower matrix can be checked from cached storage and interpolation tables,
without reevaluating the entire quadratic construction at each entry. -/
theorem lowerMatrix_factored {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin (ℓ + 1) × Fin 2) :
    lowerMatrix c e i j =
      (storageMatrix c e i j + storageMatrix c e j i) / 2 -
        (∑ b : Block, ∑ a : Option (Fin ℓ), ∑ d : Option (Fin ℓ),
          reconstructMu c b a d * interpolationEntry (endpointGamma c e) b a d i j) -
        c.zeta * currentPairMatrix ℓ i j := by
  unfold lowerMatrix
  simp_rw [polar_sub, polar_sum, polar_smul]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    polar_storage, polar_interpolation, interpolationEntry, currentPairMatrix]

/-- A symmetric outer-product entry of two coordinate forms. -/
def productEntry (f g : (ι → ℚ) → ℚ) (i j : ι) : ℚ :=
  (f (unitVector i) * g (unitVector j) + f (unitVector j) * g (unitVector i)) / 2

theorem graphPosition_add {ℓ : ℕ} (b : Block) (d : Fin (ℓ + 1))
    (x y : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    ADMM.FiniteMemory.graphPosition b (x + y) d =
      ADMM.FiniteMemory.graphPosition b x d + ADMM.FiniteMemory.graphPosition b y d := by
  cases b <;> simp [ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual,
    Pi.add_apply] <;> ring

theorem graphNormal_add {ℓ : ℕ} (γ : ℚ) (b : Block) (d : Fin (ℓ + 1))
    (x y : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    graphNormal γ b (x + y) d = graphNormal γ b x d + graphNormal γ b y d := by
  cases b <;> simp [graphNormal, ADMM.FiniteMemory.graphPosition,
    ADMM.FiniteMemory.residual, Pi.add_apply] <;> ring

theorem polar_graph {ℓ : ℕ} (γ : ℚ) (b : Block) (a d : Fin (ℓ + 1))
    (i j : Fin (ℓ + 2) × Fin 2) :
    matrixOfQuadratic (fun Z ↦ graphNormal γ b Z a *
      ADMM.FiniteMemory.graphPosition b Z d) i j =
    productEntry (fun Z ↦ graphNormal γ b Z a)
      (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d) i j :=
  polar_mul _ _ (graphNormal_add γ b a) (graphPosition_add b d) i j

theorem polar_graph_diff {ℓ : ℕ} (γ : ℚ) (b : Block) (n a d : Fin (ℓ + 1))
    (i j : Fin (ℓ + 2) × Fin 2) :
    matrixOfQuadratic (fun Z ↦ graphNormal γ b Z n *
      (ADMM.FiniteMemory.graphPosition b Z a - ADMM.FiniteMemory.graphPosition b Z d)) i j =
    productEntry (fun Z ↦ graphNormal γ b Z n)
      (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z a -
        ADMM.FiniteMemory.graphPosition b Z d) i j := by
  apply polar_mul _ _ (graphNormal_add γ b n) _ i j
  intro x y
  rw [graphPosition_add, graphPosition_add]
  ring

theorem polar_residual {ℓ : ℕ} (d : Fin (ℓ + 1)) (i j : Fin (ℓ + 2) × Fin 2) :
    matrixOfQuadratic (fun Z ↦ ADMM.FiniteMemory.residual Z d *
      ADMM.FiniteMemory.residual Z d) i j =
    productEntry (fun Z ↦ ADMM.FiniteMemory.residual Z d)
      (fun Z ↦ ADMM.FiniteMemory.residual Z d) i j := by
  apply polar_mul <;> intro x y <;> simp [ADMM.FiniteMemory.residual, Pi.add_apply] <;> ring

/-- Sparse coordinate expression for the supply matrix before storage completion. -/
def supplyEntry {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i j : Fin (ℓ + 2) × Fin 2) : ℚ :=
  c.omega *
    (productEntry (fun Z ↦ graphNormal γ .F Z 0)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition .F Z 0) i j +
      productEntry (fun Z ↦ graphNormal γ .J Z 0)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition .J Z 0) i j) +
    c.epsilon * productEntry (fun Z ↦ ADMM.FiniteMemory.residual Z 0)
      (fun Z ↦ ADMM.FiniteMemory.residual Z 0) i j +
    ∑ b : Block, ∑ d : Fin ℓ,
      (lagMinusValue c b d * productEntry (fun Z ↦ graphNormal γ b Z 0)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z 0 -
          ADMM.FiniteMemory.graphPosition b Z d.succ) i j +
       lagPlusValue c b d * productEntry (fun Z ↦ graphNormal γ b Z d.succ)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d.succ -
          ADMM.FiniteMemory.graphPosition b Z 0) i j)

/-- Factoring before numeric evaluation avoids three evaluations of every supply. -/
theorem supplyMatrix_factored {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i j : Fin (ℓ + 2) × Fin 2) : supplyMatrix c γ i j = supplyEntry c γ i j := by
  unfold supplyMatrix supply
  simp_rw [pow_two, mul_assoc, polar_add, polar_sum, polar_smul]
  simp only [polar_add, polar_smul, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, polar_graph, polar_graph_diff, polar_residual, supplyEntry]

end ADMM.FiniteMemory.Reconstruction.MatrixAssembly
