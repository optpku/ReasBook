/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.Certificate

@[expose] public section

open scoped BigOperators NNReal

namespace ADMM.FiniteMemory.Reconstruction

universe u v

noncomputable section

/-- The lower and upper parameter endpoints used by an exact rational certificate. -/
inductive Endpoint
  | lower
  | upper
  deriving DecidableEq, Fintype

/-- The independent exact rational inputs for one finite-memory certificate interval. -/
structure RationalCase (ℓ : ℕ) where
  gammaLower : ℚ
  gammaUpper : ℚ
  omega : ℚ
  epsilon : ℚ
  zeta : ℚ
  lagMinus : Block → List ℚ
  lagPlus : Block → List ℚ
  packedMu : Block → List ℚ
  upperTriangle : Endpoint → List ℚ

namespace RationalCase

/-- Convert a list of signed integer numerators with a common denominator to rationals. -/
def rationalList (denominator : ℤ) (numerators : List ℤ) : List ℚ :=
  numerators.map fun numerator ↦ (numerator : ℚ) / denominator

/-- Entries of `rationalList` are the corresponding integer numerators divided by
the common denominator. -/
theorem rationalList_getD (denominator : ℤ) (numerators : List ℤ) (i : ℕ) :
    (rationalList denominator numerators).getD i 0 =
      (numerators.getD i 0 : ℚ) / denominator := by
  -- Induct through the list; at an absent index both sides use the zero default.
  induction numerators generalizing i with
  | nil => simp [rationalList, List.getD]
  | cons numerator numerators inductionHypothesis =>
      cases i with
      | zero => simp [rationalList, List.getD]
      | succ i =>
          simpa [rationalList, List.getD] using inductionHypothesis i

/-- Construct a rational case from the signed integer tables and their common denominators. -/
def ofNumerators {ℓ : ℕ} (gammaLower gammaUpper omega epsilon zeta : ℚ)
    (lagDenominator muDenominator : ℤ)
    (lagMinusNumerators lagPlusNumerators packedMuNumerators : Block → List ℤ)
    (upperDenominator : Endpoint → ℤ) (upperNumerators : Endpoint → List ℤ) :
    RationalCase ℓ where
  gammaLower := gammaLower
  gammaUpper := gammaUpper
  omega := omega
  epsilon := epsilon
  zeta := zeta
  lagMinus := fun b ↦ rationalList lagDenominator (lagMinusNumerators b)
  lagPlus := fun b ↦ rationalList lagDenominator (lagPlusNumerators b)
  packedMu := fun b ↦ rationalList muDenominator (packedMuNumerators b)
  upperTriangle := fun e ↦ rationalList (upperDenominator e) (upperNumerators e)

/-- The lower endpoint of a case constructed by `ofNumerators` is the supplied rational. -/
theorem ofNumerators_gammaLower {ℓ : ℕ} (gammaLower gammaUpper omega epsilon zeta : ℚ)
    (lagDenominator muDenominator : ℤ)
    (lagMinusNumerators lagPlusNumerators packedMuNumerators : Block → List ℤ)
    (upperDenominator : Endpoint → ℤ) (upperNumerators : Endpoint → List ℤ) :
    (ofNumerators gammaLower gammaUpper omega epsilon zeta lagDenominator muDenominator
      lagMinusNumerators lagPlusNumerators packedMuNumerators upperDenominator
      upperNumerators : RationalCase ℓ).gammaLower = gammaLower := by
  -- The lower endpoint is stored verbatim by the constructor.
  rfl

/-- `ofNumerators` stores the five scalar inputs and decodes all four exact tables. -/
theorem ofNumerators_spec {ℓ : ℕ} (gammaLower gammaUpper omega epsilon zeta : ℚ)
    (lagDenominator muDenominator : ℤ)
    (lagMinusNumerators lagPlusNumerators packedMuNumerators : Block → List ℤ)
    (upperDenominator : Endpoint → ℤ) (upperNumerators : Endpoint → List ℤ) :
    let c : RationalCase ℓ :=
      ofNumerators gammaLower gammaUpper omega epsilon zeta lagDenominator muDenominator
        lagMinusNumerators lagPlusNumerators packedMuNumerators upperDenominator upperNumerators
    (c.gammaLower, c.gammaUpper, c.omega, c.epsilon, c.zeta) =
        (gammaLower, gammaUpper, omega, epsilon, zeta) ∧
      (c.lagMinus, c.lagPlus, c.packedMu, c.upperTriangle) =
        (fun b ↦ rationalList lagDenominator (lagMinusNumerators b),
          fun b ↦ rationalList lagDenominator (lagPlusNumerators b),
          fun b ↦ rationalList muDenominator (packedMuNumerators b),
          fun e ↦ rationalList (upperDenominator e) (upperNumerators e)) := by
  -- Each conjunct follows independently by reducing the constructor projections.
  constructor
  · rfl
  · rfl

end RationalCase

/-- Select the parameter value belonging to an endpoint. -/
def endpointGamma {ℓ : ℕ} (c : RationalCase ℓ) : Endpoint → ℚ
  | .lower => c.gammaLower
  | .upper => c.gammaUpper

/-- Endpoint selection returns the two stored rational parameters. -/
theorem endpointGamma_apply {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    endpointGamma c e = match e with
      | .lower => c.gammaLower
      | .upper => c.gammaUpper := by
  -- Endpoint elimination exposes the corresponding stored parameter.
  rfl

/-- Read a negative-direction lag weight at the zero-based lag index `i`. -/
def lagMinusValue {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) : ℚ :=
  (c.lagMinus b).getD i 0

/-- A negative-direction lag value is the indicated entry of its exact table. -/
theorem lagMinusValue_apply {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) :
    lagMinusValue c b i = (c.lagMinus b).getD i 0 := by
  -- Lookup is exactly the defining table access.
  rfl

/-- Read a positive-direction lag weight from its exact rational table. -/
def lagPlusValue {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) : ℚ :=
  (c.lagPlus b).getD i 0

/-- A positive-direction lag value is the indicated entry of its exact table. -/
theorem lagPlusValue_apply {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) :
    lagPlusValue c b i = (c.lagPlus b).getD i 0 := by
  -- Lookup is exactly the defining table access.
  rfl

/-- The exact rational analogue of the signed function-value coefficient `h`. -/
def lagCoefficient {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) : ℚ :=
  ∑ d : Fin ℓ, if i ≤ d then lagMinusValue c b d - lagPlusValue c b d else 0

/-- The lag coefficient is the sum of all signed lag weights after the chosen value index. -/
theorem lagCoefficient_apply {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) :
    lagCoefficient c b i =
      ∑ d : Fin ℓ, if i ≤ d then lagMinusValue c b d - lagPlusValue c b d else 0 := by
  -- The displayed finite sum is the definition of the coefficient.
  rfl

/-- The row-major location of an interpolation weight in the packed rational table. -/
def packedIndex {ℓ : ℕ} (i : Option (Fin ℓ)) (j : Fin ℓ) : ℕ :=
  match i with
  | none => j
  | some k => ℓ + k.val * (ℓ - 1) + if j < k then j.val else j.val - 1

/-- The packed index uses the origin row first and then skips each generated diagonal. -/
theorem packedIndex_apply {ℓ : ℕ} (i : Option (Fin ℓ)) (j : Fin ℓ) :
    packedIndex i j = match i with
      | none => j
      | some k => ℓ + k.val * (ℓ - 1) + if j < k then j.val else j.val - 1 := by
  -- Optional-index elimination is already built into the packed rank.
  rfl

/-- Read a displayed interpolation weight, setting the omitted diagonal entries to zero. -/
def packedMuValue {ℓ : ℕ} (c : RationalCase ℓ) (b : Block)
    (i : Option (Fin ℓ)) (j : Fin ℓ) : ℚ :=
  match i with
  | none => (c.packedMu b).getD (packedIndex none j) 0
  | some k => if k = j then 0 else (c.packedMu b).getD (packedIndex (some k) j) 0

/-- Packed interpolation lookup reads the origin row and sets generated diagonals to zero. -/
theorem packedMuValue_apply {ℓ : ℕ} (c : RationalCase ℓ) (b : Block)
    (i : Option (Fin ℓ)) (j : Fin ℓ) :
    packedMuValue c b i j = match i with
      | none => (c.packedMu b).getD (packedIndex none j) 0
      | some k => if k = j then 0 else (c.packedMu b).getD (packedIndex (some k) j) 0 := by
  -- Optional-index elimination gives the two lookup clauses.
  rfl

/-- Reconstruct every interpolation weight, including the omitted origin column. -/
def reconstructMu {ℓ : ℕ} (c : RationalCase ℓ) (b : Block)
    (i j : Option (Fin ℓ)) : ℚ :=
  match i, j with
  | none, none => 0
  | none, some k => packedMuValue c b none k
  | some k, some j => packedMuValue c b (some k) j
  | some k, none =>
      lagCoefficient c b k + packedMuValue c b none k +
        (∑ i : Fin ℓ, if i = k then 0 else packedMuValue c b (some i) k) -
        ∑ j : Fin ℓ, if j = k then 0 else packedMuValue c b (some k) j

/-- A displayed non-diagonal entry of `reconstructMu` is read from the packed table. -/
theorem reconstructMu_packed {ℓ : ℕ} (c : RationalCase ℓ) (b : Block)
    (i : Option (Fin ℓ)) (j : Fin ℓ) (hij : i ≠ some j) :
    reconstructMu c b i (some j) = packedMuValue c b i j := by
  -- The origin row is direct; a generated row uses the non-diagonal hypothesis.
  cases i with
  | none => rfl
  | some k =>
      simp only [reconstructMu]

/-- Every diagonal entry of the reconstructed interpolation weights is zero. -/
theorem reconstructMu_diag {ℓ : ℕ} (c : RationalCase ℓ) (b : Block)
    (i : Option (Fin ℓ)) : reconstructMu c b i i = 0 := by
  -- The origin diagonal is explicit and each generated diagonal is suppressed in the packed table.
  cases i with
  | none => rfl
  | some k => simp [reconstructMu, packedMuValue]

/-- The omitted origin-column weight is the displayed balance reconstruction formula. -/
theorem reconstructMu_origin {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (i : Fin ℓ) :
    reconstructMu c b (some i) none =
      lagCoefficient c b i + packedMuValue c b none i +
        (∑ j : Fin ℓ, if j = i then 0 else packedMuValue c b (some j) i) -
        ∑ j : Fin ℓ, if j = i then 0 else packedMuValue c b (some i) j := by
  -- This is the defining omitted-column clause.
  rfl

/-- Reconstructed interpolation weights satisfy the function-value coefficient identity. -/
theorem reconstructMu_balance {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (j : Fin ℓ) :
    (∑ i : Option (Fin ℓ), reconstructMu c b (some j) i) -
      (∑ i : Option (Fin ℓ), reconstructMu c b i (some j)) = lagCoefficient c b j := by
  -- Expand the optional origin in both sums; the reconstructed row and column cancel.
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [reconstructMu, packedMuValue]
  simp only [eq_comm]
  have collapse (f : Fin ℓ → ℚ) :
      (∑ i, if j = i then 0 else if j = i then 0 else f i) =
        ∑ i, if j = i then 0 else f i := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  rw [collapse, collapse]
  ring

/-- The exact rational graph normal corresponding to `a_j` for `F` and `c_j` for `J`. -/
def graphNormal {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) (j : Fin (ℓ + 1)) : ℚ :=
  match b with
  | .F => Z (j.succ, 0) - gamma * Z (j.succ, 1) -
      ADMM.FiniteMemory.graphPosition .F Z j
  | .J => gamma * Z (j.succ, 1) + ADMM.FiniteMemory.residual Z j

/-- The rational graph normal has the defining formulas at blocks `F` and `J`. -/
theorem graphNormal_apply {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) (j : Fin (ℓ + 1)) :
    graphNormal gamma b Z j = match b with
      | .F => Z (j.succ, 0) - gamma * Z (j.succ, 1) -
          ADMM.FiniteMemory.graphPosition .F Z j
      | .J => gamma * Z (j.succ, 1) + ADMM.FiniteMemory.residual Z j := by
  -- Block elimination exposes the defining normal formula.
  rfl

/-- The exact scalar supply expression determined by a rational case. -/
def supply {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) : ℚ :=
  c.omega *
      (graphNormal gamma .F Z 0 * ADMM.FiniteMemory.graphPosition .F Z 0 +
        graphNormal gamma .J Z 0 * ADMM.FiniteMemory.graphPosition .J Z 0) +
    c.epsilon * ADMM.FiniteMemory.residual Z 0 ^ 2 +
    ∑ b : Block, ∑ d : Fin ℓ,
      (lagMinusValue c b d * graphNormal gamma b Z 0 *
          (ADMM.FiniteMemory.graphPosition b Z 0 -
            ADMM.FiniteMemory.graphPosition b Z d.succ) +
        lagPlusValue c b d * graphNormal gamma b Z d.succ *
          (ADMM.FiniteMemory.graphPosition b Z d.succ -
            ADMM.FiniteMemory.graphPosition b Z 0))

/-- Evaluation formula for the exact rational supply. -/
theorem supply_apply {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    supply c gamma Z =
      c.omega *
          (graphNormal gamma .F Z 0 * ADMM.FiniteMemory.graphPosition .F Z 0 +
            graphNormal gamma .J Z 0 * ADMM.FiniteMemory.graphPosition .J Z 0) +
        c.epsilon * ADMM.FiniteMemory.residual Z 0 ^ 2 +
        ∑ b : Block, ∑ d : Fin ℓ,
          (lagMinusValue c b d * graphNormal gamma b Z 0 *
              (ADMM.FiniteMemory.graphPosition b Z 0 -
                ADMM.FiniteMemory.graphPosition b Z d.succ) +
            lagPlusValue c b d * graphNormal gamma b Z d.succ *
              (ADMM.FiniteMemory.graphPosition b Z d.succ -
                ADMM.FiniteMemory.graphPosition b Z 0)) := by
  -- The displayed expression is the definition of the rational supply.
  rfl

/-- Polarize an exact rational quadratic expression into a symmetric matrix. -/
def matrixOfQuadratic {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ℚ) → ℚ) : Matrix ι ι ℚ := fun i j ↦
  (Q (fun k ↦ (if k = i then 1 else 0) + (if k = j then 1 else 0)) -
    Q (fun k ↦ if k = i then 1 else 0) - Q (fun k ↦ if k = j then 1 else 0)) / 2

/-- Entry formula for exact rational polarization. -/
theorem matrixOfQuadratic_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ℚ) → ℚ) (i j : ι) :
    matrixOfQuadratic Q i j =
      (Q (fun k ↦ (if k = i then 1 else 0) + (if k = j then 1 else 0)) -
        Q (fun k ↦ if k = i then 1 else 0) -
          Q (fun k ↦ if k = j then 1 else 0)) / 2 := by
  -- The matrix entry is exactly the polarization formula.
  rfl

/-- The exact symmetric matrix representing the rational supply quadratic form. -/
def supplyMatrix {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ) :
    Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℚ :=
  matrixOfQuadratic (supply c gamma)

/-- The polarization matrix of a rational quadratic form agrees with its matrix representation for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private lemma rationalMatrixOfQuadratic_eq_toMatrix' {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm ℚ (ι → ℚ)) :
    matrixOfQuadratic (fun Z ↦ Q Z) = Q.toMatrix' := by
  -- Compare both matrices on standard basis vectors and normalize the quadratic-map API.
  ext i j
  rw [matrixOfQuadratic_apply, QuadraticForm.toMatrix',
    LinearMap.toMatrix₂'_apply, QuadraticMap.associated_apply]
  have basis_i : (fun k : ι ↦ if k = i then (1 : ℚ) else 0) = Pi.single i 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  have basis_j : (fun k : ι ↦ if k = j then (1 : ℚ) else 0) = Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  have basis_add : (fun k : ι ↦
      (if k = i then (1 : ℚ) else 0) + if k = j then 1 else 0) =
      Pi.single i 1 + Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [congrArg (Q : (ι → ℚ) → ℚ) basis_add,
    congrArg (Q : (ι → ℚ) → ℚ) basis_i,
    congrArg (Q : (ι → ℚ) → ℚ) basis_j]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul]
  norm_num
  ring_nf

/-- Rational polarization contracts back to the quadratic form for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private lemma rationalMatrixOfQuadraticForm_apply {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm ℚ (ι → ℚ)) (Z : ι → ℚ) :
    (∑ i, ∑ j, matrixOfQuadratic (fun X ↦ Q X) i j * Z i * Z j) = Q Z := by
  -- Pass through the associated bilinear form, then evaluate it on the diagonal.
  rw [rationalMatrixOfQuadratic_eq_toMatrix',
    ← QuadraticMap.associated_eq_self_apply ℚ Q Z,
    ← Matrix.toBilin'_toMatrix' Q.associated, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have matrix_entry : Q.toMatrix' i j =
      LinearMap.BilinForm.toMatrix' Q.associated i j := rfl
  rw [matrix_entry]
  ring

/-- Evaluation at one scalar rational state coordinate for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private def rationalStateCoordinate {n : ℕ} (i : Fin n × Fin 2) :
    (((Fin n × Fin 2) → ℚ) →ₗ[ℚ] ℚ) :=
  LinearMap.proj i

/-- A rational residual is represented by a linear functional for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private def rationalStateResidualLinear {ℓ : ℕ} (j : Fin (ℓ + 1)) :
    (((Fin (ℓ + 2) × Fin 2) → ℚ) →ₗ[ℚ] ℚ) :=
  rationalStateCoordinate (j.castSucc, 1) - rationalStateCoordinate (j.succ, 1)

/-- Applying the rational residual functional recovers `residual` for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private lemma rationalStateResidualLinear_apply {ℓ : ℕ} (j : Fin (ℓ + 1))
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalStateResidualLinear j Z = ADMM.FiniteMemory.residual Z j := by
  -- Reduce the two projections to the adjacent history coordinates.
  simp [rationalStateResidualLinear, rationalStateCoordinate, ADMM.FiniteMemory.residual]

/-- A rational graph position is represented by a linear functional for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private def rationalStateGraphPositionLinear {ℓ : ℕ} (b : Block) (j : Fin (ℓ + 1)) :
    (((Fin (ℓ + 2) × Fin 2) → ℚ) →ₗ[ℚ] ℚ) :=
  match b with
  | .F => rationalStateCoordinate (j.castSucc, 0) + rationalStateResidualLinear j
  | .J => rationalStateCoordinate (j.castSucc, 0)

/-- Applying the rational graph-position functional recovers `graphPosition` for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private lemma rationalStateGraphPositionLinear_apply {ℓ : ℕ} (b : Block) (j : Fin (ℓ + 1))
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalStateGraphPositionLinear b j Z = ADMM.FiniteMemory.graphPosition b Z j := by
  -- Use the residual interface and split on the graph block.
  cases b <;> simp [rationalStateGraphPositionLinear, rationalStateCoordinate,
    ADMM.FiniteMemory.graphPosition, rationalStateResidualLinear_apply]

/-- A rational graph normal is represented by a linear functional for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private def rationalStateGraphNormalLinear {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (j : Fin (ℓ + 1)) :
    (((Fin (ℓ + 2) × Fin 2) → ℚ) →ₗ[ℚ] ℚ) :=
  match b with
  | .F => rationalStateCoordinate (j.succ, 0) - gamma • rationalStateCoordinate (j.succ, 1) -
      rationalStateGraphPositionLinear .F j
  | .J => gamma • rationalStateCoordinate (j.succ, 1) + rationalStateResidualLinear j

/-- Applying the rational graph-normal functional recovers `graphNormal` for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private lemma rationalStateGraphNormalLinear_apply {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (j : Fin (ℓ + 1)) (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalStateGraphNormalLinear gamma b j Z = graphNormal gamma b Z j := by
  -- Reduce the block formulas to the named position and residual interfaces.
  cases b <;> simp [rationalStateGraphNormalLinear, rationalStateCoordinate,
    graphNormal, rationalStateGraphPositionLinear_apply, rationalStateResidualLinear_apply]

/-- The rational supply is represented by a quadratic form for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private def rationalSupplyQuadraticForm {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ) :
    QuadraticForm ℚ ((Fin (ℓ + 2) × Fin 2) → ℚ) :=
  c.omega • (QuadraticMap.linMulLin (rationalStateGraphNormalLinear gamma .F 0)
      (rationalStateGraphPositionLinear .F 0) +
    QuadraticMap.linMulLin (rationalStateGraphNormalLinear gamma .J 0)
      (rationalStateGraphPositionLinear .J 0)) +
  c.epsilon • QuadraticMap.linMulLin (rationalStateResidualLinear 0)
    (rationalStateResidualLinear 0) +
  ∑ b : Block, ∑ d : Fin ℓ,
    ((lagMinusValue c b d) • QuadraticMap.linMulLin
        (rationalStateGraphNormalLinear gamma b 0)
        (rationalStateGraphPositionLinear b 0 -
          rationalStateGraphPositionLinear b d.succ) +
      (lagPlusValue c b d) • QuadraticMap.linMulLin
        (rationalStateGraphNormalLinear gamma b d.succ)
        (rationalStateGraphPositionLinear b d.succ -
          rationalStateGraphPositionLinear b 0))

/-- Evaluating the rational supply quadratic form gives `supply` for ADMM.FiniteMemory.Reconstruction.supplyMatrix_quadratic. -/
private lemma rationalSupplyQuadraticForm_apply {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalSupplyQuadraticForm c gamma Z = supply c gamma Z := by
  -- Evaluate each quadratic product through its named linear factors and normalize.
  simp only [rationalSupplyQuadraticForm, QuadraticMap.add_apply, QuadraticMap.smul_apply,
    QuadraticMap.linMulLin_apply, QuadraticMap.sum_apply, LinearMap.sub_apply,
    rationalStateGraphNormalLinear_apply, rationalStateGraphPositionLinear_apply,
    rationalStateResidualLinear_apply]
  rw [supply_apply]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The supply matrix evaluates to the exact rational supply on every scalar history. -/
theorem supplyMatrix_quadratic {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    (∑ i, ∑ j, supplyMatrix c gamma i j * Z i * Z j) = supply c gamma Z := by
  -- Identify the supply with the rational quadratic-form interface, then apply polarization.
  have supply_function :
      (supply c gamma : ((Fin (ℓ + 2) × Fin 2) → ℚ) → ℚ) =
        fun Z ↦ rationalSupplyQuadraticForm c gamma Z := by
    funext X
    exact (rationalSupplyQuadraticForm_apply c gamma X).symm
  rw [supplyMatrix, supply_function, rationalMatrixOfQuadraticForm_apply]

/-- The constant-mode matrix stacking `k` copies of the two-dimensional identity. -/
def constantModes (k : ℕ) : Matrix (Fin k × Fin 2) (Fin 2) ℚ := fun i j ↦
  if i.2 = j then 1 else 0

/-- Entry formula for the stacked constant-mode matrix. -/
theorem constantModes_apply (k : ℕ) (i : Fin k × Fin 2) (j : Fin 2) :
    constantModes k i j = if i.2 = j then 1 else 0 := by
  -- The constant-mode entry is its defining Kronecker delta.
  rfl

/-- Multiplication by constant modes sums the matching scalar column in every block. -/
private lemma matrix_mul_constantModes_apply {ρ : Type u} {k : ℕ}
    (K : Matrix ρ (Fin k × Fin 2) ℚ) (i : ρ) (a : Fin 2) :
    (K * constantModes k) i a = ∑ t : Fin k, K i (t, a) := by
  -- Split the paired column index and collapse the Kronecker delta in the scalar coordinate.
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [constantModes]

/-- Rank a paired history coordinate in row-major scalar order. -/
def coordinateRank {k : ℕ} (i : Fin k × Fin 2) : ℕ := 2 * i.1 + i.2

/-- Paired coordinates are ranked in the scalar order `η₀, w₀, η₁, w₁, …`. -/
theorem coordinateRank_apply {k : ℕ} (i : Fin k × Fin 2) :
    coordinateRank i = 2 * i.1 + i.2 := by
  -- The scalar rank is defined in row-major order.
  rfl

/-- Row-major position of an entry in a packed upper triangle. -/
def upperTriangleIndex {k : ℕ} (i j : Fin k × Fin 2) : ℕ :=
  let a := coordinateRank i
  let b := coordinateRank j
  if a ≤ b then a * (4 * k - a + 1) / 2 + (b - a)
  else b * (4 * k - b + 1) / 2 + (a - b)

/-- The packed upper-triangle rank is symmetric in its two coordinates. -/
theorem upperTriangleIndex_comm {k : ℕ} (i j : Fin k × Fin 2) :
    upperTriangleIndex i j = upperTriangleIndex j i := by
  -- Swapping the entries exchanges the two order branches and preserves the packed rank.
  simp only [upperTriangleIndex]
  split_ifs with hij hji
  · rw [Nat.le_antisymm hij hji]
  · omega
  · omega
  · omega

/-- Decode a packed upper-triangle table into the symmetric endpoint principal block. -/
def upperTriangleMatrix {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin ℓ × Fin 2) (Fin ℓ × Fin 2) ℚ := fun i j ↦
  (c.upperTriangle e).getD (upperTriangleIndex i j) 0

/-- Entries of the decoded principal block are read at their packed upper-triangle ranks. -/
theorem upperTriangleMatrix_apply {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin ℓ × Fin 2) :
    upperTriangleMatrix c e i j =
      (c.upperTriangle e).getD (upperTriangleIndex i j) 0 := by
  -- Decoding is exactly lookup at the symmetric packed rank.
  rfl

/-- The upper-triangle decoder is symmetric. -/
theorem upperTriangleMatrix_isSymm {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    (upperTriangleMatrix c e).IsSymm := by
  -- Symmetry follows by swapping the packed upper-triangle rank.
  ext i j
  rw [Matrix.transpose_apply, upperTriangleMatrix_apply, upperTriangleMatrix_apply,
    upperTriangleIndex_comm]

/-- The product `Qγ C` used to complete the storage matrix. -/
def supplyConstantModes {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ) :
    Matrix (Fin (ℓ + 2) × Fin 2) (Fin 2) ℚ :=
  supplyMatrix c gamma * constantModes (ℓ + 2)

/-- The matrix `supplyConstantModes` is the exact product `Qγ C`. -/
theorem supplyConstantModes_apply {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ)
    (i : Fin (ℓ + 2) × Fin 2) (j : Fin 2) :
    supplyConstantModes c gamma i j =
      (supplyMatrix c gamma * constantModes (ℓ + 2)) i j := by
  -- This is the defining matrix product.
  rfl

/-- The cumulative block rows `X_j = -∑_{t=0}^j R_t`. -/
def cumulativePrefix {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin 2) ℚ := fun i j ↦
  -∑ t : Fin (ℓ + 2), if t ≤ i.1.castSucc then supplyConstantModes c gamma (t, i.2) j else 0

/-- Entry formula for the cumulative block rows `X_j`. -/
theorem cumulativePrefix_apply {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℚ)
    (i : Fin (ℓ + 1) × Fin 2) (j : Fin 2) :
    cumulativePrefix c gamma i j =
      -∑ t : Fin (ℓ + 2),
        if t ≤ i.1.castSucc then supplyConstantModes c gamma (t, i.2) j else 0 := by
  -- The entry is the defining cumulative block-row sum.
  rfl

/-- The off-diagonal block `T = X_a - A C` in the completed storage matrix. -/
def storageOffDiagonal {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin ℓ × Fin 2) (Fin 2) ℚ :=
  fun i j ↦ cumulativePrefix c (endpointGamma c e) (i.1.castSucc, i.2) j -
    (upperTriangleMatrix c e * constantModes ℓ) i j

/-- Entry formula for the reconstructed off-diagonal block `T`. -/
theorem storageOffDiagonal_apply {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i : Fin ℓ × Fin 2) (j : Fin 2) :
    storageOffDiagonal c e i j =
      cumulativePrefix c (endpointGamma c e) (i.1.castSucc, i.2) j -
        (upperTriangleMatrix c e * constantModes ℓ) i j := by
  -- The off-diagonal block is defined by subtracting the principal action.
  rfl

/-- The final `2 × 2` block `W = X_b - Tᵀ C` in the storage completion. -/
def storageTerminal {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin 2) (Fin 2) ℚ := fun i j ↦
  cumulativePrefix c (endpointGamma c e) (Fin.last ℓ, i) j -
    ∑ k : Fin ℓ × Fin 2, storageOffDiagonal c e k i * constantModes ℓ k j

/-- Entry formula for the reconstructed terminal block `W`. -/
theorem storageTerminal_apply {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin 2) :
    storageTerminal c e i j =
      cumulativePrefix c (endpointGamma c e) (Fin.last ℓ, i) j -
        ∑ k : Fin ℓ × Fin 2, storageOffDiagonal c e k i * constantModes ℓ k j := by
  -- The terminal block is the remaining prescribed block row.
  rfl

/-- Complete an endpoint storage matrix from its packed principal block and `Qγ C`. -/
def storageMatrix {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ := fun i j ↦
  if hi : i.1 < ℓ then
    if hj : j.1 < ℓ then
      upperTriangleMatrix c e (⟨i.1, hi⟩, i.2) (⟨j.1, hj⟩, j.2)
    else storageOffDiagonal c e (⟨i.1, hi⟩, i.2) j.2
  else if hj : j.1 < ℓ then storageOffDiagonal c e (⟨j.1, hj⟩, j.2) i.2
  else storageTerminal c e i.2 j.2

/-- The supplied packed block is the principal block of the completed storage matrix. -/
theorem storageMatrix_principal {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin ℓ × Fin 2) :
    storageMatrix c e (i.1.castSucc, i.2) (j.1.castSucc, j.2) =
      upperTriangleMatrix c e i j := by
  -- Both embedded coordinates satisfy the principal-block bounds.
  simp [storageMatrix]

/-- Symmetry of the completed terminal block implies symmetry of the whole storage matrix. -/
theorem storageMatrix_isSymm {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (terminal_symm : (storageTerminal c e).IsSymm) : (storageMatrix c e).IsSymm := by
  -- Check the principal, off-diagonal, and terminal blocks separately.
  ext i j
  rw [Matrix.transpose_apply]
  by_cases hi : i.1 < ℓ
  · by_cases hj : j.1 < ℓ
    · simp only [storageMatrix, hi, hj, ↓reduceDIte]
      simpa only [Matrix.transpose_apply] using congrFun
        (congrFun (upperTriangleMatrix_isSymm c e)
          (⟨j.1, hj⟩, j.2)) (⟨i.1, hi⟩, i.2) |>.symm
    · simp [storageMatrix, hi, hj]
  · by_cases hj : j.1 < ℓ
    · simp [storageMatrix, hi, hj]
    · simp only [storageMatrix, hi, hj, ↓reduceDIte]
      exact congrFun (congrFun terminal_symm i.2) j.2

/-- The completed storage matrix has the prescribed action on constant histories. -/
theorem storageMatrix_mul_constantModes {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (terminal_symm : (storageTerminal c e).IsSymm) :
    storageMatrix c e * constantModes (ℓ + 1) =
      cumulativePrefix c (endpointGamma c e) := by
  -- Split a row into its principal coordinates and its final two-coordinate block.
  ext i a
  rw [matrix_mul_constantModes_apply]
  by_cases hi : i.1 < ℓ
  · rw [Fin.sum_univ_castSucc]
    simp only [storageMatrix, hi, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte,
      Fin.val_last, lt_self_iff_false]
    rw [storageOffDiagonal_apply, matrix_mul_constantModes_apply]
    ring_nf
    have row_eq : (⟨i.1, hi⟩ : Fin ℓ).castSucc = i.1 := Fin.ext rfl
    rw [row_eq]
  · have first_eq : i.1 = Fin.last ℓ := by
      exact Fin.eq_last_of_not_lt hi
    have row_eq : i = (Fin.last ℓ, i.2) := by
      apply Prod.ext
      · exact first_eq
      · rfl
    rw [row_eq, Fin.sum_univ_castSucc]
    simp only [storageMatrix, Fin.val_last, lt_self_iff_false, Fin.val_castSucc,
      Fin.is_lt, ↓reduceDIte]
    rw [storageTerminal_apply]
    simp [Fintype.sum_prod_type, constantModes]

/-- The exact rational quadratic storage form. -/
def quadraticStorage {k : ℕ} (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin k × Fin 2) → ℚ) : ℚ := ∑ i, ∑ j, P i j * Z i * Z j

/-- Evaluation formula for the exact rational storage form. -/
theorem quadraticStorage_apply {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin k × Fin 2) → ℚ) :
    quadraticStorage P Z = ∑ i, ∑ j, P i j * Z i * Z j := by
  -- Scalar storage is defined by this double contraction.
  rfl

/-- Matrix quadratic-form evaluation agrees with exact rational storage. -/
private lemma rationalMatrixQuadraticForm_apply {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin k × Fin 2) → ℚ) :
    Matrix.toQuadraticForm' P Z = quadraticStorage P Z := by
  -- Expand the associated bilinear form and commute scalar factors entrywise.
  rw [quadraticStorage_apply]
  have toBilin : Matrix.toQuadraticForm' P Z = Matrix.toBilin' P Z Z := rfl
  rw [toBilin, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Dropping the newest pair is a linear map on exact rational histories. -/
private def rationalPreviousHistoryLinear {ℓ : ℕ} :
    (((Fin (ℓ + 2) × Fin 2) → ℚ) →ₗ[ℚ] ((Fin (ℓ + 1) × Fin 2) → ℚ)) :=
  LinearMap.pi fun i ↦ rationalStateCoordinate (i.1.succ, i.2)

/-- Keeping the newest pairs is a linear map on exact rational histories. -/
private def rationalCurrentHistoryLinear {ℓ : ℕ} :
    (((Fin (ℓ + 2) × Fin 2) → ℚ) →ₗ[ℚ] ((Fin (ℓ + 1) × Fin 2) → ℚ)) :=
  LinearMap.pi fun i ↦ rationalStateCoordinate (i.1.castSucc, i.2)

/-- The previous-history map evaluates by shifting every pair forward. -/
private lemma rationalPreviousHistoryLinear_apply {ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalPreviousHistoryLinear Z = fun i ↦ Z (i.1.succ, i.2) := by
  -- Extensionality reduces the history map to its coordinate projections.
  funext i
  rfl

/-- The current-history map evaluates by retaining every initial pair. -/
private lemma rationalCurrentHistoryLinear_apply {ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalCurrentHistoryLinear Z = fun i ↦ Z (i.1.castSucc, i.2) := by
  -- Extensionality reduces the history map to its coordinate projections.
  funext i
  rfl

/-- The exact rational descent expression is a quadratic form. -/
private def rationalDescentQuadraticForm {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    QuadraticForm ℚ ((Fin (ℓ + 2) × Fin 2) → ℚ) :=
  (Matrix.toQuadraticForm' (storageMatrix c e)).comp rationalPreviousHistoryLinear -
    (Matrix.toQuadraticForm' (storageMatrix c e)).comp rationalCurrentHistoryLinear -
      rationalSupplyQuadraticForm c (endpointGamma c e)

/-- Evaluating the rational descent form gives the exact descent expression. -/
private lemma rationalDescentQuadraticForm_apply {ℓ : ℕ} (c : RationalCase ℓ)
    (e : Endpoint) (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    rationalDescentQuadraticForm c e Z =
      quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.succ, i.2)) -
        quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.castSucc, i.2)) -
          supply c (endpointGamma c e) Z := by
  -- Evaluate both history shifts and the supply through their named interfaces.
  simp only [rationalDescentQuadraticForm, QuadraticMap.sub_apply,
    QuadraticMap.comp_apply, rationalPreviousHistoryLinear_apply,
    rationalCurrentHistoryLinear_apply, rationalMatrixQuadraticForm_apply,
    rationalSupplyQuadraticForm_apply]

/-- The exact rational descent test matrix at an endpoint. -/
def descentMatrix {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℚ :=
  matrixOfQuadratic fun Z ↦
    quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.succ, i.2)) -
      quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.castSucc, i.2)) -
        supply c (endpointGamma c e) Z

/-- The exact descent matrix represents previous storage minus current storage and supply. -/
theorem descentMatrix_quadratic {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    (∑ i, ∑ j, descentMatrix c e i j * Z i * Z j) =
      quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.succ, i.2)) -
        quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.castSucc, i.2)) -
          supply c (endpointGamma c e) Z := by
  -- Replace the scalar expression by its quadratic-form interface before polarizing.
  have descent_function :
      (fun X ↦
        quadraticStorage (storageMatrix c e) (fun i ↦ X (i.1.succ, i.2)) -
          quadraticStorage (storageMatrix c e) (fun i ↦ X (i.1.castSucc, i.2)) -
            supply c (endpointGamma c e) X) =
        fun X ↦ rationalDescentQuadraticForm c e X := by
    funext X
    exact (rationalDescentQuadraticForm_apply c e X).symm
  rw [descentMatrix, descent_function, rationalMatrixOfQuadraticForm_apply,
    rationalDescentQuadraticForm_apply]

/-- The principal restriction used in the unpivoted endpoint descent test. -/
def descentPrincipal {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ := fun i j ↦
  descentMatrix c e (i.1.castSucc, i.2) (j.1.castSucc, j.2)

/-- The principal descent restriction omits the final state pair. -/
theorem descentPrincipal_apply {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin (ℓ + 1) × Fin 2) :
    descentPrincipal c e i j =
      descentMatrix c e (i.1.castSucc, i.2) (j.1.castSucc, j.2) := by
  -- The principal matrix is the defining restriction.
  rfl

/-- The rational interpolation position, with `none` representing the zero datum. -/
def interpolationPosition {ℓ : ℕ} (b : Block) (i : Option (Fin ℓ))
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) : ℚ :=
  match i with
  | none => 0
  | some j => match b with
    | .F => Z (j.castSucc, 0) + Z (j.castSucc, 1) - Z (j.succ, 1)
    | .J => Z (j.castSucc, 0)

/-- Evaluation formula for the rational interpolation position. -/
theorem interpolationPosition_apply {ℓ : ℕ} (b : Block) (i : Option (Fin ℓ))
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    interpolationPosition b i Z = match i with
      | none => 0
      | some j => match b with
        | .F => Z (j.castSucc, 0) + Z (j.castSucc, 1) - Z (j.succ, 1)
        | .J => Z (j.castSucc, 0) := by
  -- Optional and block elimination expose the position formula.
  rfl

/-- The rational interpolation normal, affine in the parameter. -/
def interpolationNormal {ℓ : ℕ} (gamma : ℚ) (b : Block) (i : Option (Fin ℓ))
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) : ℚ :=
  match i with
  | none => 0
  | some j => match b with
    | .F => Z (j.succ, 0) - gamma * Z (j.succ, 1) - interpolationPosition .F i Z
    | .J => gamma * Z (j.succ, 1) + Z (j.castSucc, 1) - Z (j.succ, 1)

/-- Evaluation formula for the rational interpolation normal. -/
theorem interpolationNormal_apply {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    interpolationNormal gamma b i Z = match i with
      | none => 0
      | some j => match b with
        | .F => Z (j.succ, 0) - gamma * Z (j.succ, 1) -
            interpolationPosition .F i Z
        | .J => gamma * Z (j.succ, 1) + Z (j.castSucc, 1) - Z (j.succ, 1) := by
  -- Optional and block elimination expose the affine normal formula.
  rfl

/-- Rational interpolation positions are linear functionals on scalar histories. -/
private def rationalInterpolationPositionLinear {ℓ : ℕ} (b : Block)
    (i : Option (Fin ℓ)) :
    (((Fin (ℓ + 1) × Fin 2) → ℚ) →ₗ[ℚ] ℚ) :=
  match i with
  | none => 0
  | some j => match b with
    | .F => rationalStateCoordinate (j.castSucc, 0) +
        rationalStateCoordinate (j.castSucc, 1) - rationalStateCoordinate (j.succ, 1)
    | .J => rationalStateCoordinate (j.castSucc, 0)

/-- Rational interpolation normals are linear functionals on scalar histories. -/
private def rationalInterpolationNormalLinear {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (i : Option (Fin ℓ)) :
    (((Fin (ℓ + 1) × Fin 2) → ℚ) →ₗ[ℚ] ℚ) :=
  match i with
  | none => 0
  | some j => match b with
    | .F => rationalStateCoordinate (j.succ, 0) -
        gamma • rationalStateCoordinate (j.succ, 1) -
          rationalInterpolationPositionLinear .F i
    | .J => gamma • rationalStateCoordinate (j.succ, 1) +
        rationalStateCoordinate (j.castSucc, 1) - rationalStateCoordinate (j.succ, 1)

/-- Applying the position functional recovers the rational interpolation position. -/
private lemma rationalInterpolationPositionLinear_apply {ℓ : ℕ} (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    rationalInterpolationPositionLinear b i Z = interpolationPosition b i Z := by
  -- Optional-index and block elimination reduce the functional to coordinate arithmetic.
  cases i with
  | none => simp [rationalInterpolationPositionLinear, interpolationPosition]
  | some j =>
      cases b <;> simp [rationalInterpolationPositionLinear, interpolationPosition,
        rationalStateCoordinate]

/-- Applying the normal functional recovers the rational interpolation normal. -/
private lemma rationalInterpolationNormalLinear_apply {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    rationalInterpolationNormalLinear gamma b i Z = interpolationNormal gamma b i Z := by
  -- Optional-index and block elimination reduce the functional to coordinate arithmetic.
  cases i with
  | none => simp [rationalInterpolationNormalLinear, interpolationNormal]
  | some j =>
      cases b <;> simp [rationalInterpolationNormalLinear, interpolationNormal,
        rationalInterpolationPositionLinear_apply, rationalStateCoordinate]

/-- A directed rational interpolation gap is a quadratic form. -/
private def rationalDirectedGapQuadraticForm {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (i j : Option (Fin ℓ)) : QuadraticForm ℚ ((Fin (ℓ + 1) × Fin 2) → ℚ) :=
  -QuadraticMap.linMulLin (rationalInterpolationNormalLinear gamma b j)
    (rationalInterpolationPositionLinear b i - rationalInterpolationPositionLinear b j)

/-- The directed-gap form evaluates to the negative normal-position product. -/
private lemma rationalDirectedGapQuadraticForm_apply {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (i j : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    rationalDirectedGapQuadraticForm gamma b i j Z =
      -interpolationNormal gamma b j Z *
        (interpolationPosition b i Z - interpolationPosition b j Z) := by
  -- Evaluate the product form and identify both linear factors.
  simp only [rationalDirectedGapQuadraticForm, QuadraticMap.neg_apply,
    QuadraticMap.linMulLin_apply, LinearMap.sub_apply,
    rationalInterpolationNormalLinear_apply, rationalInterpolationPositionLinear_apply]
  ring

/-- The squared norm of the current scalar pair is a quadratic form. -/
private def rationalCurrentPairQuadraticForm {ℓ : ℕ} :
    QuadraticForm ℚ ((Fin (ℓ + 1) × Fin 2) → ℚ) :=
  QuadraticMap.linMulLin (rationalStateCoordinate (0, 0))
      (rationalStateCoordinate (0, 0)) +
    QuadraticMap.linMulLin (rationalStateCoordinate (0, 1))
      (rationalStateCoordinate (0, 1))

/-- The current-pair quadratic form evaluates to the sum of two squares. -/
private lemma rationalCurrentPairQuadraticForm_apply {ℓ : ℕ}
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    rationalCurrentPairQuadraticForm Z = Z (0, 0) ^ 2 + Z (0, 1) ^ 2 := by
  -- Evaluate both coordinate products and normalize them as squares.
  simp [rationalCurrentPairQuadraticForm, rationalStateCoordinate, pow_two]

/-- The exact rational lower-test expression is a quadratic form. -/
private def rationalLowerQuadraticForm {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    QuadraticForm ℚ ((Fin (ℓ + 1) × Fin 2) → ℚ) :=
  Matrix.toQuadraticForm' (storageMatrix c e) -
    (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
      reconstructMu c b i j •
        rationalDirectedGapQuadraticForm (endpointGamma c e) b i j) -
    c.zeta • rationalCurrentPairQuadraticForm

/-- Evaluating the rational lower-test form gives the exact scalar expression. -/
private lemma rationalLowerQuadraticForm_apply {ℓ : ℕ} (c : RationalCase ℓ)
    (e : Endpoint) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    rationalLowerQuadraticForm c e Z =
      quadraticStorage (storageMatrix c e) Z -
        (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          reconstructMu c b i j *
            (-interpolationNormal (endpointGamma c e) b j Z *
              (interpolationPosition b i Z - interpolationPosition b j Z))) -
        c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2) := by
  -- Evaluate storage, all directed gaps, and the current-pair norm through their interfaces.
  simp only [rationalLowerQuadraticForm, QuadraticMap.sub_apply,
    QuadraticMap.sum_apply, QuadraticMap.smul_apply, rationalMatrixQuadraticForm_apply,
    rationalDirectedGapQuadraticForm_apply, rationalCurrentPairQuadraticForm_apply, smul_eq_mul]

/-- The exact rational lower-bound test matrix at an endpoint. -/
def lowerMatrix {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ :=
  matrixOfQuadratic fun Z ↦
    quadraticStorage (storageMatrix c e) Z -
      (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        reconstructMu c b i j *
          (-interpolationNormal (endpointGamma c e) b j Z *
            (interpolationPosition b i Z - interpolationPosition b j Z))) -
      c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2)

/-- The exact lower matrix represents storage minus all interpolation gaps and the current norm. -/
theorem lowerMatrix_quadratic {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    (∑ a, ∑ d, lowerMatrix c e a d * Z a * Z d) =
      quadraticStorage (storageMatrix c e) Z -
        (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          reconstructMu c b i j *
            (-interpolationNormal (endpointGamma c e) b j Z *
              (interpolationPosition b i Z - interpolationPosition b j Z))) -
        c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2) := by
  -- Replace the scalar expression by its quadratic-form interface before polarizing.
  have lower_function :
      (fun X ↦
        quadraticStorage (storageMatrix c e) X -
          (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            reconstructMu c b i j *
              (-interpolationNormal (endpointGamma c e) b j X *
                (interpolationPosition b i X - interpolationPosition b j X))) -
          c.zeta * (X (0, 0) ^ 2 + X (0, 1) ^ 2)) =
        fun X ↦ rationalLowerQuadraticForm c e X := by
    funext X
    exact (rationalLowerQuadraticForm_apply c e X).symm
  rw [lowerMatrix, lower_function, rationalMatrixOfQuadraticForm_apply,
    rationalLowerQuadraticForm_apply]

/-- An explicit lower factor and pivot vector produced by unpivoted exact `LDLᵀ`. -/
structure LDL (k : ℕ) where
  lower : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ
  pivot : Fin k × Fin 2 → ℚ

/-- Enumerate paired coordinates in row-major order. -/
def coordinateList (k : ℕ) : List (Fin k × Fin 2) :=
  (List.finRange k).flatMap fun i ↦ (List.finRange 2).map fun j ↦ (i, j)

/-- The row-major coordinate list has exactly `2 * k` entries. -/
theorem coordinateList_length (k : ℕ) : (coordinateList k).length = 2 * k := by
  -- Each of the `k` outer coordinates contributes the two scalar coordinates.
  simp [coordinateList, Nat.mul_comm]

/-- Perform one column update in the exact unpivoted `LDLᵀ` recurrence. -/
def ldlStep {k : ℕ} (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (s : LDL k) (i : Fin k × Fin 2) : LDL k :=
  let d := K i i - ∑ h : Fin k × Fin 2,
    if coordinateRank h < coordinateRank i then s.lower i h ^ 2 * s.pivot h else 0
  { lower := fun j h ↦
      if h = i then
        if j = i then 1
        else if coordinateRank i < coordinateRank j then
          (K j i - ∑ r : Fin k × Fin 2,
            if coordinateRank r < coordinateRank i then
              s.lower j r * s.lower i r * s.pivot r else 0) / d
        else s.lower j h
      else s.lower j h
    pivot := Function.update s.pivot i d }

/-- The updated pivot is the exact diagonal recurrence at the selected coordinate. -/
theorem ldlStep_pivot {k : ℕ} (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (s : LDL k) (i : Fin k × Fin 2) :
    (ldlStep K s i).pivot i = K i i - ∑ h : Fin k × Fin 2,
      if coordinateRank h < coordinateRank i then s.lower i h ^ 2 * s.pivot h else 0 := by
  -- The selected pivot is updated to the displayed Schur-complement recurrence.
  simp [ldlStep]

/-- Updating a different column preserves every entry of the selected lower-factor column. -/
private lemma ldlStep_lower_of_ne {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (s : LDL k)
    (q j i : Fin k × Fin 2) (hqi : q ≠ i) :
    (ldlStep K s q).lower j i = s.lower j i := by
  -- The step changes only the column indexed by its selected coordinate.
  simp [ldlStep, Ne.symm hqi]

/-- Folding updates outside a column leaves that lower-factor column unchanged. -/
private lemma ldlFold_lower_of_not_mem {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (xs : List (Fin k × Fin 2)) (s : LDL k) (j i : Fin k × Fin 2)
    (hi : i ∉ xs) :
    (xs.foldl (ldlStep K) s).lower j i = s.lower j i := by
  -- Induct through the fold; each selected coordinate differs from the protected column.
  induction xs generalizing s with
  | nil => rfl
  | cons q xs inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      · exact ldlStep_lower_of_ne K s q j i (fun h ↦ hi (by simp [h]))
      · intro hmem
        exact hi (by simp [hmem])

/-- A no-duplicate fold sets every processed lower-factor diagonal entry to one. -/
private lemma ldlFold_lower_self_of_mem {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (xs : List (Fin k × Fin 2)) (s : LDL k) (i : Fin k × Fin 2)
    (hi : i ∈ xs) (nodup : xs.Nodup) :
    (xs.foldl (ldlStep K) s).lower i i = 1 := by
  -- Process the first occurrence of the coordinate and preserve its column thereafter.
  induction xs generalizing s with
  | nil => simp at hi
  | cons q xs inductionHypothesis =>
      simp only [List.foldl_cons]
      have nodup_tail : xs.Nodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp hi with rfl | hi_tail
      · rw [ldlFold_lower_of_not_mem K xs (ldlStep K s i) i i
          (List.nodup_cons.mp nodup).1]
        · simp [ldlStep]
      · exact inductionHypothesis (ldlStep K s q) hi_tail nodup_tail

/-- Every paired coordinate occurs in the canonical row-major enumeration. -/
private lemma mem_coordinateList {k : ℕ} (i : Fin k × Fin 2) :
    i ∈ coordinateList k := by
  -- Both components occur in their finite ranges.
  rcases i with ⟨i, j⟩
  simp [coordinateList]

/-- The canonical row-major coordinate enumeration has no repetitions. -/
private lemma coordinateList_nodup (k : ℕ) : (coordinateList k).Nodup := by
  -- Distinct outer coordinates give disjoint rows, and each row lists distinct scalar indices.
  apply (List.nodup_flatMap).2
  constructor
  · intro i hi
    exact (List.nodup_finRange 2).map (fun _ _ h ↦ (Prod.mk.inj h).2)
  · have rows_pairwise : ∀ xs : List (Fin k), xs.Nodup →
        xs.Pairwise (Function.onFun List.Disjoint
          fun i ↦ (List.finRange 2).map fun j ↦ (i, j)) := by
      intro xs nodup
      induction xs with
      | nil => simp
      | cons i xs inductionHypothesis =>
          rw [List.pairwise_cons]
          constructor
          · intro j hj
            apply List.disjoint_left.mpr
            intro p hip hjp
            rcases List.mem_map.mp hip with ⟨a, ha, rfl⟩
            rcases List.mem_map.mp hjp with ⟨b, hb, hab⟩
            have hij : i ≠ j := fun h ↦ (List.nodup_cons.mp nodup).1 (h ▸ hj)
            exact hij (Prod.mk.inj hab).1.symm
          · exact inductionHypothesis (List.nodup_cons.mp nodup).2
    exact rows_pairwise (List.finRange k) (List.nodup_finRange k)

/-- An injective map preserves the index of an element in a list. -/
private lemma idxOf_map_injective {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) (x : α) (hx : x ∈ l) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  -- Peel the list; injectivity preserves the equality test used by `idxOf`.
  induction l with
  | nil => simp at hx
  | cons a l inductionHypothesis =>
      by_cases hax : a = x
      · subst hax
        simp
      · have hxl : x ∈ l := by
          rcases List.mem_cons.mp hx with h | h
          · exact False.elim (hax h.symm)
          · exact h
        have hfa : f a ≠ f x := fun h ↦ hax (hf h)
        simp only [List.map_cons, List.idxOf_cons_ne _ hfa, List.idxOf_cons_ne _ hax]
        rw [inductionHypothesis hxl]

/-- The row-major list index agrees with the scalar rank of every coordinate. -/
private lemma coordinateList_idxOf (k : ℕ) (i : Fin k × Fin 2) :
    (coordinateList k).idxOf i = coordinateRank i := by
  induction k with
  | zero => exact Fin.elim0 i.1
  | succ k inductionHypothesis =>
      rcases i with ⟨i, j⟩
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · fin_cases j <;> simp [coordinateList, coordinateRank, List.finRange_succ]
      · let f : (Fin k × Fin 2) → (Fin (k + 1) × Fin 2) :=
          fun p ↦ (p.1.succ, p.2)
        have hf : Function.Injective f := by
          intro p q h
          apply Prod.ext
          · apply Fin.ext
            exact Nat.succ.inj (by simpa [Fin.succ] using congrArg Fin.val (Prod.mk.inj h).1)
          · exact (Prod.mk.inj h).2
        have hmap : ∀ xs : List (Fin k),
            ((xs.map Fin.succ).flatMap
                (fun i ↦ [(i, (0 : Fin 2)), (i, (1 : Fin 2))])) =
              (xs.flatMap (fun i ↦ [(i, (0 : Fin 2)), (i, (1 : Fin 2))])).map f := by
          intro xs
          induction xs with
          | nil => simp
          | cons a xs inductionHypothesis =>
              simp only [List.map_cons, List.flatMap_cons]
              rw [inductionHypothesis]
              rfl
        have hcoord : coordinateList (k + 1) =
            [(0, (0 : Fin 2)), (0, (1 : Fin 2))] ++ (coordinateList k).map f := by
          change (List.finRange (k + 1)).flatMap
              (fun i ↦ [(i, (0 : Fin 2)), (i, (1 : Fin 2))]) =
            [(0, (0 : Fin 2)), (0, (1 : Fin 2))] ++
              ((List.finRange k).flatMap
                (fun i ↦ [(i, (0 : Fin 2)), (i, (1 : Fin 2))])).map f
          rw [List.finRange_succ]
          simp only [List.flatMap_cons]
          rw [hmap]
        rw [hcoord]
        have hnot : (i.succ, j) ∉ [(0, (0 : Fin 2)), (0, (1 : Fin 2))] := by
          simp
        rw [List.idxOf_append_of_notMem hnot]
        change [(0, (0 : Fin 2)), (0, (1 : Fin 2))].length +
          (List.map f (coordinateList k)).idxOf (f (i, j)) = coordinateRank (i.succ, j)
        have hidx : (List.map f (coordinateList k)).idxOf (f (i, j)) =
            (coordinateList k).idxOf (i, j) :=
          idxOf_map_injective f hf (coordinateList k) (i, j) (mem_coordinateList (i, j))
        rw [hidx]
        rw [inductionHypothesis (i, j)]
        simp [coordinateRank]
        omega

/-- Row-major prefixes contain exactly the coordinates below their scalar rank bound. -/
private lemma coordinateList_rank_spec {k n : ℕ} (i : Fin k × Fin 2) :
    i ∈ (coordinateList k).take n ↔ coordinateRank i < n := by
  -- The generic prefix/index theorem reduces membership to the explicit rank formula.
  rw [List.mem_take_iff_idxOf_lt (mem_coordinateList i), coordinateList_idxOf]

/-- In a list without repetitions, an element of a suffix cannot occur before the
suffix's starting index. -/
private lemma idxOf_le_of_mem_drop {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (n : ℕ) (nodup : xs.Nodup) (hx : x ∈ xs.drop n) :
    n ≤ xs.idxOf x := by
  -- Remove one list entry and one suffix offset at a time, using nodupness at the head.
  induction xs generalizing n with
  | nil => simp at hx
  | cons a xs inductionHypothesis =>
      cases n with
      | zero => exact Nat.zero_le _
      | succ n =>
          have hxTail : x ∈ xs.drop n := hx
          have hxXs : x ∈ xs := List.mem_of_mem_drop hxTail
          have hax : a ≠ x := by
            intro h
            subst h
            exact (List.nodup_cons.mp nodup).1 hxXs
          have hindex := inductionHypothesis n (List.nodup_cons.mp nodup).2 hxTail
          simp only [List.idxOf_cons_ne _ hax]
          omega

/-- The scalar row-major rank determines a paired coordinate uniquely. -/
private lemma coordinateRank_injective {k : ℕ} :
    Function.Injective (@coordinateRank k) := by
  -- The rank equation recovers the quotient and remainder on division by two.
  intro i j hij
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  change 2 * i.val + a.val = 2 * j.val + b.val at hij
  have first : i.val = j.val := by omega
  have second : a.val = b.val := by omega
  exact Prod.ext (Fin.ext first) (Fin.ext second)

/-- Dropping the row-major list at a coordinate's rank exposes that coordinate as the head. -/
private lemma coordinateList_drop_rank {k : ℕ} (i : Fin k × Fin 2) :
    (coordinateList k).drop (coordinateRank i) =
      i :: (coordinateList k).drop (coordinateRank i + 1) := by
  -- The explicit rank is the coordinate's `idxOf`, so the generic drop decomposition applies.
  have hidx : (coordinateList k).idxOf i < (coordinateList k).length :=
    List.idxOf_lt_length_iff.mpr (mem_coordinateList i)
  have hrank : coordinateRank i < (coordinateList k).length := by
    simpa only [coordinateList_idxOf] using hidx
  have hentry : (coordinateList k)[coordinateRank i] = i := by
    simpa only [coordinateList_idxOf] using List.getElem_idxOf hidx
  calc
    (coordinateList k).drop (coordinateRank i) =
        (coordinateList k)[coordinateRank i] ::
          (coordinateList k).drop (coordinateRank i + 1) :=
      List.cons_getElem_drop_succ.symm
    _ = i :: (coordinateList k).drop (coordinateRank i + 1) := by rw [hentry]

/-- A coordinate does not reappear after its unique row-major occurrence. -/
private lemma coordinateList_not_mem_drop_succ {k : ℕ} (i : Fin k × Fin 2) :
    i ∉ (coordinateList k).drop (coordinateRank i + 1) := by
  -- A suffix member has index at least the suffix offset, contradicting the explicit index.
  intro hmem
  have hindex := idxOf_le_of_mem_drop (coordinateList k) i (coordinateRank i + 1)
    (coordinateList_nodup k) hmem
  rw [coordinateList_idxOf] at hindex
  omega

/-- A fold that does not select coordinate `i` leaves its pivot unchanged. -/
private lemma ldlFold_pivot_of_not_mem {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (xs : List (Fin k × Fin 2)) (s : LDL k) (i : Fin k × Fin 2)
    (hi : i ∉ xs) :
    (xs.foldl (ldlStep K) s).pivot i = s.pivot i := by
  -- Each fold step updates only its selected pivot, so a protected coordinate is unchanged.
  induction xs generalizing s with
  | nil => rfl
  | cons q xs inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      · have hqi : q ≠ i := fun h ↦ hi (by simp [h])
        have hiq : i ≠ q := Ne.symm hqi
        simp [ldlStep, Function.update, hiq]
      · intro hmem
        exact hi (by simp [hmem])

/-- Compute the exact unpivoted `LDLᵀ` recurrence by a finite row-major fold. -/
def ldl {k : ℕ} (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) : LDL k :=
  (coordinateList k).foldl (ldlStep K) { lower := 0, pivot := 0 }

/-- The row-major prefix fold agrees with the completed LDL state on all lower-rank columns
and pivots. -/
private lemma ldlPrefixInvariant {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i : Fin k × Fin 2) :
    let pre := (coordinateList k).take (coordinateRank i)
    let state := pre.foldl (ldlStep K) { lower := 0, pivot := 0 }
    i ∉ pre ∧
      ∀ h, coordinateRank h < coordinateRank i →
        state.pivot h = (ldl K).pivot h ∧
          ∀ j, state.lower j h = (ldl K).lower j h := by
  -- Split the completed fold into the rank prefix and its suffix.
  let pre := (coordinateList k).take (coordinateRank i)
  let state := pre.foldl (ldlStep K) { lower := 0, pivot := 0 }
  have splitFold :
      (coordinateList k).foldl (ldlStep K) { lower := 0, pivot := 0 } =
        ((coordinateList k).drop (coordinateRank i)).foldl (ldlStep K) state := by
    rw [← List.foldl_append]
    exact congrArg (fun xs ↦ xs.foldl (ldlStep K) { lower := 0, pivot := 0 })
      (List.take_append_drop (coordinateRank i) (coordinateList k)).symm
  have iNotMem : i ∉ pre := by
    rw [coordinateList_rank_spec]
    exact Nat.lt_irrefl _
  refine ⟨iNotMem, ?_⟩
  intro h hrank
  have hNotMem : h ∉ (coordinateList k).drop (coordinateRank i) := by
    intro hmem
    have hindex := idxOf_le_of_mem_drop (coordinateList k) h (coordinateRank i)
      (coordinateList_nodup k) hmem
    rw [coordinateList_idxOf] at hindex
    omega
  constructor
  · -- Later suffix updates do not change an already-computed pivot.
    have stable := ldlFold_pivot_of_not_mem K
      ((coordinateList k).drop (coordinateRank i)) state h hNotMem
    rw [ldl, splitFold]
    exact stable.symm
  · intro j
    -- Later suffix updates likewise preserve the whole earlier lower-factor column.
    have stable := ldlFold_lower_of_not_mem K
      ((coordinateList k).drop (coordinateRank i)) state j h hNotMem
    rw [ldl, splitFold]
    exact stable.symm

/-- The completed LDL state is the strict suffix fold starting from the update at a
chosen row-major coordinate. -/
private lemma ldl_eq_fold_after_coordinate {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i : Fin k × Fin 2) :
    ldl K =
      ((coordinateList k).drop (coordinateRank i + 1)).foldl (ldlStep K)
        (ldlStep K
          (((coordinateList k).take (coordinateRank i)).foldl (ldlStep K)
            { lower := 0, pivot := 0 }) i) := by
  -- Decompose the enumeration into the strict prefix, the selected coordinate, and the suffix.
  have split : coordinateList k =
      (coordinateList k).take (coordinateRank i) ++
        i :: (coordinateList k).drop (coordinateRank i + 1) := by
    rw [← coordinateList_drop_rank i]
    exact (List.take_append_drop (coordinateRank i) (coordinateList k)).symm
  calc
    ldl K = (coordinateList k).foldl (ldlStep K) { lower := 0, pivot := 0 } := rfl
    _ = ((coordinateList k).take (coordinateRank i) ++
          i :: (coordinateList k).drop (coordinateRank i + 1)).foldl (ldlStep K)
          { lower := 0, pivot := 0 } :=
      congrArg (fun xs ↦ xs.foldl (ldlStep K) { lower := 0, pivot := 0 }) split
    _ = ((coordinateList k).drop (coordinateRank i + 1)).foldl (ldlStep K)
          (ldlStep K
            (((coordinateList k).take (coordinateRank i)).foldl (ldlStep K)
              { lower := 0, pivot := 0 }) i) := by
      rw [List.foldl_append]
      rfl

/-- Every computed diagonal entry of the lower factor is one. -/
theorem ldl_unitDiagonal {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i : Fin k × Fin 2) :
    (ldl K).lower i i = 1 := by
  -- Apply the fold invariant to the complete no-duplicate coordinate enumeration.
  exact ldlFold_lower_self_of_mem K (coordinateList k) { lower := 0, pivot := 0 } i
    (mem_coordinateList i) (coordinateList_nodup k)

/-- The computed factors satisfy the displayed unpivoted recurrence. -/
theorem ldl_pivot {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i : Fin k × Fin 2) :
    (ldl K).pivot i = K i i - ∑ h : Fin k × Fin 2,
      if coordinateRank h < coordinateRank i then
        (ldl K).lower i h ^ 2 * (ldl K).pivot h else 0 := by
  -- Read the selected pivot update, then replace every prefix value by its completed value.
  let state := ((coordinateList k).take (coordinateRank i)).foldl (ldlStep K)
    { lower := 0, pivot := 0 }
  have invariant := ldlPrefixInvariant K i
  dsimp only at invariant
  have stable := ldlFold_pivot_of_not_mem K
    ((coordinateList k).drop (coordinateRank i + 1)) (ldlStep K state i) i
    (coordinateList_not_mem_drop_succ i)
  have selected : (ldl K).pivot i = (ldlStep K state i).pivot i := by
    rw [ldl_eq_fold_after_coordinate K i]
    exact stable
  rw [selected, ldlStep_pivot]
  apply congrArg (fun x : ℚ ↦ K i i - x)
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hrank : coordinateRank h < coordinateRank i
  · simp only [hrank, if_true]
    rw [(invariant.2 h hrank).1, (invariant.2 h hrank).2 i]
  · simp only [hrank, if_false]

/-- A strict lower entry created by one LDL step is its Schur-complement quotient. -/
private lemma ldlStep_lower_of_rank_lt {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (s : LDL k)
    (i j : Fin k × Fin 2) (hij : coordinateRank i < coordinateRank j) :
    (ldlStep K s i).lower j i =
      (K j i - ∑ r : Fin k × Fin 2,
        if coordinateRank r < coordinateRank i then
          s.lower j r * s.lower i r * s.pivot r else 0) /
        (ldlStep K s i).pivot i := by
  -- Both sides use the same pivot value introduced by this selected update.
  have hji : j ≠ i := by
    intro h
    subst j
    exact (Nat.lt_irrefl _ hij).elim
  rw [ldlStep_pivot]
  simp [ldlStep, hij, hji]

/-- A strictly lower entry of the computed factor satisfies the displayed quotient recurrence. -/
theorem ldl_lower {k : ℕ} (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (i j : Fin k × Fin 2) (hij : coordinateRank i < coordinateRank j) :
    (ldl K).lower j i =
      (K j i - ∑ r : Fin k × Fin 2,
        if coordinateRank r < coordinateRank i then
          (ldl K).lower j r * (ldl K).lower i r * (ldl K).pivot r else 0) /
        (ldl K).pivot i := by
  -- Read the selected column update and transport its prefix entries to the completed factors.
  let state := ((coordinateList k).take (coordinateRank i)).foldl (ldlStep K)
    { lower := 0, pivot := 0 }
  have invariant := ldlPrefixInvariant K i
  dsimp only at invariant
  have lowerStable := ldlFold_lower_of_not_mem K
    ((coordinateList k).drop (coordinateRank i + 1)) (ldlStep K state i) j i
    (coordinateList_not_mem_drop_succ i)
  have pivotStable := ldlFold_pivot_of_not_mem K
    ((coordinateList k).drop (coordinateRank i + 1)) (ldlStep K state i) i
    (coordinateList_not_mem_drop_succ i)
  have selectedLower : (ldl K).lower j i = (ldlStep K state i).lower j i := by
    rw [ldl_eq_fold_after_coordinate K i]
    exact lowerStable
  have selectedPivot : (ldl K).pivot i = (ldlStep K state i).pivot i := by
    rw [ldl_eq_fold_after_coordinate K i]
    exact pivotStable
  rw [selectedLower, ldlStep_lower_of_rank_lt K state i j hij, ← selectedPivot]
  apply congrArg (fun x : ℚ ↦ (K j i - x) / (ldl K).pivot i)
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrank : coordinateRank r < coordinateRank i
  · simp only [hrank, if_true]
    rw [(invariant.2 r hrank).1, (invariant.2 r hrank).2 i,
      (invariant.2 r hrank).2 j]
  · simp only [hrank, if_false]

/-- Entries of the computed lower factor above its row-major diagonal are zero. -/
private lemma ldl_lower_zero_of_rank_lt {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (i j : Fin k × Fin 2) (hij : coordinateRank i < coordinateRank j) :
    (ldl K).lower i j = 0 := by
  -- Column `j` is zero before selection, remains zero in its update, and is untouched later.
  let state := ((coordinateList k).take (coordinateRank j)).foldl (ldlStep K)
    { lower := 0, pivot := 0 }
  have invariant := ldlPrefixInvariant K j
  dsimp only at invariant
  have stateZero : state.lower i j = 0 := by
    exact ldlFold_lower_of_not_mem K ((coordinateList k).take (coordinateRank j))
      { lower := 0, pivot := 0 } i j invariant.1
  have hijNe : i ≠ j := by
    intro h
    subst j
    exact (Nat.lt_irrefl _ hij).elim
  have selectedZero : (ldlStep K state j).lower i j = 0 := by
    simp [ldlStep, hijNe, Nat.not_lt.mpr (Nat.le_of_lt hij), stateZero]
  have stable := ldlFold_lower_of_not_mem K
    ((coordinateList k).drop (coordinateRank j + 1)) (ldlStep K state j) i j
    (coordinateList_not_mem_drop_succ j)
  calc
    (ldl K).lower i j =
        (((coordinateList k).drop (coordinateRank j + 1)).foldl (ldlStep K)
          (ldlStep K state j)).lower i j := by rw [ldl_eq_fold_after_coordinate K j]
    _ = (ldlStep K state j).lower i j := stable
    _ = 0 := selectedZero

/-- An LDL contraction against row `i` consists of its strict rank prefix and diagonal term. -/
private lemma ldl_sum_eq_rankPrefix_add_diagonal {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (i j : Fin k × Fin 2) :
    (∑ h, (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h) =
      (∑ h, if coordinateRank h < coordinateRank i then
        (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h else 0) +
        (ldl K).lower j i * (ldl K).pivot i := by
  -- Every higher-rank term vanishes, while equal rank identifies the unique diagonal coordinate.
  calc
    (∑ h, (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h) =
        ∑ h, ((if coordinateRank h < coordinateRank i then
            (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h else 0) +
          if h = i then
            (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h else 0) := by
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hrank : coordinateRank h < coordinateRank i
      · have hne : h ≠ i := by
          intro heq
          subst h
          exact (Nat.lt_irrefl _ hrank).elim
        simp [hrank, hne]
      · by_cases heq : h = i
        · subst h
          simp [hrank]
        · have rankNe : coordinateRank i ≠ coordinateRank h := by
            intro rankEq
            exact heq (coordinateRank_injective rankEq.symm)
          have rankLt : coordinateRank i < coordinateRank h :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt hrank) rankNe
          rw [ldl_lower_zero_of_rank_lt K i h rankLt]
          simp [hrank, heq]
    _ = (∑ h, if coordinateRank h < coordinateRank i then
          (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h else 0) +
        (ldl K).lower j i * (ldl K).pivot i := by
      rw [Finset.sum_add_distrib]
      simp [ldl_unitDiagonal]

/-- The strict-lower recurrence reconstructs a matrix entry below the row-major diagonal. -/
private lemma ldl_factorization_entry_of_lower_rank {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (nonzero : ∀ i, (ldl K).pivot i ≠ 0) (i j : Fin k × Fin 2)
    (hij : coordinateRank i < coordinateRank j) :
    K j i = ∑ h, (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h := by
  -- Multiply the quotient recurrence by its nonzero pivot, then use triangular support.
  have recurrence := ldl_lower K i j hij
  have multiplied := (eq_div_iff (nonzero i)).mp recurrence
  have prefixOrder :
      (∑ h, if coordinateRank h < coordinateRank i then
        (ldl K).lower j h * (ldl K).lower i h * (ldl K).pivot h else 0) =
      ∑ h, if coordinateRank h < coordinateRank i then
        (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h else 0 := by
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hrank : coordinateRank h < coordinateRank i
    · simp only [hrank, if_true]
      ring
    · simp only [hrank, if_false]
  rw [ldl_sum_eq_rankPrefix_add_diagonal K i j]
  rw [← prefixOrder]
  linarith

/-- The pivot recurrence reconstructs a diagonal matrix entry. -/
private lemma ldl_factorization_entry_self {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (i : Fin k × Fin 2) :
    K i i = ∑ h, (ldl K).lower i h * (ldl K).pivot h * (ldl K).lower i h := by
  -- Normalize the contraction to its prefix and diagonal, then apply the pivot recurrence.
  have recurrence := ldl_pivot K i
  have prefixOrder :
      (∑ h, if coordinateRank h < coordinateRank i then
        (ldl K).lower i h ^ 2 * (ldl K).pivot h else 0) =
      ∑ h, if coordinateRank h < coordinateRank i then
        (ldl K).lower i h * (ldl K).pivot h * (ldl K).lower i h else 0 := by
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hrank : coordinateRank h < coordinateRank i
    · simp only [hrank, if_true]
      ring
    · simp only [hrank, if_false]
  rw [ldl_sum_eq_rankPrefix_add_diagonal K i i]
  rw [ldl_unitDiagonal, one_mul, ← prefixOrder]
  linarith

/-- A symmetric matrix with nonzero pivots is reconstructed by its exact `LDLᵀ` factors. -/
theorem ldl_factorization {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (symm : K.IsSymm)
    (nonzero : ∀ i, (ldl K).pivot i ≠ 0) :
    ∀ i j, K i j = ∑ h, (ldl K).lower i h * (ldl K).pivot h * (ldl K).lower j h := by
  -- Split by row-major rank; strict cases use the lower recurrence and equality uses the pivot.
  intro i j
  have symmEntry : K i j = K j i := by
    have entry := congrFun (congrFun symm j) i
    simpa only [Matrix.transpose_apply] using entry
  rcases lt_trichotomy (coordinateRank i) (coordinateRank j) with hij | heq | hji
  · calc
      K i j = K j i := symmEntry
      _ = ∑ h, (ldl K).lower j h * (ldl K).pivot h * (ldl K).lower i h :=
        ldl_factorization_entry_of_lower_rank K nonzero i j hij
      _ = ∑ h, (ldl K).lower i h * (ldl K).pivot h * (ldl K).lower j h := by
        apply Finset.sum_congr rfl
        intro h hh
        ring
  · have hijEq : i = j := coordinateRank_injective heq
    subst j
    exact ldl_factorization_entry_self K i
  · exact ldl_factorization_entry_of_lower_rank K nonzero j i hji

/-- All exact unpivoted pivots exceed a specified rational threshold. -/
def PositivePivots {k : ℕ} (threshold : ℚ)
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) : Prop :=
  ∀ i, threshold < (ldl K).pivot i

/-- Pointwise characterization of the positive-pivot check. -/
theorem positivePivots_iff {k : ℕ} (threshold : ℚ)
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) :
    PositivePivots threshold K ↔ ∀ i, threshold < (ldl K).pivot i := by
  -- The predicate is defined pointwise on the computed pivots.
  rfl

/-- Positive pivots above a nonnegative threshold are nonzero. -/
theorem positivePivots_ne_zero {k : ℕ} {threshold : ℚ}
    {K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ}
    (threshold_nonneg : 0 ≤ threshold) (pivots : PositivePivots threshold K) :
    ∀ i, (ldl K).pivot i ≠ 0 := by
  -- Every pivot is strictly above a nonnegative threshold.
  intro i
  exact ne_of_gt (lt_of_le_of_lt threshold_nonneg (pivots i))

/-- On a finite index type, a finitely supported rational quadratic contraction is a double sum. -/
private lemma rationalFinsuppMatrixQuadratic_eq {ι : Type u} [Fintype ι]
    (M : Matrix ι ι ℚ) (x : ι →₀ ℚ) :
    x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj) =
      ∑ i, ∑ j, M i j * x i * x j := by
  -- Finite support sums may be expanded over `univ`, and rational star is trivial.
  classical
  simp only [star_trivial]
  rw [Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · intro j
      simp
  · intro i
    simp

/-- The quadratic contraction of a symmetric matrix is the pivot-weighted sum of LDL squares. -/
private lemma ldl_quadratic_eq_sum_squares {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (symm : K.IsSymm)
    (nonzero : ∀ i, (ldl K).pivot i ≠ 0) (x : Fin k × Fin 2 → ℚ) :
    (∑ i, ∑ j, K i j * x i * x j) =
      ∑ h, (ldl K).pivot h * (∑ i, (ldl K).lower i h * x i) ^ 2 := by
  -- Expand the factorization and commute the three finite sums to group each pivot column.
  calc
    (∑ i, ∑ j, K i j * x i * x j) =
        ∑ i, ∑ j, ∑ h,
          ((ldl K).lower i h * (ldl K).pivot h * (ldl K).lower j h) *
            x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [ldl_factorization K symm nonzero i j, Finset.sum_mul, Finset.sum_mul]
    _ = ∑ i, ∑ h, ∑ j,
          ((ldl K).lower i h * (ldl K).pivot h * (ldl K).lower j h) *
            x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ h, ∑ i, ∑ j,
          ((ldl K).lower i h * (ldl K).pivot h * (ldl K).lower j h) *
            x i * x j := by
      rw [Finset.sum_comm]
    _ = ∑ h, (ldl K).pivot h * (∑ i, (ldl K).lower i h * x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A symmetric exact matrix with positive unpivoted pivots is positive semidefinite. -/
theorem posSemidef_of_positivePivots {k : ℕ} {threshold : ℚ}
    {K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ} (symm : K.IsSymm)
    (threshold_nonneg : 0 ≤ threshold) (pivots : PositivePivots threshold K) :
    K.PosSemidef := by
  -- Rewrite every quadratic contraction as a sum of nonnegative pivot-weighted squares.
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr symm, ?_⟩
  intro x
  rw [rationalFinsuppMatrixQuadratic_eq,
    ldl_quadratic_eq_sum_squares K symm (positivePivots_ne_zero threshold_nonneg pivots) x]
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg (le_of_lt (lt_of_le_of_lt threshold_nonneg (pivots h))) (sq_nonneg _)

/-- A constant-mode kernel reduces the full quadratic contraction to the centered
principal restriction. -/
private lemma quadratic_eq_principal_of_constantModes_kernel {ℓ : ℕ}
    (K : Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℚ)
    (symm : K.IsSymm) (kernel : K * constantModes (ℓ + 2) = 0)
    (x : Fin (ℓ + 2) × Fin 2 → ℚ) :
    (∑ p, ∑ q, K p q * x p * x q) =
      ∑ i : Fin (ℓ + 1) × Fin 2, ∑ j : Fin (ℓ + 1) × Fin 2,
        K (i.1.castSucc, i.2) (j.1.castSucc, j.2) *
          (x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)) *
          (x (j.1.castSucc, j.2) - x (Fin.last (ℓ + 1), j.2)) := by
  -- Separate the constant final pair from the centered history.
  let constant : (Fin (ℓ + 2) × Fin 2) → ℚ :=
    fun p ↦ x (Fin.last (ℓ + 1), p.2)
  let centered : (Fin (ℓ + 2) × Fin 2) → ℚ :=
    fun p ↦ x p - constant p
  have symmetric (p q : Fin (ℓ + 2) × Fin 2) : K p q = K q p := by
    have entry := congrFun (congrFun symm q) p
    simpa only [Matrix.transpose_apply] using entry
  have rowKernel (p : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
      (∑ t : Fin (ℓ + 2), K p (t, a)) = 0 := by
    have entry := congrFun (congrFun kernel p) a
    rw [matrix_mul_constantModes_apply, Matrix.zero_apply] at entry
    exact entry
  have rowConstant (p : Fin (ℓ + 2) × Fin 2) :
      (∑ q, K p q * constant q) = 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ t : Fin (ℓ + 2), ∑ a : Fin 2, K p (t, a) * constant (t, a)) =
          ∑ a : Fin 2, ∑ t : Fin (ℓ + 2), K p (t, a) * constant (t, a) := by
        rw [Finset.sum_comm]
      _ = ∑ a : Fin 2,
          (∑ t : Fin (ℓ + 2), K p (t, a)) * x (Fin.last (ℓ + 1), a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
      _ = 0 := by simp only [rowKernel, zero_mul, Finset.sum_const_zero]
  have columnConstant (q : Fin (ℓ + 2) × Fin 2) :
      (∑ p, constant p * K p q) = 0 := by
    calc
      (∑ p, constant p * K p q) = ∑ p, K q p * constant p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [symmetric p q]
        ring
      _ = 0 := rowConstant q
  have rowCentered (p : Fin (ℓ + 2) × Fin 2) :
      (∑ q, K p q * x q) = ∑ q, K p q * centered q := by
    calc
      (∑ q, K p q * x q) =
          ∑ q, (K p q * centered q + K p q * constant q) := by
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [centered]
        ring
      _ = (∑ q, K p q * centered q) + ∑ q, K p q * constant q := by
        rw [Finset.sum_add_distrib]
      _ = ∑ q, K p q * centered q := by rw [rowConstant, add_zero]
  have constantCross :
      (∑ p, constant p * (∑ q, K p q * centered q)) = 0 := by
    calc
      (∑ p, constant p * (∑ q, K p q * centered q)) =
          ∑ p, ∑ q, constant p * K p q * centered q := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = ∑ q, ∑ p, constant p * K p q * centered q := by
        rw [Finset.sum_comm]
      _ = ∑ q, (∑ p, constant p * K p q) * centered q := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_mul]
      _ = 0 := by simp only [columnConstant, zero_mul, Finset.sum_const_zero]
  calc
    (∑ p, ∑ q, K p q * x p * x q) =
        ∑ p, x p * (∑ q, K p q * x q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ p, x p * (∑ q, K p q * centered q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [rowCentered]
    _ = ∑ p, (centered p * (∑ q, K p q * centered q) +
          constant p * (∑ q, K p q * centered q)) := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [centered]
      ring
    _ = (∑ p, centered p * (∑ q, K p q * centered q)) +
        ∑ p, constant p * (∑ q, K p q * centered q) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ p, centered p * (∑ q, K p q * centered q) := by
      rw [constantCross, add_zero]
    _ = ∑ p, ∑ q, K p q * centered p * centered q := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ i : Fin (ℓ + 1) × Fin 2, ∑ j : Fin (ℓ + 1) × Fin 2,
        K (i.1.castSucc, i.2) (j.1.castSucc, j.2) *
          (x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)) *
          (x (j.1.castSucc, j.2) - x (Fin.last (ℓ + 1), j.2)) := by
      simp only [Fintype.sum_prod_type]
      rw [Fin.sum_univ_castSucc]
      simp only [centered, constant, Fin.val_last, sub_self, zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      rw [Fin.sum_univ_castSucc]
      simp only [centered, constant, Fin.val_castSucc, Prod.fst, Prod.snd,
        Fin.val_last, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

/-- A constant-kernel matrix is positive semidefinite when its principal restriction has
strictly positive exact pivots. -/
theorem posSemidef_of_kernel_and_principalPivots {ℓ : ℕ} {threshold : ℚ}
    {K : Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℚ}
    (symm : K.IsSymm) (kernel : K * constantModes (ℓ + 2) = 0)
    (threshold_nonneg : 0 ≤ threshold)
    (pivots : PositivePivots threshold
      (fun i j ↦ K (i.1.castSucc, i.2) (j.1.castSucc, j.2))) :
    K.PosSemidef := by
  -- Center a vector by its final pair and apply positivity of the principal restriction.
  let principal : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ :=
    fun i j ↦ K (i.1.castSucc, i.2) (j.1.castSucc, j.2)
  have principalSymm : principal.IsSymm := by
    ext i j
    have entry := congrFun (congrFun symm (j.1.castSucc, j.2)) (i.1.castSucc, i.2)
    simpa only [principal, Matrix.transpose_apply] using entry.symm
  have principalPSD : principal.PosSemidef :=
    posSemidef_of_positivePivots principalSymm threshold_nonneg pivots
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr symm, ?_⟩
  intro x
  rw [rationalFinsuppMatrixQuadratic_eq,
    quadratic_eq_principal_of_constantModes_kernel K symm kernel]
  let centered : Fin (ℓ + 1) × Fin 2 → ℚ :=
    fun i ↦ x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)
  have nonnegative := principalPSD.dotProduct_mulVec_nonneg centered
  have contraction : dotProduct (star centered) (Matrix.mulVec principal centered) =
      ∑ i, ∑ j, principal i j * centered i * centered j := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [contraction] at nonnegative
  simpa only [principal, centered] using nonnegative

/-- Exact table checks needed to reconstruct endpoint and interval certificates. -/
structure Valid {ℓ : ℕ} (c : RationalCase ℓ) : Prop where
  memory_pos : 0 < ℓ
  gammaLower_pos : 0 < c.gammaLower
  gamma_order : c.gammaLower < c.gammaUpper
  omega_pos : 0 < c.omega
  epsilon_pos : 0 < c.epsilon
  zeta_pos : 0 < c.zeta
  lagMinus_length : ∀ b, (c.lagMinus b).length = ℓ
  lagPlus_length : ∀ b, (c.lagPlus b).length = ℓ
  packedMu_length : ∀ b, (c.packedMu b).length = ℓ * ℓ
  upperTriangle_length : ∀ e, (c.upperTriangle e).length = ℓ * (2 * ℓ + 1)
  lagMinus_nonneg : ∀ b i, 0 ≤ lagMinusValue c b i
  lagPlus_nonneg : ∀ b i, 0 ≤ lagPlusValue c b i
  mu_nonneg : ∀ b i j, 0 ≤ reconstructMu c b i j
  terminal_symm : ∀ e, (storageTerminal c e).IsSymm
  descent_kernel : ∀ e, descentMatrix c e * constantModes (ℓ + 2) = 0
  descent_pivots : ∀ e, PositivePivots (1 / 10000000) (descentPrincipal c e)
  lower_pivots : ∀ e, PositivePivots (1 / 10000000) (lowerMatrix c e)

namespace Valid

/-- Assemble validity from the exact positivity, size, symmetry, kernel, and pivot checks. -/
def ofChecks {ℓ : ℕ} {c : RationalCase ℓ} (memory_pos : 0 < ℓ)
    (gammaLower_pos : 0 < c.gammaLower) (gamma_order : c.gammaLower < c.gammaUpper)
    (omega_pos : 0 < c.omega) (epsilon_pos : 0 < c.epsilon) (zeta_pos : 0 < c.zeta)
    (lagMinus_length : ∀ b, (c.lagMinus b).length = ℓ)
    (lagPlus_length : ∀ b, (c.lagPlus b).length = ℓ)
    (packedMu_length : ∀ b, (c.packedMu b).length = ℓ * ℓ)
    (upperTriangle_length : ∀ e, (c.upperTriangle e).length = ℓ * (2 * ℓ + 1))
    (lagMinus_nonneg : ∀ b i, 0 ≤ lagMinusValue c b i)
    (lagPlus_nonneg : ∀ b i, 0 ≤ lagPlusValue c b i)
    (mu_nonneg : ∀ b i j, 0 ≤ reconstructMu c b i j)
    (terminal_symm : ∀ e, (storageTerminal c e).IsSymm)
    (descent_kernel : ∀ e, descentMatrix c e * constantModes (ℓ + 2) = 0)
    (descent_pivots : ∀ e, PositivePivots (1 / 10000000) (descentPrincipal c e))
    (lower_pivots : ∀ e, PositivePivots (1 / 10000000) (lowerMatrix c e)) : Valid c :=
  { memory_pos := memory_pos
    gammaLower_pos := gammaLower_pos
    gamma_order := gamma_order
    omega_pos := omega_pos
    epsilon_pos := epsilon_pos
    zeta_pos := zeta_pos
    lagMinus_length := lagMinus_length
    lagPlus_length := lagPlus_length
    packedMu_length := packedMu_length
    upperTriangle_length := upperTriangle_length
    lagMinus_nonneg := lagMinus_nonneg
    lagPlus_nonneg := lagPlus_nonneg
    mu_nonneg := mu_nonneg
    terminal_symm := terminal_symm
    descent_kernel := descent_kernel
    descent_pivots := descent_pivots
    lower_pivots := lower_pivots }

/-- Validity exposes the endpoint symmetry and kernel checks together with both pivot tests. -/
theorem spec {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c) :
    ∀ e, ((storageTerminal c e).IsSymm ∧
        descentMatrix c e * constantModes (ℓ + 2) = 0) ∧
      (PositivePivots (1 / 10000000) (descentPrincipal c e) ∧
        PositivePivots (1 / 10000000) (lowerMatrix c e)) := by
  -- Expose the four endpoint checks stored in validity.
  intro e
  exact ⟨⟨valid.terminal_symm e, valid.descent_kernel e⟩,
    valid.descent_pivots e, valid.lower_pivots e⟩

end Valid

/-- Cast an exact rational matrix entrywise to a real matrix. -/
def castMatrix {ι : Type u} {κ : Type v} (K : Matrix ι κ ℚ) : Matrix ι κ ℝ :=
  fun i j ↦ K i j

/-- Entry formula for the rational-to-real matrix cast. -/
theorem castMatrix_apply {ι : Type u} {κ : Type v} (K : Matrix ι κ ℚ) (i : ι) (j : κ) :
    castMatrix K i j = K i j := by
  -- Entrywise casting is the definition of the real matrix.
  rfl

/-- A valid negative-direction lag entry stays nonnegative after casting to `ℝ`. -/
theorem lagMinusValue_cast_nonneg {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Fin ℓ) : (0 : ℝ) ≤ lagMinusValue c b i := by
  -- Ordered rational casts preserve the checked nonnegativity.
  exact_mod_cast valid.lagMinus_nonneg b i

/-- Convert an exact nonnegative lag entry into the canonical `NNReal` coefficient. -/
def lagMinusNNReal {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Fin ℓ) : NNReal :=
  ⟨lagMinusValue c b i, lagMinusValue_cast_nonneg valid b i⟩

/-- Coercing a reconstructed negative-direction lag coefficient returns its rational value. -/
theorem lagMinusNNReal_coe {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Fin ℓ) :
    (lagMinusNNReal valid b i : ℝ) = lagMinusValue c b i := by
  -- The `NNReal` constructor retains its underlying real value.
  rfl

/-- A valid positive-direction lag entry stays nonnegative after casting to `ℝ`. -/
theorem lagPlusValue_cast_nonneg {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Fin ℓ) : (0 : ℝ) ≤ lagPlusValue c b i := by
  -- Ordered rational casts preserve the checked nonnegativity.
  exact_mod_cast valid.lagPlus_nonneg b i

/-- Convert an exact nonnegative positive-direction lag entry to `NNReal`. -/
def lagPlusNNReal {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Fin ℓ) : NNReal :=
  ⟨lagPlusValue c b i, lagPlusValue_cast_nonneg valid b i⟩

/-- Coercing a reconstructed positive-direction lag coefficient returns its rational value. -/
theorem lagPlusNNReal_coe {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Fin ℓ) :
    (lagPlusNNReal valid b i : ℝ) = lagPlusValue c b i := by
  -- The `NNReal` constructor retains its underlying real value.
  rfl

/-- A valid interpolation weight stays nonnegative after casting to `ℝ`. -/
theorem reconstructMu_cast_nonneg {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i j : Option (Fin ℓ)) : (0 : ℝ) ≤ reconstructMu c b i j := by
  -- Ordered rational casts preserve the checked nonnegativity.
  exact_mod_cast valid.mu_nonneg b i j

/-- Convert an exact nonnegative reconstructed interpolation weight to `NNReal`. -/
def muNNReal {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i j : Option (Fin ℓ)) : NNReal :=
  ⟨reconstructMu c b i j, reconstructMu_cast_nonneg valid b i j⟩

/-- Coercing a reconstructed interpolation coefficient returns its rational value. -/
theorem muNNReal_coe {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i j : Option (Fin ℓ)) :
    (muNNReal valid b i j : ℝ) = reconstructMu c b i j := by
  -- The `NNReal` constructor retains its underlying real value.
  rfl

/-- The real endpoint storage matrix used by the canonical certificate. -/
def endpointStorage {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ :=
  castMatrix (storageMatrix c e)

/-- Entries of the real endpoint storage are the casts of the exact entries. -/
theorem endpointStorage_apply {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (i j : Fin (ℓ + 1) × Fin 2) :
    endpointStorage c e i j = storageMatrix c e i j := by
  -- Endpoint storage is the entrywise cast of the exact matrix.
  rfl

/-- Casting a rational residual gives the corresponding real residual. -/
private lemma residual_cast {ℓ : ℕ} (Z : (Fin (ℓ + 2) × Fin 2) → ℚ)
    (j : Fin (ℓ + 1)) :
    (ADMM.FiniteMemory.residual (E := ℚ) Z j : ℝ) =
      ADMM.FiniteMemory.residual (fun i ↦ (Z i : ℝ)) j := by
  -- Both residuals are the same adjacent-coordinate difference.
  simp [ADMM.FiniteMemory.residual]

/-- Casting a rational graph position gives the corresponding real graph position. -/
private lemma graphPosition_cast {ℓ : ℕ} (b : Block)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) (j : Fin (ℓ + 1)) :
    (ADMM.FiniteMemory.graphPosition (E := ℚ) b Z j : ℝ) =
      ADMM.FiniteMemory.graphPosition b (fun i ↦ (Z i : ℝ)) j := by
  -- Split the graph block and use the residual cast in the `F` case.
  cases b <;> simp [ADMM.FiniteMemory.graphPosition, residual_cast]

/-- Casting an exact rational graph normal gives the canonical real graph normal. -/
private lemma graphNormal_cast {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) (j : Fin (ℓ + 1)) :
    (graphNormal gamma b Z j : ℝ) =
      ADMM.FiniteMemory.graphNormal gamma b (fun i ↦ (Z i : ℝ)) j := by
  -- The two block formulas agree after casting positions, residuals, and scalar products.
  cases b <;> simp [graphNormal, ADMM.FiniteMemory.graphNormal,
    graphPosition_cast, residual_cast]

/-- Casting exact rational storage evaluation gives canonical real scalar storage evaluation. -/
private lemma quadraticStorage_cast {ℓ : ℕ}
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    (quadraticStorage P Z : ℝ) =
      ADMM.FiniteMemory.quadraticStorage (castMatrix P) (fun i ↦ (Z i : ℝ)) := by
  -- Push the cast through the finite contraction and reduce scalar real inner products.
  rw [quadraticStorage_apply, ADMM.FiniteMemory.quadraticStorage_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp
  rw [castMatrix_apply]
  ring

/-- Casting the exact rational supply gives the canonical real scalar supply. -/
private lemma supply_cast {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℚ) (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    (supply c gamma Z : ℝ) =
      ADMM.FiniteMemory.supply gamma c.omega c.epsilon
        (lagMinusNNReal valid) (lagPlusNNReal valid) (fun i ↦ (Z i : ℝ)) := by
  -- Cast each graph factor and coefficient, then normalize scalar inner products and norms.
  rw [supply_apply, ADMM.FiniteMemory.supply_apply]
  push_cast
  simp_rw [graphNormal_cast, graphPosition_cast, residual_cast]
  simp only [lagMinusNNReal_coe, lagPlusNNReal_coe]
  simp [Real.norm_eq_abs, sq_abs]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    ring

/-- Entrywise casting commutes with polarization when the scalar quadratic expressions commute
with the rational-to-real cast. -/
private lemma castMatrix_matrixOfQuadratic {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Qq : (ι → ℚ) → ℚ) (Qr : (ι → ℝ) → ℝ)
    (cast_apply : ∀ Z, (Qq Z : ℝ) = Qr (fun i ↦ (Z i : ℝ))) :
    castMatrix (matrixOfQuadratic Qq) = ADMM.FiniteMemory.matrixOfQuadratic Qr := by
  -- Compare the three standard-basis evaluations in each polarization entry.
  ext i j
  rw [castMatrix_apply, matrixOfQuadratic_apply,
    ADMM.FiniteMemory.matrixOfQuadratic_apply]
  push_cast
  rw [cast_apply, cast_apply, cast_apply]
  have cast_indicator (a b : ι) :
      (((if a = b then (1 : ℚ) else 0 : ℚ) : ℝ)) =
        if a = b then (1 : ℝ) else 0 := by
    by_cases hab : a = b
    · simp only [if_pos hab, Rat.cast_one]
    · simp only [if_neg hab, Rat.cast_zero]
  have cast_basis_add :
      (fun k : ι ↦
        (((if k = i then (1 : ℚ) else 0) + if k = j then 1 else 0 : ℚ) : ℝ)) =
        fun k ↦ (if k = i then (1 : ℝ) else 0) + if k = j then 1 else 0 := by
    funext k
    push_cast
    rw [cast_indicator, cast_indicator]
  have cast_basis_left :
      (fun k : ι ↦ ((if k = i then (1 : ℚ) else 0 : ℚ) : ℝ)) =
        fun k ↦ if k = i then (1 : ℝ) else 0 := by
    funext k
    exact cast_indicator k i
  have cast_basis_right :
      (fun k : ι ↦ ((if k = j then (1 : ℚ) else 0 : ℚ) : ℝ)) =
        fun k ↦ if k = j then (1 : ℝ) else 0 := by
    funext k
    exact cast_indicator k j
  rw [cast_basis_add, cast_basis_left, cast_basis_right]

/-- The cast of the exact endpoint descent expression is the canonical real descent expression. -/
private lemma descentExpression_cast {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) (Z : (Fin (ℓ + 2) × Fin 2) → ℚ) :
    ((quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.succ, i.2)) -
        quadraticStorage (storageMatrix c e) (fun i ↦ Z (i.1.castSucc, i.2)) -
          supply c (endpointGamma c e) Z : ℚ) : ℝ) =
      ADMM.FiniteMemory.descentExpression (endpointGamma c e) c.omega c.epsilon
        (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c e)
          (fun i ↦ (Z i : ℝ)) := by
  -- Cast the two storage evaluations and supply term independently.
  rw [ADMM.FiniteMemory.descentExpression_apply]
  push_cast
  rw [quadraticStorage_cast, quadraticStorage_cast, supply_cast]
  rfl

/-- Exact endpoint descent reconstruction agrees with the canonical real descent matrix. -/
theorem cast_descentMatrix {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) :
    castMatrix (descentMatrix c e) =
      ADMM.FiniteMemory.descentMatrix (endpointGamma c e) c.omega c.epsilon
        (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c e) := by
  -- Apply the polarization cast bridge to the endpoint descent-expression identity.
  rw [descentMatrix, ADMM.FiniteMemory.descentMatrix]
  exact castMatrix_matrixOfQuadratic _ _ (descentExpression_cast valid e)

/-- Casting a rational interpolation position gives the canonical real interpolation position. -/
private lemma interpolationPosition_cast {ℓ : ℕ} (b : Block) (i : Option (Fin ℓ))
    (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    (interpolationPosition b i Z : ℝ) =
      ADMM.FiniteMemory.interpolationPosition b i (fun a ↦ (Z a : ℝ)) := by
  -- Split the optional index and block until only casts of coordinate arithmetic remain.
  cases i with
  | none => simp [interpolationPosition, ADMM.FiniteMemory.interpolationPosition]
  | some j =>
      cases b <;> simp [interpolationPosition, ADMM.FiniteMemory.interpolationPosition]

/-- Casting a rational interpolation normal gives the canonical real interpolation normal. -/
private lemma interpolationNormal_cast {ℓ : ℕ} (gamma : ℚ) (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    (interpolationNormal gamma b i Z : ℝ) =
      ADMM.FiniteMemory.interpolationNormal gamma b i (fun a ↦ (Z a : ℝ)) := by
  -- Reduce each optional/block case and reuse the position cast in the `F` branch.
  cases i with
  | none => simp [interpolationNormal, ADMM.FiniteMemory.interpolationNormal]
  | some j =>
      cases b <;> simp [interpolationNormal, ADMM.FiniteMemory.interpolationNormal,
        interpolationPosition_cast]

/-- The exact lower-test scalar expression commutes with the rational-to-real cast. -/
private lemma lowerExpression_cast {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    ((quadraticStorage (storageMatrix c e) Z -
        (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          reconstructMu c b i j *
            (-interpolationNormal (endpointGamma c e) b j Z *
              (interpolationPosition b i Z - interpolationPosition b j Z))) -
        c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2) : ℚ) : ℝ) =
      ADMM.FiniteMemory.quadraticStorage (endpointStorage c e)
          (fun a ↦ (Z a : ℝ)) -
        (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (muNNReal valid b i j : ℝ) *
            (-ADMM.FiniteMemory.interpolationNormal (endpointGamma c e) b j
                (fun a ↦ (Z a : ℝ)) *
              (ADMM.FiniteMemory.interpolationPosition b i (fun a ↦ (Z a : ℝ)) -
                ADMM.FiniteMemory.interpolationPosition b j (fun a ↦ (Z a : ℝ))))) -
        (c.zeta : ℝ) * ((Z (0, 0) : ℝ) ^ 2 + (Z (0, 1) : ℝ) ^ 2) := by
  -- Push casts through the finite sums, then identify storage, coefficients, and graph data.
  push_cast
  rw [quadraticStorage_cast]
  simp_rw [interpolationNormal_cast, interpolationPosition_cast]
  simp only [muNNReal_coe]
  rfl

/-- Real polarization of a quadratic form is its canonical matrix representation. -/
private lemma realMatrixOfQuadratic_eq_toMatrix' {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm ℝ (ι → ℝ)) :
    ADMM.FiniteMemory.matrixOfQuadratic (fun Z ↦ Q Z) = Q.toMatrix' := by
  -- Compare both matrices on standard basis vectors and normalize the associated form.
  ext i j
  rw [ADMM.FiniteMemory.matrixOfQuadratic_apply, QuadraticForm.toMatrix',
    LinearMap.toMatrix₂'_apply, QuadraticMap.associated_apply]
  have basis_i : (fun k : ι ↦ if k = i then (1 : ℝ) else 0) = Pi.single i 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  have basis_j : (fun k : ι ↦ if k = j then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  have basis_add : (fun k : ι ↦
      (if k = i then (1 : ℝ) else 0) + if k = j then 1 else 0) =
      Pi.single i 1 + Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [congrArg (Q : (ι → ℝ) → ℝ) basis_add,
    congrArg (Q : (ι → ℝ) → ℝ) basis_i,
    congrArg (Q : (ι → ℝ) → ℝ) basis_j]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul,
    smul_eq_mul]
  norm_num
  ring_nf

/-- Polarization recovers a symmetric real matrix from its finite quadratic contraction. -/
private lemma realMatrixOfQuadratic_contraction {ι : Type u} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι ℝ) (symm : M.IsSymm) :
    ADMM.FiniteMemory.matrixOfQuadratic
        (fun Z ↦ ∑ i, ∑ j, M i j * Z i * Z j) = M := by
  -- Identify the contraction with `Matrix.toQuadraticForm'`, then recover its symmetric bilinear
  -- form and hence its original matrix.
  have contraction_eq :
      (fun Z : ι → ℝ ↦ ∑ i, ∑ j, M i j * Z i * Z j) =
        fun Z ↦ Matrix.toQuadraticForm' M Z := by
    funext Z
    have diagonal : Matrix.toQuadraticForm' M Z = Matrix.toBilin' M Z Z := rfl
    rw [diagonal, Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [contraction_eq, realMatrixOfQuadratic_eq_toMatrix']
  have bilinearSymm : (Matrix.toBilin' M).IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr symm
  have associated_eq :
      (Matrix.toQuadraticForm' M).associated = Matrix.toBilin' M :=
    QuadraticMap.associated_left_inverse ℝ fun x y ↦ bilinearSymm.eq x y
  rw [QuadraticForm.toMatrix', associated_eq]
  exact (LinearMap.toMatrix₂' ℝ).apply_symm_apply M

/-- Every real polarization matrix is symmetric. -/
private lemma realMatrixOfQuadratic_isSymm {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : (ι → ℝ) → ℝ) :
    (ADMM.FiniteMemory.matrixOfQuadratic Q).IsSymm := by
  -- Swapping the two basis vectors only commutes their pointwise sum and the two subtractions.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  rw [ADMM.FiniteMemory.matrixOfQuadratic_apply,
    ADMM.FiniteMemory.matrixOfQuadratic_apply]
  have basis_comm :
      (fun k : ι ↦ (if k = j then (1 : ℝ) else 0) + if k = i then 1 else 0) =
        fun k ↦ (if k = i then (1 : ℝ) else 0) + if k = j then 1 else 0 := by
    funext k
    ring
  rw [congrArg Q basis_comm]
  ring

/-- Entrywise casting preserves matrix symmetry. -/
private lemma castMatrix_isSymm {ι : Type u} (M : Matrix ι ι ℚ) (symm : M.IsSymm) :
    (castMatrix M).IsSymm := by
  -- Cast the exact symmetry equation at each pair of entries.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  rw [castMatrix_apply, castMatrix_apply]
  exact congrArg (fun x : ℚ ↦ (x : ℝ)) (symm.apply i j)

/-- The canonical real lower matrix is symmetric whenever its storage matrix is symmetric. -/
private lemma realLowerMatrix_isSymm {ℓ : ℕ} (gamma zeta : ℝ)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (mu : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal) (symm : P.IsSymm) :
    (ADMM.FiniteMemory.lowerMatrix gamma zeta P mu).IsSymm := by
  -- Each directed gap is a polarization matrix; finite sums, scaling, and subtraction preserve
  -- symmetry, as does the diagonal current-coordinate selector.
  have gapsSymm :
      (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        (mu b i j : ℝ) • ADMM.FiniteMemory.gapMatrix gamma b i j).IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro a d
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have gapSymm := realMatrixOfQuadratic_isSymm
      (fun Z ↦ -ADMM.FiniteMemory.interpolationNormal gamma b j Z *
        (ADMM.FiniteMemory.interpolationPosition b i Z -
          ADMM.FiniteMemory.interpolationPosition b j Z))
    rw [ADMM.FiniteMemory.gapMatrix]
    exact congrArg (fun x : ℝ ↦ (mu b i j : ℝ) * x) (gapSymm.apply a d)
  have currentSymm :
      (ADMM.FiniteMemory.currentMatrix :
        Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ).IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    by_cases hij : i = j
    · simp [ADMM.FiniteMemory.currentMatrix, hij]
    · simp [ADMM.FiniteMemory.currentMatrix, hij, Ne.symm hij]
  rw [ADMM.FiniteMemory.lowerMatrix]
  exact (symm.sub gapsSymm).sub (currentSymm.smul zeta)

/-- Casting the exact lower expression gives the quadratic contraction of the canonical real lower
matrix. -/
private lemma lowerMatrixContraction_cast {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) (Z : (Fin (ℓ + 1) × Fin 2) → ℚ) :
    ((quadraticStorage (storageMatrix c e) Z -
        (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          reconstructMu c b i j *
            (-interpolationNormal (endpointGamma c e) b j Z *
              (interpolationPosition b i Z - interpolationPosition b j Z))) -
        c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2) : ℚ) : ℝ) =
      ∑ a, ∑ d,
        ADMM.FiniteMemory.lowerMatrix (endpointGamma c e) c.zeta
            (endpointStorage c e) (muNNReal valid) a d *
          (Z a : ℝ) * (Z d : ℝ) := by
  -- First cast the scalar expression, then use the real lower-matrix computation theorem.
  rw [lowerExpression_cast valid e Z]
  symm
  exact ADMM.FiniteMemory.lowerMatrix_quadratic _ _ _ _ _

/-- Exact endpoint lower reconstruction agrees with the canonical real lower matrix. -/
theorem cast_lowerMatrix {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) :
    castMatrix (lowerMatrix c e) =
      ADMM.FiniteMemory.lowerMatrix (endpointGamma c e) c.zeta
        (endpointStorage c e) (muNNReal valid) := by
  -- Cast the defining polarization, then recover the symmetric real lower matrix from its
  -- quadratic contraction.
  rw [lowerMatrix]
  calc
    castMatrix (matrixOfQuadratic fun Z ↦
        quadraticStorage (storageMatrix c e) Z -
          (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
            reconstructMu c b i j *
              (-interpolationNormal (endpointGamma c e) b j Z *
                (interpolationPosition b i Z - interpolationPosition b j Z))) -
          c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2)) =
        ADMM.FiniteMemory.matrixOfQuadratic (fun Z ↦
          ∑ a, ∑ d,
            ADMM.FiniteMemory.lowerMatrix (endpointGamma c e) c.zeta
                (endpointStorage c e) (muNNReal valid) a d * Z a * Z d) := by
      exact castMatrix_matrixOfQuadratic _ _ (lowerMatrixContraction_cast valid e)
    _ = ADMM.FiniteMemory.lowerMatrix (endpointGamma c e) c.zeta
        (endpointStorage c e) (muNNReal valid) := by
      exact realMatrixOfQuadratic_contraction _
        (realLowerMatrix_isSymm _ _ _ _
          (castMatrix_isSymm _ (storageMatrix_isSymm c e (valid.terminal_symm e))))

/-- Rational polarization matrices are symmetric. -/
private lemma rationalMatrixOfQuadratic_isSymm {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : (ι → ℚ) → ℚ) : (matrixOfQuadratic Q).IsSymm := by
  -- Swapping the two basis vectors commutes their pointwise sum and the two subtractions.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  rw [matrixOfQuadratic_apply, matrixOfQuadratic_apply]
  have basis_comm :
      (fun k : ι ↦ (if k = j then (1 : ℚ) else 0) + if k = i then 1 else 0) =
        fun k ↦ (if k = i then (1 : ℚ) else 0) + if k = j then 1 else 0 := by
    funext k
    ring
  rw [congrArg Q basis_comm]
  ring

/-- After casting, an exact `LDLᵀ` factorization evaluates as a real pivot-weighted sum of
squares. -/
private lemma castLdl_quadratic_eq_sum_squares {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (symm : K.IsSymm)
    (nonzero : ∀ i, (ldl K).pivot i ≠ 0) (x : Fin k × Fin 2 → ℝ) :
    (∑ i, ∑ j, castMatrix K i j * x i * x j) =
      ∑ h, ((ldl K).pivot h : ℝ) *
        (∑ i, ((ldl K).lower i h : ℝ) * x i) ^ 2 := by
  -- Cast the exact entrywise factorization, then commute the finite sums by pivot column.
  calc
    (∑ i, ∑ j, castMatrix K i j * x i * x j) =
        ∑ i, ∑ j, ∑ h,
          (((ldl K).lower i h : ℝ) * ((ldl K).pivot h : ℝ) *
              ((ldl K).lower j h : ℝ)) * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [castMatrix_apply, ldl_factorization K symm nonzero i j]
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ i, ∑ h, ∑ j,
          (((ldl K).lower i h : ℝ) * ((ldl K).pivot h : ℝ) *
              ((ldl K).lower j h : ℝ)) * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ h, ∑ i, ∑ j,
          (((ldl K).lower i h : ℝ) * ((ldl K).pivot h : ℝ) *
              ((ldl K).lower j h : ℝ)) * x i * x j := by
      rw [Finset.sum_comm]
    _ = ∑ h, ((ldl K).pivot h : ℝ) *
        (∑ i, ((ldl K).lower i h : ℝ) * x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Positive exact pivots make the entrywise real cast positive semidefinite. -/
private lemma castMatrix_posSemidef_of_positivePivots {k : ℕ} {threshold : ℚ}
    {K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ} (symm : K.IsSymm)
    (threshold_nonneg : 0 ≤ threshold) (pivots : PositivePivots threshold K) :
    (castMatrix K).PosSemidef := by
  -- Expand a real matrix-vector contraction and apply the cast LDL sum-of-squares identity.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (castMatrix_isSymm K symm)) ?_
  intro x
  have contraction : dotProduct (star x) (Matrix.mulVec (castMatrix K) x) =
      ∑ i, ∑ j, castMatrix K i j * x i * x j := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [contraction, castLdl_quadratic_eq_sum_squares K symm
    (positivePivots_ne_zero threshold_nonneg pivots)]
  apply Finset.sum_nonneg
  intro h hh
  have pivot_nonneg : (0 : ℝ) ≤ (ldl K).pivot h := by
    exact_mod_cast le_of_lt (lt_of_le_of_lt threshold_nonneg (pivots h))
  exact mul_nonneg pivot_nonneg (sq_nonneg _)

/-- Every endpoint parameter of a valid rational case is positive after casting to `ℝ`. -/
theorem endpointGamma_cast_pos {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) : (0 : ℝ) < endpointGamma c e := by
  -- The lower endpoint is positive, and the upper endpoint is larger.
  cases e with
  | lower => exact_mod_cast valid.gammaLower_pos
  | upper => exact_mod_cast lt_trans valid.gammaLower_pos valid.gamma_order

/-- The storage weight of a valid rational case is positive after casting to `ℝ`. -/
theorem omega_cast_pos {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c) :
    (0 : ℝ) < c.omega := by
  -- Ordered rational casts preserve strict positivity.
  exact_mod_cast valid.omega_pos

/-- The residual weight of a valid rational case is positive after casting to `ℝ`. -/
theorem epsilon_cast_pos {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c) :
    (0 : ℝ) < c.epsilon := by
  -- Ordered rational casts preserve strict positivity.
  exact_mod_cast valid.epsilon_pos

/-- The lower-bound weight of a valid rational case is positive after casting to `ℝ`. -/
theorem zeta_cast_pos {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c) :
    (0 : ℝ) < c.zeta := by
  -- Ordered rational casts preserve strict positivity.
  exact_mod_cast valid.zeta_pos

/-- Vanishing row sums in both constant modes reduce a real quadratic contraction to its centered
principal restriction. -/
private lemma realQuadratic_eq_principal_of_rowSums_zero {ℓ : ℕ}
    (M : Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℝ)
    (symm : M.IsSymm)
    (rowKernel : ∀ (p : Fin (ℓ + 2) × Fin 2) (a : Fin 2),
      (∑ t : Fin (ℓ + 2), M p (t, a)) = 0)
    (x : Fin (ℓ + 2) × Fin 2 → ℝ) :
    (∑ p, ∑ q, M p q * x p * x q) =
      ∑ i : Fin (ℓ + 1) × Fin 2, ∑ j : Fin (ℓ + 1) × Fin 2,
        M (i.1.castSucc, i.2) (j.1.castSucc, j.2) *
          (x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)) *
          (x (j.1.castSucc, j.2) - x (Fin.last (ℓ + 1), j.2)) := by
  -- Split the history into its final constant pair and centered remainder; both cross terms vanish
  -- by the row sums, and the final centered pair is zero.
  let constant : (Fin (ℓ + 2) × Fin 2) → ℝ :=
    fun p ↦ x (Fin.last (ℓ + 1), p.2)
  let centered : (Fin (ℓ + 2) × Fin 2) → ℝ :=
    fun p ↦ x p - constant p
  have symmetric (p q : Fin (ℓ + 2) × Fin 2) : M p q = M q p := by
    have entry := congrFun (congrFun symm q) p
    simpa only [Matrix.transpose_apply] using entry
  have rowConstant (p : Fin (ℓ + 2) × Fin 2) :
      (∑ q, M p q * constant q) = 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ t : Fin (ℓ + 2), ∑ a : Fin 2, M p (t, a) * constant (t, a)) =
          ∑ a : Fin 2, ∑ t : Fin (ℓ + 2), M p (t, a) * constant (t, a) := by
        rw [Finset.sum_comm]
      _ = ∑ a : Fin 2,
          (∑ t : Fin (ℓ + 2), M p (t, a)) * x (Fin.last (ℓ + 1), a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
      _ = 0 := by simp only [rowKernel, zero_mul, Finset.sum_const_zero]
  have columnConstant (q : Fin (ℓ + 2) × Fin 2) :
      (∑ p, constant p * M p q) = 0 := by
    calc
      (∑ p, constant p * M p q) = ∑ p, M q p * constant p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [symmetric p q]
        ring
      _ = 0 := rowConstant q
  have rowCentered (p : Fin (ℓ + 2) × Fin 2) :
      (∑ q, M p q * x q) = ∑ q, M p q * centered q := by
    calc
      (∑ q, M p q * x q) =
          ∑ q, (M p q * centered q + M p q * constant q) := by
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [centered]
        ring
      _ = (∑ q, M p q * centered q) + ∑ q, M p q * constant q := by
        rw [Finset.sum_add_distrib]
      _ = ∑ q, M p q * centered q := by rw [rowConstant, add_zero]
  have constantCross :
      (∑ p, constant p * (∑ q, M p q * centered q)) = 0 := by
    calc
      (∑ p, constant p * (∑ q, M p q * centered q)) =
          ∑ p, ∑ q, constant p * M p q * centered q := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = ∑ q, ∑ p, constant p * M p q * centered q := by
        rw [Finset.sum_comm]
      _ = ∑ q, (∑ p, constant p * M p q) * centered q := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_mul]
      _ = 0 := by simp only [columnConstant, zero_mul, Finset.sum_const_zero]
  calc
    (∑ p, ∑ q, M p q * x p * x q) =
        ∑ p, x p * (∑ q, M p q * x q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ p, x p * (∑ q, M p q * centered q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [rowCentered]
    _ = ∑ p, (centered p * (∑ q, M p q * centered q) +
          constant p * (∑ q, M p q * centered q)) := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [centered]
      ring
    _ = (∑ p, centered p * (∑ q, M p q * centered q)) +
        ∑ p, constant p * (∑ q, M p q * centered q) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ p, centered p * (∑ q, M p q * centered q) := by
      rw [constantCross, add_zero]
    _ = ∑ p, ∑ q, M p q * centered p * centered q := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ i : Fin (ℓ + 1) × Fin 2, ∑ j : Fin (ℓ + 1) × Fin 2,
        M (i.1.castSucc, i.2) (j.1.castSucc, j.2) *
          (x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)) *
          (x (j.1.castSucc, j.2) - x (Fin.last (ℓ + 1), j.2)) := by
      simp only [Fintype.sum_prod_type]
      rw [Fin.sum_univ_castSucc]
      simp only [centered, constant, sub_self, zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      rw [Fin.sum_univ_castSucc]
      simp only [centered, constant, Fin.val_castSucc, Prod.fst, Prod.snd,
        sub_self, mul_zero, Finset.sum_const_zero, add_zero]

/-- An exact constant-mode kernel and positive principal pivots make the entrywise real cast
positive semidefinite. -/
private lemma castMatrix_posSemidef_of_kernel_and_principalPivots {ℓ : ℕ}
    {threshold : ℚ}
    {K : Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℚ}
    (symm : K.IsSymm) (kernel : K * constantModes (ℓ + 2) = 0)
    (threshold_nonneg : 0 ≤ threshold)
    (pivots : PositivePivots threshold
      (fun i j ↦ K (i.1.castSucc, i.2) (j.1.castSucc, j.2))) :
    (castMatrix K).PosSemidef := by
  -- Cast the principal LDL certificate and center an arbitrary real vector using the cast kernel.
  let principal : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ :=
    fun i j ↦ K (i.1.castSucc, i.2) (j.1.castSucc, j.2)
  have principalSymm : principal.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    exact symm.apply (i.1.castSucc, i.2) (j.1.castSucc, j.2)
  have principalPSD : (castMatrix principal).PosSemidef :=
    castMatrix_posSemidef_of_positivePivots principalSymm threshold_nonneg pivots
  have rowKernel (p : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
      (∑ t : Fin (ℓ + 2), castMatrix K p (t, a)) = 0 := by
    have exactEntry := congrFun (congrFun kernel p) a
    rw [matrix_mul_constantModes_apply, Matrix.zero_apply] at exactEntry
    have castEntry := congrArg (fun z : ℚ ↦ (z : ℝ)) exactEntry
    push_cast at castEntry
    simpa only [castMatrix_apply, Rat.cast_zero] using castEntry
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (castMatrix_isSymm K symm)) ?_
  intro x
  have contraction : dotProduct (star x) (Matrix.mulVec (castMatrix K) x) =
      ∑ p, ∑ q, castMatrix K p q * x p * x q := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [contraction,
    realQuadratic_eq_principal_of_rowSums_zero (castMatrix K)
      (castMatrix_isSymm K symm) rowKernel]
  let centered : Fin (ℓ + 1) × Fin 2 → ℝ :=
    fun i ↦ x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)
  have nonnegative := principalPSD.dotProduct_mulVec_nonneg centered
  have principalContraction :
      dotProduct (star centered) (Matrix.mulVec (castMatrix principal) centered) =
        ∑ i, ∑ j, castMatrix principal i j * centered i * centered j := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [principalContraction] at nonnegative
  simpa only [principal, centered, castMatrix_apply] using nonnegative

/-- The exact kernel and positive principal pivots imply endpoint descent positivity. -/
theorem endpointDescent_posSemidef {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) :
    (ADMM.FiniteMemory.descentMatrix (endpointGamma c e) c.omega c.epsilon
      (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c e)).PosSemidef := by
  -- Apply the cast kernel/principal-pivot bridge to the exact endpoint matrix, then identify the
  -- canonical real descent matrix.
  have exactSymm : (descentMatrix c e).IsSymm := by
    rw [descentMatrix]
    exact rationalMatrixOfQuadratic_isSymm _
  have castPSD : (castMatrix (descentMatrix c e)).PosSemidef :=
    castMatrix_posSemidef_of_kernel_and_principalPivots exactSymm
      (valid.descent_kernel e) (by norm_num) (valid.descent_pivots e)
  rw [cast_descentMatrix valid e] at castPSD
  exact castPSD

/-- Positive exact pivots imply endpoint lower-test positivity. -/
theorem endpointLower_posSemidef {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) :
    (ADMM.FiniteMemory.lowerMatrix (endpointGamma c e) c.zeta
      (endpointStorage c e) (muNNReal valid)).PosSemidef := by
  -- Apply the cast LDL positivity bridge to the exact lower endpoint test, then rewrite it to the
  -- canonical real matrix.
  have exactSymm : (lowerMatrix c e).IsSymm := by
    rw [lowerMatrix]
    exact rationalMatrixOfQuadratic_isSymm _
  have castPSD : (castMatrix (lowerMatrix c e)).PosSemidef :=
    castMatrix_posSemidef_of_positivePivots exactSymm (by norm_num) (valid.lower_pivots e)
  rw [cast_lowerMatrix valid e] at castPSD
  exact castPSD

/-- The real endpoint storage matrix is symmetric. -/
theorem endpointStorage_isSymm {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) : (endpointStorage c e).IsSymm := by
  -- Cast the exact symmetry of the completed endpoint matrix entrywise.
  ext i j
  rw [Matrix.transpose_apply, endpointStorage_apply, endpointStorage_apply]
  have exactSymmetry := storageMatrix_isSymm c e (valid.terminal_symm e)
  have exactEntry := congrFun (congrFun exactSymmetry i) j
  simpa only [Matrix.transpose_apply] using
    congrArg (fun x : ℚ ↦ (x : ℝ)) exactEntry

/-- The canonical nonnegative interpolation weights have zero diagonal. -/
theorem muNNReal_diag {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (i : Option (Fin ℓ)) : muNNReal valid b i i = 0 := by
  -- Equality in `NNReal` follows from the exact reconstructed diagonal.
  apply NNReal.eq
  rw [muNNReal_coe]
  simpa only [Rat.cast_zero, NNReal.coe_zero] using
    congrArg (fun x : ℚ ↦ (x : ℝ)) (reconstructMu_diag c b i)

/-- The canonical nonnegative interpolation weights satisfy value balance. -/
theorem muNNReal_balance {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (b : Block) (j : Fin ℓ) :
    (∑ i : Option (Fin ℓ), (muNNReal valid b (some j) i : ℝ)) -
      (∑ i : Option (Fin ℓ), (muNNReal valid b i (some j) : ℝ)) =
        ADMM.FiniteMemory.lagCoefficient (lagMinusNNReal valid) (lagPlusNNReal valid) b j := by
  -- Cast the exact rational balance identity and identify every canonical coefficient.
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [ADMM.FiniteMemory.lagCoefficient_apply, muNNReal_coe,
    lagMinusNNReal_coe, lagPlusNNReal_coe]
  have exactBalance := congrArg (fun x : ℚ ↦ (x : ℝ)) (reconstructMu_balance c b j)
  simp only [lagCoefficient] at exactBalance
  push_cast at exactBalance
  rw [Fintype.sum_option, Fintype.sum_option] at exactBalance
  rw [exactBalance]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hji : j ≤ i
  · simp [hji]
  · simp [hji]

/-- Construct the canonical finite-memory certificate at either rational endpoint. -/
def toEndpointCertificate {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) : Certificate ℓ (endpointGamma c e) where
  lagMinus := lagMinusNNReal valid
  lagPlus := lagPlusNNReal valid
  omega := c.omega
  epsilon := c.epsilon
  zeta := c.zeta
  P := endpointStorage c e
  μ := muNNReal valid
  memory_pos := valid.memory_pos
  gamma_pos := endpointGamma_cast_pos valid e
  omega_pos := omega_cast_pos valid
  epsilon_pos := epsilon_cast_pos valid
  zeta_pos := zeta_cast_pos valid
  P_symm := endpointStorage_isSymm valid e
  μ_diag := muNNReal_diag valid
  value_balance := muNNReal_balance valid
  descent_psd := endpointDescent_posSemidef valid e
  lower_psd := endpointLower_posSemidef valid e

/-- An endpoint certificate stores exactly the reconstructed endpoint matrix. -/
theorem toEndpointCertificate_P {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (e : Endpoint) : (toEndpointCertificate valid e).P = endpointStorage c e := by
  -- The endpoint matrix is stored verbatim in the certificate.
  rfl

/-- Affinely interpolate the two exact endpoint storage matrices at a real parameter. -/
def intervalStorage {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℝ) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ :=
  let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
  fun i j ↦ (1 - theta) * endpointStorage c .lower i j +
    theta * endpointStorage c .upper i j

/-- The interpolation parameter gives the displayed affine storage-matrix formula. -/
theorem intervalStorage_apply {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℝ)
    (i j : Fin (ℓ + 1) × Fin 2) :
    intervalStorage c gamma i j =
      let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
      (1 - theta) * endpointStorage c .lower i j + theta * endpointStorage c .upper i j := by
  -- The displayed entry is the definition of affine storage interpolation.
  rfl

/-- Affine interpolation preserves symmetry of the endpoint storage matrices. -/
theorem intervalStorage_isSymm {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) : (intervalStorage c gamma).IsSymm := by
  -- A common affine combination of two symmetric endpoint matrices is symmetric.
  ext i j
  rw [Matrix.transpose_apply, intervalStorage_apply, intervalStorage_apply]
  have lowerSymmetry := endpointStorage_isSymm valid .lower
  have upperSymmetry := endpointStorage_isSymm valid .upper
  have lowerEntry := congrFun (congrFun lowerSymmetry i) j
  have upperEntry := congrFun (congrFun upperSymmetry i) j
  simp only [Matrix.transpose_apply] at lowerEntry upperEntry
  rw [lowerEntry, upperEntry]

/-- The interpolation parameter expresses `gamma` as the affine combination of the two endpoints. -/
private lemma gamma_eq_affine_endpoints {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) :
    let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
    gamma = (1 - theta) * c.gammaLower + theta * c.gammaUpper := by
  -- Clear the nonzero endpoint gap and normalize the defining quotient.
  dsimp
  have gap_ne : (c.gammaUpper : ℝ) - c.gammaLower ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast valid.gamma_order))
  field_simp [gap_ne]
  ring

/-- Scalar quadratic storage is linear in its matrix argument. -/
private lemma quadraticStorage_affine {ℓ : ℕ} (a b : ℝ)
    (P Q : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    ADMM.FiniteMemory.quadraticStorage (a • P + b • Q) Z =
      a * ADMM.FiniteMemory.quadraticStorage P Z +
        b * ADMM.FiniteMemory.quadraticStorage Q Z := by
  -- Distribute each entry and then split both finite sums.
  rw [ADMM.FiniteMemory.quadraticStorage_apply,
    ADMM.FiniteMemory.quadraticStorage_apply,
    ADMM.FiniteMemory.quadraticStorage_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ i, ∑ j, (a * P i j + b * Q i j) * inner ℝ (Z i) (Z j)) =
        ∑ i, ∑ j,
          (a * (P i j * inner ℝ (Z i) (Z j)) +
            b * (Q i j * inner ℝ (Z i) (Z j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ((a * ∑ j, P i j * inner ℝ (Z i) (Z j)) +
          (b * ∑ j, Q i j * inner ℝ (Z i) (Z j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = a * (∑ i, ∑ j, P i j * inner ℝ (Z i) (Z j)) +
        b * (∑ i, ∑ j, Q i j * inner ℝ (Z i) (Z j)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The interpolated storage matrix is its displayed affine endpoint combination. -/
private lemma intervalStorage_eq_affine {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℝ) :
    intervalStorage c gamma =
      (1 - (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)) •
          endpointStorage c .lower +
        ((gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)) •
          endpointStorage c .upper := by
  -- Compare entries and unfold only the interpolation formula.
  ext i j
  rw [intervalStorage_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
  rfl

/-- Affine interpolation of the storage matrix gives affine interpolation of scalar storage. -/
private lemma intervalQuadraticStorage_affine {ℓ : ℕ} (c : RationalCase ℓ) (gamma : ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
    ADMM.FiniteMemory.quadraticStorage (intervalStorage c gamma) Z =
      (1 - theta) * ADMM.FiniteMemory.quadraticStorage (endpointStorage c .lower) Z +
        theta * ADMM.FiniteMemory.quadraticStorage (endpointStorage c .upper) Z := by
  -- Identify the storage matrix with its affine endpoint combination, then use matrix linearity.
  dsimp
  rw [intervalStorage_eq_affine, quadraticStorage_affine]

/-- Graph normals are affine in the scalar parameter. -/
private lemma graphNormal_affine {ℓ : ℕ} (a b gamma lower upper : ℝ)
    (coefficient_sum : a + b = 1) (gamma_eq : gamma = a * lower + b * upper)
    (block : Block) (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) (j : Fin (ℓ + 1)) :
    ADMM.FiniteMemory.graphNormal gamma block Z j =
      a * ADMM.FiniteMemory.graphNormal lower block Z j +
        b * ADMM.FiniteMemory.graphNormal upper block Z j := by
  -- The two block formulas are linear in `gamma`; constant coordinate terms use `a + b = 1`.
  cases block with
  | F =>
      simp only [ADMM.FiniteMemory.graphNormal, smul_eq_mul]
      rw [gamma_eq]
      calc
        Z (j.succ, 0) - (a * lower + b * upper) * Z (j.succ, 1) -
            ADMM.FiniteMemory.graphPosition .F Z j =
          (a + b) * Z (j.succ, 0) - (a * lower + b * upper) * Z (j.succ, 1) -
            (a + b) * ADMM.FiniteMemory.graphPosition .F Z j := by
              rw [coefficient_sum]
              ring
        _ = a * (Z (j.succ, 0) - lower * Z (j.succ, 1) -
              ADMM.FiniteMemory.graphPosition .F Z j) +
            b * (Z (j.succ, 0) - upper * Z (j.succ, 1) -
              ADMM.FiniteMemory.graphPosition .F Z j) := by ring
  | J =>
      simp only [ADMM.FiniteMemory.graphNormal, smul_eq_mul]
      rw [gamma_eq]
      calc
        (a * lower + b * upper) * Z (j.succ, 1) +
            ADMM.FiniteMemory.residual Z j =
          (a * lower + b * upper) * Z (j.succ, 1) +
            (a + b) * ADMM.FiniteMemory.residual Z j := by
              rw [coefficient_sum]
              ring
        _ = a * (lower * Z (j.succ, 1) + ADMM.FiniteMemory.residual Z j) +
            b * (upper * Z (j.succ, 1) + ADMM.FiniteMemory.residual Z j) := by ring

/-- The scalar supply is affine in the algorithmic parameter. -/
private lemma supply_affine {ℓ : ℕ} (a b gamma lower upper omega epsilon : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (coefficient_sum : a + b = 1) (gamma_eq : gamma = a * lower + b * upper)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    ADMM.FiniteMemory.supply gamma omega epsilon lagMinus lagPlus Z =
      a * ADMM.FiniteMemory.supply lower omega epsilon lagMinus lagPlus Z +
        b * ADMM.FiniteMemory.supply upper omega epsilon lagMinus lagPlus Z := by
  -- Rewrite every normal by its affine formula, distribute coefficients through both finite sums,
  -- and use `a + b = 1` for the residual term.
  have normalAffine (block : Block) (j : Fin (ℓ + 1)) :
      ADMM.FiniteMemory.graphNormal gamma block Z j =
        a * ADMM.FiniteMemory.graphNormal lower block Z j +
          b * ADMM.FiniteMemory.graphNormal upper block Z j :=
    graphNormal_affine a b gamma lower upper coefficient_sum gamma_eq block Z j
  have residualAffine :
      epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2 =
        a * (epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2) +
          b * (epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2) := by
    calc
      epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2 =
          (a + b) * (epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2) := by
            rw [coefficient_sum]
            ring
      _ = a * (epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2) +
          b * (epsilon * ‖ADMM.FiniteMemory.residual Z 0‖ ^ 2) := by ring
  have lagAffine :
      (∑ block : Block, ∑ d : Fin ℓ,
        ((lagMinus block d : ℝ) *
            inner ℝ (ADMM.FiniteMemory.graphNormal gamma block Z 0)
              (ADMM.FiniteMemory.graphPosition block Z 0 -
                ADMM.FiniteMemory.graphPosition block Z d.succ) +
          (lagPlus block d : ℝ) *
            inner ℝ (ADMM.FiniteMemory.graphNormal gamma block Z d.succ)
              (ADMM.FiniteMemory.graphPosition block Z d.succ -
                ADMM.FiniteMemory.graphPosition block Z 0))) =
        a * (∑ block : Block, ∑ d : Fin ℓ,
          ((lagMinus block d : ℝ) *
              inner ℝ (ADMM.FiniteMemory.graphNormal lower block Z 0)
                (ADMM.FiniteMemory.graphPosition block Z 0 -
                  ADMM.FiniteMemory.graphPosition block Z d.succ) +
            (lagPlus block d : ℝ) *
              inner ℝ (ADMM.FiniteMemory.graphNormal lower block Z d.succ)
                (ADMM.FiniteMemory.graphPosition block Z d.succ -
                  ADMM.FiniteMemory.graphPosition block Z 0))) +
        b * (∑ block : Block, ∑ d : Fin ℓ,
          ((lagMinus block d : ℝ) *
              inner ℝ (ADMM.FiniteMemory.graphNormal upper block Z 0)
                (ADMM.FiniteMemory.graphPosition block Z 0 -
                  ADMM.FiniteMemory.graphPosition block Z d.succ) +
            (lagPlus block d : ℝ) *
              inner ℝ (ADMM.FiniteMemory.graphNormal upper block Z d.succ)
                (ADMM.FiniteMemory.graphPosition block Z d.succ -
                  ADMM.FiniteMemory.graphPosition block Z 0))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro block hblock
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [normalAffine block 0, normalAffine block d.succ]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [ADMM.FiniteMemory.supply_apply, ADMM.FiniteMemory.supply_apply,
    ADMM.FiniteMemory.supply_apply]
  rw [normalAffine .F 0, normalAffine .J 0, lagAffine]
  simp only [RCLike.inner_apply, conj_trivial]
  linear_combination residualAffine

/-- Polarization commutes with affine combinations of scalar quadratic expressions. -/
private lemma realMatrixOfQuadratic_affine {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a b : ℝ) (Q R : (ι → ℝ) → ℝ) :
    ADMM.FiniteMemory.matrixOfQuadratic (fun Z ↦ a * Q Z + b * R Z) =
      a • ADMM.FiniteMemory.matrixOfQuadratic Q +
        b • ADMM.FiniteMemory.matrixOfQuadratic R := by
  -- Expand one polarization entry; linearity is ordinary scalar ring arithmetic.
  ext i j
  rw [ADMM.FiniteMemory.matrixOfQuadratic_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    ADMM.FiniteMemory.matrixOfQuadratic_apply,
    ADMM.FiniteMemory.matrixOfQuadratic_apply]
  ring

/-- The scalar descent expression is the affine combination of its endpoint expressions. -/
private lemma descentExpression_affine {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
    ADMM.FiniteMemory.descentExpression gamma c.omega c.epsilon
        (lagMinusNNReal valid) (lagPlusNNReal valid) (intervalStorage c gamma) Z =
      (1 - theta) * ADMM.FiniteMemory.descentExpression c.gammaLower c.omega c.epsilon
          (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c .lower) Z +
        theta * ADMM.FiniteMemory.descentExpression c.gammaUpper c.omega c.epsilon
          (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c .upper) Z := by
  -- Apply affine storage to the previous/current histories and affine supply to the same history.
  dsimp
  let theta : ℝ := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
  have coefficient_sum : (1 - theta) + theta = 1 := by ring
  have gamma_eq : gamma = (1 - theta) * c.gammaLower + theta * c.gammaUpper := by
    exact gamma_eq_affine_endpoints valid gamma
  rw [ADMM.FiniteMemory.descentExpression_apply,
    ADMM.FiniteMemory.descentExpression_apply,
    ADMM.FiniteMemory.descentExpression_apply]
  rw [intervalQuadraticStorage_affine c gamma,
    intervalQuadraticStorage_affine c gamma]
  rw [supply_affine (1 - theta) theta gamma c.gammaLower c.gammaUpper
    c.omega c.epsilon (lagMinusNNReal valid) (lagPlusNNReal valid)
    coefficient_sum gamma_eq Z]
  ring

/-- The canonical descent matrix is the affine interpolation of its endpoint matrices. -/
theorem intervalDescentMatrix_eq_affine {ℓ : ℕ} {c : RationalCase ℓ}
    (valid : Valid c) (gamma : ℝ) :
    let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
    ADMM.FiniteMemory.descentMatrix gamma c.omega c.epsilon
        (lagMinusNNReal valid) (lagPlusNNReal valid) (intervalStorage c gamma) =
      (1 - theta) • ADMM.FiniteMemory.descentMatrix c.gammaLower c.omega c.epsilon
          (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c .lower) +
        theta • ADMM.FiniteMemory.descentMatrix c.gammaUpper c.omega c.epsilon
          (lagMinusNNReal valid) (lagPlusNNReal valid) (endpointStorage c .upper) := by
  -- Rewrite the descent expression pointwise as an affine endpoint combination and polarize.
  dsimp
  rw [ADMM.FiniteMemory.descentMatrix]
  have expression_eq :
      ADMM.FiniteMemory.descentExpression gamma c.omega c.epsilon
          (lagMinusNNReal valid) (lagPlusNNReal valid) (intervalStorage c gamma) =
        fun Z ↦
          (1 - (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)) *
              ADMM.FiniteMemory.descentExpression c.gammaLower c.omega c.epsilon
                (lagMinusNNReal valid) (lagPlusNNReal valid)
                (endpointStorage c .lower) Z +
            ((gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)) *
              ADMM.FiniteMemory.descentExpression c.gammaUpper c.omega c.epsilon
                (lagMinusNNReal valid) (lagPlusNNReal valid)
                (endpointStorage c .upper) Z := by
    funext Z
    exact descentExpression_affine valid gamma Z
  rw [expression_eq, realMatrixOfQuadratic_affine]
  rfl

/-- Interpolation normals are affine in the scalar parameter. -/
private lemma interpolationNormal_affine {ℓ : ℕ} (a b gamma lower upper : ℝ)
    (coefficient_sum : a + b = 1) (gamma_eq : gamma = a * lower + b * upper)
    (block : Block) (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    ADMM.FiniteMemory.interpolationNormal gamma block i Z =
      a * ADMM.FiniteMemory.interpolationNormal lower block i Z +
        b * ADMM.FiniteMemory.interpolationNormal upper block i Z := by
  -- The origin is zero; generated points use the same affine normal calculation as graph points.
  cases i with
  | none =>
      simp [ADMM.FiniteMemory.interpolationNormal]
  | some j =>
      cases block with
      | F =>
          simp only [ADMM.FiniteMemory.interpolationNormal]
          rw [gamma_eq]
          calc
            Z (j.succ, 0) - (a * lower + b * upper) * Z (j.succ, 1) -
                ADMM.FiniteMemory.interpolationPosition .F (some j) Z =
              (a + b) * Z (j.succ, 0) -
                  (a * lower + b * upper) * Z (j.succ, 1) -
                (a + b) * ADMM.FiniteMemory.interpolationPosition .F (some j) Z := by
                  rw [coefficient_sum]
                  ring
            _ = a * (Z (j.succ, 0) - lower * Z (j.succ, 1) -
                  ADMM.FiniteMemory.interpolationPosition .F (some j) Z) +
                b * (Z (j.succ, 0) - upper * Z (j.succ, 1) -
                  ADMM.FiniteMemory.interpolationPosition .F (some j) Z) := by ring
      | J =>
          simp only [ADMM.FiniteMemory.interpolationNormal]
          rw [gamma_eq]
          calc
            (a * lower + b * upper) * Z (j.succ, 1) + Z (j.castSucc, 1) -
                Z (j.succ, 1) =
              (a * lower + b * upper) * Z (j.succ, 1) +
                (a + b) * (Z (j.castSucc, 1) - Z (j.succ, 1)) := by
                  rw [coefficient_sum]
                  ring
            _ = a * (lower * Z (j.succ, 1) + Z (j.castSucc, 1) - Z (j.succ, 1)) +
                b * (upper * Z (j.succ, 1) + Z (j.castSucc, 1) - Z (j.succ, 1)) := by
                  ring

/-- Every directed gap matrix is affine in the scalar parameter. -/
private lemma gapMatrix_affine {ℓ : ℕ} (a b gamma lower upper : ℝ)
    (coefficient_sum : a + b = 1) (gamma_eq : gamma = a * lower + b * upper)
    (block : Block) (i j : Option (Fin ℓ)) :
    ADMM.FiniteMemory.gapMatrix gamma block i j =
      a • ADMM.FiniteMemory.gapMatrix lower block i j +
        b • ADMM.FiniteMemory.gapMatrix upper block i j := by
  -- Rewrite the normal in the scalar gap expression, then use polarization linearity.
  rw [ADMM.FiniteMemory.gapMatrix, ADMM.FiniteMemory.gapMatrix,
    ADMM.FiniteMemory.gapMatrix]
  have expression_eq :
      (fun Z ↦ -ADMM.FiniteMemory.interpolationNormal gamma block j Z *
        (ADMM.FiniteMemory.interpolationPosition block i Z -
          ADMM.FiniteMemory.interpolationPosition block j Z)) =
      fun Z ↦
        a * (-ADMM.FiniteMemory.interpolationNormal lower block j Z *
          (ADMM.FiniteMemory.interpolationPosition block i Z -
            ADMM.FiniteMemory.interpolationPosition block j Z)) +
        b * (-ADMM.FiniteMemory.interpolationNormal upper block j Z *
          (ADMM.FiniteMemory.interpolationPosition block i Z -
            ADMM.FiniteMemory.interpolationPosition block j Z)) := by
    funext Z
    rw [interpolationNormal_affine a b gamma lower upper coefficient_sum gamma_eq]
    ring
  rw [expression_eq, realMatrixOfQuadratic_affine]

/-- The weighted sum of all directed gaps is affine in the scalar parameter. -/
private lemma gapSum_affine {ℓ : ℕ} (a b gamma lower upper : ℝ)
    (coefficient_sum : a + b = 1) (gamma_eq : gamma = a * lower + b * upper)
    (mu : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal) :
    (∑ block : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
      (mu block i j : ℝ) • ADMM.FiniteMemory.gapMatrix gamma block i j) =
      a • (∑ block : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        (mu block i j : ℝ) • ADMM.FiniteMemory.gapMatrix lower block i j) +
      b • (∑ block : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        (mu block i j : ℝ) • ADMM.FiniteMemory.gapMatrix upper block i j) := by
  -- Compare entries, expand the affine gap identity, and distribute through the three sums.
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro block hblock
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have gapEntry := congrFun
    (congrFun (gapMatrix_affine a b gamma lower upper coefficient_sum gamma_eq block i j) p) q
  simp only [Matrix.add_apply, Matrix.smul_apply] at gapEntry
  rw [gapEntry]
  ring

/-- The canonical lower matrix is the affine interpolation of its endpoint matrices. -/
theorem intervalLowerMatrix_eq_affine {ℓ : ℕ} {c : RationalCase ℓ}
    (valid : Valid c) (gamma : ℝ) :
    let theta := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
    ADMM.FiniteMemory.lowerMatrix gamma c.zeta (intervalStorage c gamma) (muNNReal valid) =
      (1 - theta) • ADMM.FiniteMemory.lowerMatrix c.gammaLower c.zeta
          (endpointStorage c .lower) (muNNReal valid) +
        theta • ADMM.FiniteMemory.lowerMatrix c.gammaUpper c.zeta
          (endpointStorage c .upper) (muNNReal valid) := by
  -- Rewrite storage and the complete directed-gap sum affinely; the current-pair matrix is common
  -- to both endpoints and uses that the two coefficients sum to one.
  dsimp
  let theta : ℝ := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
  have coefficient_sum : (1 - theta) + theta = 1 := by ring
  have gamma_eq : gamma = (1 - theta) * c.gammaLower + theta * c.gammaUpper :=
    gamma_eq_affine_endpoints valid gamma
  rw [ADMM.FiniteMemory.lowerMatrix, ADMM.FiniteMemory.lowerMatrix,
    ADMM.FiniteMemory.lowerMatrix]
  rw [intervalStorage_eq_affine,
    gapSum_affine (1 - theta) theta gamma c.gammaLower c.gammaUpper
      coefficient_sum gamma_eq (muNNReal valid)]
  ext p q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination
    (-c.zeta * ADMM.FiniteMemory.currentMatrix p q) * coefficient_sum

/-- Nonnegative real scaling preserves positive semidefiniteness. -/
private lemma realPosSemidef_smul_nonneg {ι : Type*} (A : Matrix ι ι ℝ) (a : ℝ)
    (hA : A.PosSemidef) (ha : 0 ≤ a) : (a • A).PosSemidef := by
  -- Real scaling preserves symmetry entrywise.
  have symmA : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr ?_, ?_⟩
  · ext i j
    have entryA := symmA.apply i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply] at entryA ⊢
    rw [entryA]
  · intro x
    -- Pull the scalar through both finitely supported sums in the defining contraction.
    simpa only [Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using
      smul_nonneg ha (hA.2 x)

/-- A nonnegative real linear combination of positive semidefinite matrices is positive
semidefinite. -/
private lemma realPosSemidef_add_nonneg_smul {ι : Type*} (A B : Matrix ι ι ℝ)
    (a b : ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • A + b • B).PosSemidef := by
  -- Scale each endpoint certificate, then use additive closure of real PSD matrices.
  exact (realPosSemidef_smul_nonneg A a hA ha).add
    (realPosSemidef_smul_nonneg B b hB hb)

/-- The endpoint exact tests imply the descent test throughout the closed interval. -/
theorem intervalDescent_posSemidef {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) (lower : (c.gammaLower : ℝ) ≤ gamma)
    (upper : gamma ≤ (c.gammaUpper : ℝ)) :
    (ADMM.FiniteMemory.descentMatrix gamma c.omega c.epsilon
      (lagMinusNNReal valid) (lagPlusNNReal valid) (intervalStorage c gamma)).PosSemidef := by
  -- The interval bounds make both affine endpoint coefficients nonnegative.
  let theta : ℝ := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
  have gap_pos : 0 < (c.gammaUpper : ℝ) - c.gammaLower := by
    exact sub_pos.mpr (by exact_mod_cast valid.gamma_order)
  have theta_nonneg : 0 ≤ theta := by
    exact div_nonneg (sub_nonneg.mpr lower) (le_of_lt gap_pos)
  have theta_le_one : theta ≤ 1 := by
    apply (div_le_one gap_pos).2
    linarith
  have one_sub_theta_nonneg : 0 ≤ 1 - theta := sub_nonneg.mpr theta_le_one
  -- Rewrite the interval matrix as its convex endpoint combination and use PSD closure.
  rw [intervalDescentMatrix_eq_affine valid gamma]
  exact realPosSemidef_add_nonneg_smul _ _ _ _
    (endpointDescent_posSemidef valid .lower)
    (endpointDescent_posSemidef valid .upper) one_sub_theta_nonneg theta_nonneg

/-- The endpoint exact tests imply the lower test throughout the closed interval. -/
theorem intervalLower_posSemidef {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) (lower : (c.gammaLower : ℝ) ≤ gamma)
    (upper : gamma ≤ (c.gammaUpper : ℝ)) :
    (ADMM.FiniteMemory.lowerMatrix gamma c.zeta (intervalStorage c gamma)
      (muNNReal valid)).PosSemidef := by
  -- The same interval calculation supplies nonnegative endpoint weights for the lower test.
  let theta : ℝ := (gamma - c.gammaLower) / (c.gammaUpper - c.gammaLower)
  have gap_pos : 0 < (c.gammaUpper : ℝ) - c.gammaLower := by
    exact sub_pos.mpr (by exact_mod_cast valid.gamma_order)
  have theta_nonneg : 0 ≤ theta := by
    exact div_nonneg (sub_nonneg.mpr lower) (le_of_lt gap_pos)
  have theta_le_one : theta ≤ 1 := by
    apply (div_le_one gap_pos).2
    linarith
  have one_sub_theta_nonneg : 0 ≤ 1 - theta := sub_nonneg.mpr theta_le_one
  -- Rewrite affinely and combine the two endpoint lower-test certificates.
  rw [intervalLowerMatrix_eq_affine valid gamma]
  exact realPosSemidef_add_nonneg_smul _ _ _ _
    (endpointLower_posSemidef valid .lower)
    (endpointLower_posSemidef valid .upper) one_sub_theta_nonneg theta_nonneg

/-- Every parameter in a valid closed certificate interval is positive. -/
theorem intervalGamma_pos {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) (lower : (c.gammaLower : ℝ) ≤ gamma) : 0 < gamma := by
  -- Positivity of the lower endpoint passes to every larger parameter.
  exact lt_of_lt_of_le (by exact_mod_cast valid.gammaLower_pos) lower

/-- Construct a canonical certificate at every parameter in the closed endpoint interval. -/
def toIntervalCertificate {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) (lower : (c.gammaLower : ℝ) ≤ gamma)
    (upper : gamma ≤ (c.gammaUpper : ℝ)) : Certificate ℓ gamma where
  lagMinus := lagMinusNNReal valid
  lagPlus := lagPlusNNReal valid
  omega := c.omega
  epsilon := c.epsilon
  zeta := c.zeta
  P := intervalStorage c gamma
  μ := muNNReal valid
  memory_pos := valid.memory_pos
  gamma_pos := intervalGamma_pos valid gamma lower
  omega_pos := omega_cast_pos valid
  epsilon_pos := epsilon_cast_pos valid
  zeta_pos := zeta_cast_pos valid
  P_symm := intervalStorage_isSymm valid gamma
  μ_diag := muNNReal_diag valid
  value_balance := muNNReal_balance valid
  descent_psd := intervalDescent_posSemidef valid gamma lower upper
  lower_psd := intervalLower_posSemidef valid gamma lower upper

/-- The interval certificate stores exactly the affine storage matrix. -/
theorem toIntervalCertificate_P {ℓ : ℕ} {c : RationalCase ℓ} (valid : Valid c)
    (gamma : ℝ) (lower : (c.gammaLower : ℝ) ≤ gamma)
    (upper : gamma ≤ (c.gammaUpper : ℝ)) :
    (toIntervalCertificate valid gamma lower upper).P = intervalStorage c gamma := by
  -- The interpolated matrix is stored verbatim in the certificate.
  rfl

end

end ADMM.FiniteMemory.Reconstruction
