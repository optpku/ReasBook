module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

open scoped BigOperators NNReal

namespace ADMM.FiniteMemory

universe u

noncomputable section

/-- The two convex-function blocks occurring in a finite-memory ADMM certificate. -/
inductive Block
  | F
  | J
  deriving DecidableEq, Fintype

/-- The residual `r_j = w_j - w_{j+1}` of a newest-first state history. -/
def residual {ℓ : ℕ} {E : Type u} [AddGroup E]
    (Z : (Fin (ℓ + 2) × Fin 2) → E) (j : Fin (ℓ + 1)) : E :=
  Z (j.castSucc, 1) - Z (j.succ, 1)

/-- Evaluation formula for a residual in newest-first coordinates. -/
theorem residual_apply {ℓ : ℕ} {E : Type u} [AddGroup E]
    (Z : (Fin (ℓ + 2) × Fin 2) → E) (j : Fin (ℓ + 1)) :
    residual Z j = Z (j.castSucc, 1) - Z (j.succ, 1) := by
  -- Unfolding exposes exactly the two adjacent newest-first coordinates.
  rfl

/-- The graph position `q_j` for `F`, and `η_j` for `J`. -/
def graphPosition {ℓ : ℕ} {E : Type u} [AddGroup E]
    (b : Block) (Z : (Fin (ℓ + 2) × Fin 2) → E) (j : Fin (ℓ + 1)) : E :=
  match b with
  | .F => Z (j.castSucc, 0) + residual Z j
  | .J => Z (j.castSucc, 0)

/-- Evaluation formula for the blockwise graph position. -/
theorem graphPosition_apply {ℓ : ℕ} {E : Type u} [AddGroup E]
    (b : Block) (Z : (Fin (ℓ + 2) × Fin 2) → E) (j : Fin (ℓ + 1)) :
    graphPosition b Z j = match b with
      | .F => Z (j.castSucc, 0) + residual Z j
      | .J => Z (j.castSucc, 0) := by
  -- The block split is the defining split of the graph position.
  rfl

/-- The graph normal `a_j` for `F`, and `c_j` for `J`. -/
def graphNormal {ℓ : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (b : Block) (Z : (Fin (ℓ + 2) × Fin 2) → E)
    (j : Fin (ℓ + 1)) : E :=
  match b with
  | .F => Z (j.succ, 0) - γ • Z (j.succ, 1) - graphPosition .F Z j
  | .J => γ • Z (j.succ, 1) + residual Z j

/-- Evaluation formula for the blockwise graph normal. -/
theorem graphNormal_apply {ℓ : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (γ : ℝ) (b : Block) (Z : (Fin (ℓ + 2) × Fin 2) → E)
    (j : Fin (ℓ + 1)) :
    graphNormal γ b Z j = match b with
      | .F => Z (j.succ, 0) - γ • Z (j.succ, 1) - graphPosition .F Z j
      | .J => γ • Z (j.succ, 1) + residual Z j := by
  -- The block split is the defining split of the graph normal.
  rfl

/-- The signed coefficient
`h_{b,j} = ∑ d, (λ_{b,-d} - λ_{b,d})` contributed by all lags after `j`. -/
def lagCoefficient {ℓ : ℕ} (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (b : Block) (j : Fin ℓ) : ℝ :=
  ∑ d : Fin ℓ, if j ≤ d then (lagMinus b d : ℝ) - lagPlus b d else 0

/-- Evaluation formula for `lagCoefficient`, where `d : Fin ℓ` represents the
one-based lag `d + 1`. -/
theorem lagCoefficient_apply {ℓ : ℕ} (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (b : Block) (j : Fin ℓ) :
    lagCoefficient lagMinus lagPlus b j =
      ∑ d : Fin ℓ, if j ≤ d then (lagMinus b d : ℝ) - lagPlus b d else 0 := by
  -- The displayed tail sum is the definition of the signed lag coefficient.
  rfl

/-- The ADMM finite-memory supply on a newest-first history of `ℓ + 2` state pairs. -/
def supply {ℓ : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ ω ε : ℝ) (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (Z : (Fin (ℓ + 2) × Fin 2) → E) : ℝ :=
  ω * (inner ℝ (graphNormal γ .F Z 0) (graphPosition .F Z 0) +
    inner ℝ (graphNormal γ .J Z 0) (graphPosition .J Z 0)) +
  ε * ‖residual Z 0‖ ^ 2 +
  ∑ b : Block, ∑ d : Fin ℓ,
    ((lagMinus b d : ℝ) *
        inner ℝ (graphNormal γ b Z 0) (graphPosition b Z 0 - graphPosition b Z d.succ) +
      (lagPlus b d : ℝ) *
        inner ℝ (graphNormal γ b Z d.succ) (graphPosition b Z d.succ - graphPosition b Z 0))

/-- The complete expansion of the finite-memory supply. -/
theorem supply_apply {ℓ : ℕ} {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (Z : (Fin (ℓ + 2) × Fin 2) → E) :
    supply γ ω ε lagMinus lagPlus Z =
      ω * (inner ℝ (graphNormal γ .F Z 0) (graphPosition .F Z 0) +
        inner ℝ (graphNormal γ .J Z 0) (graphPosition .J Z 0)) +
      ε * ‖residual Z 0‖ ^ 2 +
      ∑ b : Block, ∑ d : Fin ℓ,
        ((lagMinus b d : ℝ) *
            inner ℝ (graphNormal γ b Z 0)
              (graphPosition b Z 0 - graphPosition b Z d.succ) +
          (lagPlus b d : ℝ) *
            inner ℝ (graphNormal γ b Z d.succ)
              (graphPosition b Z d.succ - graphPosition b Z 0)) := by
  -- Unfolding records the current merit, residual, and all lagged pairings.
  rfl

/-- Evaluation of `P ⊗ I` on a finite history in a real inner-product space. -/
def quadraticStorage {ℓ : ℕ} {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → E) : ℝ :=
  ∑ i, ∑ j, P i j * inner ℝ (Z i) (Z j)

/-- The quadratic-storage formula is the matrix quadratic form with inner-product entries. -/
theorem quadraticStorage_apply {ℓ : ℕ} {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → E) :
    quadraticStorage P Z = ∑ i, ∑ j, P i j * inner ℝ (Z i) (Z j) := by
  -- The storage quadratic is defined by this double contraction.
  rfl

/-- The candidate storage `U = V + H`, with function values ordered by block and newest first. -/
def storage {ℓ : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → E) (Φ : Block → Fin ℓ → ℝ) : ℝ :=
  quadraticStorage P Z +
    ∑ b : Block, ∑ j : Fin ℓ, lagCoefficient lagMinus lagPlus b j * Φ b j

/-- The storage decomposes as its quadratic and signed function-value parts. -/
theorem storage_def {ℓ : ℕ} {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → E) (Φ : Block → Fin ℓ → ℝ) :
    storage lagMinus lagPlus P Z Φ = quadraticStorage P Z +
      ∑ b : Block, ∑ j : Fin ℓ,
        lagCoefficient lagMinus lagPlus b j * Φ b j := by
  -- The two displayed summands are precisely the fields of the storage definition.
  rfl

/-- The symmetric matrix obtained by polarizing a concrete real quadratic expression. -/
def matrixOfQuadratic {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ℝ) → ℝ) : Matrix ι ι ℝ := fun i j ↦
  (Q (fun k ↦ (if k = i then 1 else 0) + (if k = j then 1 else 0)) -
    Q (fun k ↦ if k = i then 1 else 0) - Q (fun k ↦ if k = j then 1 else 0)) / 2

/-- Entry formula for the polarization matrix of a quadratic expression. -/
theorem matrixOfQuadratic_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ℝ) → ℝ) (i j : ι) :
    matrixOfQuadratic Q i j =
      (Q (fun k ↦ (if k = i then 1 else 0) + (if k = j then 1 else 0)) -
        Q (fun k ↦ if k = i then 1 else 0) -
          Q (fun k ↦ if k = j then 1 else 0)) / 2 := by
  -- This is the polarization formula used to define each matrix entry.
  rfl

/-- Polarization of a quadratic form agrees with its canonical matrix. -/
private lemma matrixOfQuadratic_eq_toMatrix' {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm ℝ (ι → ℝ)) :
    matrixOfQuadratic (fun Z ↦ Q Z) = Q.toMatrix' := by
  -- Compare both matrices on pairs of standard basis vectors.
  ext i j
  rw [matrixOfQuadratic_apply, QuadraticForm.toMatrix',
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
  have quadratic_basis_i := congrArg (Q : (ι → ℝ) → ℝ) basis_i
  have quadratic_basis_j := congrArg (Q : (ι → ℝ) → ℝ) basis_j
  have quadratic_basis_add := congrArg (Q : (ι → ℝ) → ℝ) basis_add
  rw [quadratic_basis_add, quadratic_basis_i, quadratic_basis_j]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul]
  norm_num
  ring_nf

/-- The polarization matrix of a quadratic form evaluates back to that form. -/
private lemma matrixOfQuadratic_quadraticForm_apply {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm ℝ (ι → ℝ)) (Z : ι → ℝ) :
    (∑ i, ∑ j, matrixOfQuadratic (fun X ↦ Q X) i j * Z i * Z j) = Q Z := by
  -- Pass through the associated bilinear form and evaluate it on the diagonal.
  rw [matrixOfQuadratic_eq_toMatrix', ← QuadraticMap.associated_eq_self_apply ℝ Q Z,
    ← Matrix.toBilin'_toMatrix' Q.associated, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have matrix_entry : Q.toMatrix' i j =
      LinearMap.BilinForm.toMatrix' Q.associated i j := rfl
  rw [matrix_entry]
  ring

/-- A graph position, extended by zero to the interpolation origin. -/
def interpolationPosition {ℓ : ℕ} (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) : ℝ :=
  match i with
  | none => 0
  | some j => match b with
    | .F => Z (j.castSucc, 0) + Z (j.castSucc, 1) - Z (j.succ, 1)
    | .J => Z (j.castSucc, 0)

/-- Evaluation formula for a scalar interpolation position, with the origin mapped to zero. -/
theorem interpolationPosition_apply {ℓ : ℕ} (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    interpolationPosition b i Z = match i with
      | none => 0
      | some j => match b with
        | .F => Z (j.castSucc, 0) + Z (j.castSucc, 1) - Z (j.succ, 1)
        | .J => Z (j.castSucc, 0) := by
  -- Splitting the optional interpolation index gives the origin and generated cases.
  rfl

/-- A graph normal, extended by zero to the interpolation origin. -/
def interpolationNormal {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) : ℝ :=
  match i with
  | none => 0
  | some j => match b with
    | .F => Z (j.succ, 0) - γ * Z (j.succ, 1) - interpolationPosition .F i Z
    | .J => γ * Z (j.succ, 1) + Z (j.castSucc, 1) - Z (j.succ, 1)

/-- Evaluation formula for a scalar interpolation normal, with the origin mapped to zero. -/
theorem interpolationNormal_apply {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    interpolationNormal γ b i Z = match i with
      | none => 0
      | some j => match b with
        | .F => Z (j.succ, 0) - γ * Z (j.succ, 1) - interpolationPosition .F i Z
        | .J => γ * Z (j.succ, 1) + Z (j.castSucc, 1) - Z (j.succ, 1) := by
  -- Splitting the optional interpolation index gives the origin and generated cases.
  rfl

/-- Evaluation at one scalar state coordinate is a linear map. -/
private def stateCoordinate {n : ℕ} (i : Fin n × Fin 2) :
    (((Fin n × Fin 2) → ℝ) →ₗ[ℝ] ℝ) :=
  LinearMap.proj i

/-- Scalar interpolation positions form linear maps of the state history. -/
private def interpolationPositionLinear {ℓ : ℕ} (b : Block) (i : Option (Fin ℓ)) :
    (((Fin (ℓ + 1) × Fin 2) → ℝ) →ₗ[ℝ] ℝ) :=
  match i with
  | none => 0
  | some j => match b with
    | .F => stateCoordinate (j.castSucc, 0) + stateCoordinate (j.castSucc, 1) -
        stateCoordinate (j.succ, 1)
    | .J => stateCoordinate (j.castSucc, 0)

/-- Applying the interpolation-position linear map recovers `interpolationPosition`. -/
private lemma interpolationPositionLinear_apply {ℓ : ℕ} (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    interpolationPositionLinear b i Z = interpolationPosition b i Z := by
  -- Both optional-index cases reduce to coordinate projections.
  cases i with
  | none => simp [interpolationPositionLinear, interpolationPosition]
  | some j =>
      cases b <;> simp [interpolationPositionLinear, interpolationPosition, stateCoordinate]

/-- Scalar interpolation normals form linear maps of the state history. -/
private def interpolationNormalLinear {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i : Option (Fin ℓ)) : (((Fin (ℓ + 1) × Fin 2) → ℝ) →ₗ[ℝ] ℝ) :=
  match i with
  | none => 0
  | some j => match b with
    | .F => stateCoordinate (j.succ, 0) - γ • stateCoordinate (j.succ, 1) -
        interpolationPositionLinear .F i
    | .J => γ • stateCoordinate (j.succ, 1) + stateCoordinate (j.castSucc, 1) -
        stateCoordinate (j.succ, 1)

/-- Applying the interpolation-normal linear map recovers `interpolationNormal`. -/
private lemma interpolationNormalLinear_apply {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    interpolationNormalLinear γ b i Z = interpolationNormal γ b i Z := by
  -- Both optional-index cases reduce to scalar coordinate arithmetic.
  cases i with
  | none => simp [interpolationNormalLinear, interpolationNormal]
  | some j =>
      cases b <;> simp [interpolationNormalLinear, interpolationNormal,
        interpolationPositionLinear_apply, stateCoordinate]

/-- The negative product in a directed interpolation gap is a quadratic form. -/
private def directedGapQuadraticForm {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i j : Option (Fin ℓ)) : QuadraticForm ℝ ((Fin (ℓ + 1) × Fin 2) → ℝ) :=
  -QuadraticMap.linMulLin (interpolationNormalLinear γ b j)
    (interpolationPositionLinear b i - interpolationPositionLinear b j)

/-- The directed-gap quadratic form evaluates to the negative normal-position product. -/
private lemma directedGapQuadraticForm_apply {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i j : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    directedGapQuadraticForm γ b i j Z =
      -interpolationNormal γ b j Z *
        (interpolationPosition b i Z - interpolationPosition b j Z) := by
  -- Evaluate the product form and then identify its two linear factors.
  simp only [directedGapQuadraticForm, QuadraticMap.neg_apply,
    QuadraticMap.linMulLin_apply, LinearMap.sub_apply,
    interpolationNormalLinear_apply, interpolationPositionLinear_apply]
  ring

/-- The symmetric matrix representing one directed convexity-gap inner-product term. -/
def gapMatrix {ℓ : ℕ} (γ : ℝ) (b : Block) (i j : Option (Fin ℓ)) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ :=
  matrixOfQuadratic fun Z ↦
    -interpolationNormal γ b j Z *
      (interpolationPosition b i Z - interpolationPosition b j Z)

/-- `gapMatrix` evaluates to the negative inner-product part of a directed convexity gap. -/
theorem gapMatrix_quadratic {ℓ : ℕ} (γ : ℝ) (b : Block)
    (i j : Option (Fin ℓ)) (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    (∑ a, ∑ d, gapMatrix γ b i j a d * Z a * Z d) =
      -interpolationNormal γ b j Z *
        (interpolationPosition b i Z - interpolationPosition b j Z) := by
  -- Replace the concrete gap expression by its quadratic-form interface.
  have gap_function :
      (fun X ↦ -interpolationNormal γ b j X *
        (interpolationPosition b i X - interpolationPosition b j X)) =
      fun X ↦ directedGapQuadraticForm γ b i j X := by
    funext X
    exact (directedGapQuadraticForm_apply γ b i j X).symm
  rw [gapMatrix, gap_function,
    matrixOfQuadratic_quadraticForm_apply,
    directedGapQuadraticForm_apply]

/-- A residual coordinate is a linear functional on scalar histories. -/
private def stateResidualLinear {ℓ : ℕ} (j : Fin (ℓ + 1)) :
    (((Fin (ℓ + 2) × Fin 2) → ℝ) →ₗ[ℝ] ℝ) :=
  stateCoordinate (j.castSucc, 1) - stateCoordinate (j.succ, 1)

/-- Applying the residual linear functional recovers `residual`. -/
private lemma stateResidualLinear_apply {ℓ : ℕ} (j : Fin (ℓ + 1))
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) : stateResidualLinear j Z = residual Z j := by
  -- The two linear projections are the adjacent residual coordinates.
  simp [stateResidualLinear, stateCoordinate, residual]

/-- A blockwise graph position is a linear functional on scalar histories. -/
private def stateGraphPositionLinear {ℓ : ℕ} (b : Block) (j : Fin (ℓ + 1)) :
    (((Fin (ℓ + 2) × Fin 2) → ℝ) →ₗ[ℝ] ℝ) :=
  match b with
  | .F => stateCoordinate (j.castSucc, 0) + stateResidualLinear j
  | .J => stateCoordinate (j.castSucc, 0)

/-- Applying the graph-position linear functional recovers `graphPosition`. -/
private lemma stateGraphPositionLinear_apply {ℓ : ℕ} (b : Block) (j : Fin (ℓ + 1))
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    stateGraphPositionLinear b j Z = graphPosition b Z j := by
  -- Each block reduces to its coordinate formula and the residual interface.
  cases b <;> simp [stateGraphPositionLinear, stateCoordinate, graphPosition,
    stateResidualLinear_apply]

/-- A blockwise graph normal is a linear functional on scalar histories. -/
private def stateGraphNormalLinear {ℓ : ℕ} (γ : ℝ) (b : Block) (j : Fin (ℓ + 1)) :
    (((Fin (ℓ + 2) × Fin 2) → ℝ) →ₗ[ℝ] ℝ) :=
  match b with
  | .F => stateCoordinate (j.succ, 0) - γ • stateCoordinate (j.succ, 1) -
      stateGraphPositionLinear .F j
  | .J => γ • stateCoordinate (j.succ, 1) + stateResidualLinear j

/-- Applying the graph-normal linear functional recovers `graphNormal`. -/
private lemma stateGraphNormalLinear_apply {ℓ : ℕ} (γ : ℝ) (b : Block)
    (j : Fin (ℓ + 1)) (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    stateGraphNormalLinear γ b j Z = graphNormal γ b Z j := by
  -- Each block reduces to its coordinate formula and the position/residual interfaces.
  cases b <;> simp [stateGraphNormalLinear, stateCoordinate, graphNormal,
    stateGraphPositionLinear_apply, stateResidualLinear_apply]

/-- The scalar finite-memory supply is a quadratic form on histories. -/
private def supplyQuadraticForm {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal) :
    QuadraticForm ℝ ((Fin (ℓ + 2) × Fin 2) → ℝ) :=
  ω • (QuadraticMap.linMulLin (stateGraphNormalLinear γ .F 0)
      (stateGraphPositionLinear .F 0) +
    QuadraticMap.linMulLin (stateGraphNormalLinear γ .J 0)
      (stateGraphPositionLinear .J 0)) +
  ε • QuadraticMap.linMulLin (stateResidualLinear 0) (stateResidualLinear 0) +
  ∑ b : Block, ∑ d : Fin ℓ,
    ((lagMinus b d : ℝ) • QuadraticMap.linMulLin (stateGraphNormalLinear γ b 0)
        (stateGraphPositionLinear b 0 - stateGraphPositionLinear b d.succ) +
      (lagPlus b d : ℝ) • QuadraticMap.linMulLin (stateGraphNormalLinear γ b d.succ)
        (stateGraphPositionLinear b d.succ - stateGraphPositionLinear b 0))

/-- Evaluating the supply quadratic form gives the scalar supply expression. -/
private lemma supplyQuadraticForm_apply {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    supplyQuadraticForm γ ω ε lagMinus lagPlus Z =
      supply γ ω ε lagMinus lagPlus Z := by
  -- Evaluate every quadratic product through its named linear factors.
  simp only [supplyQuadraticForm, QuadraticMap.add_apply, QuadraticMap.smul_apply,
    QuadraticMap.linMulLin_apply, QuadraticMap.sum_apply, LinearMap.sub_apply,
    stateGraphNormalLinear_apply, stateGraphPositionLinear_apply,
    stateResidualLinear_apply]
  rw [supply_apply]
  simp [Real.norm_eq_abs, sq_abs]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The matrix quadratic form evaluates to `quadraticStorage` on scalar histories. -/
private lemma matrixQuadraticForm_apply {ℓ : ℕ}
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    Matrix.toQuadraticForm' P Z = quadraticStorage P Z := by
  -- Expand the matrix bilinear form and commute scalar factors entrywise.
  rw [quadraticStorage_apply]
  have toBilin : Matrix.toQuadraticForm' P Z = Matrix.toBilin' P Z Z := rfl
  rw [toBilin, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- The scalar expression `V_previous - V_current - S` on an `ℓ + 2`-pair history. -/
def descentExpression {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) : ℝ :=
  quadraticStorage P (fun i ↦ Z (i.1.succ, i.2)) -
    quadraticStorage P (fun i ↦ Z (i.1.castSucc, i.2)) -
      supply γ ω ε lagMinus lagPlus Z

/-- Evaluation formula for `V_previous - V_current - S`. -/
theorem descentExpression_apply {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    descentExpression γ ω ε lagMinus lagPlus P Z =
      quadraticStorage P (fun i ↦ Z (i.1.succ, i.2)) -
        quadraticStorage P (fun i ↦ Z (i.1.castSucc, i.2)) -
          supply γ ω ε lagMinus lagPlus Z := by
  -- The expression is defined as previous storage minus current storage and supply.
  rfl

/-- Dropping the newest state pair is a linear map of histories. -/
private def previousHistoryLinear {ℓ : ℕ} :
    (((Fin (ℓ + 2) × Fin 2) → ℝ) →ₗ[ℝ] ((Fin (ℓ + 1) × Fin 2) → ℝ)) :=
  LinearMap.pi fun i ↦ stateCoordinate (i.1.succ, i.2)

/-- Keeping the newest state pairs is a linear map of histories. -/
private def currentHistoryLinear {ℓ : ℕ} :
    (((Fin (ℓ + 2) × Fin 2) → ℝ) →ₗ[ℝ] ((Fin (ℓ + 1) × Fin 2) → ℝ)) :=
  LinearMap.pi fun i ↦ stateCoordinate (i.1.castSucc, i.2)

/-- The previous-history map discards the newest state pair pointwise. -/
private lemma previousHistoryLinear_apply {ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    previousHistoryLinear Z = fun i ↦ Z (i.1.succ, i.2) := by
  -- Extensionality reduces the history map to a coordinate projection.
  funext i
  rfl

/-- The current-history map retains the newest state pairs pointwise. -/
private lemma currentHistoryLinear_apply {ℓ : ℕ}
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    currentHistoryLinear Z = fun i ↦ Z (i.1.castSucc, i.2) := by
  -- Extensionality reduces the history map to a coordinate projection.
  funext i
  rfl

/-- The scalar descent expression is represented by a quadratic form. -/
private def descentQuadraticForm {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ) :
    QuadraticForm ℝ ((Fin (ℓ + 2) × Fin 2) → ℝ) :=
  (Matrix.toQuadraticForm' P).comp previousHistoryLinear -
    (Matrix.toQuadraticForm' P).comp currentHistoryLinear -
      supplyQuadraticForm γ ω ε lagMinus lagPlus

/-- Evaluating the descent quadratic form gives `descentExpression`. -/
private lemma descentQuadraticForm_apply {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    descentQuadraticForm γ ω ε lagMinus lagPlus P Z =
      descentExpression γ ω ε lagMinus lagPlus P Z := by
  -- Evaluate the two history shifts and the supply through their interfaces.
  simp only [descentQuadraticForm, QuadraticMap.sub_apply, QuadraticMap.comp_apply,
    previousHistoryLinear_apply, currentHistoryLinear_apply,
    matrixQuadraticForm_apply, supplyQuadraticForm_apply]
  rw [descentExpression_apply]

/-- The concrete order-`2(ℓ+2)` matrix for the universal scalar descent test. -/
def descentMatrix {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ) :
    Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℝ :=
  matrixOfQuadratic (descentExpression γ ω ε lagMinus lagPlus P)

/-- Evaluation of the descent-test matrix on a scalar state history. -/
theorem descentMatrix_quadratic {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 2) × Fin 2) → ℝ) :
    (∑ i, ∑ j, descentMatrix γ ω ε lagMinus lagPlus P i j * Z i * Z j) =
      descentExpression γ ω ε lagMinus lagPlus P Z := by
  -- Replace the descent expression by its quadratic-form interface before polarizing.
  have descent_function : descentExpression γ ω ε lagMinus lagPlus P =
      fun X ↦ descentQuadraticForm γ ω ε lagMinus lagPlus P X := by
    funext X
    symm
    exact descentQuadraticForm_apply γ ω ε lagMinus lagPlus P X
  rw [descentMatrix, descent_function, matrixOfQuadratic_quadraticForm_apply]

/-- The diagonal matrix selecting the current `η` and `w` coordinates. -/
def currentMatrix {ℓ : ℕ} :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ := fun i j ↦
  if i = j ∧ i.1 = 0 then 1 else 0

/-- Entry formula for the matrix selecting the current state pair. -/
theorem currentMatrix_apply {ℓ : ℕ} (i j : Fin (ℓ + 1) × Fin 2) :
    currentMatrix i j = if i = j ∧ i.1 = 0 then 1 else 0 := by
  -- The selector entry is exactly its defining conditional.
  rfl

/-- The current-coordinate selector evaluates to the squared norm of the newest state pair. -/
private lemma currentMatrix_quadratic {ℓ : ℕ}
    (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    (∑ a, ∑ d, currentMatrix a d * Z a * Z d) =
      Z (0, 0) ^ 2 + Z (0, 1) ^ 2 := by
  -- The diagonal condition kills every coordinate except `(0, 0)` and `(0, 1)`.
  simp only [currentMatrix_apply]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, pow_two]
  have zero_ne_succ (i : Fin ℓ) : (0 : Fin (ℓ + 1)) ≠ i.succ :=
    Ne.symm i.succ_ne_zero
  simp [zero_ne_succ]

/-- A matrix bilinear form on the diagonal is its usual quadratic contraction. -/
private lemma matrixToBilin_self {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (Z : ι → ℝ) :
    Matrix.toBilin' M Z Z = ∑ i, ∑ j, M i j * Z i * Z j := by
  -- Expand the bilinear form and commute the three scalar factors entrywise.
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- On scalar histories, matrix contraction agrees with `quadraticStorage`. -/
private lemma matrixQuadratic_eq_storage {ℓ : ℕ}
    (M : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    (∑ i, ∑ j, M i j * Z i * Z j) = quadraticStorage M Z := by
  -- Scalar inner products are ordinary products, up to commutation of factors.
  rw [quadraticStorage_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- The lower-bound test matrix, including all directed origin/generated interpolation gaps. -/
def lowerMatrix {ℓ : ℕ} (γ ζ : ℝ)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal) :
    Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ :=
  P - (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
    (μ b i j : ℝ) • gapMatrix γ b i j) - ζ • currentMatrix

/-- Evaluation of the lower-bound matrix on a scalar storage history. -/
theorem lowerMatrix_quadratic {ℓ : ℕ} (γ ζ : ℝ)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal)
    (Z : (Fin (ℓ + 1) × Fin 2) → ℝ) :
    (∑ a, ∑ d, lowerMatrix γ ζ P μ a d * Z a * Z d) =
      quadraticStorage P Z -
        (∑ b : Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
          (μ b i j : ℝ) *
            (-interpolationNormal γ b j Z *
              (interpolationPosition b i Z - interpolationPosition b j Z))) -
        ζ * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2) := by
  -- Evaluate the matrix expression through the bilinear map, which preserves its linear structure.
  rw [← matrixToBilin_self]
  rw [lowerMatrix]
  simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [matrixToBilin_self, matrixQuadratic_eq_storage]
  simp_rw [matrixToBilin_self, gapMatrix_quadratic]
  rw [currentMatrix_quadratic]

/-- The descent matrix is the canonical matrix of the descent quadratic form. -/
private lemma descentMatrix_eq_toMatrix' {ℓ : ℕ} (γ ω ε : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ) :
    descentMatrix γ ω ε lagMinus lagPlus P =
      (descentQuadraticForm γ ω ε lagMinus lagPlus P).toMatrix' := by
  -- Identify the defining scalar function with the quadratic-form interface.
  have descent_function : descentExpression γ ω ε lagMinus lagPlus P =
      fun X ↦ descentQuadraticForm γ ω ε lagMinus lagPlus P X := by
    funext X
    symm
    exact descentQuadraticForm_apply γ ω ε lagMinus lagPlus P X
  rw [descentMatrix, descent_function, matrixOfQuadratic_eq_toMatrix']

/-- A finitely supported quadratic contraction is the corresponding finite double sum. -/
private lemma finsuppMatrixQuadratic_eq {ι : Type u} [Fintype ι]
    (M : Matrix ι ι ℝ) (x : ι →₀ ℝ) :
    x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj) =
      ∑ i, ∑ j, M i j * x i * x j := by
  -- On a finite index type both finitely supported sums may be taken over `univ`.
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
      ring
  · intro i
    simp

/-- An explicit finite-memory ADMM certificate with its two finite PSD tests.
The separate lower test is essential because the stored objective coefficients may be signed. -/
structure Certificate (ℓ : ℕ) (γ : ℝ) where
  lagMinus : Block → Fin ℓ → NNReal
  lagPlus : Block → Fin ℓ → NNReal
  omega : ℝ
  epsilon : ℝ
  zeta : ℝ
  P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ
  μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal
  memory_pos : 0 < ℓ
  gamma_pos : 0 < γ
  omega_pos : 0 < omega
  epsilon_pos : 0 < epsilon
  zeta_pos : 0 < zeta
  P_symm : P.IsSymm
  μ_diag : ∀ b i, μ b i i = 0
  value_balance : ∀ b j,
    (∑ i : Option (Fin ℓ), (μ b (some j) i : ℝ)) -
      (∑ i : Option (Fin ℓ), (μ b i (some j) : ℝ)) =
        lagCoefficient lagMinus lagPlus b j
  descent_psd : (descentMatrix γ omega epsilon lagMinus lagPlus P).PosSemidef
  lower_psd : (lowerMatrix γ zeta P μ).PosSemidef

namespace Certificate

/-- Construct a certificate from its concrete weights, matrices, multipliers, and test proofs. -/
def ofTests {ℓ : ℕ} {γ : ℝ} (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (omega epsilon zeta : ℝ)
    (P : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (μ : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal)
    (memory_pos : 0 < ℓ) (gamma_pos : 0 < γ)
    (omega_pos : 0 < omega) (epsilon_pos : 0 < epsilon) (zeta_pos : 0 < zeta)
    (P_symm : P.IsSymm) (μ_diag : ∀ b i, μ b i i = 0)
    (value_balance : ∀ b j,
      (∑ i : Option (Fin ℓ), (μ b (some j) i : ℝ)) -
        (∑ i : Option (Fin ℓ), (μ b i (some j) : ℝ)) =
          lagCoefficient lagMinus lagPlus b j)
    (descent_psd : (descentMatrix γ omega epsilon lagMinus lagPlus P).PosSemidef)
    (lower_psd : (lowerMatrix γ zeta P μ).PosSemidef) : Certificate ℓ γ :=
  { lagMinus := lagMinus, lagPlus := lagPlus, omega := omega, epsilon := epsilon,
    zeta := zeta, P := P, μ := μ, memory_pos := memory_pos, gamma_pos := gamma_pos,
    omega_pos := omega_pos, epsilon_pos := epsilon_pos, zeta_pos := zeta_pos,
    P_symm := P_symm, μ_diag := μ_diag, value_balance := value_balance,
    descent_psd := descent_psd, lower_psd := lower_psd }

/-- The descent PSD test is equivalent to the universal scalar-history inequality. -/
theorem descent_iff {ℓ : ℕ} {γ : ℝ} (c : Certificate ℓ γ) :
    (descentMatrix γ c.omega c.epsilon c.lagMinus c.lagPlus c.P).PosSemidef ↔
      ∀ Z : (Fin (ℓ + 2) × Fin 2) → ℝ,
        0 ≤ quadraticStorage c.P (fun i ↦ Z (i.1.succ, i.2)) -
          quadraticStorage c.P (fun i ↦ Z (i.1.castSucc, i.2)) -
            supply γ c.omega c.epsilon c.lagMinus c.lagPlus Z := by
  -- Convert the PSD inequality from finitely supported vectors to finite functions.
  constructor
  · intro h Z
    have hZ := h.2 (Finsupp.equivFunOnFinite.symm Z)
    rw [finsuppMatrixQuadratic_eq, descentMatrix_quadratic] at hZ
    rw [Finsupp.coe_equivFunOnFinite_symm] at hZ
    simpa only [descentExpression_apply] using hZ
  · intro h
    constructor
    · -- Symmetry of the canonical quadratic-form matrix gives Hermitianity over `ℝ`.
      rw [descentMatrix_eq_toMatrix', Matrix.isHermitian_iff_isSymm]
      exact QuadraticForm.isSymm_toMatrix' _
    · intro x
      rw [finsuppMatrixQuadratic_eq, descentMatrix_quadratic]
      simpa only [descentExpression_apply] using h (fun i ↦ x i)

/-- The value-balance identity and lower PSD condition constituting the second finite test. -/
theorem lower_spec {ℓ : ℕ} {γ : ℝ} (c : Certificate ℓ γ) :
    (∀ b j,
      (∑ i : Option (Fin ℓ), (c.μ b (some j) i : ℝ)) -
        (∑ i : Option (Fin ℓ), (c.μ b i (some j) : ℝ)) =
          lagCoefficient c.lagMinus c.lagPlus b j) ∧
      (lowerMatrix γ c.zeta c.P c.μ).PosSemidef := by
  -- The two requested finite tests are stored verbatim in the certificate.
  exact ⟨c.value_balance, c.lower_psd⟩

end Certificate

end

end ADMM.FiniteMemory
