module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.Certificate

@[expose] public section

open scoped BigOperators

namespace ADMM.FiniteMemory.CertificateInterpolation

universe u

noncomputable section

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
theorem realPosSemidef_add_nonneg_smul {ι : Type*} (A B : Matrix ι ι ℝ)
    (a b : ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • A + b • B).PosSemidef := by
  -- Scale each endpoint certificate, then use additive closure of real PSD matrices.
  exact (realPosSemidef_smul_nonneg A a hA ha).add
    (realPosSemidef_smul_nonneg B b hB hb)

/-- Both storage and supply interpolate affinely with arbitrary real data. -/
theorem descentMatrix_affine {ℓ : ℕ} (a b gamma lower upper omega epsilon : ℝ)
    (lagMinus lagPlus : Block → Fin ℓ → NNReal)
    (P Q : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (hab : a + b = 1) (hgamma : gamma = a * lower + b * upper) :
    descentMatrix gamma omega epsilon lagMinus lagPlus (a • P + b • Q) =
      a • descentMatrix lower omega epsilon lagMinus lagPlus P +
        b • descentMatrix upper omega epsilon lagMinus lagPlus Q := by
  have hexpr : descentExpression gamma omega epsilon lagMinus lagPlus (a • P + b • Q) =
      fun Z ↦ a * descentExpression lower omega epsilon lagMinus lagPlus P Z +
        b * descentExpression upper omega epsilon lagMinus lagPlus Q Z := by
    funext Z
    simp only [descentExpression_apply]
    rw [quadraticStorage_affine, quadraticStorage_affine,
      supply_affine a b gamma lower upper omega epsilon lagMinus lagPlus hab hgamma]
    ring
  unfold descentMatrix
  rw [hexpr, realMatrixOfQuadratic_affine]

/-- The lower test interpolates with no rationality or strict definiteness assumption. -/
theorem lowerMatrix_affine {ℓ : ℕ} (a b gamma lower upper zeta : ℝ)
    (P Q : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℝ)
    (mu : Block → Option (Fin ℓ) → Option (Fin ℓ) → NNReal)
    (hab : a + b = 1) (hgamma : gamma = a * lower + b * upper) :
    lowerMatrix gamma zeta (a • P + b • Q) mu =
      a • lowerMatrix lower zeta P mu + b • lowerMatrix upper zeta Q mu := by
  unfold lowerMatrix
  rw [gapSum_affine a b gamma lower upper hab hgamma mu]
  ext p q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (zeta * currentMatrix p q) * hab

end
end ADMM.FiniteMemory.CertificateInterpolation

namespace ADMM.FiniteMemory.Certificate

open CertificateInterpolation

/-- Common weights at two arbitrary real endpoints give a certificate at every
parameter of the closed interval. Only the storage matrix is interpolated. -/
noncomputable def interpolate {ℓ : ℕ} {gammaMinus gammaPlus gamma : ℝ}
    (cMinus : Certificate ℓ gammaMinus) (cPlus : Certificate ℓ gammaPlus)
    (hEndpoints : gammaMinus < gammaPlus) (hLower : gammaMinus ≤ gamma)
    (hUpper : gamma ≤ gammaPlus)
    (hLagMinus : cMinus.lagMinus = cPlus.lagMinus)
    (hLagPlus : cMinus.lagPlus = cPlus.lagPlus)
    (hOmega : cMinus.omega = cPlus.omega)
    (hEpsilon : cMinus.epsilon = cPlus.epsilon)
    (hZeta : cMinus.zeta = cPlus.zeta) (hMu : cMinus.μ = cPlus.μ) :
    Certificate ℓ gamma := by
  let theta : ℝ := (gamma - gammaMinus) / (gammaPlus - gammaMinus)
  have hgap : 0 < gammaPlus - gammaMinus := sub_pos.mpr hEndpoints
  have htheta : 0 ≤ theta := div_nonneg (sub_nonneg.mpr hLower) hgap.le
  have hthetaOne : theta ≤ 1 := (div_le_one hgap).2 (by linarith)
  have hone : 0 ≤ 1 - theta := sub_nonneg.mpr hthetaOne
  have hsum : (1 - theta) + theta = 1 := by ring
  have hgamma : gamma = (1 - theta) * gammaMinus + theta * gammaPlus := by
    dsimp only [theta]
    field_simp [hgap.ne']
    ring
  refine {
    lagMinus := cMinus.lagMinus
    lagPlus := cMinus.lagPlus
    omega := cMinus.omega
    epsilon := cMinus.epsilon
    zeta := cMinus.zeta
    P := (1 - theta) • cMinus.P + theta • cPlus.P
    μ := cMinus.μ
    memory_pos := cMinus.memory_pos
    gamma_pos := cMinus.gamma_pos.trans_le hLower
    omega_pos := cMinus.omega_pos
    epsilon_pos := cMinus.epsilon_pos
    zeta_pos := cMinus.zeta_pos
    P_symm := ?_
    μ_diag := cMinus.μ_diag
    value_balance := cMinus.value_balance
    descent_psd := ?_
    lower_psd := ?_ }
  · ext i j
    have hm := cMinus.P_symm.apply i j
    have hp := cPlus.P_symm.apply i j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply] at hm hp ⊢
    rw [hm, hp]
  · rw [descentMatrix_affine _ _ _ _ _ _ _ _ _ _ _ hsum hgamma]
    apply realPosSemidef_add_nonneg_smul _ _ _ _ cMinus.descent_psd _ hone htheta
    simpa only [hLagMinus, hLagPlus, hOmega, hEpsilon] using cPlus.descent_psd
  · rw [lowerMatrix_affine _ _ _ _ _ _ _ _ _ hsum hgamma]
    apply realPosSemidef_add_nonneg_smul _ _ _ _ cMinus.lower_psd _ hone htheta
    simpa only [hZeta, hMu] using cPlus.lower_psd

end ADMM.FiniteMemory.Certificate
