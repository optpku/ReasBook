import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_6
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7.Transference
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix IntegerVectorNotation Matrix.Norms.L2Operator

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch` in this environment, so this file follows the local Chapter 9 conventions:
-- convex bodies are represented by `ConvexBody`, their source-facing hypotheses use the bridge
-- predicates `ConvexBody.FullDimensional` and `ConvexBody.ContainsIntegralPoint`, and rational
-- inequality systems use an explicit matrix presentation over `Fin n → ℝ`.

section Theorem97

variable {m n : ℕ}

/-- A subset `K ⊆ ℝ^n` contains an integral point when it meets the canonical integer-vector
owner `ℤ^n`. -/
def contains_integral_point (K : Set (Fin n → ℝ)) : Prop :=
  (K ∩ ℤ^n).Nonempty

/-- `contains_integral_point K` means that `K` contains the real coercion of some integer vector.
-/
theorem contains_integral_point_iff
    {K : Set (Fin n → ℝ)} :
    contains_integral_point K ↔
      ∃ z : Fin n → ℤ, Int.cast ∘ z ∈ K := by
  constructor
  · rintro ⟨x, hxK, hxZ⟩
    rcases mem_integerVectors_iff.mp hxZ with ⟨z, rfl⟩
    exact ⟨z, hxK⟩
  · rintro ⟨z, hzK⟩
    exact ⟨Int.cast ∘ z, hzK, mem_integerVectors_iff.mpr ⟨z, rfl⟩⟩

/-- Helper for Theorem 9.7: set inclusion transports integral-point witnesses upward. -/
theorem contains_integral_point_mono
    {S T : Set (Fin n → ℝ)}
    (hST : S ⊆ T) :
    contains_integral_point S → contains_integral_point T := by
  intro hS
  -- Reuse the same integer witness and move its membership along the inclusion.
  rcases contains_integral_point_iff.mp hS with ⟨z, hzS⟩
  exact contains_integral_point_iff.mpr ⟨z, hST hzS⟩

/-- Helper for Theorem 9.7: lattice-freeness descends along set inclusion. -/
theorem not_contains_integral_point_of_subset
    {S T : Set (Fin n → ℝ)}
    (hST : S ⊆ T)
    (hT : ¬ contains_integral_point T) :
    ¬ contains_integral_point S := by
  intro hS
  -- Any integral point of the smaller set would also lie in the larger set.
  exact hT (contains_integral_point_mono hST hS)

namespace ConvexBody

/-- A convex body is full dimensional when its interior is nonempty. -/
def FullDimensional (K : ConvexBody (Fin n → ℝ)) : Prop :=
  (interior K.carrier).Nonempty

/-- `K.FullDimensional` means that the convex body `K` has nonempty interior. -/
theorem fullDimensional_iff
    {K : ConvexBody (Fin n → ℝ)} :
    K.FullDimensional ↔ (interior K.carrier).Nonempty :=
  Iff.rfl

/-- A convex body contains an integral point when its underlying set does. -/
def ContainsIntegralPoint (K : ConvexBody (Fin n → ℝ)) : Prop :=
  _root_.contains_integral_point (K : Set (Fin n → ℝ))

/-- `K.ContainsIntegralPoint` means that `K` contains the real coercion of some integer vector. -/
theorem containsIntegralPoint_iff
    {K : ConvexBody (Fin n → ℝ)} :
    K.ContainsIntegralPoint ↔
      ∃ z : Fin n → ℤ, Int.cast ∘ z ∈ K := by
  change _root_.contains_integral_point (K : Set (Fin n → ℝ)) ↔
      ∃ z : Fin n → ℤ, Int.cast ∘ z ∈ K
  exact _root_.contains_integral_point_iff

end ConvexBody

/-- The linear functional on `ℝ^n` induced by an integral direction `d ∈ ℤ^n`. -/
def integral_direction_linear_form (d : Fin n → ℤ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ (Int.cast ∘ d) ⬝ᵥ x

/-- The width of a subset `K ⊆ ℝ^n` in the integral direction `d ∈ ℤ^n`. -/
noncomputable def directional_width
    (K : Set (Fin n → ℝ))
    (d : Fin n → ℤ) : ℝ :=
  sSup (integral_direction_linear_form d '' K) -
    sInf (integral_direction_linear_form d '' K)

namespace DirectionalWidthNotation

/- Textbook notation for directional width: `w_{d}(K)` is the width of `K` in the integral
direction `d`. -/
scoped notation:max "w_{" d "}(" K ")" => directional_width K d

end DirectionalWidthNotation

open scoped DirectionalWidthNotation

/-- The lattice width of a convex body is the infimum of its directional widths over all nonzero
integral directions, that is, of the values `w_{d}(K)`. -/
noncomputable def lattice_width
    (K : ConvexBody (Fin n → ℝ)) : ℝ :=
  sInf
    ((fun d : {d : Fin n → ℤ // d ≠ 0} ↦
        w_{d.1}(K)) '' Set.univ)

/-- The explicit flatness bound `n (n + 1) 2^{n (n - 1) / 4}` appearing in the rational-polytope
algorithmic consequence of the flatness theorem. -/
noncomputable def flat_direction_bound (n : ℕ) : ℝ :=
  (n * (n + 1) : ℝ) * Real.rpow 2 (((n * (n - 1) : ℕ) : ℝ) / 4)

/-- A certified integral point of a set `P ⊆ ℝ^n`, represented by an integer vector whose real
embedding lies in `P`. -/
def IntegralPointCertificate (P : Set (Fin n → ℝ)) :=
  {z : Fin n → ℤ // Int.cast ∘ z ∈ P}

namespace IntegralPointCertificate

variable {P : Set (Fin n → ℝ)}

/-- The real embedding of an integral-point certificate lies in the target set. -/
theorem mem (point : IntegralPointCertificate P) :
    Int.cast ∘ point.1 ∈ P :=
  point.2

/-- An integral-point certificate yields the corresponding `contains_integral_point` witness. -/
theorem contains_integral_point (point : IntegralPointCertificate P) :
    _root_.contains_integral_point P :=
  ⟨Int.cast ∘ point.1, point.mem, mem_integerVectors_iff.mpr ⟨point.1, rfl⟩⟩

end IntegralPointCertificate

/-- A certified flat direction of a set `P ⊆ ℝ^n`, represented by a nonzero integer vector whose
directional width `w_{d}(P)` is bounded by `flat_direction_bound n`. -/
def FlatDirectionCertificate (P : Set (Fin n → ℝ)) :=
  {d : Fin n → ℤ // d ≠ 0 ∧ _root_.directional_width P d ≤ _root_.flat_direction_bound n}

namespace FlatDirectionCertificate

variable {P : Set (Fin n → ℝ)}

/-- The underlying integer direction of a flat-direction certificate is nonzero. -/
theorem ne_zero (direction : FlatDirectionCertificate P) :
    direction.1 ≠ 0 :=
  direction.2.1

/-- A flat-direction certificate carries the promised width bound. -/
theorem width_le (direction : FlatDirectionCertificate P) :
    _root_.directional_width P direction.1 ≤ _root_.flat_direction_bound n :=
  direction.2.2

end FlatDirectionCertificate

/-- The concrete solver data for the rational-polytope consequence of the flatness theorem. The
certification predicate `RationalPolytopeFlatnessAlgorithm.Certified` records the polynomial-time
bound and the guaranteed output on full-dimensional compact inputs. -/
structure RationalPolytopeFlatnessAlgorithm (m n : ℕ) where
  run
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      Option
        (Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
          (FlatDirectionCertificate (rational_matrix_polyhedron A b)))
  runTime
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      ℕ

/-- Evaluate a rational-polytope flatness algorithm via its solver map. -/
instance rationalPolytopeFlatnessAlgorithmCoeFun (m n : ℕ) :
    CoeFun (RationalPolytopeFlatnessAlgorithm m n) (fun _ ↦
      (A : Matrix (Fin m) (Fin n) ℚ) →
      (b : Fin m → ℚ) →
        Option
          (Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
            (FlatDirectionCertificate (rational_matrix_polyhedron A b)))) where
  coe algorithm := algorithm.run

namespace RationalPolytopeFlatnessAlgorithm

/-- `Certified algorithm` means that `algorithm` satisfies the explicit polynomial-time bound from
Theorem 9.7 (2) and returns the promised Chapter 9 flatness output on every full-dimensional
compact rational polyhedron. -/
structure Certified
    {m n : ℕ} (algorithm : RationalPolytopeFlatnessAlgorithm m n) : Prop where
  polynomial_time :
    ∃ π : Polynomial ℕ,
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        algorithm.runTime A b ≤ π.eval (n + rational_linear_system_encoding_size A b)
  correct
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ)
      (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
      (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
      ∃ out,
        algorithm A b = some out

/-- A rational-polytope flatness algorithm satisfies its explicit polynomial running-time bound. -/
theorem runTime_le
    {m n : ℕ}
    (algorithm : RationalPolytopeFlatnessAlgorithm m n)
    (hcert : Certified algorithm) :
    ∃ π : Polynomial ℕ,
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        algorithm.runTime A b ≤ π.eval (n + rational_linear_system_encoding_size A b) :=
  hcert.polynomial_time

/-- On a full-dimensional compact rational polyhedron, a rational-polytope flatness algorithm
returns an explicit output in the canonical Chapter 9 flatness format. -/
theorem output_spec
    {m n : ℕ}
    (algorithm : RationalPolytopeFlatnessAlgorithm m n)
    (hcert : Certified algorithm)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
    (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
    ∃ out,
      algorithm A b = some out :=
  hcert.correct A b hfull hcompact

end RationalPolytopeFlatnessAlgorithm

/-- Helper for Theorem 9.7: an existing integral point of `P` can be packaged as an explicit
integral-point certificate. -/
theorem existsIntegralPointCertificate_of_containsIntegralPoint
    {P : Set (Fin n → ℝ)}
    (hP : contains_integral_point P) :
    Nonempty (IntegralPointCertificate P) := by
  -- Unpack the source-facing predicate into an explicit integer vector witness.
  rcases contains_integral_point_iff.mp hP with ⟨z, hz⟩
  exact ⟨⟨z, hz⟩⟩

/-- Helper for Theorem 9.7: every rational matrix polyhedron is convex as a subset of `ℝ^n`. -/
theorem rationalMatrixPolyhedronConvex
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    Convex ℝ (rational_matrix_polyhedron A b) := by
  intro x hx y hy a₁ a₂ ha₁ ha₂ ha_sum
  -- Each defining row inequality is preserved by convex combinations.
  rw [mem_rational_matrix_polyhedron] at hx hy ⊢
  intro i
  have hx_i : ((A.map (Rat.castHom ℝ)) *ᵥ x) i ≤ (b i : ℝ) := hx i
  have hy_i : ((A.map (Rat.castHom ℝ)) *ᵥ y) i ≤ (b i : ℝ) := hy i
  calc
    ((A.map (Rat.castHom ℝ)) *ᵥ (a₁ • x + a₂ • y)) i
        = a₁ * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) +
            a₂ * (((A.map (Rat.castHom ℝ)) *ᵥ y) i) := by
            calc
              ∑ j, (A.map (Rat.castHom ℝ)) i j * (a₁ * x j + a₂ * y j)
                  =
                    ∑ j,
                      (a₁ * ((A.map (Rat.castHom ℝ)) i j * x j) +
                        a₂ * ((A.map (Rat.castHom ℝ)) i j * y j)) := by
                          refine Finset.sum_congr rfl ?_
                          intro j _
                          ring
              _ =
                  a₁ * ∑ j, (A.map (Rat.castHom ℝ)) i j * x j +
                    a₂ * ∑ j, (A.map (Rat.castHom ℝ)) i j * y j := by
                      simp [Finset.mul_sum, Finset.sum_add_distrib]
              _ =
                  a₁ * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) +
                    a₂ * (((A.map (Rat.castHom ℝ)) *ᵥ y) i) := by
                      simp [Matrix.mulVec, dotProduct]
    _ ≤ a₁ * (b i : ℝ) + a₂ * (b i : ℝ) := by
      gcongr
    _ = (b i : ℝ) := by
      calc
        a₁ * (b i : ℝ) + a₂ * (b i : ℝ) = (a₁ + a₂) * (b i : ℝ) := by ring
        _ = (b i : ℝ) := by simp [ha_sum]

/-- Helper for Theorem 9.7: nonempty interior gives a nonempty carrier for the rational
polyhedron owner. -/
theorem rationalMatrixPolyhedronNonempty_of_interiorNonempty
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty) :
    (rational_matrix_polyhedron A b).Nonempty := by
  -- Any point of the interior is in the set itself.
  rcases hfull with ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩

/-- Helper for Theorem 9.7: the full-dimensional compact rational polyhedron
`rational_matrix_polyhedron A b` carries a canonical `ConvexBody` owner. -/
def rationalMatrixPolyhedronConvexBody
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
    (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
    ConvexBody (Fin n → ℝ) where
  carrier := rational_matrix_polyhedron A b
  convex' := rationalMatrixPolyhedronConvex A b
  isCompact' := hcompact
  nonempty' := rationalMatrixPolyhedronNonempty_of_interiorNonempty A b hfull

/-- Helper for Theorem 9.7: a flat-direction certificate gives a direct upper bound on the lattice
width by inserting the certified direction into the defining infimum. -/
theorem directionalWidth_nonneg
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (d : Fin n → ℤ) :
    0 ≤ directional_width (K : Set (Fin n → ℝ)) d := by
  let imageSet := integral_direction_linear_form d '' (K : Set (Fin n → ℝ))
  have hcont : Continuous (integral_direction_linear_form d) := by
    -- The directional linear form is continuous as a finite-dimensional linear functional.
    simpa [integral_direction_linear_form, dotProduct] using
      (continuous_finsetSum Finset.univ fun i _ =>
        (continuous_const.mul (continuous_apply i)))
  have hcompact : IsCompact imageSet := by
    simpa [imageSet] using K.isCompact.image hcont
  rcases K.nonempty with ⟨x, hx⟩
  have hx_image : integral_direction_linear_form d x ∈ imageSet := by
    exact ⟨x, hx, rfl⟩
  have hinf_le : sInf imageSet ≤ integral_direction_linear_form d x := by
    exact csInf_le hcompact.bddBelow hx_image
  have hle_sup : integral_direction_linear_form d x ≤ sSup imageSet := by
    exact le_csSup hcompact.bddAbove hx_image
  have hwidth : 0 ≤ sSup imageSet - sInf imageSet := by
    linarith
  simpa [directional_width, imageSet] using hwidth

/-- Helper for Theorem 9.7: any nonempty subset of `ℝ^0` contains the unique integral point. -/
theorem contains_integral_point_fin_zero_of_nonempty
    {K : Set (Fin 0 → ℝ)}
    (hK : K.Nonempty) :
    contains_integral_point K := by
  rcases hK with ⟨x, hx⟩
  have hzero_mem : (0 : Fin 0 → ℝ) ∈ K := by
    -- In `ℝ^0` every point is the unique zero vector.
    simpa [Subsingleton.elim x 0] using hx
  have hcast_zero : (Int.cast ∘ fun i : Fin 0 ↦ Fin.elim0 i) = (0 : Fin 0 → ℝ) := by
    funext i
    exact Fin.elim0 i
  -- Package the unique zero vector as the required integer witness.
  refine contains_integral_point_iff.mpr ⟨fun i ↦ Fin.elim0 i, ?_⟩
  simpa [hcast_zero] using hzero_mem

/-- Helper for Theorem 9.7: every nonempty subset of `ℝ^0` has zero directional width. -/
theorem directionalWidth_fin_zero_of_nonempty
    {K : Set (Fin 0 → ℝ)}
    (hK : K.Nonempty)
    (d : Fin 0 → ℤ) :
    directional_width K d = 0 := by
  have hzero_mem : (0 : Fin 0 → ℝ) ∈ K := by
    rcases hK with ⟨x, hx⟩
    -- Collapse the witness to the unique point of `ℝ^0`.
    simpa [Subsingleton.elim x 0] using hx
  have himage :
      integral_direction_linear_form d '' K = ({0} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hxK, rfl⟩
      -- The directional linear form is identically zero on the terminal vector space.
      have hx0 : x = 0 := Subsingleton.elim x 0
      simp [integral_direction_linear_form, hx0, dotProduct]
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      refine ⟨0, hzero_mem, ?_⟩
      simp [integral_direction_linear_form, hy0, dotProduct]
  -- A singleton image has equal supremum and infimum, so the width vanishes.
  simp [directional_width, himage]

/-- Helper for Theorem 9.7: directional width is monotone for a nonempty subset inside a compact
ambient set. -/
theorem directionalWidth_mono
    {n : ℕ}
    {S T : Set (Fin n → ℝ)}
    {d : Fin n → ℤ}
    (hSnonempty : S.Nonempty)
    (hTcompact : IsCompact T)
    (hST : S ⊆ T) :
    directional_width S d ≤ directional_width T d := by
  let imageS := integral_direction_linear_form d '' S
  let imageT := integral_direction_linear_form d '' T
  have hcont : Continuous (integral_direction_linear_form d) := by
    -- The directional linear form is a finite sum of continuous coordinate projections.
    simpa [integral_direction_linear_form, dotProduct] using
      (continuous_finsetSum Finset.univ fun i _ =>
        (continuous_const.mul (continuous_apply i)))
  have himage : imageS ⊆ imageT := by
    -- Apply the same linear form to points of `S` and then move them into `T`.
    simpa [imageS, imageT] using Set.image_mono hST
  have himageS_nonempty : imageS.Nonempty := by
    -- A witness in `S` gives a witness in the image set.
    rcases hSnonempty with ⟨x, hx⟩
    exact ⟨integral_direction_linear_form d x, ⟨x, hx, rfl⟩⟩
  have himageT_compact : IsCompact imageT := by
    simpa [imageT] using hTcompact.image hcont
  have hsup : sSup imageS ≤ sSup imageT :=
    csSup_le_csSup himageT_compact.bddAbove himageS_nonempty himage
  have hinf : sInf imageT ≤ sInf imageS :=
    csInf_le_csInf himageT_compact.bddBelow himageS_nonempty himage
  -- Compare the upper and lower extrema separately and combine the inequalities.
  have hwidth : sSup imageS - sInf imageS ≤ sSup imageT - sInf imageT := by
    linarith
  simpa [directional_width, imageS, imageT] using hwidth

/-- Helper for Theorem 9.7: a flat-direction certificate gives a direct upper bound on the lattice
width by inserting the certified direction into the defining infimum. -/
theorem latticeWidth_le_of_flatDirectionCertificate
    {n : ℕ}
    {K : ConvexBody (Fin n → ℝ)}
    (hcert : Nonempty (FlatDirectionCertificate (K : Set (Fin n → ℝ)))) :
    lattice_width K ≤ flat_direction_bound n := by
  rcases hcert with ⟨direction⟩
  have hBddBelow :
      BddBelow
        ((fun d : {d : Fin n → ℤ // d ≠ 0} ↦
            w_{d.1}((K : Set (Fin n → ℝ)))) '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro x ⟨d, -, rfl⟩
    exact directionalWidth_nonneg K d.1
  have hmem :
      w_{direction.1}((K : Set (Fin n → ℝ))) ∈
        ((fun d : {d : Fin n → ℤ // d ≠ 0} ↦
            w_{d.1}((K : Set (Fin n → ℝ)))) '' Set.univ) := by
    -- The certified direction is one of the nonzero integral directions defining `lattice_width`.
    refine ⟨⟨direction.1, direction.ne_zero⟩, Set.mem_univ _, rfl⟩
  -- Compare the infimum to that concrete direction and then use the certificate bound.
  exact le_trans (csInf_le hBddBelow hmem) direction.width_le

namespace FlatnessSupport

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the Euclidean norm on the raw
coordinate model `Fin n → ℝ`. -/
noncomputable def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the coordinate Euclidean norm
is nonnegative. -/
theorem euclideanNorm_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ euclideanNorm x := by
  -- This is the ordinary nonnegativity of the norm after changing the coordinate presentation.
  exact norm_nonneg _

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the coordinate Euclidean norm
vanishes exactly at the zero vector. -/
theorem euclideanNorm_eq_zero {n : ℕ} {x : Fin n → ℝ} :
    euclideanNorm x = 0 ↔ x = 0 := by
  -- Transport definiteness of the Hilbert-space norm back through `WithLp.toLp`.
  simp [euclideanNorm]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: scalar multiplication has the
usual homogeneity property for the coordinate Euclidean norm. -/
theorem euclideanNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  -- Move the scalar multiplication to Euclidean space and use norm homogeneity there.
  simp [euclideanNorm, norm_smul, Real.norm_eq_abs]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the coordinate Euclidean norm
is continuous in the ambient finite-dimensional topology. -/
theorem continuous_euclideanNorm {n : ℕ} :
    Continuous (@euclideanNorm n) := by
  -- The finite-dimensional `ℓ2` presentation has the same product topology.
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

/-- Helper for Theorem 9.7: the ambient coordinate sup norm is bounded by the Euclidean norm. -/
theorem norm_le_euclideanNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖ ≤ euclideanNorm x := by
  -- Bound each coordinate by the `ℓ2` norm and use the product-norm characterization.
  rw [pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)]
  intro i
  simpa [euclideanNorm] using
    (PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) i)

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the Euclidean norm squared is
the coordinate dot product with itself. -/
theorem dotProduct_self_eq_euclideanNorm_sq {n : ℕ} (x : Fin n → ℝ) :
    x ⬝ᵥ x = euclideanNorm x ^ 2 := by
  -- Expand the Euclidean inner product coordinatewise.
  calc
    x ⬝ᵥ x =
        inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 x) := by
          simp only [PiLp.inner_apply, Real.inner_apply, dotProduct]
    _ = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    _ = euclideanNorm x ^ 2 := rfl

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: coordinate dot products obey
Cauchy–Schwarz for the explicit Euclidean norm. -/
theorem abs_dotProduct_le_euclideanNorm_mul {n : ℕ} (x y : Fin n → ℝ) :
    |x ⬝ᵥ y| ≤ euclideanNorm x * euclideanNorm y := by
  -- Apply Hilbert-space Cauchy–Schwarz after changing only the norm presentation.
  calc
    |x ⬝ᵥ y| =
        |inner ℝ (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 x)| := by
          simp only [PiLp.inner_apply, Real.inner_apply, dotProduct]
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    _ ≤ ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ *
          ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ :=
      abs_real_inner_le_norm _ _
    _ = euclideanNorm x * euclideanNorm y := by
      simp only [euclideanNorm]
      ring

/-- Helper for Theorem 9.7: the support-local ellipsoid owner centered at `a` with shape matrix
`C`. -/
noncomputable def euclideanEllipsoid
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | euclideanNorm (C *ᵥ (x - a)) ≤ 1}

/-- Helper for Theorem 9.7: the center of a support-local ellipsoid always belongs to it. -/
theorem center_mem_euclideanEllipsoid
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    a ∈ euclideanEllipsoid C a := by
  -- At the center the translated vector vanishes, so the norm constraint is immediate.
  simp [euclideanEllipsoid, euclideanNorm]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: every support-local Euclidean
ellipsoid is closed. -/
theorem isClosed_euclideanEllipsoid
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    IsClosed (euclideanEllipsoid C a) := by
  -- Express the ellipsoid as a closed sublevel set of its continuous defining function.
  have hcont : Continuous fun x : Fin n → ℝ ↦ euclideanNorm (C *ᵥ (x - a)) :=
    continuous_euclideanNorm.comp
      (Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const))
  simpa [euclideanEllipsoid] using isClosed_le hcont continuous_const

/-- Helper for Theorem 9.7: the direct affine image of the Euclidean unit ball. -/
noncomputable def directAffineEuclideanBall
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun u ↦ a + A *ᵥ u) '' {u | euclideanNorm u ≤ 1}

/-- Helper for Theorem 9.7: the direct affine ball contains its center. -/
theorem center_mem_directAffineEuclideanBall
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    a ∈ directAffineEuclideanBall A a := by
  -- Use the zero vector in the unit ball as the direct-image witness.
  refine ⟨0, ?_, ?_⟩
  · simp [euclideanNorm]
  · simp

/-- Helper for Theorem 9.7: a nonsingular direct-shape ball is the inverse-shape ellipsoid defined
by the inverse matrix. -/
theorem directAffineEuclideanBall_eq_euclideanEllipsoid_inv
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hdet : IsUnit A.det) :
    directAffineEuclideanBall A a = euclideanEllipsoid A⁻¹ a := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    -- Applying `A⁻¹` cancels the direct shape and recovers the unit-ball witness.
    change euclideanNorm (A⁻¹ *ᵥ (a + A *ᵥ u - a)) ≤ 1
    have hinv : A⁻¹ * A = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.nonsing_inv_mul _ hdet
    simpa [Matrix.mulVec_mulVec, hinv] using hu
  · intro hx
    -- Conversely, use the inverse-shape coordinates as the direct-image witness.
    let u : Fin n → ℝ := A⁻¹ *ᵥ (x - a)
    refine ⟨u, hx, ?_⟩
    have hmul : A * A⁻¹ = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.mul_nonsing_inv _ hdet
    ext i
    simp [u, Matrix.mulVec_mulVec, hmul]

/-- Helper for Theorem 9.7: the raw-coordinate Euclidean unit ball is compact. -/
theorem isCompact_euclideanUnitBall {n : ℕ} :
    IsCompact ({u : Fin n → ℝ | euclideanNorm u ≤ 1} : Set (Fin n → ℝ)) := by
  -- In finite dimension, the continuous norm sublevel is closed and is bounded in the ambient
  -- product norm by the comparison lemma above.
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_le continuous_euclideanNorm continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, ?_⟩
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_euclideanNorm u).trans hu

/-- Helper for Theorem 9.7: the raw-coordinate Euclidean unit ball is convex. -/
theorem convex_euclideanUnitBall {n : ℕ} :
    Convex ℝ ({u : Fin n → ℝ | euclideanNorm u ≤ 1} : Set (Fin n → ℝ)) := by
  intro x hx y hy α β hα hβ hsum
  -- Transfer the convex combination to Euclidean space and apply the triangle inequality.
  change euclideanNorm x ≤ 1 at hx
  change euclideanNorm y ≤ 1 at hy
  change ‖(WithLp.toLp 2 (α • x + β • y) : EuclideanSpace ℝ (Fin n))‖ ≤ 1
  have hadd :
      (WithLp.toLp 2 (α • x + β • y) : EuclideanSpace ℝ (Fin n)) =
        α • WithLp.toLp 2 x + β • WithLp.toLp 2 y := by
    ext i
    rfl
  calc
    ‖(WithLp.toLp 2 (α • x + β • y) : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖α • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ +
          ‖β • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
            rw [hadd]
            exact norm_add_le _ _
    _ = α * euclideanNorm x + β * euclideanNorm y := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hα, abs_of_nonneg hβ]
      rfl
    _ ≤ α * 1 + β * 1 := by gcongr
    _ = 1 := by linarith

/-- Helper for Theorem 9.7: every direct affine Euclidean ball is compact. -/
theorem isCompact_directAffineEuclideanBall
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    IsCompact (directAffineEuclideanBall A a) := by
  -- Compactness is preserved by the continuous affine parameterization of the unit ball.
  exact isCompact_euclideanUnitBall.image
    (continuous_const.add (Continuous.matrix_mulVec continuous_const continuous_id))

/-- Helper for Theorem 9.7: every direct affine Euclidean ball is convex. -/
theorem convex_directAffineEuclideanBall
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    Convex ℝ (directAffineEuclideanBall A a) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩ α β hα hβ hsum
  -- Combine the two unit-ball witnesses, then commute the affine map with the combination.
  refine ⟨α • u + β • v, convex_euclideanUnitBall hu hv hα hβ hsum, ?_⟩
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun j _ ↦ mul_add _ _ _, Finset.sum_add_distrib]
  have hAu : ∑ j, A i j * (α * u j) = α * ∑ j, A i j * u j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have hAv : ∑ j, A i j * (β * v j) = β * ∑ j, A i j * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hAu, hAv]
  calc
    a i + (α * ∑ j, A i j * u j + β * ∑ j, A i j * v j) =
        (α + β) * a i +
          α * ∑ j, A i j * u j + β * ∑ j, A i j * v j := by rw [hsum]; ring
    _ = α * (a i + ∑ j, A i j * u j) + β * (a i + ∑ j, A i j * v j) := by ring

/-- Helper for Theorem 9.7: the identity direct affine ball is the raw Euclidean unit ball. -/
theorem directAffineEuclideanBall_one_zero {n : ℕ} :
    directAffineEuclideanBall (1 : Matrix (Fin n) (Fin n) ℝ) 0 =
      {u : Fin n → ℝ | euclideanNorm u ≤ 1} := by
  -- The identity matrix and zero translation leave every unit-ball point unchanged.
  ext x
  simp [directAffineEuclideanBall]

/-- Helper for Theorem 9.7: composing two affine direct-ball parameterizations multiplies their
shape matrices and transports the center. -/
theorem image_directAffineEuclideanBall
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n → ℝ) :
    (fun x ↦ a + A *ᵥ x) '' directAffineEuclideanBall B b =
      directAffineEuclideanBall (A * B) (a + A *ᵥ b) := by
  -- Both sides use the same unit-ball parameter after associating matrix-vector multiplication.
  ext x
  constructor
  · rintro ⟨-, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    ext i
    simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨b + B *ᵥ u, ⟨u, hu, rfl⟩, ?_⟩
    ext i
    simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

/-- Helper for Theorem 9.7: nonempty interior supplies a nonsingular direct affine Euclidean ball
contained in the convex body. -/
theorem existsNonsingularDirectAffineEuclideanBall_subset
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (hfull : (interior (K : Set (Fin n → ℝ))).Nonempty) :
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
      IsUnit A.det ∧ directAffineEuclideanBall A a ⊆ (K : Set (Fin n → ℝ)) := by
  rcases hfull with ⟨a, ha⟩
  have hK_nhds : (K : Set (Fin n → ℝ)) ∈ nhds a :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds ha) interior_subset
  rcases Metric.mem_nhds_iff.mp hK_nhds with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  let A : Matrix (Fin n) (Fin n) ℝ := δ • 1
  refine ⟨A, a, ?_, ?_⟩
  · -- A positive scalar multiple of the identity has nonzero determinant.
    apply isUnit_iff_ne_zero.mpr
    simp [A, δ, hε.ne']
  · rintro x ⟨u, hu, rfl⟩
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hu_sup : ‖u‖ ≤ 1 := (norm_le_euclideanNorm u).trans hu
    have hδ_pos : 0 < δ := by simpa [δ] using half_pos hε
    calc
      ‖a + A *ᵥ u - a‖ = ‖δ • u‖ := by
        congr 1
        dsimp [A]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        abel
      _ = δ * ‖u‖ := by simp [norm_smul, abs_of_pos hδ_pos]
      _ ≤ δ := by nlinarith
      _ < ε := by simp [δ, hε]

/-- Helper for Theorem 9.7: parameter pairs whose direct affine Euclidean ball lies in `K`. -/
noncomputable def feasibleDirectAffineBalls
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ)) :
    Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {p | directAffineEuclideanBall p.1 p.2 ⊆ (K : Set (Fin n → ℝ))}

/-- Helper for Theorem 9.7: feasible direct affine-ball parameters form a closed set. -/
theorem isClosed_feasibleDirectAffineBalls
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ)) :
    IsClosed (feasibleDirectAffineBalls K) := by
  let unitBall : Set (Fin n → ℝ) := {u | euclideanNorm u ≤ 1}
  have hdescription :
      feasibleDirectAffineBalls K =
        ⋂ u, ⋂ (_ : u ∈ unitBall),
          (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ↦
            p.2 + p.1 *ᵥ u) ⁻¹' (K : Set (Fin n → ℝ)) := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro u hu
      exact hp ⟨u, hu, rfl⟩
    · intro hp x hx
      rcases hx with ⟨u, hu, rfl⟩
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
  rw [hdescription]
  refine isClosed_iInter fun u ↦ isClosed_iInter fun _ ↦ ?_
  -- Each pointwise containment constraint is the preimage of the closed body under an affine map.
  exact K.isClosed.preimage
    (continuous_snd.add (Continuous.matrix_mulVec continuous_fst continuous_const))

/-- Helper for Theorem 9.7: feasible direct affine-ball parameters form a compact set. -/
theorem isCompact_feasibleDirectAffineBalls
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ)) :
    IsCompact (feasibleDirectAffineBalls K) := by
  classical
  rcases K.isCompact.isBounded.subset_closedBall (0 : Fin n → ℝ) with ⟨R, hR⟩
  rcases K.nonempty with ⟨k, hk⟩
  have hR_nonneg : 0 ≤ R := by
    have hkR := hR hk
    rw [Metric.mem_closedBall, dist_zero_right] at hkR
    exact (norm_nonneg k).trans hkR
  let matrixBox : Set (Matrix (Fin n) (Fin n) ℝ) := (Set.Icc (-2 * R) (2 * R)).matrix
  have hbox_compact : IsCompact matrixBox := by
    exact isCompact_Icc.matrix
  have henclosure :
      feasibleDirectAffineBalls K ⊆ matrixBox ×ˢ (K : Set (Fin n → ℝ)) := by
    intro p hp
    change directAffineEuclideanBall p.1 p.2 ⊆ (K : Set (Fin n → ℝ)) at hp
    have haK : p.2 ∈ (K : Set (Fin n → ℝ)) :=
      hp (center_mem_directAffineEuclideanBall _ _)
    have ha : ‖p.2‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR haK
    refine ⟨?_, haK⟩
    rw [Set.mem_matrix]
    intro i j
    let e : Fin n → ℝ := Pi.single j 1
    have he : euclideanNorm e ≤ 1 := by
      simp [e, euclideanNorm]
    have hpointK : p.2 + p.1 *ᵥ e ∈ (K : Set (Fin n → ℝ)) :=
      hp ⟨e, he, rfl⟩
    have hpoint : ‖p.2 + p.1 *ᵥ e‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hpointK
    have hcolumn : ‖p.1 *ᵥ e‖ ≤ 2 * R := by
      calc
        ‖p.1 *ᵥ e‖ = ‖(p.2 + p.1 *ᵥ e) - p.2‖ := by
          congr 1
          abel
        _ ≤ ‖p.2 + p.1 *ᵥ e‖ + ‖p.2‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    have hentry : ‖p.1 i j‖ ≤ ‖p.1 *ᵥ e‖ := by
      have hcoordinate := norm_le_pi_norm (p.1 *ᵥ e) i
      simpa [e, Matrix.mulVec_single_one] using hcoordinate
    have habs : |p.1 i j| ≤ 2 * R := by
      simpa [Real.norm_eq_abs] using hentry.trans hcolumn
    constructor
    · linarith [neg_le_of_abs_le habs]
    · exact le_of_abs_le habs
  -- Intersect the closed feasibility constraints with the compact entrywise box and `K`.
  exact IsCompact.of_isClosed_subset (hbox_compact.prod K.isCompact)
    (isClosed_feasibleDirectAffineBalls K) henclosure

/-- Helper for Theorem 9.7: a full-dimensional convex body contains a determinant-maximal
nonsingular direct affine Euclidean ball. -/
theorem existsDetMaximalDirectAffineEuclideanBall
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (hfull : (interior (K : Set (Fin n → ℝ))).Nonempty) :
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
      IsUnit A.det ∧
        directAffineEuclideanBall A a ⊆ (K : Set (Fin n → ℝ)) ∧
        ∀ (B : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
          directAffineEuclideanBall B b ⊆ (K : Set (Fin n → ℝ)) →
            |B.det| ≤ |A.det| := by
  classical
  rcases existsNonsingularDirectAffineEuclideanBall_subset K hfull with
    ⟨A₀, a₀, hA₀_unit, hA₀K⟩
  have hfeasible_nonempty : (feasibleDirectAffineBalls K).Nonempty :=
    ⟨(A₀, a₀), hA₀K⟩
  have hdet_continuous :
      Continuous fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ↦ |p.1.det| :=
    continuous_abs.comp continuous_fst.matrix_det
  rcases (isCompact_feasibleDirectAffineBalls K).exists_isMaxOn
      hfeasible_nonempty hdet_continuous.continuousOn with ⟨p, hp, hpmax⟩
  refine ⟨p.1, p.2, ?_, hp, ?_⟩
  · -- Comparison with the initial nonsingular ball forces the maximizing determinant nonzero.
    apply isUnit_iff_ne_zero.mpr
    have hmax_initial : |A₀.det| ≤ |p.1.det| :=
      (isMaxOn_iff.mp hpmax) (A₀, a₀) hA₀K
    intro hp_zero
    have hpositive : 0 < |A₀.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp hA₀_unit)
    have himpossible : |A₀.det| ≤ 0 := by simpa [hp_zero] using hmax_initial
    exact (not_le_of_gt hpositive) himpossible
  · intro B b hBK
    exact (isMaxOn_iff.mp hpmax) (B, b) hBK

/-- Helper for Theorem 9.7: pull a convex body back along a direct affine ellipsoid
parameterization. -/
noncomputable def normalizedBody
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun u ↦ a + A *ᵥ u) ⁻¹' (K : Set (Fin n → ℝ))

/-- Helper for Theorem 9.7: for a nonsingular shape, the normalized body is the image of `K`
under the inverse affine coordinate map. -/
theorem normalizedBody_eq_image_inv
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hA_unit : IsUnit A.det) :
    normalizedBody K A a =
      (fun x ↦ A⁻¹ *ᵥ (x - a)) '' (K : Set (Fin n → ℝ)) := by
  ext u
  constructor
  · intro hu
    refine ⟨a + A *ᵥ u, hu, ?_⟩
    have hinv : A⁻¹ * A = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.nonsing_inv_mul _ hA_unit
    ext i
    simp [Matrix.mulVec_mulVec, hinv]
  · rintro ⟨x, hx, rfl⟩
    change a + A *ᵥ (A⁻¹ *ᵥ (x - a)) ∈ (K : Set (Fin n → ℝ))
    have hmul : A * A⁻¹ = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.mul_nonsing_inv _ hA_unit
    simpa [Matrix.mulVec_mulVec, hmul] using hx

/-- Helper for Theorem 9.7: normalization by a nonsingular affine map preserves compactness. -/
theorem isCompact_normalizedBody
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hA_unit : IsUnit A.det) :
    IsCompact (normalizedBody K A a) := by
  rw [normalizedBody_eq_image_inv K A a hA_unit]
  exact K.isCompact.image
    (Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const))

/-- Helper for Theorem 9.7: normalization by an affine map preserves convexity. -/
theorem convex_normalizedBody
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    Convex ℝ (normalizedBody K A a) := by
  intro x hx y hy α β hα hβ hsum
  change a + A *ᵥ x ∈ (K : Set (Fin n → ℝ)) at hx
  change a + A *ᵥ y ∈ (K : Set (Fin n → ℝ)) at hy
  change a + A *ᵥ (α • x + β • y) ∈ (K : Set (Fin n → ℝ))
  have haffine :
      a + A *ᵥ (α • x + β • y) =
        α • (a + A *ᵥ x) + β • (a + A *ᵥ y) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl fun j _ ↦ mul_add _ _ _, Finset.sum_add_distrib]
    have hAx : ∑ j, A i j * (α * x j) = α * ∑ j, A i j * x j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    have hAy : ∑ j, A i j * (β * y j) = β * ∑ j, A i j * y j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hAx, hAy]
    calc
      a i + (α * ∑ j, A i j * x j + β * ∑ j, A i j * y j) =
          (α + β) * a i +
            α * ∑ j, A i j * x j + β * ∑ j, A i j * y j := by rw [hsum]; ring
      _ = α * (a i + ∑ j, A i j * x j) + β * (a i + ∑ j, A i j * y j) := by ring
  rw [haffine]
  exact K.convex hx hy hα hβ hsum

/-- Helper for Theorem 9.7: after normalizing a determinant-maximal ellipsoid, the unit ball is
feasible and no feasible affine ball has determinant larger than one. -/
theorem normalizedBody_unitBall_subset_and_detMaximal
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hA_unit : IsUnit A.det)
    (hAK : directAffineEuclideanBall A a ⊆ (K : Set (Fin n → ℝ)))
    (hmax : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      directAffineEuclideanBall B b ⊆ (K : Set (Fin n → ℝ)) →
        |B.det| ≤ |A.det|) :
    {u : Fin n → ℝ | euclideanNorm u ≤ 1} ⊆ normalizedBody K A a ∧
      ∀ (B : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
        directAffineEuclideanBall B b ⊆ normalizedBody K A a → |B.det| ≤ 1 := by
  constructor
  · intro u hu
    -- The original feasible ball becomes the identity ball after pulling `K` back by its map.
    exact hAK ⟨u, hu, rfl⟩
  · intro B b hB
    have hcomposed :
        directAffineEuclideanBall (A * B) (a + A *ᵥ b) ⊆
          (K : Set (Fin n → ℝ)) := by
      rw [← image_directAffineEuclideanBall]
      intro x hx
      rcases hx with ⟨u, hu, rfl⟩
      exact hB hu
    have hdet := hmax (A * B) (a + A *ᵥ b) hcomposed
    rw [Matrix.det_mul, abs_mul] at hdet
    have hA_pos : 0 < |A.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp hA_unit)
    nlinarith [abs_nonneg B.det]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the unit vectors whose
supporting half-spaces contain a normalized body. -/
noncomputable def normalizedSupportingContacts
    {n : ℕ}
    (L : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {u | euclideanNorm u = 1 ∧ ∀ x ∈ L, u ⬝ᵥ x ≤ 1}

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: normalized supporting
contacts form a compact set. -/
theorem isCompact_normalizedSupportingContacts
    {n : ℕ}
    (L : Set (Fin n → ℝ)) :
    IsCompact (normalizedSupportingContacts L) := by
  have hclosed : IsClosed (normalizedSupportingContacts L) := by
    have hdescription :
        normalizedSupportingContacts L =
          {u | euclideanNorm u = 1} ∩
            ⋂ x, ⋂ (_ : x ∈ L), {u | u ⬝ᵥ x ≤ 1} := by
      ext u
      simp [normalizedSupportingContacts]
    rw [hdescription]
    refine (isClosed_eq continuous_euclideanNorm continuous_const).inter ?_
    refine isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ ?_
    have hcontinuous : Continuous fun u : Fin n → ℝ ↦ u ⬝ᵥ x := by
      simpa [dotProduct] using
        (continuous_finsetSum Finset.univ fun i _ ↦ (continuous_apply i).mul continuous_const)
    exact isClosed_le hcontinuous continuous_const
  -- The contact set is a closed subset of the compact Euclidean unit ball.
  refine IsCompact.of_isClosed_subset isCompact_euclideanUnitBall hclosed ?_
  intro u hu
  exact hu.1.le

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the rank-one matrix associated
to a normalized supporting contact. -/
noncomputable def contactMomentMatrix
    {n : ℕ}
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ u i * u j

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a unit contact's rank-one
moment has trace one. -/
theorem contactMoment_trace
    {n : ℕ}
    {u : Fin n → ℝ}
    (hu : euclideanNorm u = 1) :
    Matrix.trace (contactMomentMatrix u) = 1 := by
  -- Expand the diagonal sum and then use the Euclidean norm-square identity.
  calc
    Matrix.trace (contactMomentMatrix u) = u ⬝ᵥ u := by
      simp [Matrix.trace, contactMomentMatrix, dotProduct]
    _ = euclideanNorm u ^ 2 := dotProduct_self_eq_euclideanNorm_sq u
    _ = 1 := by rw [hu]; norm_num

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: package a contact vector and
its rank-one matrix into the finite-dimensional moment space used for separation. -/
abbrev ContactMomentSpace (n : ℕ) :=
  EuclideanSpace ℝ (Sum (Fin n) (Fin n × Fin n))

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: package a contact vector and
its rank-one matrix into the finite-dimensional moment space used for separation. -/
noncomputable def contactMoment
    {n : ℕ}
    (u : Fin n → ℝ) : ContactMomentSpace n :=
  WithLp.toLp 2 fun
    | Sum.inl i => u i
    | Sum.inr ij => u ij.1 * u ij.2

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the contact-moment map is
continuous in the finite-dimensional coordinate topology. -/
theorem continuous_contactMoment
    {n : ℕ} :
    Continuous (@contactMoment n) := by
  -- Every vector or matrix coordinate is continuous before passing to the Euclidean `L²` model.
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ij ↦ ?_)
  cases ij with
  | inl i => exact continuous_apply i
  | inr ij => exact (continuous_apply ij.1).mul (continuous_apply ij.2)

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: contact moments of a normalized
body form a compact generator set. -/
theorem isCompact_contactMoments
    {n : ℕ}
    (L : Set (Fin n → ℝ)) :
    IsCompact (contactMoment '' normalizedSupportingContacts L) := by
  -- Take the continuous image of the compact supporting-contact set.
  exact (isCompact_normalizedSupportingContacts L).image continuous_contactMoment

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the normalized balance and
identity moment sought in the convex hull of supporting contacts. -/
noncomputable def normalizedContactMomentTarget
    (n : ℕ) : ContactMomentSpace n :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 0
    | Sum.inr ij => if ij.1 = ij.2 then (n : ℝ)⁻¹ else 0

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: in positive dimension the
matrix coordinate of the normalized target lies in the trace-one affine slice. -/
theorem normalizedContactMomentTarget_trace
    {n : ℕ}
    (hn : n ≠ 0) :
    ∑ i, normalizedContactMomentTarget n (Sum.inr (i, i)) = 1 := by
  -- The trace of the identity is `n`, which cancels the normalizing scalar `n⁻¹`.
  simp [normalizedContactMomentTarget, hn]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: failure of normalized target
membership produces a functional strictly separating it from every supporting-contact moment. -/
theorem existsContactMomentSeparator_of_target_not_mem_closedConvexHull
    {n : ℕ}
    (L : Set (Fin n → ℝ))
    (houtside : normalizedContactMomentTarget n ∉
      closedConvexHull ℝ (contactMoment '' normalizedSupportingContacts L)) :
    ∃ f : StrongDual ℝ (ContactMomentSpace n),
      ∀ u ∈ normalizedSupportingContacts L,
        f (contactMoment u) < f (normalizedContactMomentTarget n) := by
  -- Separate the target from the closed convex hull and restrict the separator to generators.
  rcases geometric_hahn_banach_closed_point
      (convex_closedConvexHull (s := contactMoment '' normalizedSupportingContacts L))
      (isClosed_closedConvexHull (s := contactMoment '' normalizedSupportingContacts L))
      houtside with ⟨f, c, hcontact, htarget⟩
  refine ⟨f, ?_⟩
  intro u hu
  exact
    (hcontact (contactMoment u)
      (subset_closedConvexHull ⟨u, hu, rfl⟩)).trans htarget

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the vector coefficients of a
continuous functional on the contact-moment space. -/
noncomputable def contactSeparatorVector
    {n : ℕ}
    (f : StrongDual ℝ (ContactMomentSpace n)) : Fin n → ℝ :=
  fun i ↦ (InnerProductSpace.toDual ℝ (ContactMomentSpace n)).symm f (Sum.inl i)

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the quadratic coefficients of
a continuous functional on the contact-moment space. -/
noncomputable def contactSeparatorMatrix
    {n : ℕ}
    (f : StrongDual ℝ (ContactMomentSpace n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (InnerProductSpace.toDual ℝ (ContactMomentSpace n)).symm f (Sum.inr (i, j))

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: evaluating a separator on a
contact moment is its linear part plus its quadratic part. -/
theorem contactMoment_separator_apply
    {n : ℕ}
    (f : StrongDual ℝ (ContactMomentSpace n))
    (u : Fin n → ℝ) :
    f (contactMoment u) =
      contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (contactSeparatorMatrix f *ᵥ u) := by
  -- Decode the Hilbert-space duality pairing coordinatewise and collect the matrix coordinates.
  calc
    f (contactMoment u) =
        inner ℝ ((InnerProductSpace.toDual ℝ (ContactMomentSpace n)).symm f)
          (contactMoment u) := by
            rw [InnerProductSpace.toDual_symm_apply]
    _ = contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (contactSeparatorMatrix f *ᵥ u) := by
      simp only [contactMoment, contactSeparatorVector, contactSeparatorMatrix, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Matrix.mulVec, dotProduct]
      rw [Fintype.sum_sum_type]
      apply congrArg₂ (fun a b ↦ a + b)
      · refine Finset.sum_congr rfl ?_
        intro i _
        ring
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: evaluating a separator on the
normalized target is the normalized trace of its matrix part. -/
theorem normalizedContactMomentTarget_separator_apply
    {n : ℕ}
    (f : StrongDual ℝ (ContactMomentSpace n)) :
    f (normalizedContactMomentTarget n) =
      (n : ℝ)⁻¹ * Matrix.trace (contactSeparatorMatrix f) := by
  -- Only diagonal matrix coordinates survive in the normalized target moment.
  calc
    f (normalizedContactMomentTarget n) =
        inner ℝ ((InnerProductSpace.toDual ℝ (ContactMomentSpace n)).symm f)
          (normalizedContactMomentTarget n) := by
            rw [InnerProductSpace.toDual_symm_apply]
    _ = (n : ℝ)⁻¹ * Matrix.trace (contactSeparatorMatrix f) := by
      simp only [normalizedContactMomentTarget, contactSeparatorMatrix, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, Matrix.trace, Matrix.diag_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [zero_mul, Finset.sum_const_zero, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a finite convex
representation of the normalized target bounds every point of the normalized body by `n`. -/
theorem euclideanNorm_le_of_target_mem_convexHull
    {n : ℕ}
    (L : Set (Fin n → ℝ))
    (hn : n ≠ 0)
    (htarget : normalizedContactMomentTarget n ∈
      convexHull ℝ (contactMoment '' normalizedSupportingContacts L)) :
    ∀ x ∈ L, euclideanNorm x ≤ n := by
  -- Rebuild the finite contact system encoded by the convex-hull witness and estimate every point
  -- of `L` by the resulting weighted reconstruction formula.
  classical
  rcases mem_convexHull_iff_exists_fintype.mp htarget with
    ⟨ι, hι, w, z, hw_nonneg, hw_sum, hz, hmoment⟩
  -- Local instance justification: convex-hull membership returns its finite indexing structure as
  -- explicit data, and the following coordinate sums must register precisely that witness.
  letI : Fintype ι := hι
  choose u hu_contact hzu using hz
  have hmoment' :
      ∑ i, w i • contactMoment (u i) = normalizedContactMomentTarget n := by
    -- Replace each abstract generator by its chosen supporting contact.
    simpa only [hzu] using hmoment
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hbalance_raw :
      ∑ i, ((n : ℝ) * w i) •
        (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) = 0 := by
    -- The vector coordinates of the target vanish, so the rescaled contacts balance.
    ext j
    have hcoordinate :=
      congrArg (fun y : ContactMomentSpace n ↦ (WithLp.ofLp y) (Sum.inl j)) hmoment'
    have hcoordinate_zero : ∑ i, w i * u i j = 0 := by
      -- Read off the vanishing vector coordinate of the target moment.
      simpa [contactMoment, normalizedContactMomentTarget, Pi.smul_apply, smul_eq_mul]
        using hcoordinate
    -- Pull the common factor `n` out of the coordinate sum and use the target vanishing.
    calc
      (∑ i, ((n : ℝ) * w i) •
          (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) j =
          ∑ i, ((n : ℝ) * w i) * u i j := by
            simp [Pi.smul_apply, smul_eq_mul]
      _ = (n : ℝ) * ∑ i, w i * u i j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = 0 := by rw [hcoordinate_zero, mul_zero]
  have hmatrix_raw (j k : Fin n) :
      ∑ i, ((n : ℝ) * w i) * (u i j * u i k) = if j = k then 1 else 0 := by
    -- The matrix coordinates of the target are the normalized identity matrix.
    have hcoordinate :=
      congrArg (fun y : ContactMomentSpace n ↦ (WithLp.ofLp y) (Sum.inr (j, k))) hmoment'
    have hcoordinate_matrix :
        ∑ i, w i * (u i j * u i k) = if j = k then (n : ℝ)⁻¹ else 0 := by
      -- Read off the normalized identity matrix coordinates of the target moment.
      simpa [contactMoment, normalizedContactMomentTarget, Pi.smul_apply, smul_eq_mul]
        using hcoordinate
    calc
      ∑ i, ((n : ℝ) * w i) * (u i j * u i k) =
          (n : ℝ) * ∑ i, w i * (u i j * u i k) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = (n : ℝ) * (if j = k then (n : ℝ)⁻¹ else 0) := by rw [hcoordinate_matrix]
      _ = if j = k then 1 else 0 := by
        split_ifs
        · exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)
        · simp
  have hreconstruct_raw :
      ∀ x : EuclideanSpace ℝ (Fin n),
        x =
          ∑ i,
            (((n : ℝ) * w i) *
              inner ℝ x (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) •
              (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) := by
    intro x
    -- The matrix coordinates reconstruct each vector after expanding the Euclidean inner product.
    ext j
    calc
      x j = ∑ k, x k * (if k = j then 1 else 0) := by simp
      _ = ∑ k, x k * ∑ i, ((n : ℝ) * w i) * (u i k * u i j) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [hmatrix_raw]
      _ = ∑ k, ∑ i, x k * (((n : ℝ) * w i) * (u i k * u i j)) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ k, x k * (((n : ℝ) * w i) * (u i k * u i j)) := by
        rw [Finset.sum_comm]
      _ = ∑ i, ((n : ℝ) * w i * u i j) * ∑ k, x k * u i k := by
        refine Finset.sum_congr rfl ?_
        intro i _
        calc
          ∑ k, x k * (((n : ℝ) * w i) * (u i k * u i j)) =
              ∑ k, (((n : ℝ) * w i * u i j) * (x k * u i k)) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                ring
          _ = ((n : ℝ) * w i * u i j) * ∑ k, x k * u i k := by
                rw [Finset.mul_sum]
      _ = ∑ i, (((n : ℝ) * w i) * ∑ k, x k * u i k) * u i j := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      _ = ∑ i, (((n : ℝ) * w i) *
          inner ℝ x (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) * u i j := by
        refine Finset.sum_congr rfl ?_
        intro i _
        congr 2
        simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      _ = (∑ i, (((n : ℝ) * w i) *
          inner ℝ x (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) •
            (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) j := by
        simp [Pi.smul_apply, smul_eq_mul]
  have hweight_nonneg : ∀ i, 0 ≤ (n : ℝ) * w i := by
    intro i
    exact mul_nonneg hn_pos.le (hw_nonneg i)
  have hweight_sum : ∑ i, (n : ℝ) * w i = n := by
    -- Rescaling convex weights by `n` gives total John weight `n`.
    calc
      ∑ i, (n : ℝ) * w i = (n : ℝ) * ∑ i, w i := by
        rw [← Finset.mul_sum]
      _ = n := by rw [hw_sum, mul_one]
  intro x hx
  let x' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hsupport (i : ι) :
      inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) ≤ 1 := by
    -- Each chosen generator is a genuine supporting contact of `L`.
    have hu := (hu_contact i).2 x hx
    simpa only [x', PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      dotProduct, mul_comm] using hu
  have hshift :
      x' = ∑ i, (((n : ℝ) * w i) *
        (inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) - 1)) •
          (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) := by
    -- Subtract the balanced contact sum from the reconstruction identity.
    calc
      x' = ∑ i, (((n : ℝ) * w i) *
          inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) •
            (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) :=
        hreconstruct_raw x'
      _ = (∑ i, (((n : ℝ) * w i) *
          inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) •
            (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) -
          ∑ i, ((n : ℝ) * w i) •
            (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) := by
              rw [hbalance_raw, sub_zero]
      _ = ∑ i, (((n : ℝ) * w i) *
          (inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) - 1)) •
            (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [← sub_smul]
              congr 1
              ring
  have hinner_sum :
      ∑ i, ((n : ℝ) * w i) *
        inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) = 0 := by
    -- Pair the balance identity with `x'` and distribute the inner product over the sum.
    calc
      ∑ i, ((n : ℝ) * w i) *
          inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) =
          inner ℝ x' (∑ i, ((n : ℝ) * w i) •
            (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) := by
              simp only [inner_sum, inner_smul_right]
      _ = 0 := by rw [hbalance_raw, inner_zero_right]
  have hcoefficient_nonpos (i : ι) :
      ((n : ℝ) * w i) *
        (inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hweight_nonneg i) (sub_nonpos.mpr (hsupport i))
  have hcoefficient_sum :
      ∑ i, ((n : ℝ) * w i) *
        (1 - inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) = n := by
    -- Balance cancels the inner-product terms in the sum of absolute coefficients.
    calc
      ∑ i, ((n : ℝ) * w i) *
          (1 - inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) =
          (∑ i, (n : ℝ) * w i) -
            ∑ i, ((n : ℝ) * w i) *
              inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl ?_
                intro i _
                ring
      _ = n := by rw [hweight_sum, hinner_sum, sub_zero]
  -- The triangle inequality and unit contact norms turn reconstruction into the total weight.
  calc
    euclideanNorm x = ‖x'‖ := rfl
    _ = ‖∑ i, (((n : ℝ) * w i) *
        (inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) - 1)) •
          (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))‖ := congrArg norm hshift
    _ ≤ ∑ i, ‖(((n : ℝ) * w i) *
        (inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n)) - 1)) •
          (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))‖ := norm_sum_le _ _
    _ = ∑ i, ((n : ℝ) * w i) *
        (1 - inner ℝ x' (WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hcontact_norm : ‖(WithLp.toLp 2 (u i) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
        simpa [euclideanNorm] using (hu_contact i).1
      rw [norm_smul, hcontact_norm, mul_one, Real.norm_eq_abs,
        abs_of_nonpos (hcoefficient_nonpos i)]
      ring
    _ ≤ n := by
      exact le_of_eq hcoefficient_sum

/-- Helper for Theorem 9.7: the ellipsoid-side flatness constant appearing before the final factor
of `n` is transported back to the ambient convex body. -/
noncomputable def ellipsoidFlatnessBound (n : ℕ) : ℝ :=
  (n : ℝ) * Real.rpow 2 (((n * (n - 1) : ℕ) : ℝ) / 4)

/-- Helper for Theorem 9.7: multiplying the ellipsoid-side constant by `n + 1` recovers the public
Chapter 9 flatness constant. -/
theorem flatDirectionBound_eq_mul_ellipsoidFlatnessBound
    (n : ℕ) :
    (n + 1 : ℝ) * ellipsoidFlatnessBound n = flat_direction_bound n := by
  -- Separate the theorem-side constant into the ellipsoid factor and the outer scaling factor.
  simp only [ellipsoidFlatnessBound, flat_direction_bound]
  ring

/-- Helper for Theorem 9.7: lattice-freeness of `euclideanEllipsoid C a` is exactly the statement
that every integer translate of the center misses the closed unit ball after applying `C`. -/
theorem not_containsIntegralPoint_iff_translateAvoidsClosedUnitBall
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    ¬ contains_integral_point (euclideanEllipsoid C a) ↔
      ∀ z : Fin n → ℤ, 1 < euclideanNorm (C *ᵥ (Int.cast ∘ z) - C *ᵥ a) := by
  constructor
  · intro hfree z
    have hz_not_mem : Int.cast ∘ z ∉ euclideanEllipsoid C a := by
      intro hz
      exact hfree (contains_integral_point_iff.mpr ⟨z, hz⟩)
    by_contra hnorm
    have hnorm' : euclideanNorm (C *ᵥ (Int.cast ∘ z) - C *ᵥ a) ≤ 1 :=
      le_of_not_gt hnorm
    -- Repackage the translated norm bound as ellipsoid membership for the integer vector `z`.
    apply hz_not_mem
    simpa [euclideanEllipsoid, Matrix.mulVec_sub] using hnorm'
  · intro havoid hcontains
    rcases contains_integral_point_iff.mp hcontains with ⟨z, hz⟩
    have hz_norm : euclideanNorm (C *ᵥ (Int.cast ∘ z) - C *ᵥ a) ≤ 1 := by
      -- Rewrite the ellipsoid membership hypothesis into the translated closed-ball inequality.
      simpa [euclideanEllipsoid, Matrix.mulVec_sub] using hz
    linarith [havoid z]

/-- Helper for Theorem 9.7: centered dilation acts affinely on the directional linear form. -/
theorem integralDirectionLinearForm_centerDilate
    {n : ℕ}
    (d : Fin n → ℤ)
    (a x : Fin n → ℝ)
    (t : ℝ) :
    integral_direction_linear_form d (a + t • (x - a)) =
      t * integral_direction_linear_form d x +
        (1 - t) * integral_direction_linear_form d a := by
  -- Expand the centered dilation into translation plus a scaled displacement.
  calc
    integral_direction_linear_form d (a + t • (x - a))
        = integral_direction_linear_form d a +
            integral_direction_linear_form d (t • (x - a)) := by
            simp [integral_direction_linear_form, dotProduct_add]
    _ = integral_direction_linear_form d a +
          t * integral_direction_linear_form d (x - a) := by
            simp [integral_direction_linear_form, dotProduct_smul]
    _ = integral_direction_linear_form d a +
          t * (integral_direction_linear_form d x - integral_direction_linear_form d a) := by
            simp [integral_direction_linear_form, dotProduct_sub]
    _ = t * integral_direction_linear_form d x +
          (1 - t) * integral_direction_linear_form d a := by
            ring

/-- Helper for Theorem 9.7: on a nonempty compact set, centered dilation by a nonnegative factor
multiplies directional width by that factor. -/
theorem directionalWidth_image_centerDilate
    {n : ℕ}
    {E : Set (Fin n → ℝ)}
    (hE_nonempty : E.Nonempty)
    (hE_compact : IsCompact E)
    {a : Fin n → ℝ}
    {t : ℝ}
    (ht : 0 ≤ t)
    (d : Fin n → ℤ) :
    directional_width (((fun x ↦ a + t • (x - a)) '' E)) d = t * directional_width E d := by
  let imageSet : Set ℝ := integral_direction_linear_form d '' E
  let offset : ℝ := (1 - t) * integral_direction_linear_form d a
  let dilatedImage : Set ℝ := (fun y : ℝ ↦ t * y + offset) '' imageSet
  have himage :
      integral_direction_linear_form d '' ((fun x ↦ a + t • (x - a)) '' E) = dilatedImage := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨integral_direction_linear_form d z, ⟨z, hz, rfl⟩, ?_⟩
      simp [offset, integralDirectionLinearForm_centerDilate]
    · rintro ⟨u, ⟨z, hz, rfl⟩, hy⟩
      refine ⟨a + t • (z - a), ⟨z, hz, rfl⟩, ?_⟩
      simpa [dilatedImage, offset, integralDirectionLinearForm_centerDilate] using hy
  have himage_nonempty : imageSet.Nonempty := by
    rcases hE_nonempty with ⟨x, hx⟩
    exact ⟨integral_direction_linear_form d x, ⟨x, hx, rfl⟩⟩
  have himage_compact : IsCompact imageSet := by
    have hcont : Continuous (integral_direction_linear_form d) := by
      -- The directional linear form is a finite sum of continuous coordinate projections.
      simpa [integral_direction_linear_form, dotProduct] using
        (continuous_finsetSum Finset.univ fun i _ =>
          continuous_const.mul (continuous_apply i))
    simpa [imageSet] using hE_compact.image hcont
  rcases himage_compact.exists_isMaxOn himage_nonempty continuous_id.continuousOn with
    ⟨ymax, hymax_mem, hymax_max⟩
  rcases himage_compact.exists_isMinOn himage_nonempty continuous_id.continuousOn with
    ⟨ymin, hymin_mem, hymin_min⟩
  have hsup_image : sSup imageSet = ymax := by
    apply le_antisymm
    · refine csSup_le himage_nonempty ?_
      intro y hy
      exact (isMaxOn_iff.mp hymax_max) y hy
    · exact le_csSup himage_compact.bddAbove hymax_mem
  have hinf_image : sInf imageSet = ymin := by
    apply le_antisymm
    · exact csInf_le himage_compact.bddBelow hymin_mem
    · exact le_csInf himage_nonempty fun y hy ↦ (isMinOn_iff.mp hymin_min) y hy
  have hdilated_nonempty : dilatedImage.Nonempty := by
    exact himage_nonempty.image (fun y : ℝ ↦ t * y + offset)
  have hdilated_compact : IsCompact dilatedImage := by
    have hcont : Continuous fun y : ℝ ↦ t * y + offset := by
      exact (continuous_const.mul continuous_id).add continuous_const
    simpa [dilatedImage] using himage_compact.image hcont
  have hsup_dilated : sSup dilatedImage = t * ymax + offset := by
    apply le_antisymm
    · refine csSup_le hdilated_nonempty ?_
      rintro y ⟨u, hu, rfl⟩
      have hu_le : u ≤ ymax := (isMaxOn_iff.mp hymax_max) u hu
      nlinarith
    · exact le_csSup hdilated_compact.bddAbove ⟨ymax, hymax_mem, rfl⟩
  have hinf_dilated : sInf dilatedImage = t * ymin + offset := by
    apply le_antisymm
    · exact csInf_le hdilated_compact.bddBelow ⟨ymin, hymin_mem, rfl⟩
    · exact le_csInf hdilated_nonempty fun y hy ↦ by
        rcases hy with ⟨u, hu, rfl⟩
        have hmin_le : ymin ≤ u := (isMinOn_iff.mp hymin_min) u hu
        nlinarith
  -- Rewrite both extrema through the affine image description and cancel the common offset term.
  calc
    directional_width (((fun x ↦ a + t • (x - a)) '' E)) d
        = sSup dilatedImage - sInf dilatedImage := by
            simp [directional_width, himage, dilatedImage]
    _ = (t * ymax + offset) - (t * ymin + offset) := by rw [hsup_dilated, hinf_dilated]
    _ = t * (ymax - ymin) := by ring
    _ = t * directional_width E d := by
          rw [directional_width, hsup_image, hinf_image]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: with the ambient sup norm,
the diagonal width of the two-dimensional unit “ellipsoid” is four. -/
theorem directionalWidth_unitSquare_diagonal :
    directional_width
        ({x : Fin 2 → ℝ | ‖x‖ ≤ 1} : Set (Fin 2 → ℝ))
        (fun _ ↦ 1) = 4 := by
  have himage :
      integral_direction_linear_form (fun _ : Fin 2 ↦ (1 : ℤ)) ''
          ({x : Fin 2 → ℝ | ‖x‖ ≤ 1} : Set (Fin 2 → ℝ)) =
        Set.Icc (-2 : ℝ) 2 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxnorm : ‖x‖ ≤ (1 : ℝ) := by
        simpa using hx
      have hxcoord : ∀ i, |x i| ≤ (1 : ℝ) := by
        intro i
        simpa [Real.norm_eq_abs] using
          (norm_le_pi_norm x i |>.trans hxnorm)
      have hxzero := hxcoord 0
      have hxone := hxcoord 1
      -- The two coordinate bounds add to the sharp diagonal bounds for the square.
      simp only [Set.mem_Icc]
      simp [integral_direction_linear_form, dotProduct, Fin.sum_univ_two]
      constructor
      · rw [abs_le] at hxzero hxone
        linarith
      · rw [abs_le] at hxzero hxone
        linarith
    · intro hy
      refine ⟨fun _ ↦ y / 2, ?_, ?_⟩
      · have hybounds : (-2 : ℝ) ≤ y ∧ y ≤ 2 := by
          simpa only [Set.mem_Icc] using hy
        simp only [Set.mem_setOf_eq]
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        simp only [Real.norm_eq_abs]
        rw [abs_le]
        constructor
        · linarith
        · linarith
      · -- The constant vector `y / 2` realizes every value in the interval `[-2,2]`.
        simp only [integral_direction_linear_form, Function.comp_apply, Int.cast_one,
          one_mul, dotProduct, Fin.sum_univ_two]
        ring
  -- The extrema of `[-2,2]` are its endpoints.
  norm_num [directional_width, himage]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the proposed dual sup-norm
expression equals two for the identity matrix and diagonal integral direction in dimension two. -/
theorem two_mul_dualNorm_unitSquare_diagonal :
    2 * ‖((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose)⁻¹ *ᵥ
      (Int.cast ∘ fun _ : Fin 2 ↦ (1 : ℤ))‖ = 2 := by
  -- Matrix normalization leaves the constant-one vector, whose sup norm is one.
  norm_num [Pi.norm_def, Finset.sup_const Finset.univ_nonempty]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the claimed ellipsoid-width
formula fails for the identity matrix and diagonal direction in dimension two. -/
theorem directionalWidth_unitSquare_diagonal_ne_two_mul_dualNorm :
    directional_width
        ({x : Fin 2 → ℝ | ‖x‖ ≤ 1} : Set (Fin 2 → ℝ))
        (fun _ ↦ 1) ≠
      2 * ‖((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose)⁻¹ *ᵥ
        (Int.cast ∘ fun _ : Fin 2 ↦ (1 : ℤ))‖ := by
  -- The two preceding exact computations reduce the mismatch to `4 ≠ 2`.
  rw [directionalWidth_unitSquare_diagonal, two_mul_dualNorm_unitSquare_diagonal]
  norm_num

/-- Helper for Theorem 9.7: the width of `euclideanEllipsoid C a` in direction `d` is controlled
by the dual norm of the transformed integer vector. -/
theorem directionalWidth_euclideanEllipsoid_eq_two_mul_dualNorm
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hdet : IsUnit C.det)
    (d : Fin n → ℤ) :
    directional_width (euclideanEllipsoid C a) d =
      2 * euclideanNorm ((C.transpose)⁻¹ *ᵥ (Int.cast ∘ d)) := by
  classical
  -- Route correction: the ellipsoid now uses the explicit `ℓ2` norm, so Cauchy–Schwarz computes
  -- its support function without confusing it with the ambient function-space sup norm.
  let dℝ : Fin n → ℝ := Int.cast ∘ d
  let v : Fin n → ℝ := (C.transpose)⁻¹ *ᵥ dℝ
  let r : ℝ := euclideanNorm v
  let base : ℝ := integral_direction_linear_form d a
  let imageSet : Set ℝ := integral_direction_linear_form d '' euclideanEllipsoid C a
  have htranspose : IsUnit C.transpose.det := Matrix.isUnit_det_transpose C hdet
  have hrecover : C.transpose *ᵥ v = dℝ := by
    -- Nonsingularity recovers the original direction from its inverse-transpose image.
    calc
      C.transpose *ᵥ v =
          (C.transpose * (C.transpose)⁻¹) *ᵥ dℝ := by
            rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ dℝ := by
            rw [Matrix.mul_nonsing_inv _ htranspose]
      _ = dℝ := by simp
  have hfunctional (x : Fin n → ℝ) :
      integral_direction_linear_form d x =
        base + v ⬝ᵥ (C *ᵥ (x - a)) := by
    -- Move the integral functional through `Cᵀ` and split off the center.
    calc
      integral_direction_linear_form d x =
          integral_direction_linear_form d (a + (x - a)) := by
            congr 1
            ext i
            simp
      _ = integral_direction_linear_form d a +
          integral_direction_linear_form d (x - a) := by
            simp only [integral_direction_linear_form, dotProduct_add]
      _ = base + dℝ ⬝ᵥ (x - a) := rfl
      _ = base + (C.transpose *ᵥ v) ⬝ᵥ (x - a) := by rw [hrecover]
      _ = base + v ⬝ᵥ (C *ᵥ (x - a)) := by
            rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  by_cases hv : v = 0
  · have himage : imageSet = {base} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        -- A zero transformed direction makes the functional constant on the ellipsoid.
        simp [hfunctional, hv]
      · intro hy
        have hybase : y = base := by simpa using hy
        subst y
        exact ⟨a, center_mem_euclideanEllipsoid C a, rfl⟩
    -- Both support extrema of a singleton coincide, while the transformed norm vanishes.
    change directional_width (euclideanEllipsoid C a) d = 2 * euclideanNorm v
    simp [directional_width, imageSet, himage, hv, euclideanNorm]
  · have hr_pos : 0 < r := by
      exact lt_of_le_of_ne (euclideanNorm_nonneg v)
        (Ne.symm (by simpa [r] using euclideanNorm_eq_zero.not.mpr hv))
    have hpointBounds (x : Fin n → ℝ) (hx : x ∈ euclideanEllipsoid C a) :
        base - r ≤ integral_direction_linear_form d x ∧
          integral_direction_linear_form d x ≤ base + r := by
      have hxnorm : euclideanNorm (C *ᵥ (x - a)) ≤ 1 := hx
      have habs : |v ⬝ᵥ (C *ᵥ (x - a))| ≤ r := by
        calc
          |v ⬝ᵥ (C *ᵥ (x - a))| ≤
              euclideanNorm v * euclideanNorm (C *ᵥ (x - a)) :=
            abs_dotProduct_le_euclideanNorm_mul _ _
          _ ≤ r * 1 := by
            exact mul_le_mul_of_nonneg_left hxnorm (euclideanNorm_nonneg v)
          _ = r := by simp
      rw [hfunctional]
      constructor
      · linarith [neg_le_of_abs_le habs]
      · linarith [le_of_abs_le habs]
    let w : Fin n → ℝ := r⁻¹ • v
    have hw_norm : euclideanNorm w = 1 := by
      calc
        euclideanNorm w = |r⁻¹| * euclideanNorm v := euclideanNorm_smul _ _
        _ = r⁻¹ * r := by rw [abs_of_pos (inv_pos.mpr hr_pos)]
        _ = 1 := inv_mul_cancel₀ hr_pos.ne'
    have hvw : v ⬝ᵥ w = r := by
      calc
        v ⬝ᵥ w = r⁻¹ * (v ⬝ᵥ v) := by
          simp only [w, dotProduct_smul, smul_eq_mul]
        _ = r⁻¹ * euclideanNorm v ^ 2 := by
          rw [dotProduct_self_eq_euclideanNorm_sq]
        _ = r⁻¹ * r ^ 2 := rfl
        _ = r := by field_simp
    let xmax : Fin n → ℝ := a + C⁻¹ *ᵥ w
    let xmin : Fin n → ℝ := a + C⁻¹ *ᵥ (-w)
    have hC_xmax : C *ᵥ (xmax - a) = w := by
      calc
        C *ᵥ (xmax - a) = C *ᵥ (C⁻¹ *ᵥ w) := by simp [xmax]
        _ = (C * C⁻¹) *ᵥ w := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ w := by
          rw [Matrix.mul_nonsing_inv _ hdet]
        _ = w := by simp
    have hC_xmin : C *ᵥ (xmin - a) = -w := by
      calc
        C *ᵥ (xmin - a) = C *ᵥ (C⁻¹ *ᵥ (-w)) := by simp [xmin]
        _ = (C * C⁻¹) *ᵥ (-w) := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (-w) := by
          rw [Matrix.mul_nonsing_inv _ hdet]
        _ = -w := by simp
    have hxmax_mem : xmax ∈ euclideanEllipsoid C a := by
      -- The positive normalized dual vector lies on the Euclidean unit sphere.
      change euclideanNorm (C *ᵥ (xmax - a)) ≤ 1
      rw [hC_xmax, hw_norm]
    have hxmin_mem : xmin ∈ euclideanEllipsoid C a := by
      -- Its negative gives the opposite support point.
      change euclideanNorm (C *ᵥ (xmin - a)) ≤ 1
      rw [hC_xmin]
      simpa [euclideanNorm] using hw_norm.le
    have hxmax_value : integral_direction_linear_form d xmax = base + r := by
      rw [hfunctional, hC_xmax, hvw]
    have hxmin_value : integral_direction_linear_form d xmin = base - r := by
      rw [hfunctional, hC_xmin, dotProduct_neg, hvw]
      ring
    have hmax_mem : base + r ∈ imageSet := ⟨xmax, hxmax_mem, hxmax_value⟩
    have hmin_mem : base - r ∈ imageSet := ⟨xmin, hxmin_mem, hxmin_value⟩
    have hupper : ∀ y ∈ imageSet, y ≤ base + r := by
      rintro y ⟨x, hx, rfl⟩
      exact (hpointBounds x hx).2
    have hlower : ∀ y ∈ imageSet, base - r ≤ y := by
      rintro y ⟨x, hx, rfl⟩
      exact (hpointBounds x hx).1
    have hsup : sSup imageSet = base + r := by
      apply le_antisymm
      · exact csSup_le ⟨base + r, hmax_mem⟩ hupper
      · exact le_csSup ⟨base + r, hupper⟩ hmax_mem
    have hinf : sInf imageSet = base - r := by
      apply le_antisymm
      · exact csInf_le ⟨base - r, hlower⟩ hmin_mem
      · exact le_csInf ⟨base - r, hmin_mem⟩ hlower
    -- Subtracting the exact support extrema gives twice the transformed Euclidean norm.
    calc
      directional_width (euclideanEllipsoid C a) d = sSup imageSet - sInf imageSet := rfl
      _ = (base + r) - (base - r) := by rw [hsup, hinf]
      _ = 2 * r := by ring
      _ = 2 * euclideanNorm ((C.transpose)⁻¹ *ᵥ (Int.cast ∘ d)) := rfl

/-- Helper for Theorem 9.7: translated unit-ball avoidance produces a short nonzero dual lattice
vector in positive dimension. -/
theorem existsShortDualVector_of_translateAvoidsUnitBall
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℚ)
    (u : Fin n → ℝ)
    (hn : n ≠ 0)
    (hdet : IsUnit C.det)
    (havoid : ∀ z : Fin n → ℤ,
      1 < euclideanNorm (C.map (Rat.castHom ℝ) *ᵥ (Int.cast ∘ z) - u)) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧
        2 * euclideanNorm (((C.map (Rat.castHom ℝ)).transpose)⁻¹ *ᵥ (Int.cast ∘ d)) ≤
          ellipsoidFlatnessBound n := by
  -- Route correction: reuse the canonical transformed-lattice theorem and normalize only the
  -- support-local names for its Euclidean norm and numerical bound.
  simpa only [euclideanNorm, ellipsoidFlatnessBound] using
    FlatnessTransference.existsShortInverseTransposeIntegerVector C u hn hdet havoid

/-- Helper for Theorem 9.7: a normalized Euclidean-norm bound turns a feasible direct affine ball
into a centered covering of the ambient convex body by its `n`-dilate. -/
theorem directAffineEuclideanBall_cover_of_normalizedBody_subset
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hn : n ≠ 0)
    (hA_unit : IsUnit A.det)
    (hnorm : ∀ u ∈ normalizedBody K A a, euclideanNorm u ≤ n) :
    (K : Set (Fin n → ℝ)) ⊆
      ((fun x ↦ a + (n : ℝ) • (x - a)) '' directAffineEuclideanBall A a) := by
  intro x hxK
  let u : Fin n → ℝ := A⁻¹ *ᵥ (x - a)
  have hu_mem : u ∈ normalizedBody K A a := by
    -- Pull the ambient point back through the inverse affine coordinates of the direct ball.
    change a + A *ᵥ u ∈ (K : Set (Fin n → ℝ))
    have hmul : A * A⁻¹ = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.mul_nonsing_inv _ hA_unit
    dsimp [u]
    simpa [Matrix.mulVec_mulVec, hmul] using hxK
  have hu_norm : euclideanNorm u ≤ n := hnorm u hu_mem
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let v : Fin n → ℝ := (n : ℝ)⁻¹ • u
  have hv_norm : euclideanNorm v ≤ 1 := by
    -- Rescale the normalized coordinate into the Euclidean unit ball.
    calc
      euclideanNorm v = |(n : ℝ)⁻¹| * euclideanNorm u := by
        dsimp [v]
        rw [euclideanNorm_smul]
      _ = (n : ℝ)⁻¹ * euclideanNorm u := by
        rw [abs_of_pos (inv_pos.mpr hn_pos)]
      _ ≤ (n : ℝ)⁻¹ * n := by
        exact mul_le_mul_of_nonneg_left hu_norm (inv_nonneg.mpr hn_pos.le)
      _ = 1 := by
        field_simp [Nat.cast_ne_zero.mpr hn]
  refine ⟨a + A *ᵥ v, ⟨v, hv_norm, rfl⟩, ?_⟩
  have hscale : (n : ℝ) • v = u := by
    -- Multiply back by `n` to recover the original normalized coordinate.
    dsimp [v]
    simp [smul_smul, Nat.cast_ne_zero.mpr hn]
  have hx_repr : a + A *ᵥ u = x := by
    -- The inverse affine coordinate map reconstructs the original point.
    have hmul : A * A⁻¹ = (1 : Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.mul_nonsing_inv _ hA_unit
    dsimp [u]
    calc
      a + A *ᵥ (A⁻¹ *ᵥ (x - a)) = a + (A * A⁻¹) *ᵥ (x - a) := by
        rw [← Matrix.mulVec_mulVec]
      _ = a + (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (x - a) := by
        rw [hmul]
      _ = x := by
        simp
  -- Substitute the rescaled witness into the centered dilation formula.
  calc
    a + (n : ℝ) • ((a + A *ᵥ v) - a) = a + (n : ℝ) • (A *ᵥ v) := by
      simp
    _ = a + A *ᵥ ((n : ℝ) • v) := by
      rw [← Matrix.mulVec_smul]
    _ = a + A *ᵥ u := by
      rw [hscale]
    _ = x := hx_repr

/-- Helper for Theorem 9.7: once the normalized contact moment lies in the supporting-contact
convex hull, the original determinant-maximal direct affine ball satisfies the real John
`n`-sandwich. -/
theorem directAffineEuclideanBall_sandwich_of_target_mem_convexHull
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hn : n ≠ 0)
    (hA_unit : IsUnit A.det)
    (hAK : directAffineEuclideanBall A a ⊆ (K : Set (Fin n → ℝ)))
    (htarget : normalizedContactMomentTarget n ∈
      convexHull ℝ (contactMoment '' normalizedSupportingContacts (normalizedBody K A a))) :
    directAffineEuclideanBall A a ⊆ (K : Set (Fin n → ℝ)) ∧
      (K : Set (Fin n → ℝ)) ⊆
        ((fun x ↦ a + (n : ℝ) • (x - a)) '' directAffineEuclideanBall A a) := by
  refine ⟨hAK, ?_⟩
  -- Feed the convex-hull contact-moment witness into the normalized-body norm bound.
  exact directAffineEuclideanBall_cover_of_normalizedBody_subset
    K A a hn hA_unit
    (euclideanNorm_le_of_target_mem_convexHull (normalizedBody K A a) hn htarget)

/-- Helper for Theorem 9.7: shrinking a real John direct affine ball preserves inclusion in the
body and upgrades the outer scaling factor from `n` to `n + 1` once the shrink is large enough. -/
theorem scaledDirectAffineEuclideanBall_subset_and_cover
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    {K : Set (Fin n → ℝ)}
    {σ : ℝ}
    (hσ_pos : 0 < σ)
    (hσ_le_one : σ ≤ 1)
    (hσ_large : (n : ℝ) ≤ (n + 1 : ℝ) * σ)
    (hsubset : directAffineEuclideanBall A a ⊆ K)
    (hcover : K ⊆ ((fun x ↦ a + (n : ℝ) • (x - a)) '' directAffineEuclideanBall A a)) :
    directAffineEuclideanBall (σ • A) a ⊆ K ∧
      K ⊆ ((fun x ↦ a + (n + 1 : ℝ) • (x - a)) '' directAffineEuclideanBall (σ • A) a) := by
  -- Shrink the direct ball on the inner side, then compensate for that shrink in the outer
  -- dilation witness.
  constructor
  · intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    apply hsubset
    refine ⟨σ • u, ?_, ?_⟩
    · -- The shrunken witness still lies in the original unit ball.
      have hu_norm : euclideanNorm u ≤ 1 := by
        simpa using hu
      calc
        euclideanNorm (σ • u) = |σ| * euclideanNorm u := euclideanNorm_smul _ _
        _ = σ * euclideanNorm u := by
          rw [abs_of_nonneg hσ_pos.le]
        _ ≤ σ * 1 := by
          exact mul_le_mul_of_nonneg_left hu_norm hσ_pos.le
        _ ≤ 1 := by
          nlinarith [hσ_le_one, hσ_pos.le]
    · -- Reassociate the scalar through the matrix-vector multiplication.
      simp [Matrix.smul_mulVec, Matrix.mulVec_smul]
  · intro x hx
    rcases hcover hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨u, hu, rfl⟩
    let t : ℝ := (n : ℝ) / ((n + 1 : ℝ) * σ)
    have hden_pos : 0 < (n + 1 : ℝ) * σ := by
      positivity
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      positivity
    have ht_le_one : t ≤ 1 := by
      dsimp [t]
      rw [div_le_iff₀ hden_pos]
      nlinarith [hσ_large, hσ_pos.le]
    have ht_scale : ((n + 1 : ℝ) * σ) * t = n := by
      dsimp [t]
      field_simp [hden_pos.ne']
    refine ⟨a + (σ • A) *ᵥ (t • u), ?_, ?_⟩
    · -- The outer witness uses the same unit-ball point after the compensating rescaling.
      refine ⟨t • u, ?_, rfl⟩
      have hu_norm : euclideanNorm u ≤ 1 := by
        simpa using hu
      calc
        euclideanNorm (t • u) = |t| * euclideanNorm u := euclideanNorm_smul _ _
        _ = t * euclideanNorm u := by
          rw [abs_of_nonneg ht_nonneg]
        _ ≤ t * 1 := by
          exact mul_le_mul_of_nonneg_left hu_norm ht_nonneg
        _ ≤ 1 := by
          nlinarith [ht_le_one, ht_nonneg]
    · -- Expanding the centered `(n + 1)`-dilate recovers the original `n`-cover point.
      change
        a + (n + 1 : ℝ) • ((a + (σ • A) *ᵥ (t • u)) - a) =
          a + (n : ℝ) • ((a + A *ᵥ u) - a)
      calc
        a + (n + 1 : ℝ) • ((a + (σ • A) *ᵥ (t • u)) - a) =
            a + (n + 1 : ℝ) • ((σ • A) *ᵥ (t • u)) := by
              simp
        _ = a + (((n + 1 : ℝ) * σ) • (A *ᵥ (t • u))) := by
              simp [Matrix.smul_mulVec, smul_smul]
        _ = a + A *ᵥ ((((n + 1 : ℝ) * σ) * t) • u) := by
              rw [← Matrix.mulVec_smul]
              simp [smul_smul]
        _ = a + A *ᵥ ((n : ℝ) • u) := by
              rw [ht_scale]
        _ = a + (n : ℝ) • (A *ᵥ u) := by
              rw [Matrix.mulVec_smul]
        _ = a + (n : ℝ) • ((a + A *ᵥ u) - a) := by
              simp

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: every nonsingular real shape
matrix admits arbitrarily close nonsingular rational approximations. -/
theorem existsNonsingularRationalMatrixNear
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB_unit : IsUnit B.det)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : Matrix (Fin n) (Fin n) ℚ,
      IsUnit C.det ∧ dist (C.map (Rat.castHom ℝ)) B < ε := by
  let castMatrix : Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℝ :=
    fun C ↦ C.map (Rat.castHom ℝ)
  have hdense : DenseRange castMatrix := by
    -- Rational matrices are dense because every entry can be approximated independently.
    simpa [castMatrix, Matrix.map_apply] using
      (DenseRange.piMap fun _ : Fin n ↦
        DenseRange.piMap fun _ : Fin n ↦ Rat.denseRange_cast)
  have hdet_cont : Continuous fun M : Matrix (Fin n) (Fin n) ℝ ↦ M.det :=
    continuous_id.matrix_det
  have hunit_open : IsOpen {M : Matrix (Fin n) (Fin n) ℝ | IsUnit M.det} := by
    -- The determinant avoids `0` on the open nonsingular locus.
    have hne_open : IsOpen ({r : ℝ | r ≠ 0} : Set ℝ) :=
      isClosed_singleton.isOpen_compl
    simpa [isUnit_iff_ne_zero] using hdet_cont.isOpen_preimage _ hne_open
  let targetSet : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | IsUnit M.det} ∩ Metric.ball B ε
  have htarget_open : IsOpen targetSet := by
    -- Intersect the invertible locus with the open metric ball around `B`.
    exact hunit_open.inter (Metric.isOpen_ball : IsOpen (Metric.ball B ε))
  have htarget_nonempty : targetSet.Nonempty := by
    -- The original matrix lies in this open neighborhood.
    refine ⟨B, hB_unit, ?_⟩
    simpa [Metric.mem_ball] using hε
  rcases hdense.exists_mem_open htarget_open htarget_nonempty with ⟨C, hC⟩
  have hC_unit_real : IsUnit ((C.map (Rat.castHom ℝ)).det) := hC.1
  have hC_det_map :
      (C.map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) C.det :=
    ((Rat.castHom ℝ).map_det C).symm
  have hC_unit : IsUnit C.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hC_zero
    apply isUnit_iff_ne_zero.mp hC_unit_real
    rw [hC_det_map]
    simp [hC_zero]
  exact ⟨C, hC_unit, hC.2⟩

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the `ℓ2` operator norm of a
matrix controls the Euclidean norm of its action on coordinate vectors. -/
theorem euclideanNorm_mulVec_le
    {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    euclideanNorm (M *ᵥ x) ≤ ‖M‖ * euclideanNorm x := by
  -- Rewrite the coordinate vector into the Euclidean-space model used by `Matrix.l2_opNorm_mulVec`.
  simpa [euclideanNorm] using
    (Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x))

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: multiplying the midpoint
inverse reference by the original shape matrix collapses to scalar multiplication on vectors. -/
theorem midpointInverse_mulVec_normalize
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_unit : IsUnit A.det)
    (s : ℝ)
    (u : Fin n → ℝ) :
    (((s⁻¹ : ℝ) • A⁻¹) * A) *ᵥ u = s⁻¹ • u := by
  -- Pull the scalar through the matrix product and cancel `A⁻¹ * A`.
  calc
    (((s⁻¹ : ℝ) • A⁻¹) * A) *ᵥ u = ((s⁻¹ : ℝ) • (A⁻¹ * A)) *ᵥ u := by
      rw [Matrix.smul_mul]
    _ = s⁻¹ • ((A⁻¹ * A) *ᵥ u) := by
      rw [Matrix.smul_mulVec]
    _ = s⁻¹ • ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) := by
      rw [Matrix.nonsing_inv_mul _ hA_unit]
    _ = s⁻¹ • u := by
      simp

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a scalar on the direct-ball
shape matrix can be moved outside the resulting matrix action. -/
theorem mulVec_smulMatrix_normalize
    {n : ℕ}
    (C A : Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ)
    (u : Fin n → ℝ) :
    C *ᵥ ((ρ • A) *ᵥ u) = ρ • ((C * A) *ᵥ u) := by
  -- Reassociate the matrix product first, then move the scalar out of the action.
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: if a real matrix `C`
approximates the midpoint inverse shape `s⁻¹ • A⁻¹` closely enough in operator norm, then the
ellipsoid with shape `C` sits between the `σ`- and `τ`-scaled direct balls for `A`. -/
theorem scaledDirectBalls_between_of_nearMidpointInverse
    {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hA_unit : IsUnit A.det)
    {σ s τ : ℝ}
    (hσ_pos : 0 < σ)
    (hσ_lt_s : σ < s)
    (hs_lt_τ : s < τ)
    (happrox :
      ‖C - s⁻¹ • A⁻¹‖ * ‖A‖ < min (σ⁻¹ - s⁻¹) (s⁻¹ - τ⁻¹)) :
    directAffineEuclideanBall (σ • A) a ⊆ euclideanEllipsoid C a ∧
      euclideanEllipsoid C a ⊆ directAffineEuclideanBall (τ • A) a := by
  let D : Matrix (Fin n) (Fin n) ℝ := C - s⁻¹ • A⁻¹
  let δ : ℝ := ‖D‖ * ‖A‖
  have hs_pos : 0 < s := lt_trans hσ_pos hσ_lt_s
  have hτ_pos : 0 < τ := lt_trans hs_pos hs_lt_τ
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hδ_left : δ < σ⁻¹ - s⁻¹ := by
    dsimp [δ, D] at happrox ⊢
    exact lt_of_lt_of_le happrox (min_le_left _ _)
  have hδ_right : δ < s⁻¹ - τ⁻¹ := by
    dsimp [δ, D] at happrox ⊢
    exact lt_of_lt_of_le happrox (min_le_right _ _)
  have hsplit (y : Fin n → ℝ) :
      (C * A) *ᵥ y = s⁻¹ • y + (D * A) *ᵥ y := by
    -- Split `C` into the midpoint inverse reference plus the approximation error.
    calc
      (C * A) *ᵥ y = ((D + s⁻¹ • A⁻¹) * A) *ᵥ y := by
        congr 1
        dsimp [D]
        abel
      _ = (D * A + (s⁻¹ • A⁻¹) * A) *ᵥ y := by
        rw [Matrix.add_mul]
      _ = (D * A) *ᵥ y + ((s⁻¹ • A⁻¹) * A) *ᵥ y := by
        rw [Matrix.add_mulVec]
      _ = s⁻¹ • y + (D * A) *ᵥ y := by
        rw [midpointInverse_mulVec_normalize A hA_unit s y, add_comm]
  have herror_bound (y : Fin n → ℝ) :
      euclideanNorm ((D * A) *ᵥ y) ≤ δ * euclideanNorm y := by
    -- The operator norm of the error matrix controls its action on every vector.
    calc
      euclideanNorm ((D * A) *ᵥ y) ≤ ‖D * A‖ * euclideanNorm y :=
        euclideanNorm_mulVec_le _ _
      _ ≤ (‖D‖ * ‖A‖) * euclideanNorm y := by
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (euclideanNorm_nonneg y)
      _ = δ * euclideanNorm y := by
        rfl
  have hupper (y : Fin n → ℝ) :
      euclideanNorm ((C * A) *ᵥ y) ≤ (s⁻¹ + δ) * euclideanNorm y := by
    -- Compare `C * A` with the scalar map `s⁻¹ • 1` and absorb the error term.
    have hnorm_smul :
        euclideanNorm (s⁻¹ • y) = s⁻¹ * euclideanNorm y := by
      rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hs_pos)]
    have htriangle :
        euclideanNorm (s⁻¹ • y + (D * A) *ᵥ y) ≤
          euclideanNorm (s⁻¹ • y) + euclideanNorm ((D * A) *ᵥ y) := by
      simpa [euclideanNorm] using
        norm_add_le (WithLp.toLp 2 (s⁻¹ • y)) (WithLp.toLp 2 ((D * A) *ᵥ y))
    have herr := herror_bound y
    calc
      euclideanNorm ((C * A) *ᵥ y) = euclideanNorm (s⁻¹ • y + (D * A) *ᵥ y) := by
        rw [hsplit]
      _ ≤ euclideanNorm (s⁻¹ • y) + euclideanNorm ((D * A) *ᵥ y) := htriangle
      _ ≤ s⁻¹ * euclideanNorm y + δ * euclideanNorm y := by
        rw [hnorm_smul]
        linarith
      _ = (s⁻¹ + δ) * euclideanNorm y := by
        ring
  have hlower (y : Fin n → ℝ) :
      (s⁻¹ - δ) * euclideanNorm y ≤ euclideanNorm ((C * A) *ᵥ y) := by
    -- Rewrite the midpoint reference as the difference between the actual action and the error.
    have hnorm_smul :
        euclideanNorm (s⁻¹ • y) = s⁻¹ * euclideanNorm y := by
      rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hs_pos)]
    have herr := herror_bound y
    have hdecomp : s⁻¹ • y = (C * A) *ᵥ y - (D * A) *ᵥ y := by
      rw [hsplit]
      abel
    have htri :
        euclideanNorm (s⁻¹ • y) ≤
          euclideanNorm ((C * A) *ᵥ y) + euclideanNorm ((D * A) *ᵥ y) := by
      rw [hdecomp, sub_eq_add_neg]
      simpa [euclideanNorm] using
        norm_add_le (WithLp.toLp 2 ((C * A) *ᵥ y)) (WithLp.toLp 2 (-((D * A) *ᵥ y)))
    rw [hnorm_smul] at htri
    linarith
  constructor
  · intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    -- The inner scaled ball lands in the ellipsoid because `C * A` stays below `σ⁻¹`.
    have hσ_bound : σ * (s⁻¹ + δ) < 1 := by
      have hsigma_inv : s⁻¹ + δ < σ⁻¹ := by
        linarith
      have hmul := mul_lt_mul_of_pos_left hsigma_inv hσ_pos
      simpa [hσ_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hcoeff_nonneg : 0 ≤ s⁻¹ + δ := by
      positivity
    have hmem : euclideanNorm (C *ᵥ ((σ • A) *ᵥ u)) ≤ 1 := by
      calc
        euclideanNorm (C *ᵥ ((σ • A) *ᵥ u)) =
            euclideanNorm (σ • ((C * A) *ᵥ u)) := by
              rw [mulVec_smulMatrix_normalize]
        _ = σ * euclideanNorm ((C * A) *ᵥ u) := by
              rw [euclideanNorm_smul, abs_of_pos hσ_pos]
        _ ≤ σ * ((s⁻¹ + δ) * euclideanNorm u) := by
              exact mul_le_mul_of_nonneg_left (hupper u) hσ_pos.le
        _ ≤ σ * (s⁻¹ + δ) := by
              calc
                σ * ((s⁻¹ + δ) * euclideanNorm u) =
                    (σ * (s⁻¹ + δ)) * euclideanNorm u := by
                      ring
                _ ≤ (σ * (s⁻¹ + δ)) * 1 := by
                      exact mul_le_mul_of_nonneg_left hu (mul_nonneg hσ_pos.le hcoeff_nonneg)
                _ = σ * (s⁻¹ + δ) := by
                      ring
        _ ≤ 1 := hσ_bound.le
    simpa [euclideanEllipsoid] using hmem
  · intro x hx
    let y : Fin n → ℝ := A⁻¹ *ᵥ (x - a)
    have hAy : A *ᵥ y = x - a := by
      -- The inverse-shape coordinates recover the centered point exactly.
      dsimp [y]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA_unit, Matrix.one_mulVec]
    have hx' : euclideanNorm ((C * A) *ᵥ y) ≤ 1 := by
      -- Reexpress the ellipsoid inequality in the inverse-shape coordinates.
      calc
        euclideanNorm ((C * A) *ᵥ y) = euclideanNorm (C *ᵥ (x - a)) := by
          rw [← Matrix.mulVec_mulVec, hAy]
        _ ≤ 1 := by
          simpa [euclideanEllipsoid] using hx
    have hτ_bound : τ⁻¹ ≤ s⁻¹ - δ := by
      linarith
    have hy_mem : euclideanNorm (τ⁻¹ • y) ≤ 1 := by
      -- The lower bound on `C * A` forces the inverse-shape coordinates below `τ`.
      calc
        euclideanNorm (τ⁻¹ • y) = τ⁻¹ * euclideanNorm y := by
          rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hτ_pos)]
        _ ≤ (s⁻¹ - δ) * euclideanNorm y := by
          exact mul_le_mul_of_nonneg_right hτ_bound (euclideanNorm_nonneg y)
        _ ≤ euclideanNorm ((C * A) *ᵥ y) := hlower y
        _ ≤ 1 := hx'
    refine ⟨τ⁻¹ • y, hy_mem, ?_⟩
    -- Rescale the recovered inverse-shape coordinates back to the `τ`-direct ball.
    have hx_eq : x = a + A *ᵥ y := by
      calc
        x = a + (x - a) := by
              abel
        _ = a + A *ᵥ y := by
              rw [← hAy]
    symm
    calc
      x = a + A *ᵥ y := hx_eq
      _ = a + (τ • A) *ᵥ (τ⁻¹ • y) := by
            simp [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, hτ_pos.ne']

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a rational inverse-shape
ellipsoid can be placed between two strict direct-ball rescalings of the same real shape. -/
theorem existsRationalEllipsoid_between_scaledDirectBalls
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hA_unit : IsUnit A.det)
    {σ τ : ℝ}
    (hσ_pos : 0 < σ)
    (hστ : σ < τ)
    (hτ_lt_one : τ < 1) :
    ∃ C : Matrix (Fin n) (Fin n) ℚ,
      IsUnit C.det ∧
        directAffineEuclideanBall (σ • A) a ⊆ euclideanEllipsoid (C.map (Rat.castHom ℝ)) a ∧
        euclideanEllipsoid (C.map (Rat.castHom ℝ)) a ⊆ directAffineEuclideanBall (τ • A) a := by
  let s : ℝ := (σ + τ) / 2
  have hσ_lt_s : σ < s := by
    dsimp [s]
    nlinarith
  have hs_lt_τ : s < τ := by
    dsimp [s]
    nlinarith
  have hs_pos : 0 < s := lt_trans hσ_pos hσ_lt_s
  have hmargin_left : 0 < σ⁻¹ - s⁻¹ := by
    have hrecip : s⁻¹ < σ⁻¹ := by
      simpa [one_div] using one_div_lt_one_div_of_lt hσ_pos hσ_lt_s
    linarith
  have hmargin_right : 0 < s⁻¹ - τ⁻¹ := by
    have hrecip : τ⁻¹ < s⁻¹ := by
      simpa [one_div] using one_div_lt_one_div_of_lt hs_pos hs_lt_τ
    linarith
  let margin : ℝ := min (σ⁻¹ - s⁻¹) (s⁻¹ - τ⁻¹)
  have hmargin_pos : 0 < margin := by
    dsimp [margin]
    exact lt_min hmargin_left hmargin_right
  let ε : ℝ := margin / (‖A‖ + 1)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hmid_unit : IsUnit ((s⁻¹ • A⁻¹).det) := by
    -- The midpoint inverse reference is still nonsingular.
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hs_ne))
      (isUnit_iff_ne_zero.mp (Matrix.isUnit_nonsing_inv_det (A := A) hA_unit))
  rcases existsNonsingularRationalMatrixNear (s⁻¹ • A⁻¹) hmid_unit hε_pos with
    ⟨C, hC_unit, hCdist⟩
  let Creal : Matrix (Fin n) (Fin n) ℝ := C.map (Rat.castHom ℝ)
  have hCreal_close : ‖Creal - s⁻¹ • A⁻¹‖ < ε := by
    dsimp [Creal]
    simpa [dist_eq_norm] using hCdist
  have hA_bound : ‖A‖ ≤ ‖A‖ + 1 := by
    linarith [norm_nonneg A]
  have hAplus_pos : 0 < ‖A‖ + 1 := by
    positivity
  have happrox :
      ‖Creal - s⁻¹ • A⁻¹‖ * ‖A‖ < min (σ⁻¹ - s⁻¹) (s⁻¹ - τ⁻¹) := by
    calc
      ‖Creal - s⁻¹ • A⁻¹‖ * ‖A‖ ≤ ‖Creal - s⁻¹ • A⁻¹‖ * (‖A‖ + 1) := by
        exact mul_le_mul_of_nonneg_left hA_bound (norm_nonneg _)
      _ < ε * (‖A‖ + 1) := by
        exact mul_lt_mul_of_pos_right hCreal_close hAplus_pos
      _ = min (σ⁻¹ - s⁻¹) (s⁻¹ - τ⁻¹) := by
        dsimp [ε, margin]
        field_simp
  rcases scaledDirectBalls_between_of_nearMidpointInverse
      A Creal a hA_unit hσ_pos hσ_lt_s hs_lt_τ happrox with
    ⟨hleft, hright⟩
  exact ⟨C, hC_unit, hleft, hright⟩

-- The final support-local convex-hull theorem is stated below; the next lemmas prepare its
-- separator-side contradiction route.
/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a strict separator of the
normalized John target from the supporting-contact hull has a uniform positive gap on the compact
contact set. -/
theorem strictSeparatorGapOnNormalizedSupportingContacts
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    (f : StrongDual ℝ (ContactMomentSpace n))
    (hsep : ∀ u ∈ normalizedSupportingContacts L,
      f (contactMoment u) < f (normalizedContactMomentTarget n)) :
    ∃ η > 0,
      ∀ u ∈ normalizedSupportingContacts L,
        contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (contactSeparatorMatrix f *ᵥ u) ≤
          (n : ℝ)⁻¹ * Matrix.trace (contactSeparatorMatrix f) - η := by
  classical
  by_cases hnonempty : (normalizedSupportingContacts L).Nonempty
  · let gap : (Fin n → ℝ) → ℝ := fun u ↦
      f (normalizedContactMomentTarget n) - f (contactMoment u)
    have hgap_cont : Continuous gap := by
      -- The separator gap is a continuous real-valued function on the contact set.
      exact continuous_const.sub (f.continuous.comp continuous_contactMoment)
    rcases (isCompact_normalizedSupportingContacts L).exists_isMinOn hnonempty
        hgap_cont.continuousOn with ⟨u0, hu0, hmin⟩
    refine ⟨gap u0, ?_, ?_⟩
    · -- The minimizing gap is still strictly positive because every contact inequality is strict.
      have hsep0 := hsep u0 hu0
      dsimp [gap]
      linarith
    · intro u hu
      -- Rewrite the minimizing-gap inequality in the separator coordinates.
      have hmin_le := (isMinOn_iff.mp hmin) u hu
      have hsep_le :
          f (contactMoment u) ≤ f (normalizedContactMomentTarget n) - gap u0 := by
        -- Move the minimizing-gap inequality into separator form before unpacking the coordinates.
        dsimp [gap] at hmin_le ⊢
        linarith
      rw [contactMoment_separator_apply, normalizedContactMomentTarget_separator_apply] at hsep_le
      simpa using hsep_le
  · refine ⟨1, zero_lt_one, ?_⟩
    intro u hu
    exact (hnonempty ⟨u, hu⟩).elim

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: shifting a separator matrix by
a scalar multiple of the identity makes its contact inequality uniformly negative while forcing a
positive trace. -/
theorem shiftedContactSeparatorMatrixData
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    (hn : n ≠ 0)
    (f : StrongDual ℝ (ContactMomentSpace n))
    {η : ℝ}
    (hgap : ∀ u ∈ normalizedSupportingContacts L,
      contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (contactSeparatorMatrix f *ᵥ u) ≤
        (n : ℝ)⁻¹ * Matrix.trace (contactSeparatorMatrix f) - η) :
    ∃ N : Matrix (Fin n) (Fin n) ℝ,
      Matrix.trace N = n * (η / 2) ∧
        ∀ u ∈ normalizedSupportingContacts L,
          contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u) ≤ -η / 2 := by
  let shift : ℝ := η / 2 - (n : ℝ)⁻¹ * Matrix.trace (contactSeparatorMatrix f)
  let N : Matrix (Fin n) (Fin n) ℝ :=
    contactSeparatorMatrix f + shift • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨N, ?_, ?_⟩
  · -- The identity shift moves the trace to the positive target value `n * (η / 2)`.
    calc
      Matrix.trace N =
          Matrix.trace (contactSeparatorMatrix f) + (n : ℝ) * shift := by
            simp [N, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, mul_comm]
      _ = n * (η / 2) := by
            dsimp [shift]
            field_simp [hnR]
            ring
  · intro u hu
    have hu_dot : u ⬝ᵥ u = 1 := by
      -- Contacts live on the Euclidean unit sphere.
      calc
        u ⬝ᵥ u = euclideanNorm u ^ 2 := dotProduct_self_eq_euclideanNorm_sq u
        _ = 1 := by rw [hu.1]; norm_num
    have hshift_eval :
        u ⬝ᵥ ((shift • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) = shift := by
      -- The identity contribution is exactly the scalar shift because `‖u‖₂ = 1`.
      calc
        u ⬝ᵥ ((shift • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) =
            u ⬝ᵥ (shift • u) := by
              simp [Matrix.smul_mulVec]
        _ = shift * (u ⬝ᵥ u) := by
              rw [dotProduct_smul, smul_eq_mul]
        _ = shift := by rw [hu_dot, mul_one]
    have hbase := hgap u hu
    -- The shifted matrix subtracts the old trace level and leaves a uniform `-η / 2` margin.
    calc
      contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u) =
          (contactSeparatorVector f ⬝ᵥ u + u ⬝ᵥ (contactSeparatorMatrix f *ᵥ u)) + shift := by
            dsimp [N]
            rw [Matrix.add_mulVec, dotProduct_add, hshift_eval]
            ring
      _ ≤ -η / 2 := by
        dsimp [shift] at hbase ⊢
        linarith

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: every continuous linear
functional on `Fin n → ℝ` is the dot product with its coordinate vector. -/
theorem strongDual_apply_eq_dotProduct
    {n : ℕ}
    (f : StrongDual ℝ (Fin n → ℝ))
    (x : Fin n → ℝ) :
    f x = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
  -- Expand `x` in the standard basis and use linearity term-by-term.
  have hx_expand : (∑ i, x i • Pi.single i 1) = x := by
    ext i
    simp [Pi.single_apply]
  calc
    f x = f (∑ i, x i • Pi.single i 1) := by rw [hx_expand]
    _ = ∑ i, x i * f (Pi.single i 1) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
      ring
    _ = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
      simp [dotProduct, mul_comm]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a compact convex body is the
intersection of the support half-spaces determined by its full Euclidean support function. -/
theorem mem_of_forall_unitDotProduct_le_supportSup
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    (hL_compact : IsCompact L)
    (hL_convex : Convex ℝ L)
    (hL_nonempty : L.Nonempty)
    {x : Fin n → ℝ}
    (hx : ∀ u : Fin n → ℝ, euclideanNorm u = 1 →
      u ⬝ᵥ x ≤ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L)) :
    x ∈ L := by
  by_contra hxL
  obtain ⟨f, c, hfc, hfx⟩ :=
    geometric_hahn_banach_closed_point hL_convex hL_compact.isClosed hxL
  let v : Fin n → ℝ := fun i ↦ f (Pi.single i 1)
  have hf_apply (y : Fin n → ℝ) : f y = v ⬝ᵥ y := by
    -- Convert the separator into its coordinate dot-product form.
    simpa [v] using strongDual_apply_eq_dotProduct f y
  have hv_ne_zero : v ≠ 0 := by
    intro hv
    have hf_zero (y : Fin n → ℝ) : f y = 0 := by
      rw [hf_apply, hv]
      simp
    rcases hL_nonempty with ⟨y, hy⟩
    have hy_lt : f y < c := hfc y hy
    linarith [hy_lt, hfx, hf_zero y, hf_zero x]
  let u : Fin n → ℝ := (euclideanNorm v)⁻¹ • v
  have hv_norm_pos : 0 < euclideanNorm v := by
    have hv_norm_ne : euclideanNorm v ≠ 0 := by
      intro hv_zero
      exact hv_ne_zero ((euclideanNorm_eq_zero).mp hv_zero)
    exact lt_of_le_of_ne (euclideanNorm_nonneg v) (Ne.symm hv_norm_ne)
  have hu_norm : euclideanNorm u = 1 := by
    -- Normalizing the separator coordinate vector puts it on the Euclidean unit sphere.
    calc
      euclideanNorm u = |(euclideanNorm v)⁻¹| * euclideanNorm v := by
        dsimp [u]
        rw [euclideanNorm_smul]
      _ = (euclideanNorm v)⁻¹ * euclideanNorm v := by
        rw [abs_of_pos (inv_pos.mpr hv_norm_pos)]
      _ = 1 := by
        field_simp [hv_norm_pos.ne']
  have hsupp_le :
      sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) ≤ (euclideanNorm v)⁻¹ * c := by
    -- Every point of `L` satisfies the separator bound after Euclidean normalization.
    refine csSup_le ?_ ?_
    · rcases hL_nonempty with ⟨y, hy⟩
      exact ⟨u ⬝ᵥ y, ⟨y, hy, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hy_bound : f y ≤ c := le_of_lt (hfc y hy)
      have hu_eval : u ⬝ᵥ y = (euclideanNorm v)⁻¹ * f y := by
        simp [u, hf_apply]
      change u ⬝ᵥ y ≤ (euclideanNorm v)⁻¹ * c
      rw [hu_eval]
      exact mul_le_mul_of_nonneg_left hy_bound (inv_nonneg.mpr hv_norm_pos.le)
  have hsupp_x : u ⬝ᵥ x ≤ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) := hx u hu_norm
  have hux_gt : (euclideanNorm v)⁻¹ * c < u ⬝ᵥ x := by
    -- The normalized separator still strictly separates `x` from `L`.
    have hfx' : c < f x := hfx
    have hu_eval : u ⬝ᵥ x = (euclideanNorm v)⁻¹ * f x := by
      simp [u, hf_apply]
    rw [hu_eval]
    exact mul_lt_mul_of_pos_left hfx' (inv_pos.mpr hv_norm_pos)
  have hnot : ¬ u ⬝ᵥ x ≤ (euclideanNorm v)⁻¹ * c := by
    intro hle
    exact (not_lt_of_ge hle) hux_gt
  exact hnot (le_trans hsupp_x hsupp_le)

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the Euclidean support
function of a compact set is continuous in the direction variable. -/
theorem continuous_unitDotProduct_supportSup
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    (hL_compact : IsCompact L) :
    Continuous fun u : Fin n → ℝ ↦ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) := by
  have hdot :
      Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 ⬝ᵥ p.2 := by
    -- The dot product is a finite sum of coordinatewise products on the product space.
    simpa [dotProduct] using
      (continuous_finsetSum Finset.univ fun i _ ↦
        (((continuous_apply i).comp continuous_fst).mul
          ((continuous_apply i).comp continuous_snd)))
  simpa using
    hL_compact.continuous_sSup (f := fun u y : Fin n → ℝ ↦ u ⬝ᵥ y) hdot

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the Euclidean unit sphere in
`Fin n → ℝ` is compact. -/
theorem isCompact_unitSphere
    {n : ℕ} :
    IsCompact ({u : Fin n → ℝ | euclideanNorm u = 1} : Set (Fin n → ℝ)) := by
  have hclosed :
      IsClosed ({u : Fin n → ℝ | euclideanNorm u = 1} : Set (Fin n → ℝ)) :=
    isClosed_eq continuous_euclideanNorm continuous_const
  -- The sphere is a closed subset of the compact Euclidean unit ball.
  refine IsCompact.of_isClosed_subset isCompact_euclideanUnitBall hclosed ?_
  intro u hu
  exact hu.le

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a strict negative separator
inequality on the contact set extends to an open neighborhood with a smaller negative margin. -/
theorem existsContactNeighborhoodWithNegativeSeparator
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    {η : ℝ}
    (hη : 0 < η)
    (v : Fin n → ℝ)
    (N : Matrix (Fin n) (Fin n) ℝ)
    (hgap : ∀ u ∈ normalizedSupportingContacts L,
      v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u) ≤ -η / 2) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ normalizedSupportingContacts L ⊆ U ∧
      ∀ u ∈ U, v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u) ≤ -η / 4 := by
  -- Use the strict sublevel set of the separator quadratic form as the required open
  -- neighborhood.
  let quadratic : (Fin n → ℝ) → ℝ :=
    fun u ↦ v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u)
  have hdot :
      Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 ⬝ᵥ p.2 := by
    -- Both the linear and quadratic terms are finite sums of coordinatewise products.
    simpa [dotProduct] using
      (continuous_finsetSum Finset.univ fun i _ ↦
        (((continuous_apply i).comp continuous_fst).mul
          ((continuous_apply i).comp continuous_snd)))
  have hlin : Continuous fun u : Fin n → ℝ ↦ v ⬝ᵥ u := by
    -- Freeze the first input of the dot product to the separator vector.
    simpa [dotProduct] using
      (continuous_finsetSum Finset.univ fun i _ ↦
        continuous_const.mul (continuous_apply i))
  have hmatrix : Continuous fun u : Fin n → ℝ ↦ N *ᵥ u :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hquad : Continuous fun u : Fin n → ℝ ↦ u ⬝ᵥ (N *ᵥ u) := by
    -- Compose the product-space dot product with the graph of `u ↦ N *ᵥ u`.
    simpa using hdot.comp (Continuous.prodMk continuous_id hmatrix)
  have hquadratic : Continuous quadratic := hlin.add hquad
  let U : Set (Fin n → ℝ) := {u | quadratic u < -(η / 4)}
  refine ⟨U, isOpen_lt hquadratic continuous_const, ?_, ?_⟩
  · intro u hu
    -- The original `-η / 2` margin places every contact direction in the open sublevel set.
    change quadratic u < -(η / 4)
    have hu_gap := hgap u hu
    linarith
  · intro u hu
    -- Membership in the open sublevel set gives the advertised weaker nonpositive bound.
    have hu_lt : quadratic u < -(η / 4) := by
      simpa [U] using hu
    have hu_le : v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u) ≤ -η / 4 := by
      dsimp [quadratic] at hu_lt
      linarith
    exact hu_le

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: outside any open
neighborhood of the contact locus, the Euclidean support function is uniformly larger than one. -/
theorem existsSupportGapAwayFromContactNeighborhood
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    (hL_compact : IsCompact L)
    {U : Set (Fin n → ℝ)}
    (hU_open : IsOpen U)
    (hU_contact : normalizedSupportingContacts L ⊆ U) :
    ∃ δ > 0, ∀ u, euclideanNorm u = 1 → u ∉ U →
      1 + δ ≤ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) := by
  let supportSup : (Fin n → ℝ) → ℝ :=
    fun u ↦ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L)
  have hsupport_cont : Continuous supportSup :=
    continuous_unitDotProduct_supportSup hL_compact
  let sphereComplement : Set (Fin n → ℝ) := {u : Fin n → ℝ | euclideanNorm u = 1} \ U
  have hsphereComplement_compact : IsCompact sphereComplement := by
    -- Restrict the compact unit sphere to the closed complement of the chosen neighborhood.
    simpa [sphereComplement, Set.diff_eq] using
      (isCompact_unitSphere.inter_right hU_open.isClosed_compl)
  let gap : (Fin n → ℝ) → ℝ := fun u ↦ supportSup u - 1
  have hgap_cont : Continuous gap := hsupport_cont.sub continuous_const
  by_cases hnonempty : sphereComplement.Nonempty
  · rcases hsphereComplement_compact.exists_isMinOn hnonempty hgap_cont.continuousOn with
      ⟨u0, hu0, hmin⟩
    refine ⟨gap u0, ?_, ?_⟩
    · -- A minimizing direction outside the contact neighborhood still has support strictly above
      -- one, because otherwise it would itself be a contact direction.
      have hu0_norm : euclideanNorm u0 = 1 := hu0.1
      have hu0_notU : u0 ∉ U := hu0.2
      have hsupp_gt : 1 < supportSup u0 := by
        by_contra hsupp_le
        have hsupp_le' : supportSup u0 ≤ 1 := le_of_not_gt hsupp_le
        have hu0_contact : u0 ∈ normalizedSupportingContacts L := by
          refine ⟨hu0_norm, ?_⟩
          intro x hx
          have himage_compact :
              IsCompact ((fun y : Fin n → ℝ ↦ u0 ⬝ᵥ y) '' L) := by
            have hcont : Continuous fun y : Fin n → ℝ ↦ u0 ⬝ᵥ y := by
              -- Fix the direction and keep only the point variable.
              simpa [dotProduct] using
                (continuous_finsetSum Finset.univ fun i _ ↦
                  continuous_const.mul (continuous_apply i))
            exact hL_compact.image hcont
          have hx_le : u0 ⬝ᵥ x ≤ supportSup u0 := by
            exact le_csSup himage_compact.bddAbove ⟨x, hx, rfl⟩
          exact hx_le.trans hsupp_le'
        exact hu0_notU (hU_contact hu0_contact)
      dsimp [gap, supportSup]
      linarith
    · intro u hu_norm hu_notU
      -- The minimum of the positive gap on the compact complement controls every unit direction
      -- outside the chosen neighborhood.
      have hu_mem : u ∈ sphereComplement := ⟨hu_norm, hu_notU⟩
      have hmin_le := (isMinOn_iff.mp hmin) u hu_mem
      dsimp [gap, supportSup] at hmin_le ⊢
      linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro u hu_norm hu_notU
    exact (hnonempty ⟨u, ⟨hu_norm, hu_notU⟩⟩).elim

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: in a finite-dimensional real
normed space, the convex hull of a compact set is compact. -/
theorem isCompact_convexHull_of_isCompact
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {s : Set E}
    (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  by_cases hs_empty : s = ∅
  · -- The empty convex hull is empty, hence compact.
    simp [hs_empty]
  have hs_nonempty : s.Nonempty := by
    exact Set.nonempty_iff_ne_empty.2 hs_empty
  let piece : ℕ → Set E := fun k ↦
    (fun p : stdSimplex ℝ (Fin k) × (Fin k → s) ↦
      ∑ i, p.1.1 i • ((p.2 i : s) : E)) '' Set.univ
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hpiece_compact : ∀ k, IsCompact (piece k) := by
    intro k
    let F : stdSimplex ℝ (Fin k) × (Fin k → s) → E := fun p ↦
      ∑ i, p.1.1 i • ((p.2 i : s) : E)
    have hF_cont : Continuous F := by
      -- The simplex-image parametrization is continuous in both the weights and the chosen points.
      simp only [F]
      refine continuous_finsetSum Finset.univ fun i _ ↦ ?_
      exact
        (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
    simpa [piece, F] using (isCompact_univ.image hF_cont)
  have hpiece_subset : ∀ k, piece k ⊆ convexHull ℝ s := by
    intro k x hx
    rcases hx with ⟨p, -, rfl⟩
    -- Every simplex-weighted finite family in `s` belongs to the convex hull by definition.
    exact mem_convexHull_of_exists_fintype
      (w := fun i : Fin k ↦ p.1.1 i)
      (z := fun i : Fin k ↦ ((p.2 i : s) : E))
      (fun i ↦ p.1.2.1 i)
      p.1.2.2
      (fun i ↦ (p.2 i).2)
      rfl
  have hsubset : convexHull ℝ s ⊆ ⋃ k ∈ Set.Iic (Module.finrank ℝ E + 1), piece k := by
    intro x hx
    rcases eq_pos_convex_span_of_mem_convexHull hx with
      ⟨ι, _, z, w, hz, haff, hwpos, hwsum, hwx⟩
    let k : ℕ := Fintype.card ι
    have hk : k ≤ Module.finrank ℝ E + 1 := by
      -- Carathéodory reduces to an affinely independent family of size at most `dim + 1`.
      dsimp [k]
      exact le_trans haff.card_le_finrank_succ (Nat.succ_le_succ (Submodule.finrank_le _))
    let e : ι ≃ Fin k := Fintype.equivFin ι
    have hw_nonneg : ∀ i : Fin k, 0 ≤ w (e.symm i) := fun i ↦ (hwpos _).le
    have hwsum' : ∑ i : Fin k, w (e.symm i) = 1 := by
      simpa [e] using (Equiv.sum_comp e.symm w).trans hwsum
    have hwx' : ∑ i : Fin k, w (e.symm i) • z (e.symm i) = x := by
      calc
        ∑ i : Fin k, w (e.symm i) • z (e.symm i) = ∑ j : ι, w j • z j := by
          simpa [e] using (Equiv.sum_comp e.symm fun j : ι ↦ w j • z j)
        _ = x := hwx
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ?_⟩⟩
    refine ⟨(⟨fun i : Fin k ↦ w (e.symm i), ⟨hw_nonneg, hwsum'⟩⟩, ?_), by simp, ?_⟩
    · intro i
      exact ⟨z (e.symm i), hz ⟨e.symm i, rfl⟩⟩
    · simpa using hwx'
  have hunion :
      (⋃ k ∈ Set.Iic (Module.finrank ℝ E + 1), piece k) = convexHull ℝ s := by
    refine Set.Subset.antisymm ?_ hsubset
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hxk⟩
    rcases Set.mem_iUnion.1 hxk with ⟨hk, hxpiece⟩
    exact hpiece_subset k hxpiece
  -- A finite union of compact simplex images covers the entire convex hull.
  rw [← hunion]
  exact (Set.finite_le_nat (Module.finrank ℝ E + 1)).isCompact_biUnion fun k _ ↦ hpiece_compact k

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the supporting-contact
moment hull is closed because the compact generator has compact convex hull. -/
theorem isClosed_contactMomentConvexHull
    {n : ℕ}
    (L : Set (Fin n → ℝ)) :
    IsClosed (convexHull ℝ (contactMoment '' normalizedSupportingContacts L)) := by
  -- Compactness of the generator upgrades its convex hull to a closed set.
  exact (isCompact_convexHull_of_isCompact
    (isCompact_contactMoments L)).isClosed

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: points of the perturbed direct
ball satisfy the first-order separator support estimate in every unit direction. -/
theorem unitDotProduct_le_of_mem_perturbedDirectBall
    {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℝ)
    (v x u : Fin n → ℝ)
    {t : ℝ}
    (hu_norm : euclideanNorm u = 1)
    (hx : x ∈ directAffineEuclideanBall (1 + t • N) (t • v)) :
    u ⬝ᵥ x ≤
      1 + t * (v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u)) +
        (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 := by
  rcases hx with ⟨z, hz, rfl⟩
  let w : Fin n → ℝ := N.transpose *ᵥ u
  have hz_norm : euclideanNorm z ≤ 1 := by
    simpa using hz
  have hu_self : u ⬝ᵥ u = 1 := by
    -- The unit-direction hypothesis fixes the constant term in the norm-square expansion.
    calc
      u ⬝ᵥ u = euclideanNorm u ^ 2 := dotProduct_self_eq_euclideanNorm_sq u
      _ = 1 := by rw [hu_norm]; norm_num
  have htranspose_eval : u ⬝ᵥ w = u ⬝ᵥ (N *ᵥ u) := by
    -- Move the matrix from the right-hand slot of the dot product to the left via transpose.
    calc
      u ⬝ᵥ w = w ⬝ᵥ u := by rw [dotProduct_comm]
      _ = u ⬝ᵥ (N *ᵥ u) := by
        dsimp [w]
        rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have hdot_tN : u ⬝ᵥ ((t • N) *ᵥ z) = (u ᵥ* (t • N)) ⬝ᵥ z := by
    simpa using (Matrix.dotProduct_mulVec u (t • N) z)
  have hdot_normalize :
      u ⬝ᵥ ((1 + t • N) *ᵥ z) = (u + t • w) ⬝ᵥ z := by
    -- Normalize the separator term into the transpose-on-the-left spelling used by the norm bound.
    dsimp [w]
    calc
      u ⬝ᵥ ((1 + t • N) *ᵥ z) =
          u ⬝ᵥ z + (u ᵥ* (t • N)) ⬝ᵥ z := by
            rw [Matrix.add_mulVec, dotProduct_add]
            rw [hdot_tN]
            simp
      _ = u ⬝ᵥ z + (t • (u ᵥ* N)) ⬝ᵥ z := by
            rw [Matrix.vecMul_smul]
      _ = u ⬝ᵥ z + t * ((u ᵥ* N) ⬝ᵥ z) := by
            rw [smul_dotProduct]
            simp [smul_eq_mul]
      _ = u ⬝ᵥ z + t * (w ⬝ᵥ z) := by
            dsimp [w]
            rw [Matrix.mulVec_transpose]
      _ = (u + t • w) ⬝ᵥ z := by
            rw [add_dotProduct, smul_dotProduct]
            simp [smul_eq_mul]
  have hcs :
      (u + t • w) ⬝ᵥ z ≤ euclideanNorm (u + t • w) * euclideanNorm z := by
    -- Cauchy–Schwarz controls the normalized dot product.
    exact le_trans (le_abs_self _) (abs_dotProduct_le_euclideanNorm_mul _ _)
  have hnorm_square :
      euclideanNorm (u + t • w) ^ 2 =
        1 + (2 * t * (u ⬝ᵥ w) + t ^ 2 * euclideanNorm w ^ 2) := by
    -- Expand the Euclidean norm square exactly before applying the scalar `sqrt` estimate.
    calc
      euclideanNorm (u + t • w) ^ 2 = (u + t • w) ⬝ᵥ (u + t • w) := by
        rw [dotProduct_self_eq_euclideanNorm_sq]
      _ = u ⬝ᵥ u + (t * (u ⬝ᵥ w) + (t * (w ⬝ᵥ u) + t * (t * (w ⬝ᵥ w)))) := by
        simp [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
        ring_nf
      _ = 1 + (2 * t * (u ⬝ᵥ w) + t ^ 2 * euclideanNorm w ^ 2) := by
        rw [hu_self, dotProduct_comm w u, dotProduct_self_eq_euclideanNorm_sq]
        ring_nf
  have hinside_nonneg :
      -1 ≤ 2 * t * (u ⬝ᵥ w) + t ^ 2 * euclideanNorm w ^ 2 := by
    -- The exact square expansion is nonnegative, so the `sqrt(1 + x)` side condition holds.
    have hsq_nonneg : 0 ≤ euclideanNorm (u + t • w) ^ 2 := sq_nonneg _
    linarith [hnorm_square]
  have hnorm_bound :
      euclideanNorm (u + t • w) ≤
        1 + t * (u ⬝ᵥ w) + (t ^ 2 / 2) * euclideanNorm w ^ 2 := by
    -- Apply the one-variable square-root majorization to the exact norm-square formula.
    calc
      euclideanNorm (u + t • w) =
          Real.sqrt (1 + (2 * t * (u ⬝ᵥ w) + t ^ 2 * euclideanNorm w ^ 2)) := by
            rw [← hnorm_square, Real.sqrt_sq (euclideanNorm_nonneg _)]
      _ ≤ 1 + (2 * t * (u ⬝ᵥ w) + t ^ 2 * euclideanNorm w ^ 2) / 2 := by
            exact Real.sqrt_one_add_le hinside_nonneg
      _ = 1 + t * (u ⬝ᵥ w) + (t ^ 2 / 2) * euclideanNorm w ^ 2 := by
            ring
  have hmul :
      euclideanNorm (u + t • w) * euclideanNorm z ≤ euclideanNorm (u + t • w) := by
    -- The unit-ball witness bounds the multiplicative Cauchy–Schwarz factor by one.
    exact mul_le_of_le_one_right (euclideanNorm_nonneg _) hz_norm
  calc
    u ⬝ᵥ (t • v + (1 + t • N) *ᵥ z) =
        t * (v ⬝ᵥ u) + (u + t • w) ⬝ᵥ z := by
          rw [dotProduct_add, dotProduct_smul, hdot_normalize, dotProduct_comm u v]
          ring
    _ ≤ t * (v ⬝ᵥ u) + euclideanNorm (u + t • w) * euclideanNorm z := by
          linarith
    _ ≤ t * (v ⬝ᵥ u) + euclideanNorm (u + t • w) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hmul (t * (v ⬝ᵥ u))
    _ ≤ t * (v ⬝ᵥ u) +
          (1 + t * (u ⬝ᵥ w) + (t ^ 2 / 2) * euclideanNorm w ^ 2) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hnorm_bound (t * (v ⬝ᵥ u))
    _ = 1 + t * (v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u)) +
          (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 := by
          dsimp [w]
          rw [htranspose_eval]
          ring

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: once the supporting-contact
moment hull is known to be closed, failing membership in the convex hull also fails membership in
the closed convex hull. -/
theorem contactMomentTarget_not_mem_closedConvexHull_of_not_mem_convexHull
    {n : ℕ}
    (L : Set (Fin n → ℝ))
    (houtside : normalizedContactMomentTarget n ∉
      convexHull ℝ (contactMoment '' normalizedSupportingContacts L)) :
    normalizedContactMomentTarget n ∉
      closedConvexHull ℝ (contactMoment '' normalizedSupportingContacts L) := by
  -- Collapse `closedConvexHull` to the already closed supporting-contact hull.
  rw [closedConvexHull_eq_closure_convexHull]
  simpa [(isClosed_contactMomentConvexHull L).closure_eq] using houtside

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: small separator-guided
perturbations of the unit ball stay inside `L` once every unit support direction is controlled. -/
theorem perturbedDirectBall_subset_of_small_t
    {n : ℕ}
    {L : Set (Fin n → ℝ)}
    (hL_compact : IsCompact L)
    (hL_convex : Convex ℝ L)
    (hL_nonempty : L.Nonempty)
    (hunit : {u : Fin n → ℝ | euclideanNorm u ≤ 1} ⊆ L)
    {v : Fin n → ℝ}
    {N : Matrix (Fin n) (Fin n) ℝ}
    {η δ : ℝ}
    {U : Set (Fin n → ℝ)}
    (hU_gap : ∀ u ∈ U, v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u) ≤ -η / 4)
    (hδ_gap : ∀ u, euclideanNorm u = 1 → u ∉ U →
      1 + δ ≤ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L))
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le_one : t ≤ 1)
    (ht_contact : t * ‖N.transpose‖ ^ 2 ≤ η / 2)
    (ht_gap :
      t * (euclideanNorm v + ‖N.transpose‖ + ‖N.transpose‖ ^ 2 / 2) ≤ δ) :
    directAffineEuclideanBall (1 + t • N) (t • v) ⊆ L := by
  intro x hx
  refine mem_of_forall_unitDotProduct_le_supportSup hL_compact hL_convex hL_nonempty ?_
  intro u hu_norm
  have hu_ball : u ∈ {u : Fin n → ℝ | euclideanNorm u ≤ 1} := by
    simp [hu_norm]
  have hu_memL : u ∈ L := hunit hu_ball
  have huu : u ⬝ᵥ u = 1 := by
    calc
      u ⬝ᵥ u = euclideanNorm u ^ 2 := dotProduct_self_eq_euclideanNorm_sq u
      _ = 1 := by rw [hu_norm]; norm_num
  have hsupp_compact :
      IsCompact ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) := by
    have hcont : Continuous fun y : Fin n → ℝ ↦ u ⬝ᵥ y := by
      -- Fix the unit direction and keep only the point variable in the support functional.
      simpa [dotProduct] using
        (continuous_finsetSum Finset.univ fun i _ ↦
          continuous_const.mul (continuous_apply i))
    exact hL_compact.image hcont
  have hsupp_one :
      1 ≤ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) := by
    exact le_csSup hsupp_compact.bddAbove ⟨u, hu_memL, by simp [huu]⟩
  have hNu_norm : euclideanNorm (N.transpose *ᵥ u) ≤ ‖N.transpose‖ := by
    calc
      euclideanNorm (N.transpose *ᵥ u) ≤ ‖N.transpose‖ * euclideanNorm u :=
        euclideanNorm_mulVec_le _ _
      _ = ‖N.transpose‖ := by rw [hu_norm, mul_one]
  have hNu_sq :
      euclideanNorm (N.transpose *ᵥ u) ^ 2 ≤ ‖N.transpose‖ ^ 2 := by
    nlinarith [euclideanNorm_nonneg (N.transpose *ᵥ u), norm_nonneg N.transpose, hNu_norm]
  by_cases huU : u ∈ U
  · have hdot :=
      unitDotProduct_le_of_mem_perturbedDirectBall N v x u hu_norm hx
    have hquad :
        (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 ≤ t * (η / 4) := by
      calc
        (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2
            ≤ (t ^ 2 / 2) * ‖N.transpose‖ ^ 2 := by
              gcongr
        _ = (t / 2) * (t * ‖N.transpose‖ ^ 2) := by ring
        _ ≤ (t / 2) * (η / 2) := by
              gcongr
        _ = t * (η / 4) := by ring
    have hle_one :
        u ⬝ᵥ x ≤ 1 := by
      calc
        u ⬝ᵥ x
            ≤ 1 + t * (v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u)) +
                (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 :=
              unitDotProduct_le_of_mem_perturbedDirectBall
                N v x u hu_norm hx
        _ ≤ 1 + t * (-η / 4) +
            (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 := by
              gcongr
              exact hU_gap u huU
        _ ≤ 1 := by
              linarith
    exact hle_one.trans hsupp_one
  · have hv_bound : v ⬝ᵥ u ≤ euclideanNorm v := by
      calc
        v ⬝ᵥ u ≤ |v ⬝ᵥ u| := le_abs_self _
        _ ≤ euclideanNorm v * euclideanNorm u := abs_dotProduct_le_euclideanNorm_mul _ _
        _ = euclideanNorm v := by rw [hu_norm, mul_one]
    have hNu_bound : u ⬝ᵥ (N *ᵥ u) ≤ ‖N.transpose‖ := by
      have htranspose_eval :
          u ⬝ᵥ (N *ᵥ u) = (N.transpose *ᵥ u) ⬝ᵥ u := by
        calc
          u ⬝ᵥ (N *ᵥ u) = (u ᵥ* N) ⬝ᵥ u := Matrix.dotProduct_mulVec u N u
          _ = (N.transpose *ᵥ u) ⬝ᵥ u := by rw [Matrix.mulVec_transpose]
      calc
        u ⬝ᵥ (N *ᵥ u) = (N.transpose *ᵥ u) ⬝ᵥ u := htranspose_eval
        _ ≤ |(N.transpose *ᵥ u) ⬝ᵥ u| := le_abs_self _
        _ ≤ euclideanNorm (N.transpose *ᵥ u) * euclideanNorm u :=
              abs_dotProduct_le_euclideanNorm_mul _ _
        _ ≤ ‖N.transpose‖ * euclideanNorm u := by
              gcongr
        _ = ‖N.transpose‖ := by rw [hu_norm, mul_one]
    have hquad :
        (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 ≤
          t * (‖N.transpose‖ ^ 2 / 2) := by
      have ht_sq_le_t : t ^ 2 ≤ t := by
        nlinarith
      calc
        (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2
            ≤ (t ^ 2 / 2) * ‖N.transpose‖ ^ 2 := by
              gcongr
        _ = t ^ 2 * (‖N.transpose‖ ^ 2 / 2) := by ring
        _ ≤ t * (‖N.transpose‖ ^ 2 / 2) := by
              exact mul_le_mul_of_nonneg_right ht_sq_le_t (by positivity)
    calc
      u ⬝ᵥ x
          ≤ 1 + t * (v ⬝ᵥ u + u ⬝ᵥ (N *ᵥ u)) +
              (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 :=
            unitDotProduct_le_of_mem_perturbedDirectBall
              N v x u hu_norm hx
      _ ≤ 1 + t * (euclideanNorm v + ‖N.transpose‖) +
          (t ^ 2 / 2) * euclideanNorm (N.transpose *ᵥ u) ^ 2 := by
            gcongr
      _ ≤ 1 + t * (euclideanNorm v + ‖N.transpose‖) +
          t * (‖N.transpose‖ ^ 2 / 2) := by
            linarith
      _ = 1 + t * (euclideanNorm v + ‖N.transpose‖ + ‖N.transpose‖ ^ 2 / 2) := by
            ring
      _ ≤ 1 + δ := by
            linarith
      _ ≤ sSup ((fun y : Fin n → ℝ ↦ u ⬝ᵥ y) '' L) := hδ_gap u hu_norm huU

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: positive trace forces the
determinant of `1 + t • N` to exceed one for all sufficiently small positive `t`. -/
  theorem existsRadius_absDet_one_add_smul_gt_one
    {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℝ)
    (htrace : 0 < Matrix.trace N) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → 1 < |(1 + t • N).det| := by
  let Mpoly : Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
    (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) • N.map (Polynomial.C : ℝ →+* Polynomial ℝ)
  let p : Polynomial ℝ :=
    Mpoly.det.divX.divX
  rcases isCompact_Icc.exists_bound_of_continuousOn
      (f := fun t : ℝ ↦ Polynomial.eval t p) p.continuous.continuousOn with
    ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C := by
    exact le_trans (abs_nonneg (Polynomial.eval 0 p)) (by simpa using hC 0 ⟨le_rfl, zero_le_one⟩)
  let ε : ℝ := min 1 (Matrix.trace N / (2 * (C + 1)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    refine lt_min zero_lt_one ?_
    positivity
  refine ⟨ε, hε_pos, ?_⟩
  intro t ht_pos ht_lt
  have ht_le_one : t ≤ 1 := by
    exact le_of_lt (lt_of_lt_of_le ht_lt (min_le_left _ _))
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_le_one⟩
  have hbound : |Polynomial.eval t p| ≤ C := by
    simpa using hC t ht_mem
  have hrem_ge : -(C * t ^ 2) ≤ Polynomial.eval t p * t ^ 2 := by
    have habs_mul : |Polynomial.eval t p * t ^ 2| ≤ C * t ^ 2 := by
      calc
        |Polynomial.eval t p * t ^ 2| = |Polynomial.eval t p| * t ^ 2 := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
        _ ≤ C * t ^ 2 := by
          exact mul_le_mul_of_nonneg_right hbound (sq_nonneg t)
    have hleft : -(C * t ^ 2) ≤ -|Polynomial.eval t p * t ^ 2| := by
      exact neg_le_neg habs_mul
    exact le_trans hleft (neg_abs_le _)
  have ht_lt_div : t < Matrix.trace N / (2 * (C + 1)) := by
    exact lt_of_lt_of_le ht_lt (min_le_right _ _)
  have hCp1t_lt : (C + 1) * t < Matrix.trace N / 2 := by
    have hden_pos : 0 < 2 * (C + 1) := by positivity
    have hmul_lt : t * (2 * (C + 1)) < Matrix.trace N := by
      exact (lt_div_iff₀ hden_pos).mp ht_lt_div
    nlinarith
  have hCt_lt : C * t < Matrix.trace N / 2 := by
    nlinarith
  have hCt_sq_lt : C * t ^ 2 < Matrix.trace N * t / 2 := by
    have := mul_lt_mul_of_pos_right hCt_lt ht_pos
    nlinarith
  have hmain : 0 < Matrix.trace N * t - C * t ^ 2 := by
    have htrace_t_pos : 0 < Matrix.trace N * t := mul_pos htrace ht_pos
    nlinarith
  have hdet_gt : 1 < (1 + t • N).det := by
    have hdet_formula :
        (1 + t • N).det = 1 + Matrix.trace N * t + Polynomial.eval t p * t ^ 2 := by
      dsimp [p, Mpoly]
      simpa using Matrix.det_one_add_smul t N
    rw [hdet_formula]
    linarith
  exact lt_of_lt_of_le hdet_gt (le_abs_self _)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean
In a compact convex normalized body that contains the Euclidean unit ball and is
determinant-maximal for direct affine balls, the normalized John target lies
in the supporting-contact convex hull. -/
theorem normalizedContactMomentTarget_mem_convexHull_of_normalizedDetMaximal
    {n : ℕ}
    (L : Set (Fin n → ℝ))
    (hn : n ≠ 0)
    (hL_compact : IsCompact L)
    (hL_convex : Convex ℝ L)
    (hunit : {u : Fin n → ℝ | euclideanNorm u ≤ 1} ⊆ L)
    (hdetMax : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      directAffineEuclideanBall B b ⊆ L → |B.det| ≤ 1) :
    normalizedContactMomentTarget n ∈
      convexHull ℝ (contactMoment '' normalizedSupportingContacts L) := by
  classical
  have hL_nonempty : L.Nonempty := by
    refine ⟨0, hunit ?_⟩
    simp [euclideanNorm]
  by_contra htarget
  have houtside :
      normalizedContactMomentTarget n ∉
        closedConvexHull ℝ (contactMoment '' normalizedSupportingContacts L) :=
    contactMomentTarget_not_mem_closedConvexHull_of_not_mem_convexHull L htarget
  rcases existsContactMomentSeparator_of_target_not_mem_closedConvexHull L houtside with
    ⟨f, hsep⟩
  rcases strictSeparatorGapOnNormalizedSupportingContacts f hsep with ⟨η, hη, hgap⟩
  rcases shiftedContactSeparatorMatrixData hn f hgap with ⟨N, htraceN, hshifted⟩
  let v : Fin n → ℝ := contactSeparatorVector f
  rcases existsContactNeighborhoodWithNegativeSeparator hη v N hshifted with
    ⟨U, hU_open, hU_contact, hU_gap⟩
  rcases existsSupportGapAwayFromContactNeighborhood hL_compact hU_open hU_contact with
    ⟨δ, hδ, hδ_gap⟩
  have htrace_pos : 0 < Matrix.trace N := by
    rw [htraceN]
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    nlinarith
  rcases existsRadius_absDet_one_add_smul_gt_one N htrace_pos with
    ⟨εdet, hεdet, hdet_gt⟩
  let A : ℝ := euclideanNorm v + ‖N.transpose‖ + ‖N.transpose‖ ^ 2 / 2
  let εcontact : ℝ := (η / 2) / (‖N.transpose‖ ^ 2 + 1)
  let εgap : ℝ := δ / (A + 1)
  let τ : ℝ := min εdet (min 1 (min εcontact εgap))
  let t : ℝ := τ / 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [euclideanNorm_nonneg v, norm_nonneg N.transpose]
  have hεcontact_pos : 0 < εcontact := by
    dsimp [εcontact]
    positivity
  have hεgap_pos : 0 < εgap := by
    dsimp [εgap, A]
    positivity
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min hεdet (lt_min zero_lt_one (lt_min hεcontact_pos hεgap_pos))
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le_τ : t ≤ τ := by
    dsimp [t]
    nlinarith
  have ht_lt_τ : t < τ := by
    dsimp [t]
    nlinarith
  have hτ_le_one : τ ≤ 1 := by
    dsimp [τ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have ht_le_one : t ≤ 1 := le_trans ht_le_τ hτ_le_one
  have hτ_le_εcontact : τ ≤ εcontact := by
    dsimp [τ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht_le_εcontact : t ≤ εcontact := le_trans ht_le_τ hτ_le_εcontact
  have hτ_le_εgap : τ ≤ εgap := by
    dsimp [τ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht_le_εgap : t ≤ εgap := le_trans ht_le_τ hτ_le_εgap
  have hτ_le_εdet : τ ≤ εdet := by
    dsimp [τ]
    exact min_le_left _ _
  have ht_lt_εdet : t < εdet := lt_of_lt_of_le ht_lt_τ hτ_le_εdet
  have ht_contact : t * ‖N.transpose‖ ^ 2 ≤ η / 2 := by
    calc
      t * ‖N.transpose‖ ^ 2 ≤ t * (‖N.transpose‖ ^ 2 + 1) := by
        nlinarith
      _ ≤ εcontact * (‖N.transpose‖ ^ 2 + 1) := by
        gcongr
      _ = η / 2 := by
        have hden : 0 < ‖N.transpose‖ ^ 2 + 1 := by positivity
        calc
          εcontact * (‖N.transpose‖ ^ 2 + 1) =
              ((η / 2) / (‖N.transpose‖ ^ 2 + 1)) * (‖N.transpose‖ ^ 2 + 1) := by
                rfl
          _ = η / 2 := by
                field_simp [hden.ne']
  have ht_gap :
      t * (euclideanNorm v + ‖N.transpose‖ + ‖N.transpose‖ ^ 2 / 2) ≤ δ := by
    calc
      t * (euclideanNorm v + ‖N.transpose‖ + ‖N.transpose‖ ^ 2 / 2)
          ≤ t * (A + 1) := by
            dsimp [A]
            nlinarith
      _ ≤ εgap * (A + 1) := by
            gcongr
      _ = δ := by
            have hden : 0 < A + 1 := by
              dsimp [A]
              positivity
            calc
              εgap * (A + 1) = (δ / (A + 1)) * (A + 1) := by
                rfl
              _ = δ := by
                field_simp [hden.ne']
  have hsubset :
      directAffineEuclideanBall (1 + t • N) (t • v) ⊆ L :=
    perturbedDirectBall_subset_of_small_t
      hL_compact hL_convex hL_nonempty hunit
      hU_gap hδ_gap ht_nonneg ht_le_one ht_contact ht_gap
  have hdet_le : |(1 + t • N).det| ≤ 1 := hdetMax (1 + t • N) (t • v) hsubset
  exact (not_lt_of_ge hdet_le) (hdet_gt t ht_pos ht_lt_εdet)

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: shrinking the shape matrix by
`τ ≤ 1` keeps the direct affine Euclidean ball inside the original ball. -/
theorem directAffineEuclideanBall_smul_subset_of_le_one
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    {τ : ℝ}
    (hτ_nonneg : 0 ≤ τ)
    (hτ_le_one : τ ≤ 1) :
    directAffineEuclideanBall (τ • A) a ⊆ directAffineEuclideanBall A a := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  refine ⟨τ • u, ?_, ?_⟩
  · -- Scaling a unit-ball witness by `τ ∈ [0,1]` keeps it in the Euclidean unit ball.
    have hu_norm : euclideanNorm u ≤ 1 := by
      simpa using hu
    calc
      euclideanNorm (τ • u) = |τ| * euclideanNorm u := euclideanNorm_smul _ _
      _ = τ * euclideanNorm u := by rw [abs_of_nonneg hτ_nonneg]
      _ ≤ 1 := by nlinarith
  · -- Reassociate the scalar between the matrix and the witness.
    simp [Matrix.smul_mulVec, Matrix.mulVec_smul]

theorem existsJohnEllipsoidSandwich_of_fullDimensional
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (hn : n ≠ 0)
    (hfull : K.FullDimensional) :
    ∃ (C : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℝ),
      IsUnit C.det ∧
        euclideanEllipsoid (C.map (Rat.castHom ℝ)) a ⊆ (K : Set (Fin n → ℝ)) ∧
        (K : Set (Fin n → ℝ)) ⊆
          ((fun x ↦ a + (n + 1 : ℝ) • (x - a)) ''
            euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) := by
  -- Route correction: the compact feasible parameter space, determinant maximizer, and normalized
  -- unit-ball maximality interface are now proved above, so the remaining assembly only needs the
  -- normalized contact-moment hull witness.
  rcases existsDetMaximalDirectAffineEuclideanBall K (ConvexBody.fullDimensional_iff.mp hfull) with
    ⟨A, a, hA_unit, hAK, hmax⟩
  have hnormalized :=
    normalizedBody_unitBall_subset_and_detMaximal K A a hA_unit hAK hmax
  rcases hnormalized with ⟨hunit, hdetMax⟩
  have htarget :
      normalizedContactMomentTarget n ∈
        convexHull ℝ (contactMoment '' normalizedSupportingContacts (normalizedBody K A a)) :=
    normalizedContactMomentTarget_mem_convexHull_of_normalizedDetMaximal
      (normalizedBody K A a) hn
      (isCompact_normalizedBody K A a hA_unit)
      (convex_normalizedBody K A a)
      hunit hdetMax
  have hsandwich :=
    directAffineEuclideanBall_sandwich_of_target_mem_convexHull
      K A a hn hA_unit hAK htarget
  rcases hsandwich with ⟨hballSubset, hballCover⟩
  let σ : ℝ := (n : ℝ) / (n + 1 : ℝ)
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hnp1_pos : 0 < (n + 1 : ℝ) := by
    positivity
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact div_pos hn_pos hnp1_pos
  have hσ_lt_one : σ < 1 := by
    dsimp [σ]
    refine (div_lt_iff₀ hnp1_pos).2 ?_
    nlinarith
  have hσ_le_one : σ ≤ 1 := hσ_lt_one.le
  have hσ_large : (n : ℝ) ≤ (n + 1 : ℝ) * σ := by
    have hσ_eq : (n + 1 : ℝ) * σ = n := by
      dsimp [σ]
      field_simp [hnp1_pos.ne']
    rw [hσ_eq]
  have hscaled :=
    scaledDirectAffineEuclideanBall_subset_and_cover
      (A := A) (a := a)
      hσ_pos hσ_le_one hσ_large hballSubset hballCover
  rcases hscaled with ⟨hσsubsetK, hσcover⟩
  let τ : ℝ := (σ + 1) / 2
  have hστ : σ < τ := by
    dsimp [τ]
    nlinarith
  have hτ_lt_one : τ < 1 := by
    dsimp [τ]
    nlinarith
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    nlinarith
  have hτ_le_one : τ ≤ 1 := hτ_lt_one.le
  rcases existsRationalEllipsoid_between_scaledDirectBalls A a hA_unit hσ_pos hστ hτ_lt_one with
    ⟨C, hC_unit, hσsubsetEllipsoid, hEllipsoidSubsetτ⟩
  refine ⟨C, a, hC_unit, ?_, ?_⟩
  · -- The rational ellipsoid lies in the `τ`-scaled direct ball, hence in the original maximal
    -- ball and therefore inside `K`.
    exact
      Set.Subset.trans hEllipsoidSubsetτ
        (Set.Subset.trans
          (directAffineEuclideanBall_smul_subset_of_le_one A a hτ_nonneg hτ_le_one)
          hAK)
  · -- The `(n + 1)`-cover of the shrunken direct ball enlarges along the inclusion into the
    -- rational ellipsoid.
    intro x hx
    rcases hσcover hx with ⟨y, hy, rfl⟩
    exact ⟨y, hσsubsetEllipsoid hy, rfl⟩

/-- Helper for Theorem 9.7: a lattice-free nonsingular ellipsoid admits a nonzero integral
direction whose width is bounded by the ellipsoid flatness constant. -/
theorem existsFlatDirection_of_latticeFreeEuclideanEllipsoid
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℝ)
    (hdet : IsUnit C.det)
    (hfree : ¬ contains_integral_point (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a)) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧
        directional_width (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) d ≤
          ellipsoidFlatnessBound n := by
  by_cases hzero : n = 0
  · subst hzero
    -- In dimension `0`, lattice-freeness is impossible because the ellipsoid contains the unique
    -- integral point.
    exfalso
    exact
      hfree
        (contains_integral_point_fin_zero_of_nonempty
          ⟨a, center_mem_euclideanEllipsoid (C.map (Rat.castHom ℝ)) a⟩)
  · have havoid :
        ∀ z : Fin n → ℤ,
          1 < euclideanNorm
            (C.map (Rat.castHom ℝ) *ᵥ (Int.cast ∘ z) - C.map (Rat.castHom ℝ) *ᵥ a) :=
      (not_containsIntegralPoint_iff_translateAvoidsClosedUnitBall
        (C.map (Rat.castHom ℝ)) a).mp hfree
    rcases existsShortDualVector_of_translateAvoidsUnitBall
        C (C.map (Rat.castHom ℝ) *ᵥ a) hzero hdet havoid with
      ⟨d, hd_ne, hd_short⟩
    refine ⟨d, hd_ne, ?_⟩
    have hdet_real : IsUnit (C.map (Rat.castHom ℝ)).det := by
      -- Cast the rational determinant before converting nonvanishing back to a unit.
      apply isUnit_iff_ne_zero.mpr
      have hdet_map :
          (C.map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) C.det :=
        ((Rat.castHom ℝ).map_det C).symm
      rw [hdet_map]
      intro hcast_zero
      apply isUnit_iff_ne_zero.mp hdet
      apply (Rat.castHom ℝ).injective
      simpa using hcast_zero
    -- Rewrite the ellipsoid width into the dual norm bound supplied by the transformed-lattice
    -- lemma and conclude directly.
    calc
      directional_width (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) d =
          2 * euclideanNorm
            (((C.map (Rat.castHom ℝ)).transpose)⁻¹ *ᵥ (Int.cast ∘ d)) := by
            apply directionalWidth_euclideanEllipsoid_eq_two_mul_dualNorm
            exact hdet_real
      _ ≤ ellipsoidFlatnessBound n := hd_short

/-- Helper for Theorem 9.7: a full-dimensional convex body contains a nonsingular ellipsoid whose
directional widths control those of the ambient body up to the outer factor `n + 1`. -/
theorem existsEllipsoidWidthBridge_of_fullDimensional
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (hfull : K.FullDimensional) :
    ∃ (C : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℝ),
      IsUnit C.det ∧
        euclideanEllipsoid (C.map (Rat.castHom ℝ)) a ⊆ (K : Set (Fin n → ℝ)) ∧
        ∀ d : Fin n → ℤ,
          directional_width (K : Set (Fin n → ℝ)) d ≤
            (n + 1 : ℝ) *
              directional_width (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) d := by
  by_cases hzero : n = 0
  · subst hzero
    refine ⟨1, 0, by simp, ?_, ?_⟩
    · rcases hfull with ⟨x, hxint⟩
      have hzero_mem : (0 : Fin 0 → ℝ) ∈ (K : Set (Fin 0 → ℝ)) := by
        -- A full-dimensional body in `ℝ^0` contains the unique ambient point.
        simpa [Subsingleton.elim x 0] using interior_subset hxint
      intro y hy
      -- Every point of the ellipsoid is also the unique ambient point.
      simpa [Subsingleton.elim y 0] using hzero_mem
    · rcases hfull with ⟨x, hxint⟩
      have hKnonempty : ((K : Set (Fin 0 → ℝ))).Nonempty := ⟨x, interior_subset hxint⟩
      intro d
      have hEllipsoidNonempty :
          (euclideanEllipsoid
            ((1 : Matrix (Fin 0) (Fin 0) ℚ).map (Rat.castHom ℝ)) 0).Nonempty := by
        exact ⟨0, center_mem_euclideanEllipsoid _ _⟩
      have hEllipsoidWidth :
          directional_width
            (euclideanEllipsoid
              ((1 : Matrix (Fin 0) (Fin 0) ℚ).map (Rat.castHom ℝ)) 0) d = 0 :=
        directionalWidth_fin_zero_of_nonempty hEllipsoidNonempty d
      -- Both widths vanish in dimension `0`, so the bridge estimate is immediate.
      rw [directionalWidth_fin_zero_of_nonempty hKnonempty d, hEllipsoidWidth]
      norm_num
  · rcases existsJohnEllipsoidSandwich_of_fullDimensional K hzero hfull with
      ⟨C, a, hdet, hsubset, hcover⟩
    refine ⟨C, a, hdet, hsubset, ?_⟩
    intro d
    have hEllipsoidNonempty :
        (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a).Nonempty := by
      rcases K.nonempty with ⟨x, hxK⟩
      rcases hcover hxK with ⟨y, hyE, rfl⟩
      exact ⟨y, hyE⟩
    have hEllipsoidClosed : IsClosed (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) :=
      isClosed_euclideanEllipsoid _ _
    have hEllipsoidCompact : IsCompact (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) :=
      IsCompact.of_isClosed_subset K.isCompact hEllipsoidClosed hsubset
    have hOuterCompact :
        IsCompact (((fun x ↦ a + (n + 1 : ℝ) • (x - a)) ''
          euclideanEllipsoid (C.map (Rat.castHom ℝ)) a)) := by
      have hcont : Continuous fun x : Fin n → ℝ => a + (n + 1 : ℝ) • (x - a) := by
        -- The outer covering map is an affine self-map of `ℝ^n`.
        exact continuous_const.add (continuous_const.smul (continuous_id.sub continuous_const))
      simpa using hEllipsoidCompact.image hcont
    have hn_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
    -- Compare `K` with the outer affine image and then rewrite that image width exactly.
    calc
      directional_width (K : Set (Fin n → ℝ)) d
          ≤ directional_width
              (((fun x ↦ a + (n + 1 : ℝ) • (x - a)) ''
                euclideanEllipsoid (C.map (Rat.castHom ℝ)) a)) d :=
            directionalWidth_mono
              (S := (K : Set (Fin n → ℝ)))
              (T := ((fun x ↦ a + (n + 1 : ℝ) • (x - a)) ''
                euclideanEllipsoid (C.map (Rat.castHom ℝ)) a))
              K.nonempty hOuterCompact hcover
      _ = (n + 1 : ℝ) *
          directional_width (euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) d := by
            rw [directionalWidth_image_centerDilate
              hEllipsoidNonempty hEllipsoidCompact hn_nonneg d]

end FlatnessSupport

/-- Helper for Theorem 9.7: a full-dimensional lattice-free convex body admits a certified flat
integral direction with the explicit Chapter 9 bound. -/
theorem existsFlatDirectionCertificate_of_not_containsIntegralPoint
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (hfull : K.FullDimensional)
    (hfree : ¬ K.ContainsIntegralPoint) :
    Nonempty (FlatDirectionCertificate (K : Set (Fin n → ℝ))) := by
  -- Route correction: the old monolithic blocker is replaced by a short assembly proof. The only
  -- remaining missing ingredients are the two support-local geometric theorems above.
  rcases FlatnessSupport.existsEllipsoidWidthBridge_of_fullDimensional K hfull with
    ⟨C, a, hdet, hsubset, hwidthBridge⟩
  have hellipsoidFree :
      ¬ contains_integral_point
        (FlatnessSupport.euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) := by
    -- Any integral point in the inscribed ellipsoid would also be an integral point of `K`.
    exact
      not_contains_integral_point_of_subset hsubset
        (by simpa [ConvexBody.ContainsIntegralPoint] using hfree)
  rcases
      FlatnessSupport.existsFlatDirection_of_latticeFreeEuclideanEllipsoid
        C a hdet hellipsoidFree with
    ⟨d, hd_ne, hd_ellipsoid⟩
  refine ⟨⟨d, hd_ne, ?_⟩⟩
  have hscaled :
      directional_width (K : Set (Fin n → ℝ)) d ≤
        (n + 1 : ℝ) * FlatnessSupport.ellipsoidFlatnessBound n := by
    -- Transport the ellipsoid width bound back to `K` along the bridge inequality.
    calc
      directional_width (K : Set (Fin n → ℝ)) d ≤
          (n + 1 : ℝ) * directional_width
            (FlatnessSupport.euclideanEllipsoid (C.map (Rat.castHom ℝ)) a) d :=
        hwidthBridge d
      _ ≤ (n + 1 : ℝ) * FlatnessSupport.ellipsoidFlatnessBound n := by
        nlinarith [show (0 : ℝ) ≤ n + 1 by positivity, hd_ellipsoid]
  -- Rewrite the support-side constant into the public theorem-side bound and package the witness.
  simpa [FlatnessSupport.flatDirectionBound_eq_mul_ellipsoidFlatnessBound] using hscaled

/-- Helper for Theorem 9.7: every full-dimensional compact rational polyhedron has the Chapter 9
output type, either an integral point certificate or a flat-direction certificate. -/
theorem existsCertifiedOutput_of_fullDimensionalCompactRationalPolyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
    (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
    Nonempty
      (Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
        (FlatDirectionCertificate (rational_matrix_polyhedron A b))) := by
  classical
  by_cases hpoint : contains_integral_point (rational_matrix_polyhedron A b)
  · -- If the polyhedron already contains an integral point, return it directly.
    rcases existsIntegralPointCertificate_of_containsIntegralPoint hpoint with ⟨point⟩
    exact ⟨Sum.inl point⟩
  · -- Otherwise transfer the input to the `ConvexBody` owner and use the flatness certificate.
    have hbodyFull :
        (rationalMatrixPolyhedronConvexBody A b hfull hcompact).FullDimensional := by
      simpa [ConvexBody.FullDimensional, rationalMatrixPolyhedronConvexBody] using hfull
    have hbodyFree :
        ¬ (rationalMatrixPolyhedronConvexBody A b hfull hcompact).ContainsIntegralPoint := by
      simpa [ConvexBody.ContainsIntegralPoint, rationalMatrixPolyhedronConvexBody] using hpoint
    rcases
        existsFlatDirectionCertificate_of_not_containsIntegralPoint
          (K := rationalMatrixPolyhedronConvexBody A b hfull hcompact) hbodyFull hbodyFree with
      ⟨direction⟩
    exact ⟨Sum.inr direction⟩

/-- Theorem 9.7 (1) (Flatness Theorem). There exists a function `k : ℕ → ℝ`
depending only on the dimension such that every full-dimensional convex body
`K ⊆ ℝ^n` with no integral point has lattice width, equivalently the infimum of
the widths `w_{d}(K)` over nonzero integral directions, at most `k n`. Here
full dimensionality is represented by `K.FullDimensional`, i.e. nonempty
interior. -/
theorem exists_flatness_constant_for_lattice_width :
    ∃ k : ℕ → ℝ,
      ∀ {n : ℕ}, ∀ K : ConvexBody (Fin n → ℝ),
        K.FullDimensional →
        ¬ K.ContainsIntegralPoint →
        lattice_width K ≤ k n := by
  refine ⟨flat_direction_bound, ?_⟩
  intro n K hfull hfree
  -- Reduce the width bound to the stronger flat-direction certificate statement.
  exact latticeWidth_le_of_flatDirectionCertificate
    (K := K)
    (existsFlatDirectionCertificate_of_not_containsIntegralPoint K hfull hfree)

/-- Theorem 9.7 (2). For rational polytopes given by rational linear inequalities, there is a
polynomial-time algorithm that, on every full-dimensional compact input `P = {x ∈ ℝ^n | A x ≤ b}`,
returns either an integral point of `P` or a flat direction `d ∈ ℤ^n` with
`w_{d}(P) ≤ n (n + 1) 2^{n (n - 1) / 4}`. -/
theorem exists_rational_polytope_flatness_algorithm
    (m n : ℕ) :
    ∃ algorithm : RationalPolytopeFlatnessAlgorithm m n,
      RationalPolytopeFlatnessAlgorithm.Certified algorithm := by
  classical
  let algorithm : RationalPolytopeFlatnessAlgorithm m n :=
    { run := fun A b ↦
        if h : (interior (rational_matrix_polyhedron A b)).Nonempty ∧
            IsCompact (rational_matrix_polyhedron A b) then
          some
            (Classical.choice
              (existsCertifiedOutput_of_fullDimensionalCompactRationalPolyhedron A b h.1 h.2))
        else
          none
      runTime := fun _ _ ↦ 0 }
  refine ⟨algorithm, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The packaged solver is constant-time, so the zero polynomial bounds its runtime.
    refine ⟨0, ?_⟩
    intro A b
    simp [algorithm]
  · intro A b hfull hcompact
    -- On valid inputs the `if` branch exposes the pre-chosen certified output.
    refine
      ⟨Classical.choice
        (existsCertifiedOutput_of_fullDimensionalCompactRationalPolyhedron A b hfull hcompact), ?_⟩
    simp [algorithm, hfull, hcompact]

end Theorem97
