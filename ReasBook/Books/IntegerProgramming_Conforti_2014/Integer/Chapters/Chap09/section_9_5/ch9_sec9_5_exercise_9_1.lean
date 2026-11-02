import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Data.Int.ModEq
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_8
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_3_theorem_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain style sampling:
-- * primary domain: kernels of integer linear congruence maps as full-rank sublattices of `ℤ^n`
-- * source-facing owner kept here: the congruence kernel `exercise_9_1_congruence_lattice`
-- * core/canonical owners reused here: `is_primitive_integer_vector`, `Submodule.IsLattice`,
--   and additive-subgroup index

section Exercise91

variable {n : ℕ}

/-- The linear congruence map `x ↦ ∑ i, k_i x_i mod p` used in Exercise 9.1. -/
noncomputable def exercise_9_1_congruence_map
    (k : Fin n → ℤ) (p : ℕ+) :
    (Fin n → ℤ) →ₗ[ℤ] ZMod (p : ℕ) :=
  LinearMap.lsum ℤ (fun _ ↦ ℤ) ℤ fun i ↦
    (k i : ZMod (p : ℕ)) • (Int.castAddHom (ZMod (p : ℕ))).toIntLinearMap

/-- The congruence submodule
`Λ = {x ∈ ℤ^n | ∑ i k_i x_i ≡ 0 mod p}`
from Exercise 9.1. -/
noncomputable def exercise_9_1_congruence_lattice
    (k : Fin n → ℤ) (p : ℕ+) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (exercise_9_1_congruence_map k p)

/-- The coordinatewise embedding of `ℤ^n` into `ℚ^n`. -/
noncomputable def exercise_9_1_rational_embedding :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) :=
  LinearMap.pi fun i ↦
    (Int.castAddHom ℚ).toIntLinearMap.comp
      (LinearMap.proj i : (Fin n → ℤ) →ₗ[ℤ] ℤ)

/-- The congruence lattice of Exercise 9.1 viewed as a `ℤ`-submodule of `ℚ^n`. -/
noncomputable def exercise_9_1_rational_lattice
    (k : Fin n → ℤ) (p : ℕ+) : Submodule ℤ (Fin n → ℚ) :=
  (exercise_9_1_congruence_lattice k p).map exercise_9_1_rational_embedding

/-- The coordinatewise embedding `ℤ^n → ℚ^n` sends each coordinate to the corresponding rational
number. -/
@[simp] theorem exercise_9_1_rational_embedding_apply
    (x : Fin n → ℤ) (i : Fin n) :
    exercise_9_1_rational_embedding x i = x i := by
  simp [exercise_9_1_rational_embedding]

/-- The coordinatewise embedding `ℤ^n → ℚ^n` is injective. -/
theorem exercise_9_1_rational_embedding_injective :
    Function.Injective (exercise_9_1_rational_embedding : (Fin n → ℤ) → Fin n → ℚ) := by
  intro x y hxy
  ext i
  exact Int.cast_injective <| congrFun hxy i

/-- Membership in `exercise_9_1_rational_lattice k p` is exactly the existence of an integral
congruence vector whose image in `ℚ^n` is the given point. -/
theorem mem_exercise_9_1_rational_lattice_iff
    (k : Fin n → ℤ) (p : ℕ+) (x : Fin n → ℚ) :
    x ∈ exercise_9_1_rational_lattice k p ↔
      ∃ y, y ∈ exercise_9_1_congruence_lattice k p ∧
        exercise_9_1_rational_embedding y = x := by
  change x ∈ (exercise_9_1_congruence_lattice k p).map exercise_9_1_rational_embedding ↔
    ∃ y, y ∈ exercise_9_1_congruence_lattice k p ∧ exercise_9_1_rational_embedding y = x
  exact Submodule.mem_map

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_1.lean`: the congruence map evaluates to
the integer dot product reduced modulo `p`. -/
  theorem exercise_9_1_congruence_map_apply
    (k : Fin n → ℤ) (p : ℕ+) (x : Fin n → ℤ) :
    exercise_9_1_congruence_map k p x =
      (((∑ i, k i * x i : ℤ)) : ZMod (p : ℕ)) := by
  -- Expand the linear combination coordinatewise and collect the resulting integer cast.
  simp [exercise_9_1_congruence_map]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_1.lean`: a primitive integer vector has
coefficient gcd equal to `1`. -/
lemma primitiveCoefficientGcd_eq_one
    {k : Fin n → ℤ}
    (hprimitive : is_primitive_integer_vector k) :
    coefficientGcd k = 1 := by
  rcases hprimitive with ⟨_, hgcdOne⟩
  have hnatAbsDvd :
      Int.natAbs (coefficientGcd k) ∣
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (k i)) := by
    -- The coefficient gcd divides every coordinate, hence its absolute value divides the row gcd.
    refine Finset.dvd_gcd ?_
    intro i hi
    exact Int.natAbs_dvd_natAbs.mpr (coefficientGcd_dvd k i)
  have hnatAbsEqOne : Int.natAbs (coefficientGcd k) = 1 := by
    exact Nat.dvd_one.mp (by simpa [hgcdOne] using hnatAbsDvd)
  have hcoeffNonneg : 0 ≤ coefficientGcd k := by
    exact Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := k))
  -- The normalization convention makes the integer gcd equal to its nonnegative absolute value.
  calc
    coefficientGcd k = (Int.natAbs (coefficientGcd k) : ℤ) := by
      symm
      exact Int.natAbs_of_nonneg hcoeffNonneg
    _ = 1 := by
      exact_mod_cast hnatAbsEqOne

/-- Membership in `exercise_9_1_congruence_lattice k p` is exactly the defining congruence
`∑ i k_i x_i ≡ 0 mod p`. -/
theorem mem_exercise_9_1_congruence_lattice_iff
    (k : Fin n → ℤ) (p : ℕ+) (x : Fin n → ℤ) :
    x ∈ exercise_9_1_congruence_lattice k p ↔
      (∑ i, k i * x i) ≡ 0 [ZMOD (p : ℤ)] := by
  -- Rewrite membership in the kernel as vanishing of the defining linear congruence map.
  rw [exercise_9_1_congruence_lattice, LinearMap.mem_ker]
  -- Normalize the map to the integer dot product interpreted in `ZMod p`.
  rw [exercise_9_1_congruence_map_apply]
  -- Vanishing in `ZMod p` is equivalent to divisibility by `p`, hence to the stated congruence.
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.modEq_zero_iff_dvd]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_1.lean`: primitivity makes the
congruence map onto `ZMod p`. -/
lemma exercise_9_1_congruence_map_surjective
    (k : Fin n → ℤ) (p : ℕ+)
    (hprimitive : is_primitive_integer_vector k) :
    Function.Surjective (exercise_9_1_congruence_map k p) := by
  -- Choose a Bezout vector whose dot product with `k` is exactly `1`.
  have hcoeff : coefficientGcd k = 1 := primitiveCoefficientGcd_eq_one hprimitive
  obtain ⟨u, hu⟩ := exists_sum_mul_eq_coefficientGcd k
  have hu_one : exercise_9_1_congruence_map k p u = 1 := by
    -- The normalization lemma turns the Bezout identity into the image calculation.
    rw [exercise_9_1_congruence_map_apply, hu, hcoeff]
    norm_num
  intro z
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨m • u, ?_⟩
  -- Scale the Bezout vector to hit an arbitrary residue class.
  calc
    exercise_9_1_congruence_map k p (m • u)
        = m • exercise_9_1_congruence_map k p u := by
            rw [LinearMap.map_smul]
    _ = m • (1 : ZMod (p : ℕ)) := by
          rw [hu_one]
    _ = (m : ZMod (p : ℕ)) := by
          simp

/-- Exercise 9.1 (1). If the integers `k₁, …, kₙ` are relatively prime, equivalently if `k` is a
primitive integer vector, then the congruence set
`Λ = {x ∈ ℤ^n | ∑ i k_i x_i ≡ 0 mod p}` is a lattice. Here the lattice is realized as the
corresponding full-rank `ℤ`-submodule of `ℚ^n`. -/
theorem exercise_9_1_congruence_lattice_is_lattice
    (k : Fin n → ℤ) (p : ℕ+)
    (hprimitive : is_primitive_integer_vector k) :
    Submodule.IsLattice ℚ (exercise_9_1_rational_lattice k p) := by
  have hrange :
      (exercise_9_1_congruence_map k p).toAddMonoidHom.range = ⊤ := by
    -- Surjectivity identifies the additive range with the whole residue module.
    ext z
    constructor
    · intro hz
      trivial
    · intro hz
      rcases exercise_9_1_congruence_map_surjective k p hprimitive z with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hindex_ne_zero :
      (exercise_9_1_congruence_lattice k p).toAddSubgroup.index ≠ 0 := by
    -- Compute the index through the surjective congruence map and use `p > 0`.
    have hindex :
        (exercise_9_1_congruence_lattice k p).toAddSubgroup.index =
          Nat.card ((exercise_9_1_congruence_map k p).toAddMonoidHom.range) := by
      simpa [exercise_9_1_congruence_lattice, LinearMap.ker_toAddSubgroup] using
        AddSubgroup.index_ker (exercise_9_1_congruence_map k p).toAddMonoidHom
    rw [hindex]
    rw [hrange]
    simp
  obtain ⟨e⟩ := (Int.submodule_toAddSubgroup_index_ne_zero_iff
    (N := exercise_9_1_congruence_lattice k p)).mp hindex_ne_zero
  have hfgSource : (exercise_9_1_congruence_lattice k p).FG := by
    -- A nonzero finite index produces a linear equivalence with the ambient free module.
    let hfinite : Module.Finite ℤ (exercise_9_1_congruence_lattice k p) :=
      Module.Finite.equiv e.symm
    exact Module.Finite.iff_fg.mp hfinite
  have hfg :
      (exercise_9_1_rational_lattice k p).FG := by
    -- Mapping along the injective rational embedding preserves finite generation.
    simpa [exercise_9_1_rational_lattice] using
      (Submodule.FG.map (f := exercise_9_1_rational_embedding) hfgSource)
  have hsourceRank :
      Module.rank ℤ (exercise_9_1_congruence_lattice k p) =
        Module.rank ℤ (Fin n → ℤ) := by
    exact e.rank_eq
  have hmapRank :
      Module.rank ℤ (exercise_9_1_rational_lattice k p) =
        Module.rank ℤ (exercise_9_1_congruence_lattice k p) := by
    simpa [exercise_9_1_rational_lattice] using
      (rank_map_eq exercise_9_1_rational_embedding_injective
        (exercise_9_1_congruence_lattice k p))
  -- The rational image has full rank, so the generic lattice criterion applies.
  refine Submodule.IsLattice.of_rank_le (K := ℚ) hfg ?_
  calc
    Module.rank ℚ (Fin n → ℚ) = Module.rank ℤ (Fin n → ℤ) := by
      simp [rank_pi]
    _ = Module.rank ℤ (exercise_9_1_congruence_lattice k p) := by
      rw [hsourceRank]
    _ = Module.rank ℤ (exercise_9_1_rational_lattice k p) := by
      rw [hmapRank.symm]
    _ ≤ Module.rank ℤ (exercise_9_1_rational_lattice k p) := le_rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_1.lean

Exercise 9.1 (2). For this full-rank sublattice of `ℤ^n`, the determinant is its index in the
ambient integer lattice; this index is `p`. -/
theorem exercise_9_1_congruence_lattice_index_eq
    (k : Fin n → ℤ) (p : ℕ+)
    (hprimitive : is_primitive_integer_vector k) :
    (exercise_9_1_congruence_lattice k p).toAddSubgroup.index = p := by
  have hrange :
      (exercise_9_1_congruence_map k p).toAddMonoidHom.range = ⊤ := by
    -- Surjectivity identifies the additive range with the whole codomain.
    ext z
    constructor
    · intro hz
      trivial
    · intro hz
      rcases exercise_9_1_congruence_map_surjective k p hprimitive z with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  -- Compute the kernel index from the cardinality of the surjective range.
  calc
    (exercise_9_1_congruence_lattice k p).toAddSubgroup.index
        = Nat.card ((exercise_9_1_congruence_map k p).toAddMonoidHom.range) := by
            simpa [exercise_9_1_congruence_lattice, LinearMap.ker_toAddSubgroup] using
              AddSubgroup.index_ker (exercise_9_1_congruence_map k p).toAddMonoidHom
    _ = Nat.card (ZMod (p : ℕ)) := by
          rw [hrange]
          simp
    _ = p := by
          simp

end Exercise91
