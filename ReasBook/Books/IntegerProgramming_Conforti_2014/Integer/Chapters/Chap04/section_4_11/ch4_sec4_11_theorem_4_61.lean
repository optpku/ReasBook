/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_11.ch4_sec4_11_theorem_4_60
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_42
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_theorem_3_35
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators Matrix

section Theorem461

variable {n k : ℕ}

/-- Helper for Theorem 4.61: the feasible coefficient vectors representing `x` by `v`. -/
def realConeCoefficientFiber
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ) (x : Fin n → ℝ) : Set (ι → ℝ) :=
  {c | (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

/-- Helper for Theorem 4.61: a finite salient generated cone admits a linear functional that is
strictly positive on every nonzero generator. -/
lemma exists_strictlyPositivePairing_on_nonzeroGenerators
    {ι : Type*} [Finite ι]
    (v : ι → Fin n → ℝ)
    (hv_ne : ∀ i, v i ≠ 0)
    (h_pointed :
      ((PointedCone.hull ℝ (Set.range v) : ConvexCone ℝ (Fin n → ℝ))).Salient) :
    ∃ d : Fin n → ℝ, ∀ i, 0 < d ⬝ᵥ v i := by
  classical
  let C : PointedCone ℝ (Fin n → ℝ) := PointedCone.hull ℝ (Set.range v)
  have hC_fg : C.FG := by
    -- The finite generating family makes the cone polyhedral.
    simpa [C] using Submodule.fg_span (Set.finite_range v)
  have hC_polyhedral : is_polyhedral_cone (C : Set (Fin n → ℝ)) :=
    (Theorem442Local.isFinitelyGeneratedCone_iff_isPolyhedralCone (C := C)).mp hC_fg
  rcases (is_polyhedral_cone_iff.mp hC_polyhedral) with ⟨m, A, hC_eq⟩
  have hA_pointed : is_pointed (matrix_polyhedral_cone A) := by
    rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
    intro y hy
    have hzero : (0 : Fin n → ℝ) ∈ matrix_polyhedral_cone A :=
      matrix_polyhedral_cone_zero_mem A
    have hy_mem : y ∈ matrix_polyhedral_cone A := by
      have := (mem_linealitySpace_iff.mp hy) hzero (1 : ℝ)
      simpa using this
    have hneg_mem : -y ∈ matrix_polyhedral_cone A := by
      have := (mem_linealitySpace_iff.mp hy) hzero (-1 : ℝ)
      simpa using this
    have hyC : y ∈ (C : Set (Fin n → ℝ)) := by
      rw [hC_eq]
      exact hy_mem
    have hnegC : -y ∈ (C : Set (Fin n → ℝ)) := by
      rw [hC_eq]
      exact hneg_mem
    by_contra hy_ne
    exact h_pointed y hyC hy_ne hnegC
  refine ⟨-rowSumFunctional A, ?_⟩
  intro i
  have hviC : v i ∈ (C : Set (Fin n → ℝ)) := by
    exact Submodule.subset_span ⟨i, rfl⟩
  have hviA : v i ∈ matrix_polyhedral_cone A := by
    change v i ∈ polyhedron_le_set A 0
    rw [← hC_eq]
    exact hviC
  have hneg :=
    row_sum_strictly_negative_of_mem_matrix_polyhedral_cone_ne_zero
      A hA_pointed hviA (hv_ne i)
  -- Negating the row-sum functional turns strict negativity into strict positivity.
  simpa [dotProduct, Finset.sum_neg_distrib] using neg_pos.mpr hneg

/-- Helper for Theorem 4.61: membership in a finite real cone supplies coefficients on the
original finite index type. -/
lemma exists_nonnegative_real_coefficient_function_of_mem_hull
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ (PointedCone.hull ℝ (Set.range v) : Set (Fin n → ℝ))) :
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i := by
  classical
  rcases (mem_hull_iff.mp hx) with ⟨s, r, hr_mem, coeff, hcoeff_nonneg, hx_eq⟩
  let idx : Fin s → ι := fun j ↦ Classical.choose (hr_mem j)
  have hidx : ∀ j : Fin s, v (idx j) = r j := by
    intro j
    exact Classical.choose_spec (hr_mem j)
  let c : ι → ℝ := fun i ↦ ∑ j : Fin s, if idx j = i then coeff j else 0
  refine ⟨c, ?_, ?_⟩
  · -- Aggregating coefficients over repeated generators preserves nonnegativity.
    intro i
    have hterm_nonneg : ∀ j ∈ Finset.univ, 0 ≤ if idx j = i then coeff j else 0 := by
      intro j _
      by_cases hj : idx j = i
      · simp [hj, hcoeff_nonneg j]
      · simp [hj]
    exact Finset.sum_nonneg hterm_nonneg
  · -- Regroup the selected cone representation by its original generator indices.
    ext t
    symm
    calc
      (∑ i : ι, c i • v i) t = ∑ i : ι, c i * v i t := by
        simp [Pi.smul_apply]
      _ = ∑ i : ι, (∑ j : Fin s, if idx j = i then coeff j else 0) * v i t := by
        simp [c]
      _ = ∑ i : ι, ∑ j : Fin s, (if idx j = i then coeff j else 0) * v i t := by
        simp_rw [Finset.sum_mul]
      _ = ∑ j : Fin s, ∑ i : ι, (if idx j = i then coeff j else 0) * v i t := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin s, coeff j * r j t := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [hidx j]
      _ = (∑ j : Fin s, coeff j • r j) t := by
        simp [Pi.smul_apply]
      _ = x t := by
        simpa using (congrFun hx_eq t).symm

/-- Helper for Theorem 4.61: an integral point in a finite real cone belongs to the corresponding
rational cone. -/
lemma integral_point_mem_rational_hull_of_mem_real_hull
    {l : ℕ}
    {a : Fin l → Fin n → ℤ}
    {z : Fin n → ℤ}
    (hz :
      (fun j ↦ (z j : ℝ)) ∈
        (PointedCone.hull ℝ (Set.range fun i ↦ fun j ↦ (a i j : ℝ)) : Set (Fin n → ℝ))) :
    (fun j ↦ (z j : ℚ)) ∈
      (PointedCone.hull ℚ (Set.range fun i ↦ fun j ↦ (a i j : ℚ)) : Set (Fin n → ℚ)) := by
  classical
  rcases (mem_hull_iff.mp hz) with ⟨s, r, hr_mem, coeffR, hcoeffR_nonneg, hz_eq⟩
  let idx : Fin s → Fin l := fun j ↦ Classical.choose (hr_mem j)
  have hidx : ∀ j : Fin s, r j = fun t ↦ (a (idx j) t : ℝ) := by
    intro j
    exact (Classical.choose_spec (hr_mem j)).symm
  let M : Matrix (Fin s) (Fin n) ℚ := fun j t ↦ a (idx j) t
  have hreal :
      ∃ xR : Fin s → ℝ,
        (xR ᵥ* (M.map (Rat.castHom ℝ)) = fun t ↦ (z t : ℝ)) ∧ 0 ≤ xR := by
    refine ⟨coeffR, ?_, hcoeffR_nonneg⟩
    -- Rewrite the cone witness as the rational matrix system after scalar extension.
    ext t
    calc
      (coeffR ᵥ* (M.map (Rat.castHom ℝ))) t = ∑ j : Fin s, coeffR j * r j t := by
        simp [M, Matrix.vecMul, dotProduct, hidx]
      _ = (∑ j : Fin s, coeffR j • r j) t := by simp [smul_eq_mul]
      _ = (fun t ↦ (z t : ℝ)) t := by
        simpa using congrArg (fun f : Fin n → ℝ ↦ f t) hz_eq.symm
  obtain ⟨coeffQ, hcoeffQ_row, hcoeffQ_nonneg⟩ :=
    exists_rat_nonnegative_solution_of_real_cast_feasible
      M (fun t ↦ (z t : ℚ)) hreal
  have hzQ_eq :
      (fun t ↦ (z t : ℚ)) =
        ∑ j : Fin s, coeffQ j • (fun t ↦ (a (idx j) t : ℚ)) := by
    ext t
    calc
      (fun u ↦ (z u : ℚ)) t = (coeffQ ᵥ* M) t := by
        simpa using (congrFun hcoeffQ_row t).symm
      _ = (∑ j : Fin s, coeffQ j • (fun u ↦ (a (idx j) u : ℚ))) t := by
        simp [M, Matrix.vecMul, dotProduct, smul_eq_mul]
  have hmem_idx :
      (fun t ↦ (z t : ℚ)) ∈
        (PointedCone.hull ℚ
          (Set.range fun j : Fin s ↦ fun t ↦ (a (idx j) t : ℚ)) : Set (Fin n → ℚ)) := by
    refine mem_hull_of_equivFin_nonnegative_family
      (fun j : Fin s ↦ fun t ↦ (a (idx j) t : ℚ)) coeffQ
      (fun t ↦ (z t : ℚ)) hcoeffQ_nonneg ?_
    simpa using hzQ_eq
  have hsubset :
      Set.range (fun j : Fin s ↦ fun t ↦ (a (idx j) t : ℚ)) ⊆
        Set.range (fun i : Fin l ↦ fun t ↦ (a i t : ℚ)) := by
    rintro y ⟨j, rfl⟩
    exact ⟨idx j, rfl⟩
  -- Enlarge the rationalized selected cone to the original finite family.
  exact (Submodule.span_mono hsubset) hmem_idx

/-- Helper for Theorem 4.61: equality of integral vectors follows from equality of their rational
casts, including a finitely supported integral combination. -/
lemma eq_of_rat_finsupp_sum_eq
    {ι : Type*} [Finite ι]
    (a : ι → Fin n → ℤ)
    {z : Fin n → ℤ}
    {μ : ι →₀ ℕ}
    (hz :
      (fun t ↦ (z t : ℚ)) =
        μ.sum (fun i m ↦ m • fun t ↦ (a i t : ℚ))) :
    z = μ.sum (fun i m ↦ m • a i) := by
  classical
  -- Local instance justification (finite enumeration): `sum_fintype` expands both finitely
  -- supported sums over the finite index type.
  letI : Fintype ι := Fintype.ofFinite ι
  ext t
  have hcoord := congrFun hz t
  have hzero_int : ∀ i, (0 : ℕ) • a i = 0 := by
    intro i
    simp
  have hzero_rat : ∀ i, (0 : ℕ) • (fun s ↦ (a i s : ℚ)) = 0 := by
    intro i
    simp
  have hcast :
      ((μ.sum (fun i m ↦ m • a i)) t : ℚ) =
        (μ.sum (fun i m ↦ m • fun s ↦ (a i s : ℚ))) t := by
    rw [Finsupp.sum_fintype _ _ hzero_int, Finsupp.sum_fintype _ _ hzero_rat]
    simp
  have : (z t : ℚ) = ((μ.sum (fun i m ↦ m • a i)) t : ℚ) :=
    hcoord.trans hcast.symm
  exact_mod_cast this

/-- Helper for Theorem 4.61: a coefficient fiber over nonzero generators is compact. -/
lemma realConeCoefficientFiber_isCompact
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (x : Fin n → ℝ)
    (hv_ne : ∀ i, v i ≠ 0)
    (h_pointed :
      ((PointedCone.hull ℝ (Set.range v) : ConvexCone ℝ (Fin n → ℝ))).Salient) :
    IsCompact (realConeCoefficientFiber v x) := by
  classical
  obtain ⟨d, hd⟩ :=
    exists_strictlyPositivePairing_on_nonzeroGenerators v hv_ne h_pointed
  let B : ι → ℝ := fun i ↦ (d ⬝ᵥ x) / (d ⬝ᵥ v i)
  have hweighted (c : ι → ℝ) (hc : c ∈ realConeCoefficientFiber v x) :
      d ⬝ᵥ x = ∑ i, c i * (d ⬝ᵥ v i) := by
    rcases hc with ⟨hc_nonneg, hc_eq⟩
    rw [hc_eq]
    calc
      d ⬝ᵥ (∑ i, c i • v i) = ∑ t, ∑ i, d t * (c i * v i t) := by
        simp [dotProduct, Finset.mul_sum, Pi.smul_apply]
      _ = ∑ i, ∑ t, d t * (c i * v i t) := by
        rw [Finset.sum_comm]
      _ = ∑ i, c i * (d ⬝ᵥ v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [dotProduct, Finset.mul_sum, mul_left_comm, mul_comm]
  have hsubset : realConeCoefficientFiber v x ⊆ Set.Icc 0 B := by
    intro c hc
    rcases hc with ⟨hc_nonneg, hc_eq⟩
    constructor
    · exact hc_nonneg
    · intro i
      have hterm_nonneg : ∀ j : ι, 0 ≤ c j * (d ⬝ᵥ v j) := by
        intro j
        exact mul_nonneg (hc_nonneg j) (hd j).le
      have hi_le : c i * (d ⬝ᵥ v i) ≤ ∑ j, c j * (d ⬝ᵥ v j) := by
        exact Finset.single_le_sum (fun j _ ↦ hterm_nonneg j) (Finset.mem_univ i)
      rw [← hweighted c ⟨hc_nonneg, hc_eq⟩] at hi_le
      exact (le_div_iff₀ (hd i)).2 hi_le
  have hclosed : IsClosed (realConeCoefficientFiber v x) := by
    have hnonneg : IsClosed {c : ι → ℝ | ∀ i, 0 ≤ c i} := by
      change IsClosed (Set.Ici (0 : ι → ℝ))
      exact isClosed_Ici
    have hsum_continuous : Continuous (fun c : ι → ℝ ↦ ∑ i, c i • v i) := by
      fun_prop
    have heq : IsClosed {c : ι → ℝ | x = ∑ i, c i • v i} := by
      exact isClosed_eq continuous_const hsum_continuous
    simpa [realConeCoefficientFiber, Set.setOf_and] using hnonneg.inter heq
  -- A closed subset of the compact coordinate box is compact.
  exact IsCompact.of_isClosed_subset isCompact_Icc hclosed hsubset

/-- Helper for Theorem 4.61: total coefficient mass attains a maximum on a nonempty coefficient
fiber over nonzero generators. -/
lemma exists_massMaximal_coefficient
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (x : Fin n → ℝ)
    (hv_ne : ∀ i, v i ≠ 0)
    (h_pointed :
      ((PointedCone.hull ℝ (Set.range v) : ConvexCone ℝ (Fin n → ℝ))).Salient)
    (hx : x ∈ (PointedCone.hull ℝ (Set.range v) : Set (Fin n → ℝ))) :
    ∃ c ∈ realConeCoefficientFiber v x,
      ∀ d ∈ realConeCoefficientFiber v x, ∑ i, d i ≤ ∑ i, c i := by
  obtain ⟨c₀, hc₀_nonneg, hc₀_eq⟩ :=
    exists_nonnegative_real_coefficient_function_of_mem_hull v hx
  have hfiber_nonempty : (realConeCoefficientFiber v x).Nonempty :=
    ⟨c₀, hc₀_nonneg, hc₀_eq⟩
  have hcontinuous : Continuous (fun c : ι → ℝ ↦ ∑ i, c i) := by
    fun_prop
  -- Apply the extreme-value theorem to the compact coefficient fiber.
  exact
    (realConeCoefficientFiber_isCompact v x hv_ne h_pointed).exists_isMaxOn
      hfiber_nonempty hcontinuous.continuousOn

/-- Helper for Theorem 4.61: the finite support of a real coefficient vector. -/
noncomputable def realCoefficientSupport
    {ι : Type*} [Fintype ι] (c : ι → ℝ) : Finset ι :=
  (Finsupp.equivFunOnFinite.symm c).support

/-- Helper for Theorem 4.61: among the mass-maximizing coefficient vectors, one has minimum
support cardinality. -/
lemma exists_massMaximal_supportMinimal_coefficient
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (x : Fin n → ℝ)
    (hv_ne : ∀ i, v i ≠ 0)
    (h_pointed :
      ((PointedCone.hull ℝ (Set.range v) : ConvexCone ℝ (Fin n → ℝ))).Salient)
    (hx : x ∈ (PointedCone.hull ℝ (Set.range v) : Set (Fin n → ℝ))) :
    ∃ c ∈ realConeCoefficientFiber v x,
      (∀ d ∈ realConeCoefficientFiber v x, ∑ i, d i ≤ ∑ i, c i) ∧
        ∀ d ∈ realConeCoefficientFiber v x,
          (∑ i, d i = ∑ i, c i) →
            (realCoefficientSupport c).card ≤ (realCoefficientSupport d).card := by
  classical
  obtain ⟨cMax, hcMax, hcMaximal⟩ :=
    exists_massMaximal_coefficient v x hv_ne h_pointed hx
  let P : ℕ → Prop := fun s ↦
    ∃ c ∈ realConeCoefficientFiber v x,
      (∀ d ∈ realConeCoefficientFiber v x, ∑ i, d i ≤ ∑ i, c i) ∧
        (realCoefficientSupport c).card = s
  have hP : ∃ s, P s := by
    exact ⟨(realCoefficientSupport cMax).card, cMax, hcMax, hcMaximal, rfl⟩
  rcases Nat.find_spec hP with ⟨c, hc, hcMaximal, hcCard⟩
  refine ⟨c, hc, hcMaximal, ?_⟩
  intro d hd hdMass
  have hdMaximal : ∀ e ∈ realConeCoefficientFiber v x, ∑ i, e i ≤ ∑ i, d i := by
    intro e he
    simpa [hdMass] using hcMaximal e he
  have hfind_le : Nat.find hP ≤ (realCoefficientSupport d).card := by
    exact Nat.find_min' hP ⟨d, hd, hdMaximal, rfl⟩
  simpa [hcCard] using hfind_le

/-- Helper for Theorem 4.61: membership in `realCoefficientSupport` is coefficient nonvanishing.
-/
lemma mem_realCoefficientSupport_iff
    {ι : Type*} [Fintype ι]
    {c : ι → ℝ} {i : ι} :
    i ∈ realCoefficientSupport c ↔ c i ≠ 0 := by
  classical
  simp [realCoefficientSupport]

/-- Helper for Theorem 4.61: a nontrivial relation with a positive coordinate gives a
nonnegative coefficient perturbation that removes at least one support index. -/
lemma exists_supportReducing_coefficient_perturbation
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (c : ι → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (u : realCoefficientSupport c → ℝ)
    (hu_relation : ∑ i, u i • v i.1 = 0)
    (hu_pos : ∃ i, 0 < u i) :
    ∃ θ : ℝ, ∃ c' : ι → ℝ,
      0 < θ ∧
        (∀ i, 0 ≤ c' i) ∧
          (∑ i, c' i • v i) = ∑ i, c i • v i ∧
            (∑ i, c' i) =
              (∑ i, c i) - θ * ∑ i : realCoefficientSupport c, u i ∧
              (realCoefficientSupport c').card < (realCoefficientSupport c).card := by
  classical
  let S := realCoefficientSupport c
  let positive : Finset S := Finset.univ.filter (fun i ↦ 0 < u i)
  obtain ⟨i₀, hi₀, hmin⟩ :
      ∃ i₀ ∈ positive, ∀ j ∈ positive, c i₀.1 / u i₀ ≤ c j.1 / u j := by
    -- Choose the largest admissible step by minimizing the positive-coordinate ratios.
    apply positive.exists_min_image fun i ↦ c i.1 / u i
    obtain ⟨i, hi⟩ := hu_pos
    have hi_positive : i ∈ positive := by simp [positive, hi]
    exact ⟨i, hi_positive⟩
  have hui₀_pos : 0 < u i₀ := by
    simpa [positive] using hi₀
  have hci₀_pos : 0 < c i₀.1 := by
    have hne : c i₀.1 ≠ 0 := mem_realCoefficientSupport_iff.mp i₀.2
    exact lt_of_le_of_ne (hc_nonneg i₀.1) hne.symm
  let θ : ℝ := c i₀.1 / u i₀
  have hθ_pos : 0 < θ := div_pos hci₀_pos hui₀_pos
  let uFull : ι → ℝ := fun i ↦ if hi : i ∈ S then u ⟨i, hi⟩ else 0
  let c' : ι → ℝ := fun i ↦ c i - θ * uFull i
  have huFull_relation : ∑ i : ι, uFull i • v i = 0 := by
    calc
      ∑ i : ι, uFull i • v i =
          ∑ i ∈ S, uFull i • v i := by
            symm
            refine Finset.sum_subset (Finset.subset_univ S) ?_
            intro i hi hnot
            have hiS : i ∉ S := by simpa using hnot
            simp [uFull, hiS]
      _ = ∑ i : S, u i • v i.1 := by
            calc
              ∑ i ∈ S, uFull i • v i = ∑ i : S, uFull i.1 • v i.1 :=
                Finset.sum_subtype S (fun _ ↦ Iff.rfl) _
              _ = ∑ i : S, u i • v i.1 := by
                apply Fintype.sum_congr
                intro i
                simp [uFull, i.2]
      _ = 0 := hu_relation
  have huFull_sum : ∑ i : ι, uFull i = ∑ i : S, u i := by
    calc
      ∑ i : ι, uFull i = ∑ i ∈ S, uFull i := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) ?_
        intro i hi hnot
        have hiS : i ∉ S := by simpa using hnot
        simp [uFull, hiS]
      _ = ∑ i : S, u i := by
        calc
          ∑ i ∈ S, uFull i = ∑ i : S, uFull i.1 :=
            Finset.sum_subtype S (fun _ ↦ Iff.rfl) _
          _ = ∑ i : S, u i := by
            apply Fintype.sum_congr
            intro i
            simp [uFull, i.2]
  have hc'_nonneg : ∀ i, 0 ≤ c' i := by
    intro i
    by_cases hiS : i ∈ S
    · let is : S := ⟨i, hiS⟩
      by_cases hui_pos : 0 < u is
      · have hi_positive : is ∈ positive := by simp [positive, hui_pos]
        have hratio : θ ≤ c i / u is := by
          simpa [θ, is] using hmin is hi_positive
        have hmul : θ * u is ≤ c i := (le_div_iff₀ hui_pos).mp hratio
        simpa [c', uFull, hiS, is] using sub_nonneg.mpr hmul
      · have hui_nonpos : u is ≤ 0 := le_of_not_gt hui_pos
        have hmul_nonpos : θ * u is ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hθ_pos.le hui_nonpos
        have : θ * u is ≤ c i := le_trans hmul_nonpos (hc_nonneg i)
        simpa [c', uFull, hiS, is] using sub_nonneg.mpr this
    · have hci : c i = 0 := by
        exact not_ne_iff.mp (mt mem_realCoefficientSupport_iff.mpr hiS)
      simp [c', uFull, hiS, hci]
  have hc'_sum_v : (∑ i, c' i • v i) = ∑ i, c i • v i := by
    calc
      ∑ i, c' i • v i =
          (∑ i, c i • v i) - θ • ∑ i, uFull i • v i := by
            simp [c', sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
      _ = ∑ i, c i • v i := by rw [huFull_relation]; simp
  have hc'_mass :
      (∑ i, c' i) = (∑ i, c i) - θ * ∑ i : S, u i := by
    calc
      ∑ i, c' i = (∑ i, c i) - ∑ i, θ * uFull i := by
        simp [c', Finset.sum_sub_distrib]
      _ = (∑ i, c i) - θ * ∑ i, uFull i := by
        rw [Finset.mul_sum]
      _ = (∑ i, c i) - θ * ∑ i : S, u i := by
        rw [huFull_sum]
  have hc'i₀ : c' i₀.1 = 0 := by
    have hθ_mul : θ * u i₀ = c i₀.1 := by
      dsimp [θ]
      field_simp [hui₀_pos.ne']
    simp [c', uFull, i₀.2, hθ_mul]
  have hsupport_subset : realCoefficientSupport c' ⊆ S.erase i₀.1 := by
    intro i hi
    rw [Finset.mem_erase]
    constructor
    · intro hieq
      subst i
      exact (mem_realCoefficientSupport_iff.mp hi) hc'i₀
    · by_contra hiS
      have hci : c i = 0 := by
        exact not_ne_iff.mp (mt mem_realCoefficientSupport_iff.mpr hiS)
      have hc'i : c' i = 0 := by simp [c', uFull, hiS, hci]
      exact (mem_realCoefficientSupport_iff.mp hi) hc'i
  have hsupport_card :
      (realCoefficientSupport c').card < (realCoefficientSupport c).card := by
    calc
      (realCoefficientSupport c').card ≤ (S.erase i₀.1).card :=
        Finset.card_le_card hsupport_subset
      _ < S.card := Finset.card_erase_lt_of_mem i₀.2
      _ = (realCoefficientSupport c).card := rfl
  exact ⟨θ, c', hθ_pos, hc'_nonneg, hc'_sum_v, hc'_mass, hsupport_card⟩

/-- Helper for Theorem 4.61: a nonzero relation of nonpositive total mass on the support of a
mass maximizer has a positive coordinate. -/
lemma exists_positive_relation_coordinate_of_massMaximal
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (x : Fin n → ℝ)
    (c : ι → ℝ)
    (hc : c ∈ realConeCoefficientFiber v x)
    (hc_max : ∀ d ∈ realConeCoefficientFiber v x, ∑ i, d i ≤ ∑ i, c i)
    (u : realCoefficientSupport c → ℝ)
    (hu_relation : ∑ i, u i • v i.1 = 0)
    (hu_ne : ∃ i, u i ≠ 0)
    (hu_sum_nonpos : ∑ i, u i ≤ 0) :
    ∃ i, 0 < u i := by
  classical
  by_contra hu_not_pos
  have hu_nonpos : ∀ i, u i ≤ 0 := by
    intro i
    exact le_of_not_gt (fun hi ↦ hu_not_pos ⟨i, hi⟩)
  have hu_sum_ne : (∑ i, u i) ≠ 0 := by
    intro hu_zero
    obtain ⟨i, hi⟩ := hu_ne
    have hall_zero :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ hu_nonpos j)).mp hu_zero
    exact hi (hall_zero i (Finset.mem_univ i))
  have hu_sum_neg : ∑ i, u i < 0 := lt_of_le_of_ne hu_sum_nonpos hu_sum_ne
  let S := realCoefficientSupport c
  let uFull : ι → ℝ := fun i ↦ if hi : i ∈ S then u ⟨i, hi⟩ else 0
  let c' : ι → ℝ := fun i ↦ c i - uFull i
  have huFull_relation : ∑ i : ι, uFull i • v i = 0 := by
    calc
      ∑ i : ι, uFull i • v i = ∑ i ∈ S, uFull i • v i := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) ?_
        intro i hi hnot
        have hiS : i ∉ S := by simpa using hnot
        simp [uFull, hiS]
      _ = ∑ i : S, u i • v i.1 := by
        calc
          ∑ i ∈ S, uFull i • v i = ∑ i : S, uFull i.1 • v i.1 :=
            Finset.sum_subtype S (fun _ ↦ Iff.rfl) _
          _ = ∑ i : S, u i • v i.1 := by
            apply Fintype.sum_congr
            intro i
            simp [uFull, i.2]
      _ = 0 := hu_relation
  have huFull_sum : ∑ i : ι, uFull i = ∑ i : S, u i := by
    calc
      ∑ i : ι, uFull i = ∑ i ∈ S, uFull i := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) ?_
        intro i hi hnot
        have hiS : i ∉ S := by simpa using hnot
        simp [uFull, hiS]
      _ = ∑ i : S, u i := by
        calc
          ∑ i ∈ S, uFull i = ∑ i : S, uFull i.1 :=
            Finset.sum_subtype S (fun _ ↦ Iff.rfl) _
          _ = ∑ i : S, u i := by
            apply Fintype.sum_congr
            intro i
            simp [uFull, i.2]
  have hc'_nonneg : ∀ i, 0 ≤ c' i := by
    intro i
    by_cases hiS : i ∈ S
    · have hui : u ⟨i, hiS⟩ ≤ 0 := hu_nonpos ⟨i, hiS⟩
      have : uFull i ≤ c i := by
        simpa [uFull, hiS] using le_trans hui (hc.1 i)
      exact sub_nonneg.mpr this
    · have hci : c i = 0 := by
        exact not_ne_iff.mp (mt mem_realCoefficientSupport_iff.mpr hiS)
      simp [c', uFull, hiS, hci]
  have hc'_sum_v : (∑ i, c' i • v i) = ∑ i, c i • v i := by
    calc
      ∑ i, c' i • v i = (∑ i, c i • v i) - ∑ i, uFull i • v i := by
        simp [c', sub_smul, Finset.sum_sub_distrib]
      _ = ∑ i, c i • v i := by rw [huFull_relation]; simp
  have hc'_fiber : c' ∈ realConeCoefficientFiber v x := by
    refine ⟨hc'_nonneg, ?_⟩
    exact hc.2.trans hc'_sum_v.symm
  have hc'_mass : (∑ i, c' i) = (∑ i, c i) - ∑ i : S, u i := by
    calc
      ∑ i, c' i = (∑ i, c i) - ∑ i, uFull i := by
        simp [c', Finset.sum_sub_distrib]
      _ = (∑ i, c i) - ∑ i : S, u i := by rw [huFull_sum]
  have hmax_bound := hc_max c' hc'_fiber
  rw [hc'_mass] at hmax_bound
  linarith

/-- Helper for Theorem 4.61: a nonzero support relation of nonpositive total contradicts either
mass maximality or support minimality. -/
lemma false_of_nonpositive_relation_on_minimal_maximizer
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (x : Fin n → ℝ)
    (c : ι → ℝ)
    (hc : c ∈ realConeCoefficientFiber v x)
    (hc_max : ∀ d ∈ realConeCoefficientFiber v x, ∑ i, d i ≤ ∑ i, c i)
    (hc_min :
      ∀ d ∈ realConeCoefficientFiber v x,
        (∑ i, d i = ∑ i, c i) →
          (realCoefficientSupport c).card ≤ (realCoefficientSupport d).card)
    (u : realCoefficientSupport c → ℝ)
    (hu_relation : ∑ i, u i • v i.1 = 0)
    (hu_ne : ∃ i, u i ≠ 0)
    (hu_sum_nonpos : ∑ i, u i ≤ 0) :
    False := by
  obtain ⟨i, hui_pos⟩ :=
    exists_positive_relation_coordinate_of_massMaximal
      v x c hc hc_max u hu_relation hu_ne hu_sum_nonpos
  obtain ⟨θ, c', hθ_pos, hc'_nonneg, hc'_sum_v, hc'_mass, hc'_support⟩ :=
    exists_supportReducing_coefficient_perturbation v c hc.1 u hu_relation ⟨i, hui_pos⟩
  have hc'_fiber : c' ∈ realConeCoefficientFiber v x := by
    refine ⟨hc'_nonneg, ?_⟩
    exact hc.2.trans hc'_sum_v.symm
  rcases lt_or_eq_of_le hu_sum_nonpos with hu_sum_neg | hu_sum_zero
  · have hmax_bound := hc_max c' hc'_fiber
    rw [hc'_mass] at hmax_bound
    nlinarith
  · have hc'_same_mass : ∑ i, c' i = ∑ i, c i := by
      rw [hc'_mass, hu_sum_zero]
      ring
    have hminimal := hc_min c' hc'_fiber hc'_same_mass
    exact (not_lt_of_ge hminimal) hc'_support

/-- Helper for Theorem 4.61: a mass-maximal, support-minimal coefficient representation has
linearly independent support. -/
lemma support_linearIndependent_of_massMaximal_supportMinimal
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (x : Fin n → ℝ)
    (c : ι → ℝ)
    (hc : c ∈ realConeCoefficientFiber v x)
    (hc_max : ∀ d ∈ realConeCoefficientFiber v x, ∑ i, d i ≤ ∑ i, c i)
    (hc_min :
      ∀ d ∈ realConeCoefficientFiber v x,
        (∑ i, d i = ∑ i, c i) →
          (realCoefficientSupport c).card ≤ (realCoefficientSupport d).card) :
    LinearIndependent ℝ (fun i : realCoefficientSupport c ↦ v i.1) := by
  classical
  by_contra hdependent
  obtain ⟨u₀, hu₀_relation, i₀, hu₀_ne⟩ :=
    (Fintype.not_linearIndependent_iff).mp hdependent
  by_cases hsum : ∑ i, u₀ i ≤ 0
  · exact
      false_of_nonpositive_relation_on_minimal_maximizer
        v x c hc hc_max hc_min u₀ hu₀_relation ⟨i₀, hu₀_ne⟩ hsum
  · let u : realCoefficientSupport c → ℝ := fun i ↦ -u₀ i
    have hu_relation : ∑ i, u i • v i.1 = 0 := by
      have hneg := congrArg Neg.neg hu₀_relation
      simpa [u, neg_smul, Finset.sum_neg_distrib] using hneg
    have hu_ne : ∃ i, u i ≠ 0 := by
      have hi₀ : u i₀ ≠ 0 := by simpa [u] using hu₀_ne
      exact ⟨i₀, hi₀⟩
    have hu_sum_nonpos : ∑ i, u i ≤ 0 := by
      have hsum_pos : 0 < ∑ i, u₀ i := lt_of_not_ge hsum
      calc
        ∑ i, u i = -(∑ i, u₀ i) := by simp [u]
        _ ≤ 0 := neg_nonpos.mpr hsum_pos.le
    exact
      false_of_nonpositive_relation_on_minimal_maximizer
        v x c hc hc_max hc_min u hu_relation hu_ne hu_sum_nonpos

/-- Helper for Theorem 4.61: flooring a nonnegative real coefficient representation leaves an
integral remainder represented by the fractional parts. -/
lemma exists_floor_remainder_of_real_coefficient
    {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℤ)
    (x : Fin n → ℤ)
    (c : ι → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_eq :
      (fun t ↦ (x t : ℝ)) = ∑ i, c i • (fun t ↦ (a i t : ℝ))) :
    ∃ μ₀ : ι →₀ ℕ, ∃ ρ : Fin n → ℤ,
      x = μ₀.sum (fun i m ↦ m • a i) + ρ ∧
        (fun t ↦ (ρ t : ℝ)) =
          ∑ i, Int.fract (c i) • (fun t ↦ (a i t : ℝ)) ∧
        ∀ i, ((μ₀ i : ℕ) : ℝ) = (Int.floor (c i) : ℝ) := by
  classical
  let μNat : ι → ℕ := fun i ↦ Int.toNat (Int.floor (c i))
  let μ₀ : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm μNat
  have hμ_cast : ∀ i : ι, ((μ₀ i : ℕ) : ℝ) = (Int.floor (c i) : ℝ) := by
    intro i
    have hfloor_nonneg : 0 ≤ Int.floor (c i) := Int.floor_nonneg.mpr (hc_nonneg i)
    calc
      ((μ₀ i : ℕ) : ℝ) = (Int.toNat (Int.floor (c i)) : ℝ) := by
        simp [μ₀, μNat]
      _ = (Int.floor (c i) : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hfloor_nonneg)
  have hμ₀_real :
      (fun t ↦ ((μ₀.sum (fun i m ↦ m • a i)) t : ℝ)) =
        ∑ i, (Int.floor (c i) : ℝ) • (fun t ↦ (a i t : ℝ)) := by
    -- Cast the integral floor combination into the same real coefficient space.
    ext t
    have hzero_sum : ∀ i, (0 : ℕ) • a i = 0 := by
      intro i
      simp
    calc
      ((μ₀.sum (fun i m ↦ m • a i)) t : ℝ) =
          ∑ i, ((μ₀ i : ℕ) : ℝ) * (a i t : ℝ) := by
            rw [Finsupp.sum_fintype _ _ hzero_sum, Finset.sum_apply]
            simp
      _ = ∑ i, (Int.floor (c i) : ℝ) * (a i t : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hμ_cast i]
      _ = (∑ i, (Int.floor (c i) : ℝ) • (fun s ↦ (a i s : ℝ))) t := by
        simp [Pi.smul_apply]
  let ρ : Fin n → ℤ := x - μ₀.sum (fun i m ↦ m • a i)
  refine ⟨μ₀, ρ, ?_, ?_, hμ_cast⟩
  · -- The integral remainder is defined by subtracting the floor combination.
    ext t
    simp [ρ, sub_eq_add_neg, add_left_comm]
  · -- Subtract the floor combination and use `floor + fract = coefficient` coordinatewise.
    ext t
    calc
      (ρ t : ℝ) = (x t : ℝ) - ((μ₀.sum (fun i m ↦ m • a i)) t : ℝ) := by
        simp [ρ]
      _ = (∑ i, c i * (a i t : ℝ)) -
          ∑ i, (Int.floor (c i) : ℝ) * (a i t : ℝ) := by
            rw [congrFun hc_eq t, congrFun hμ₀_real t]
            simp [Pi.smul_apply]
      _ = ∑ i, (c i - (Int.floor (c i) : ℝ)) * (a i t : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, Int.fract (c i) * (a i t : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hdecomp : c i - (Int.floor (c i) : ℝ) = Int.fract (c i) := by
          linarith [Int.floor_add_fract (c i)]
        rw [hdecomp]
      _ = (∑ i, Int.fract (c i) • (fun s ↦ (a i s : ℝ))) t := by
        simp [Pi.smul_apply]

/-- Helper for Theorem 4.61: a nonnegative combination indexed by an arbitrary finite type lies
in the cone generated by that family. -/
lemma mem_real_hull_of_nonnegative_fintype_sum
    {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℝ)
    (c : ι → ℝ)
    (x : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hx : x = ∑ i, c i • v i) :
    x ∈ (PointedCone.hull ℝ (Set.range v) : Set (Fin n → ℝ)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine (mem_hull_iff).2 ⟨Fintype.card ι, fun j ↦ v (e.symm j), ?_,
    fun j ↦ c (e.symm j), fun j ↦ hc_nonneg (e.symm j), ?_⟩
  · intro j
    exact ⟨e.symm j, rfl⟩
  · -- Reindex the given finite sum by the canonical equivalence with `Fin`.
    calc
      x = ∑ i : ι, c i • v i := hx
      _ = ∑ j : Fin (Fintype.card ι), c (e.symm j) • v (e.symm j) := by
        simpa using (e.symm.sum_comp (fun i : ι ↦ c i • v i)).symm

/-- Helper for Theorem 4.61: a maximal coefficient representation yields an integral
representation satisfying the `2 * n - 1` support bound. -/
lemma exists_floor_remainder_witnesses_with_support_bounds
    (a : Fin k → Fin n → ℤ)
    (h_hilbert : IsHilbertBasisFamily a)
    {x : Fin n → ℤ}
    (hx_ne : x ≠ 0)
    (c : {i : Fin k // a i ≠ 0} → ℝ)
    (hc :
      c ∈ realConeCoefficientFiber
        (fun i : {i : Fin k // a i ≠ 0} ↦ fun t ↦ (a i.1 t : ℝ))
        (fun t ↦ (x t : ℝ)))
    (hc_max :
      ∀ d ∈ realConeCoefficientFiber
          (fun i : {i : Fin k // a i ≠ 0} ↦ fun t ↦ (a i.1 t : ℝ))
          (fun t ↦ (x t : ℝ)),
        ∑ i, d i ≤ ∑ i, c i)
    (hc_card : (realCoefficientSupport c).card ≤ n) :
    ∃ μ : Fin k →₀ ℕ,
      μ.support.card ≤ 2 * n - 1 ∧
        x = μ.sum (fun i m ↦ m • a i) := by
  classical
  let ι := {i : Fin k // a i ≠ 0}
  let e : ι ↪ Fin k := Function.Embedding.subtype _
  let v : ι → Fin n → ℝ := fun i ↦ fun t ↦ (a i.1 t : ℝ)
  obtain ⟨μ₀, ρ, hx_floor, hρ_fract, hμ₀_apply⟩ :=
    exists_floor_remainder_of_real_coefficient
      (fun i : ι ↦ a i.1) x c hc.1 hc.2
  have hρ_mem_sub :
      (fun t ↦ (ρ t : ℝ)) ∈
        (PointedCone.hull ℝ (Set.range v) : Set (Fin n → ℝ)) := by
    -- Fractional parts are nonnegative, so the remainder lies in the selected cone.
    exact mem_real_hull_of_nonnegative_fintype_sum
      v (fun i ↦ Int.fract (c i)) (fun t ↦ (ρ t : ℝ))
        (fun i ↦ Int.fract_nonneg (c i)) hρ_fract
  have hρ_mem_ambient :
      (fun t ↦ (ρ t : ℝ)) ∈
        (PointedCone.hull ℝ
          (Set.range fun i : Fin k ↦ fun t ↦ (a i t : ℝ)) : Set (Fin n → ℝ)) := by
    apply (Submodule.span_mono ?_) hρ_mem_sub
    rintro y ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  have hρ_mem_rat :
      (fun t ↦ (ρ t : ℚ)) ∈
        (PointedCone.hull ℚ
          (Set.range fun i : Fin k ↦ fun t ↦ (a i t : ℚ)) : Set (Fin n → ℚ)) :=
    integral_point_mem_rational_hull_of_mem_real_hull hρ_mem_ambient
  obtain ⟨ν, hν⟩ := h_hilbert ρ hρ_mem_rat
  let νnz : Fin k →₀ ℕ := ν.filter (fun i ↦ a i ≠ 0)
  have hν_sum_filter :
      ν.sum (fun i m ↦ m • fun t ↦ (a i t : ℚ)) =
        νnz.sum (fun i m ↦ m • fun t ↦ (a i t : ℚ)) := by
    -- Coefficients on zero generators can be discarded without changing the sum.
    ext t
    have hzero_sum : ∀ i, (0 : ℕ) • (fun t ↦ (a i t : ℚ)) = 0 := by
      intro i
      simp
    rw [Finsupp.sum_fintype _ _ hzero_sum, Finsupp.sum_fintype _ _ hzero_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hai : a i = 0
    · simp [νnz, hai]
    · simp [νnz, hai]
  have hρ_nz : ρ = νnz.sum (fun i m ↦ m • a i) := by
    exact eq_of_rat_finsupp_sum_eq a (hν.trans hν_sum_filter)
  have hνnz_support : (νnz.support : Set (Fin k)) ⊆ Set.range e := by
    intro i hi
    have hi' : i ∈ ν.support.filter (fun j ↦ a j ≠ 0) := by
      simpa [νnz] using hi
    exact ⟨⟨i, (Finset.mem_filter.mp hi').2⟩, rfl⟩
  let νSub : ι →₀ ℕ := Finsupp.comapDomain e νnz e.injective.injOn
  have hν_embed : νSub.embDomain e = νnz := by
    exact Finsupp.embDomain_comapDomain hνnz_support
  have hρ_sub : ρ = νSub.sum (fun i m ↦ m • a i.1) := by
    calc
      ρ = νnz.sum (fun i m ↦ m • a i) := hρ_nz
      _ = (νSub.embDomain e).sum (fun i m ↦ m • a i) := by rw [hν_embed]
      _ = νSub.sum (fun i m ↦ m • a i.1) := Finsupp.sum_embDomain
  have hx_sub : x = (μ₀ + νSub).sum (fun i m ↦ m • a i.1) := by
    calc
      x = μ₀.sum (fun i m ↦ m • a i.1) + ρ := hx_floor
      _ = μ₀.sum (fun i m ↦ m • a i.1) +
          νSub.sum (fun i m ↦ m • a i.1) := by rw [hρ_sub]
      _ = (μ₀ + νSub).sum (fun i m ↦ m • a i.1) := by
        rw [Finsupp.sum_add_index]
        · simp
        · intro i m₁ m₂
          simp [add_smul]
  let d : ι → ℝ := fun i ↦ (Int.floor (c i) : ℝ) + (νSub i : ℝ)
  have hd_fiber : d ∈ realConeCoefficientFiber v (fun t ↦ (x t : ℝ)) := by
    constructor
    · intro i
      have hfloor_nonneg : (0 : ℝ) ≤ (Int.floor (c i) : ℝ) := by
        exact_mod_cast Int.floor_nonneg.mpr (hc.1 i)
      exact add_nonneg hfloor_nonneg (Nat.cast_nonneg _)
    · -- Cast the integral reconstruction to identify the competing real coefficients.
      ext t
      have hzero_sum : ∀ i : ι, (0 : ℕ) • a i.1 = 0 := by
        intro i
        simp
      calc
        (x t : ℝ) =
            (((μ₀ + νSub).sum (fun i m ↦ m • a i.1)) t : ℝ) := by
              rw [← congrFun hx_sub t]
        _ = ∑ i : ι, (((μ₀ + νSub) i : ℕ) : ℝ) * (a i.1 t : ℝ) := by
          rw [Finsupp.sum_fintype _ _ hzero_sum, Finset.sum_apply]
          simp
        _ = ∑ i : ι, d i * (a i.1 t : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [d, hμ₀_apply i]
        _ = (∑ i : ι, d i • v i) t := by
          simp [v, Pi.smul_apply]
  have hmass_max := hc_max d hd_fiber
  have hc_mass :
      ∑ i : ι, c i =
        (∑ i : ι, (Int.floor (c i) : ℝ)) + ∑ i : ι, Int.fract (c i) := by
    calc
      ∑ i : ι, c i =
          ∑ i : ι, ((Int.floor (c i) : ℝ) + Int.fract (c i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (Int.floor_add_fract (c i)).symm
      _ = (∑ i : ι, (Int.floor (c i) : ℝ)) +
          ∑ i : ι, Int.fract (c i) := Finset.sum_add_distrib
  have hd_mass :
      ∑ i : ι, d i =
        (∑ i : ι, (Int.floor (c i) : ℝ)) + ∑ i : ι, (νSub i : ℝ) := by
    simp [d, Finset.sum_add_distrib]
  have hν_mass_le :
      ∑ i : ι, (νSub i : ℝ) ≤ ∑ i : ι, Int.fract (c i) := by
    rw [hd_mass, hc_mass] at hmass_max
    linarith
  have hc_support_nonempty : (realCoefficientSupport c).Nonempty := by
    by_contra hS
    have hS_empty : realCoefficientSupport c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hc_zero : c = 0 := by
      funext i
      by_contra hci
      have hi : i ∈ realCoefficientSupport c := mem_realCoefficientSupport_iff.mpr hci
      rw [hS_empty] at hi
      simp at hi
    have hx_real_zero : (fun t ↦ (x t : ℝ)) = 0 := by
      rw [hc.2, hc_zero]
      simp
    apply hx_ne
    ext t
    have ht := congrFun hx_real_zero t
    have ht' : (x t : ℝ) = 0 := by simpa using ht
    exact_mod_cast ht'
  have hfract_sum_support :
      ∑ i : ι, Int.fract (c i) =
        ∑ i ∈ realCoefficientSupport c, Int.fract (c i) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i hi hiS
    have hci : c i = 0 := not_ne_iff.mp (mt mem_realCoefficientSupport_iff.mpr hiS)
    simp [hci]
  have hfract_lt :
      ∑ i : ι, Int.fract (c i) < ((realCoefficientSupport c).card : ℝ) := by
    rw [hfract_sum_support]
    calc
      ∑ i ∈ realCoefficientSupport c, Int.fract (c i) <
          ∑ i ∈ realCoefficientSupport c, (1 : ℝ) := by
            exact Finset.sum_lt_sum_of_nonempty hc_support_nonempty
              (fun i hi ↦ Int.fract_lt_one (c i))
      _ = ((realCoefficientSupport c).card : ℝ) := by simp
  have hν_card_mass :
      ((νSub.support.card : ℕ) : ℝ) ≤ ∑ i : ι, (νSub i : ℝ) := by
    calc
      ((νSub.support.card : ℕ) : ℝ) = ∑ i ∈ νSub.support, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ νSub.support, (νSub i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
      _ = ∑ i : ι, (νSub i : ℝ) := by
        have hsum_support : ∀ i ∈ Finset.univ, i ∉ νSub.support → (νSub i : ℝ) = 0 := by
          intro i hi hiS
          simp [Finsupp.notMem_support_iff.mp hiS]
        exact Finset.sum_subset (Finset.subset_univ _) hsum_support
  have hν_card_lt_n : νSub.support.card < n := by
    exact_mod_cast
      lt_of_le_of_lt hν_card_mass
        (lt_of_le_of_lt hν_mass_le (lt_of_lt_of_le hfract_lt (Nat.cast_le.mpr hc_card)))
  have hν_card : νSub.support.card ≤ n - 1 := by omega
  have hμ_support_subset : μ₀.support ⊆ realCoefficientSupport c := by
    intro i hi
    apply mem_realCoefficientSupport_iff.mpr
    intro hci
    have hcast : ((μ₀ i : ℕ) : ℝ) = 0 := by
      rw [hμ₀_apply i, hci]
      simp
    have hμ₀_zero : μ₀ i = 0 := by exact_mod_cast hcast
    exact (Finsupp.mem_support_iff.mp hi) hμ₀_zero
  have hμ_card : μ₀.support.card ≤ n :=
    le_trans (Finset.card_le_card hμ_support_subset) hc_card
  let μ : Fin k →₀ ℕ := (μ₀ + νSub).embDomain e
  have hμ_card_total : μ.support.card ≤ 2 * n - 1 := by
    have hsub_card :
        (μ₀ + νSub).support.card ≤ μ₀.support.card + νSub.support.card := by
      calc
        (μ₀ + νSub).support.card ≤ (μ₀.support ∪ νSub.support).card :=
          Finset.card_le_card Finsupp.support_add
        _ ≤ μ₀.support.card + νSub.support.card :=
          Finset.card_union_le μ₀.support νSub.support
    have hsub_bound : (μ₀ + νSub).support.card ≤ 2 * n - 1 := by omega
    change ((μ₀ + νSub).support.map e).card ≤ 2 * n - 1
    simpa only [Finset.card_map] using hsub_bound
  refine ⟨μ, hμ_card_total, ?_⟩
  -- Embed the subtype-indexed decomposition back into the original generator family.
  calc
    x = (μ₀ + νSub).sum (fun i m ↦ m • a i.1) := hx_sub
    _ = μ.sum (fun i m ↦ m • a i) := by
      symm
      exact Finsupp.sum_embDomain

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_11/ch4_sec4_11_theorem_4_61.lean.

Theorem 4.61. Let `a 0, ..., a (k - 1) ∈ ℤ^n` form a Hilbert basis and let
`cone(a 0, ..., a (k - 1))` be pointed. Then every integral vector in this cone can be written as
a conic combination with integral coefficients supported on at most `2n - 1` vectors among
`a 0, ..., a (k - 1)`. -/
theorem exists_bounded_integral_conic_combination_of_hilbert_basis
    (a : Fin k → Fin n → ℤ)
    (h_hilbert : IsHilbertBasisFamily a)
    (h_pointed :
      ((PointedCone.hull ℝ (Set.range fun i ↦ fun j ↦ (a i j : ℝ)) :
        ConvexCone ℝ (Fin n → ℝ))).Salient)
    {x : Fin n → ℤ}
    (hx :
      (fun i ↦ (x i : ℝ)) ∈
        (PointedCone.hull ℝ (Set.range fun i ↦ fun j ↦ (a i j : ℝ)) :
          Set (Fin n → ℝ))) :
    ∃ μ : Fin k →₀ ℕ,
      μ.support.card ≤ 2 * n - 1 ∧
        x = μ.sum (fun j c ↦ c • a j) := by
  classical
  by_cases hx_zero : x = 0
  · subst x
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  · -- Route correction: arbitrary selected generators need not span an ambient face.  Instead,
    -- maximize coefficient mass globally and minimize support among those maximizers.
    let ι := {i : Fin k // a i ≠ 0}
    let v : ι → Fin n → ℝ := fun i ↦ fun t ↦ (a i.1 t : ℝ)
    have hx_sub :
        (fun t ↦ (x t : ℝ)) ∈
          (PointedCone.hull ℝ (Set.range v) : Set (Fin n → ℝ)) := by
      apply (Submodule.span_le.mpr ?_) hx
      rintro y ⟨i, rfl⟩
      by_cases hai : a i = 0
      · have hy_zero : (fun t ↦ (a i t : ℝ)) = (0 : Fin n → ℝ) := by
          ext t
          simp [hai]
        have hzero : (0 : Fin n → ℝ) ∈ PointedCone.hull ℝ (Set.range v) :=
          (PointedCone.hull ℝ (Set.range v)).zero_mem
        change (fun t ↦ (a i t : ℝ)) ∈ PointedCone.hull ℝ (Set.range v)
        rw [hy_zero]
        exact hzero
      · exact Submodule.subset_span ⟨⟨i, hai⟩, rfl⟩
    have hsub_le :
        (PointedCone.hull ℝ (Set.range v) : ConvexCone ℝ (Fin n → ℝ)) ≤
          (PointedCone.hull ℝ
            (Set.range fun i : Fin k ↦ fun t ↦ (a i t : ℝ)) :
              ConvexCone ℝ (Fin n → ℝ)) := by
      apply Submodule.span_mono
      rintro y ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
    have hsub_pointed :
        ((PointedCone.hull ℝ (Set.range v) : ConvexCone ℝ (Fin n → ℝ))).Salient := by
      intro y hy hy_ne hneg
      exact h_pointed y (hsub_le hy) hy_ne (hsub_le hneg)
    have hv_ne : ∀ i : ι, v i ≠ 0 := by
      intro i hi
      apply i.2
      ext t
      have ht := congrFun hi t
      have ht' : (a i.1 t : ℝ) = 0 := by simpa [v] using ht
      exact_mod_cast ht'
    obtain ⟨c, hc, hc_max, hc_min⟩ :=
      exists_massMaximal_supportMinimal_coefficient
        v (fun t ↦ (x t : ℝ)) hv_ne hsub_pointed hx_sub
    have hlin : LinearIndependent ℝ (fun i : realCoefficientSupport c ↦ v i.1) :=
      support_linearIndependent_of_massMaximal_supportMinimal
        v (fun t ↦ (x t : ℝ)) c hc hc_max hc_min
    have hc_card : (realCoefficientSupport c).card ≤ n := by
      calc
        (realCoefficientSupport c).card =
            Fintype.card (realCoefficientSupport c) := by simp
        _ ≤ Module.finrank ℝ (Fin n → ℝ) := hlin.fintype_card_le_finrank
        _ = n := by simp
    exact exists_floor_remainder_witnesses_with_support_bounds
      a h_hilbert hx_zero c hc hc_max hc_card

end Theorem461

#print axioms exists_bounded_integral_conic_combination_of_hilbert_basis
