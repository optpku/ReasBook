/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap05.ConjugateFunctionStrongDual
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_24
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_25
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_45
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_44
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open InnerProductSpace (toDualMap)

/- Lemma 12.3 is `bridge/view`: Definition 12.5 already owns the source-facing Chapter 12 terms
`F(y) = f*(Aᵀ y)` and `G(y) = g*(-y)` on the dual space, while this file exposes their primal-space
formulas and analytic properties needed downstream. The `G`-side bridge evaluates the owner along
the Riesz map `toDualMap ℝ Y`, and the `F`-side bridge additionally uses `A.adjoint` to express the
textbook transpose pullback on the primal Hilbert space. Finite-dimensional hypotheses appear only
where the Chapter 5 conjugate-smoothness or conjugate-properness API requires them. -/

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Evaluating the Chapter 12 owner `F(y) = f*(Aᵀ y)` on the primal-space variable `y` gives the
primal-space formula `(f∗) (A.adjoint y)`. -/
@[simp] theorem dual_based_proximal_gradient_dual_F_primal_apply
    (f : E → EReal) (A : E →ₗ[ℝ] Y) (y : Y) :
    dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ Y y) =
      (f∗) (A.adjoint y) := by
  -- Rewrite both Chapter 12/4 owners once, then identify the pulled-back dual functional.
  rw [dual_based_proximal_gradient_dual_F_term_apply, conjugate_function_primal_apply]
  congr 1
  ext x
  -- The transpose pullback `A.dualMap` agrees with the primal adjoint under the Riesz map.
  simpa [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply] using
    (A.adjoint_inner_left x y).symm

/-- Helper for Lemma 12.3: the primal-space dual term `F(y) = f*(Aᵀ y)` is convex. -/
theorem dual_based_proximal_gradient_dual_F_primal_convex
    (f : E → EReal) (A : E →ₗ[ℝ] Y) :
    is_convex_function (fun y : Y ↦ (f∗) (A.adjoint y)) := by
  -- Convexity of the primal conjugate is already owned by Chapter 4.
  have hconj_convex : is_convex_function (f∗) :=
    (conjugate_function_closed_and_convex f).2
  -- Precomposing a convex function with the linear map `A.adjoint` preserves convexity.
  simpa using
    is_convex_function_precompose_linearMap_add
      hconj_convex
      A.adjoint
      0

/-- Helper for Lemma 12.3: if `f` is proper, closed, and `σ`-strongly convex, then
`F(y) = f*(Aᵀ y)` is finite-valued for every `y`. -/
theorem dual_based_proximal_gradient_dual_F_primal_finite_valued
    (σ : PosReal) (f : E → EReal) (A : E →ₗ[ℝ] Y)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)) :
    ∀ y : Y,
      (f∗) (A.adjoint y) ≠ ⊥ ∧
        (f∗) (A.adjoint y) < ⊤ := by
  intro y
  let yDual : StrongDual ℝ E := InnerProductSpace.toDual ℝ E (A.adjoint y)
  have hf_strong' : is_strongly_convex_function f (σ : ℝ) := by
    refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
    exact ⟨PosReal.coe_pos σ, hf_proper.ne_bot, hf_strong⟩
  have hfiniteDual :
      conjugate_function_strongDual f yDual ≠ ⊥ ∧ conjugate_function_strongDual f yDual < ⊤ := by
    let linearPart : E → EReal := Function.toEReal fun x : E ↦ -yDual x
    let φ : E → EReal := fun x ↦ linearPart x + f x
    have hlinear_ne_bot : ∀ x : E, linearPart x ≠ ⊥ := by
      intro x
      simp [linearPart]
    have hlinear_closed : LowerSemicontinuous linearPart := by
      -- The affine perturbation term is continuous after the canonical `toEReal` lift.
      simpa [linearPart] using
        Function.toEReal_lowerSemicontinuous_of_continuous (-yDual).continuous
    have hlinear_convex : is_convex_function linearPart := by
      -- A linear functional remains convex after negation and the `toEReal` lift.
      simpa [linearPart] using
        Function.toEReal_isConvexFunction ((-yDual).convexOn convex_univ)
    have hφ_closed : LowerSemicontinuous φ := by
      -- Addition is continuous because the perturbation is finite and `f` never takes `⊥`.
      have hsum_closed : LowerSemicontinuous (linearPart + f) := by
        refine hlinear_closed.add' hf_closed ?_
        intro x
        exact EReal.continuousAt_add
          (.inl (EReal.coe_ne_top (-yDual x)))
          (.inl (hlinear_ne_bot x))
      simpa [φ, Pi.add_apply] using hsum_closed
    have hφ_strong : is_strongly_convex_function φ (σ : ℝ) := by
      -- Adding a convex finite affine term preserves the strong-convexity modulus.
      have hsum_strong :
          is_strongly_convex_function (fun x ↦ f x + linearPart x) (σ : ℝ) :=
        is_strongly_convex_function_add_of_is_convex_function
          hf_strong'
          hlinear_convex
          hlinear_ne_bot
      simpa [φ, Pi.add_apply, add_comm] using hsum_strong
    have hφ_proper : IsProperExtendedRealFunction φ := by
      refine ⟨?_, ?_⟩
      · intro x
        simpa [φ, linearPart, Pi.add_apply] using
          (EReal.add_ne_bot_iff.mpr ⟨hlinear_ne_bot x, hf_proper.ne_bot x⟩)
      · rcases hf_proper.effective_domain_nonempty with ⟨x0, hx0⟩
        refine ⟨x0, ?_⟩
        refine mem_effective_domain.mpr ?_
        simpa [φ, linearPart, Pi.add_apply] using
          EReal.add_lt_top (EReal.coe_ne_top (-yDual x0)) (ne_of_lt (mem_effective_domain.mp hx0))
    have hφ_convex : is_convex_function φ := by
      -- Strong convexity implies the convexity needed for the minimizer route.
      refine (is_convex_function_iff_convexOn_toReal (f := φ) (fun x _ ↦ hφ_proper.ne_bot x)).2 ?_
      have hstrict :
          StrictConvexOn ℝ (effective_domain φ) (fun x ↦ (φ x).toReal) :=
        (strongConvexOn_toReal_of_is_strongly_convex_function hφ_strong).strictConvexOn
          hφ_strong.sigma_pos
      exact hstrict.convexOn
    obtain ⟨x0, hx0, hg_nonempty⟩ :=
      exists_subdifferentiable_point_in_effective_domain_of_proper_convex
        φ
        hφ_proper
        hφ_convex
    obtain ⟨g, hg⟩ := hg_nonempty
    have hlevel :
        ∀ a : ℝ, Bornology.IsBounded {x | φ x ≤ (a : EReal)} :=
      boundedRealSublevelSets_of_stronglyConvexSubgradient hφ_strong x0 hx0 hg
    obtain ⟨xStar, hxStar, hxStarMin⟩ :=
      exists_isMinOn_univ_of_bounded_real_sublevelSets φ hφ_proper hφ_closed hlevel
    have hphi_domain_eq :
        effective_domain φ = effective_domain f := by
      ext x
      constructor
      · intro hx
        rw [mem_effective_domain] at hx ⊢
        by_contra hfx
        have hfx_top : f x = ⊤ := le_antisymm le_top (not_lt.mp hfx)
        have hphi_top : φ x = ⊤ := by
          simp [φ, linearPart, hfx_top]
        exact hx.ne hphi_top
      · intro hx
        refine mem_effective_domain.mpr ?_
        rw [mem_effective_domain] at hx
        simpa [φ, linearPart] using
          EReal.add_lt_top (EReal.coe_ne_top (-yDual x)) (ne_of_lt hx)
    have hxStar_f : xStar ∈ effective_domain f := by
      simpa [hphi_domain_eq] using hxStar
    have hxStar_f_eq : f xStar = (((f xStar).toReal : ℝ) : EReal) := by
      exact
        (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar_f))
          (hf_proper.ne_bot xStar)).symm
    have hbound :
        conjugate_function_strongDual f yDual ≤ (yDual xStar : EReal) - f xStar := by
      rw [conjugate_function_strongDual_apply, conjugate_function_apply]
      refine sSup_le ?_
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ effective_domain f
      · have hφx : x ∈ effective_domain φ := by
          simpa [hphi_domain_eq] using hx
        have hmin : φ xStar ≤ φ x := (isMinOn_iff.mp hxStarMin) x (by simp)
        have hφxStar_eq : φ xStar = (((φ xStar).toReal : ℝ) : EReal) := by
          exact
            (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar))
              (hφ_proper.ne_bot xStar)).symm
        have hφx_eq : φ x = (((φ x).toReal : ℝ) : EReal) := by
          exact
            (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hφx))
              (hφ_proper.ne_bot x)).symm
        have hreal : (φ xStar).toReal ≤ (φ x).toReal := by
          rw [hφxStar_eq, hφx_eq] at hmin
          exact_mod_cast hmin
        have hφxStar_toReal : (φ xStar).toReal = (f xStar).toReal - yDual xStar := by
          -- Expand the finite affine perturbation into its real-valued form.
          simpa [φ, linearPart, Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using
              (EReal.toReal_add (EReal.coe_ne_top (-yDual xStar)) (EReal.coe_ne_bot (-yDual xStar))
                (ne_of_lt (mem_effective_domain.mp hxStar_f)) (hf_proper.ne_bot xStar))
        have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) := by
          exact
            (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hx))
              (hf_proper.ne_bot x)).symm
        have hφx_toReal : (φ x).toReal = (f x).toReal - yDual x := by
          -- The same normalization holds at any finite point of `f`.
          simpa [φ, linearPart, Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using
              (EReal.toReal_add (EReal.coe_ne_top (-yDual x)) (EReal.coe_ne_bot (-yDual x))
                (ne_of_lt (mem_effective_domain.mp hx)) (hf_proper.ne_bot x))
        have hpair_real : yDual x - (f x).toReal ≤ yDual xStar - (f xStar).toReal := by
          rw [hφxStar_toReal, hφx_toReal] at hreal
          linarith
        have hpair_ereal :
            (((yDual x - (f x).toReal : ℝ) : EReal)) ≤
              (((yDual xStar - (f xStar).toReal : ℝ) : EReal)) :=
          EReal.coe_le_coe hpair_real
        have hpair_ereal' : (yDual x : EReal) - f x ≤ (yDual xStar : EReal) - f xStar := by
          rw [hxStar_f_eq, hfx_eq]
          rw [← EReal.coe_sub, ← EReal.coe_sub]
          exact hpair_ereal
        simpa using hpair_ereal'
      · have hxtop : f x = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effective_domain] using hx))
        simp [hxtop]
    have htop : conjugate_function_strongDual f yDual < ⊤ := by
      have hfinite_rhs : (yDual xStar : EReal) - f xStar < ⊤ := by
        rw [hxStar_f_eq]
        simpa [EReal.coe_sub] using EReal.coe_lt_top (yDual xStar - (f xStar).toReal)
      exact lt_of_le_of_lt hbound hfinite_rhs
    exact ⟨conjugate_function_ne_bot f hf_proper yDual, htop⟩
  -- Return to the primal-space surface via the Riesz identification.
  constructor
  · intro hbot
    have hprimal_eq :
        (f∗) (A.adjoint y) = conjugate_function_strongDual f yDual := by
      rw [conjugate_function_primal_apply, conjugate_function_strongDual_apply]
      rfl
    have hbotDual : conjugate_function_strongDual f yDual = ⊥ := by
      rw [← hprimal_eq]
      exact hbot
    exact hfiniteDual.1 hbotDual
  · have htopDual : conjugate_function_strongDual f yDual < ⊤ := hfiniteDual.2
    have hprimal_eq :
        (f∗) (A.adjoint y) = conjugate_function_strongDual f yDual := by
      rw [conjugate_function_primal_apply, conjugate_function_strongDual_apply]
      rfl
    rw [hprimal_eq]
    exact htopDual

/-- Helper for Lemma 12.3: a Euclidean subgradient of the primal conjugate
`x ↦ ((f∗) x).toReal` at `g` induces the primal subgradient relation
`toDualMap ℝ E g ∈ ∂ f(x)`. -/
lemma mem_subdifferential_of_memEuclideanSubdifferentialAt_primalConjugate
    (f : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    (hfinite : ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤)
    {x g : E}
    (hx : x ∈ euclideanSubdifferentialAt (fun y : E ↦ ((f∗) y).toReal) g) :
    (toDualMap ℝ E g : Module.Dual ℝ E) ∈ ∂ f(x) := by
  let fStarLift : E → EReal := fun z ↦ (((f∗) z).toReal : EReal)
  have hfStarLift_eq (z : E) : fStarLift z = (f∗) z := by
    -- Finite-valuedness lets us stay on the canonical `EReal` spelling of the primal conjugate.
    simpa [fStarLift] using
      (EReal.coe_toReal (ne_of_lt (hfinite z).2) (hfinite z).1)
  have hfStarLift_proper : IsProperExtendedRealFunction fStarLift := by
    -- The real lift of an everywhere-finite function is automatically proper.
    constructor
    · intro z
      simp [fStarLift]
    · refine ⟨g, ?_⟩
      rw [mem_effective_domain, hfStarLift_eq]
      exact (hfinite g).2
  have hx' : (toDualMap ℝ E x : Module.Dual ℝ E) ∈ ∂ fStarLift(g) := by
    -- Rewrite the Euclidean subgradient membership back to the owner subdifferential.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential] at hx
    simpa [fStarLift] using hx
  have hpair :
      (((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ) : EReal) =
        fStarLift g + conjugate_function fStarLift (toDualMap ℝ E x) := by
    -- Fenchel--Young equality is the canonical starting point for the conjugate-side argmax view.
    exact
      (pairing_eq_add_conjugate_iff_mem_subdifferential_of_proper
        fStarLift hfStarLift_proper g (toDualMap ℝ E x)).2 hx'
  have hpair_ne_top :
      (((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ) : EReal) ≠ ⊤ :=
    EReal.coe_ne_top _
  have hconj_ne_bot :
      conjugate_function fStarLift (toDualMap ℝ E x) ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper fStarLift hfStarLift_proper (toDualMap ℝ E x)
  have hconj_eq :
      conjugate_function fStarLift (toDualMap ℝ E x) =
        (((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ) : EReal) - fStarLift g := by
    -- Put Fenchel--Young equality into the argmax normal form expected by Theorem 4.12.
    exact
      (eq_add_iff_left_eq_sub_of_ne_bot
        hconj_ne_bot
        (hfStarLift_proper.ne_bot g)
        hpair_ne_top).mp
        (by simpa [add_comm] using hpair)
  have hmax_left :
      IsMaxOn
        (fun z : E ↦
          ((((toDualMap ℝ E x : Module.Dual ℝ E) z : ℝ)) : EReal) - fStarLift z)
        Set.univ
        g := by
    -- The primal-conjugate Fenchel equality is equivalent to primal argmax attainment at `g`.
    exact
      (conjugate_function_eq_iff_isMaxOn_pairing_sub_function
        fStarLift g (toDualMap ℝ E x)).mp hconj_eq
  have htoDualMap_surjective :
      Function.Surjective (fun z : E ↦ (toDualMap ℝ E z : Module.Dual ℝ E)) := by
    intro y
    refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap y), ?_⟩
    ext u
    simp
  have hobjective_eq (z : E) :
      ((((toDualMap ℝ E x : Module.Dual ℝ E) z : ℝ)) : EReal) - fStarLift z =
        ((toDualMap ℝ E z : Module.Dual ℝ E) x : EReal) -
          conjugate_function f (toDualMap ℝ E z) := by
    -- The two argmax objectives coincide after the Riesz change of variables.
    rw [hfStarLift_eq z, conjugate_function_primal_apply]
    simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
  have hmax_right :
      IsMaxOn
        (fun y : Module.Dual ℝ E ↦ (y x : EReal) - conjugate_function f y)
        Set.univ
        (toDualMap ℝ E g : Module.Dual ℝ E) := by
    -- Transfer the primal argmax statement to the dual argmax statement in Theorem 4.12.
    rw [isMaxOn_univ_iff] at hmax_left ⊢
    intro y
    rcases htoDualMap_surjective y with ⟨z, rfl⟩
    rw [← hobjective_eq z, ← hobjective_eq g]
    exact hmax_left z
  -- Theorem 4.12 converts the dual argmax statement back to the primal subgradient relation.
  exact
    (mem_subdifferential_iff_isMaxOn_affine_minus_conjugate
      f hf_proper hf_closed hf_convex x (toDualMap ℝ E g)).2 hmax_right

/-- Lemma 12.3: if `f` is proper, closed, and `σ`-strongly convex, then its primal conjugate is
globally smooth with constant `1 / σ`. This is the identity-map core used to prove the Chapter 12
smoothness statement for `F(y) = f*(Aᵀ y)`. -/
theorem conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
    (σ : PosReal) (f : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)) :
    is_l_smooth_on
      (fun x : E ↦ ((f∗) x).toReal)
      Set.univ
      (Real.toNNReal (1 / (σ : ℝ))) := by
  -- Route correction: avoid the unfinished Chapter 5 strong-dual smoothness owner and prove
  -- smoothness directly from singleton Euclidean subdifferentials of the primal conjugate.
  let fStarReal : E → ℝ := fun x ↦ ((f∗) x).toReal
  have hσ_pos : 0 < (σ : ℝ) := PosReal.coe_pos σ
  have hf_strong' : is_strongly_convex_function f (σ : ℝ) := by
    -- Package the source assumptions into the Chapter 5 owner predicate.
    refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
    exact ⟨hσ_pos, hf_proper.ne_bot, hf_strong⟩
  have hf_convex : is_convex_function f := by
    -- Strong convexity implies convexity of the real-valued restriction on the effective domain.
    refine (is_convex_function_iff_convexOn_toReal (f := f) (fun x _ ↦ hf_proper.ne_bot x)).2 ?_
    have hstrict :
        StrictConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) :=
      (strongConvexOn_toReal_of_is_strongly_convex_function hf_strong').strictConvexOn hσ_pos
    exact hstrict.convexOn
  have hmono :
      euclidean_subdifferential_strong_monotonicity f (σ : ℝ) := by
    -- Theorem 5.24 turns strong convexity into the Euclidean strong-monotonicity inequality.
    exact
      (is_strongly_convex_function_iff_euclidean_subdifferential_strong_monotonicity
        hσ_pos
        hf_proper
        hf_closed
        hf_convex).mp
        hf_strong'
  have hfinite : ∀ y : E, (f∗) y ≠ ⊥ ∧ (f∗) y < ⊤ := by
    intro y
    -- Strong convexity makes the primal conjugate finite-valued everywhere.
    simpa using
      dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ)
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
        hf_proper
        hf_closed
        hf_strong
        y
  have hconj_convex : is_convex_function (f∗) := by
    -- Convexity of the conjugate is already available in the Chapter 12 bridge API.
    simpa using
      dual_based_proximal_gradient_dual_F_primal_convex
        (f := f)
        (A := (LinearMap.id : E →ₗ[ℝ] E))
  have hfinite_domain_univ : effective_domain (f∗) = Set.univ := by
    -- Everywhere finiteness identifies the effective domain of the conjugate with all of `E`.
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      exact (hfinite y).2
  have hconv : ConvexOn ℝ Set.univ fStarReal := by
    -- Finite-valuedness allows us to work on the real-valued primal-conjugate surface.
    simpa [fStarReal, hfinite_domain_univ] using
      convexOn_toReal_of_is_convex_function hconj_convex
        (fun y _ ↦ (hfinite y).1)
  have hsingleton :
      ∀ y : E, ∃ x : E, euclideanSubdifferentialAt fStarReal y = {x} := by
    intro y
    obtain ⟨φ, hφ⟩ := subdifferentialAt_nonempty_of_convexOn hconv y
    rcases (InnerProductSpace.toDual ℝ E).surjective φ with ⟨x0, hx0Eq⟩
    have hx0 : x0 ∈ euclideanSubdifferentialAt fStarReal y := by
      -- Pull the owner subgradient witness back to its unique Euclidean representative.
      rw [mem_euclideanSubdifferentialAt_iff]
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hx0Eq ▸ hφ
    have hx0Sub :
        (toDualMap ℝ E y : Module.Dual ℝ E) ∈ ∂ f(x0) :=
      mem_subdifferential_of_memEuclideanSubdifferentialAt_primalConjugate
        f hf_proper hf_closed hf_convex hfinite hx0
    have hx0Euclidean : y ∈ euclideanSubdifferential f x0 := by
      -- Re-express the owner subgradient on `f` through the Euclidean/Riesz bridge.
      rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
      simpa using hx0Sub
    have hunique : ∀ z ∈ euclideanSubdifferentialAt fStarReal y, z = x0 := by
      intro z hz
      have hzSub :
          (toDualMap ℝ E y : Module.Dual ℝ E) ∈ ∂ f(z) :=
        mem_subdifferential_of_memEuclideanSubdifferentialAt_primalConjugate
          f hf_proper hf_closed hf_convex hfinite hz
      have hzEuclidean : y ∈ euclideanSubdifferential f z := by
        -- Any other primal-conjugate subgradient induces the same primal subgradient of `f`.
        rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
        simpa using hzSub
      have hmono_zero : (σ : ℝ) * ‖z - x0‖ ^ (2 : ℕ) ≤ 0 := by
        simpa using hmono z x0 y hzEuclidean y hx0Euclidean
      have hnorm_sq_zero : ‖z - x0‖ ^ (2 : ℕ) = 0 := by
        have hnorm_sq_nonneg : 0 ≤ ‖z - x0‖ ^ (2 : ℕ) := by
          positivity
        nlinarith
          [hmono_zero, hnorm_sq_nonneg, hσ_pos]
      have hnorm_zero : ‖z - x0‖ = 0 := by
        nlinarith [hnorm_sq_zero]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
    refine ⟨x0, ?_⟩
    ext z
    constructor
    · intro hz
      exact Set.mem_singleton_iff.mpr (hunique z hz)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      simpa [hz] using hx0
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  constructor
  · intro y hy
    rcases hsingleton y with ⟨x, hx⟩
    -- A singleton Euclidean subdifferential is exactly the differentiability criterion.
    exact
      (differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton
        hconv
        hx).1
  · intro y1 hy1 y2 hy2
    rcases hsingleton y1 with ⟨x1, hx1⟩
    rcases hsingleton y2 with ⟨x2, hx2⟩
    have hx1_mem : x1 ∈ euclideanSubdifferentialAt fStarReal y1 := by
      simp [hx1]
    have hx2_mem : x2 ∈ euclideanSubdifferentialAt fStarReal y2 := by
      simp [hx2]
    have hx1Sub :
        (toDualMap ℝ E y1 : Module.Dual ℝ E) ∈ ∂ f(x1) :=
      mem_subdifferential_of_memEuclideanSubdifferentialAt_primalConjugate
        f hf_proper hf_closed hf_convex hfinite hx1_mem
    have hx2Sub :
        (toDualMap ℝ E y2 : Module.Dual ℝ E) ∈ ∂ f(x2) :=
      mem_subdifferential_of_memEuclideanSubdifferentialAt_primalConjugate
        f hf_proper hf_closed hf_convex hfinite hx2_mem
    have hy1Euclidean : y1 ∈ euclideanSubdifferential f x1 := by
      -- The singleton subgradient point for `f∗` corresponds to the primal subgradient `y1`.
      rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
      simpa using hx1Sub
    have hy2Euclidean : y2 ∈ euclideanSubdifferential f x2 := by
      -- The same bridge applies at the second point.
      rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
      simpa using hx2Sub
    have hgrad1 :
        x1 = gradient fStarReal y1 := by
      -- Proposition 3.14 identifies the unique Euclidean subgradient with the gradient.
      exact
        (differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton
          hconv
          hx1).2
    have hgrad2 :
        x2 = gradient fStarReal y2 := by
      -- The same singleton-subgradient identification holds at `y2`.
      exact
        (differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton
          hconv
          hx2).2
    have hmono_ineq :
        (σ : ℝ) * ‖x1 - x2‖ ^ (2 : ℕ) ≤ inner ℝ (y1 - y2) (x1 - x2) := by
      -- Strong monotonicity compares the primal subgradients induced by the two gradient points.
      exact hmono x1 x2 y1 hy1Euclidean y2 hy2Euclidean
    have hcs :
        inner ℝ (y1 - y2) (x1 - x2) ≤ ‖y1 - y2‖ * ‖x1 - x2‖ := by
      -- Cauchy--Schwarz bounds the right-hand side by the product of norms.
      simpa using real_inner_le_norm (y1 - y2) (x1 - x2)
    have hmul :
        (σ : ℝ) * ‖x1 - x2‖ ^ (2 : ℕ) ≤ ‖y1 - y2‖ * ‖x1 - x2‖ :=
      le_trans hmono_ineq hcs
    have hL_eq : (Real.toNNReal (1 / (σ : ℝ)) : ℝ) = 1 / (σ : ℝ) := by
      rw [Real.coe_toNNReal]
      positivity
    rw [hL_eq]
    have hgoal :
        ‖gradient fStarReal y1 - gradient fStarReal y2‖ ≤
          (1 / (σ : ℝ)) * ‖y1 - y2‖ := by
      by_cases hsame : x1 = x2
      · -- In the diagonal case the gradient difference vanishes.
        have hgrad_eq : gradient fStarReal y1 = gradient fStarReal y2 := by
          simpa [hgrad1, hgrad2] using hsame
        rw [hgrad_eq]
        have hnonneg : 0 ≤ (1 / (σ : ℝ)) * ‖y1 - y2‖ := by
          positivity
        simp
      · have hnorm_pos : 0 < ‖x1 - x2‖ := by
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hsame)
        have hlinear : (σ : ℝ) * ‖x1 - x2‖ ≤ ‖y1 - y2‖ := by
          -- Cancel one positive norm factor from the quadratic strong-monotonicity bound.
          by_contra hfail
          have hfail' : ‖y1 - y2‖ < (σ : ℝ) * ‖x1 - x2‖ := by
            linarith
          have hmul' :
              ‖y1 - y2‖ * ‖x1 - x2‖ < (σ : ℝ) * ‖x1 - x2‖ ^ (2 : ℕ) := by
            nlinarith
          linarith
        have hnorm_bound :
            ‖x1 - x2‖ ≤ (1 / (σ : ℝ)) * ‖y1 - y2‖ := by
          have hdiv : ‖x1 - x2‖ ≤ ‖y1 - y2‖ / (σ : ℝ) := by
            refine (le_div_iff₀ hσ_pos).2 ?_
            simpa [mul_comm, mul_left_comm, mul_assoc] using hlinear
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
        simpa [hgrad1, hgrad2] using hnorm_bound
    simpa [fStarReal] using hgoal

/-- Helper for Lemma 12.3: if `f` is proper, closed, and `σ`-strongly convex, then the
finite-valued function `F(y) = f*(Aᵀ y)` is globally smooth with constant `‖A‖^2 / σ`, written
here as `Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊^2`. -/
theorem dual_based_proximal_gradient_dual_F_primal_is_l_smooth
    (σ : PosReal) (f : E → EReal) (A : E →ₗ[ℝ] Y)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)) :
    is_l_smooth_on
      (fun y : Y ↦ ((f∗) (A.adjoint y)).toReal)
      Set.univ
      (Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ)) := by
  simpa [LinearMap.adjoint_toContinuousLinearMap] using
    Example_10_44.is_l_smooth_on_precompose_continuousLinearMap
      A.adjoint.toContinuousLinearMap
      (fun x : E ↦ ((f∗) x).toReal)
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        σ
        f
        hf_proper
        hf_closed
        hf_strong)

/-- A consequence of Lemma 12.3 (1): under Assumption 12.1, the Chapter 12 dual term
`F(y) = f*(Aᵀ y)` is convex. -/
theorem dual_based_proximal_gradient_dual_F_convex_of_problem
    (σ : PosReal) (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (_h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    is_convex_function (fun y : Y ↦ (f∗) (A.adjoint y)) := by
  -- Lemma 12.3 packages convexity as a direct corollary of the standing hypotheses on `f`.
  simpa using
    dual_based_proximal_gradient_dual_F_primal_convex
      (f := f)
      (A := A)

/-- A consequence of Lemma 12.3 (2): under Assumption 12.1, the Chapter 12 dual term
`F(y) = f*(Aᵀ y)` is globally smooth with constant `‖A‖^2 / σ`, encoded as
`Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊^2`. -/
theorem dual_based_proximal_gradient_dual_F_is_l_smooth_of_problem
    (σ : PosReal) (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    is_l_smooth_on
      (fun y : Y ↦ ((f∗) (A.adjoint y)).toReal)
      Set.univ
      (Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ)) := by
  -- The problem assumptions are exactly the Chapter 5 hypotheses required by the transport lemma.
  simpa using
    dual_based_proximal_gradient_dual_F_primal_is_l_smooth
      (σ := σ)
      (f := f)
      (A := A)
      h_problem.toIsProperExtendedRealFunction
      h_problem.f_closed
      h_problem.f_strongly_convex

end

section

variable {Y : Type v}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Evaluating the Chapter 12 owner `G(y) = g*(-y)` on the primal-space variable `y` gives the
primal-space formula `(g∗) (-y)`. -/
@[simp] theorem dual_based_proximal_gradient_dual_G_primal_apply
    (g : Y → EReal) (y : Y) :
    dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ Y y) = (g∗) (-y) := by
  -- Rewrite the Chapter 12 owner once and replace dual negation by primal negation.
  rw [dual_based_proximal_gradient_dual_G_term_apply, conjugate_function_primal_apply]
  congr 1
  ext x
  -- Negation commutes with the Riesz identification pointwise.
  simp [InnerProductSpace.toDualMap_apply_apply]

/-- Helper for Lemma 12.3: if `g` is proper and convex, then the primal-space dual term
`G(y) = g*(-y)` is proper. -/
theorem dual_based_proximal_gradient_dual_G_primal_proper
    [FiniteDimensional ℝ Y]
    (g : Y → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g) :
    IsProperExtendedRealFunction (fun y : Y ↦ (g∗) (-y)) := by
  have hg_conj_proper : IsProperExtendedRealFunction (g∗) :=
    conjugate_function_primal_proper_of_proper_convex g hg_proper hg_convex
  refine ⟨?_, ?_⟩
  · -- Properness on `g∗` immediately gives the no-`⊥` field after negation.
    intro y
    exact hg_conj_proper.ne_bot (-y)
  · -- A finite point for `g∗` pulls back to a finite point of `y ↦ g∗(-y)`.
    rcases hg_conj_proper.effective_domain_nonempty with ⟨y0, hy0⟩
    refine ⟨-y0, ?_⟩
    simpa using hy0

/-- Helper for Lemma 12.3: the primal-space dual term `G(y) = g*(-y)` is closed and convex. -/
theorem dual_based_proximal_gradient_dual_G_primal_closed_and_convex
    (g : Y → EReal) :
    LowerSemicontinuous (fun y : Y ↦ (g∗) (-y)) ∧
      is_convex_function (fun y : Y ↦ (g∗) (-y)) := by
  let negCLM : Y →L[ℝ] Y := -ContinuousLinearMap.id ℝ Y
  let negId : Y →ₗ[ℝ] Y := -LinearMap.id
  constructor
  · -- Closedness is preserved by continuous precomposition with negation.
    have hnegClosed :
        LowerSemicontinuous (fun y : Y ↦ (g∗) (negCLM y)) :=
      (conjugate_function_closed_and_convex g).1.comp negCLM.continuous
    simpa [negCLM] using hnegClosed
  · -- Convexity is preserved by linear precomposition with the negation map.
    have hnegConvex :
        is_convex_function (fun y : Y ↦ (g∗) (negId y + 0)) :=
      is_convex_function_precompose_linearMap_add
        (conjugate_function_closed_and_convex g).2
        negId
        0
    simpa [negId] using hnegConvex

end

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- A consequence of Lemma 12.3 (3): under Assumption 12.1, the Chapter 12 dual term
`G(y) = g*(-y)` is proper. -/
theorem dual_based_proximal_gradient_dual_G_proper_of_problem
    [FiniteDimensional ℝ Y]
    (σ : PosReal) (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    IsProperExtendedRealFunction (fun y : Y ↦ (g∗) (-y)) := by
  -- The problem assumptions already provide properness and convexity of `g`.
  simpa using
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g)
      h_problem.g_proper
      h_problem.g_convex

/-- A consequence of Lemma 12.3 (4): under Assumption 12.1, the Chapter 12 dual term
`G(y) = g*(-y)` is closed. -/
theorem dual_based_proximal_gradient_dual_G_closed_of_problem
    (σ : PosReal) (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (_h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    LowerSemicontinuous (fun y : Y ↦ (g∗) (-y)) := by
  -- Lemma 12.3 packages the closedness and convexity of the `G`-term together.
  exact (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).1

/-- A consequence of Lemma 12.3 (5): under Assumption 12.1, the Chapter 12 dual term
`G(y) = g*(-y)` is convex. -/
theorem dual_based_proximal_gradient_dual_G_convex_of_problem
    (σ : PosReal) (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (_h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    is_convex_function (fun y : Y ↦ (g∗) (-y)) := by
  -- Lemma 12.3 packages the closedness and convexity of the `G`-term together.
  exact (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2

end
