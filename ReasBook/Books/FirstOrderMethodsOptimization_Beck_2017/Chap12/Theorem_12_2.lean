/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_6
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_3

universe u v

noncomputable section

open Set
open InnerProductSpace (toDual toDualMap)

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Helper for Theorem 12.2: the relative interiors of two block domains combine to the product
relative interior. -/
private theorem memIntrinsicInterior_prod
    {S : Set E} {T : Set V} {x : E} {z : V}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Use the closed-ball characterization and project product affine-span membership to each factor.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨?_, min εS εT, lt_min hεS hεT, ?_⟩
  · exact subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩
  · intro uv huv
    rcases uv with ⟨u, v⟩
    rcases huv with ⟨huv_ball, huv_span⟩
    have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
      simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
    have hu_ball : u ∈ Metric.closedBall x εS := by
      refine Metric.mem_closedBall.2 ?_
      exact le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
    have hv_ball : v ∈ Metric.closedBall z εT := by
      refine Metric.mem_closedBall.2 ?_
      exact le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
    have hu_span_prod :
        u ∈ affineSpan ℝ (((LinearMap.fst ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
      have hmem_map :
          u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ E V).toAffineMap) := by
        simpa using
          (AffineSubspace.mem_map_of_mem (f := (LinearMap.fst ℝ E V).toAffineMap) huv_span)
      rw [AffineSubspace.map_span] at hmem_map
      exact hmem_map
    have hv_span_prod :
        v ∈ affineSpan ℝ (((LinearMap.snd ℝ E V).toAffineMap) '' (S ×ˢ T)) := by
      have hmem_map :
          v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ E V).toAffineMap) := by
        simpa using
          (AffineSubspace.mem_map_of_mem (f := (LinearMap.snd ℝ E V).toAffineMap) huv_span)
      rw [AffineSubspace.map_span] at hmem_map
      exact hmem_map
    have hu_span : u ∈ affineSpan ℝ S := by
      refine (affineSpan_mono ℝ ?_) hu_span_prod
      intro p hp
      rcases hp with ⟨q, hq, rfl⟩
      exact hq.1
    have hv_span : v ∈ affineSpan ℝ T := by
      refine (affineSpan_mono ℝ ?_) hv_span_prod
      intro p hp
      rcases hp with ⟨q, hq, rfl⟩
      exact hq.2
    exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 12.2: every point of an affine subspace lies in the intrinsic interior of
its carrier set. -/
private theorem memIntrinsicInterior_affineSubspace
    {W : Type*} {P : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MetricSpace P] [NormedAddTorsor W P]
    (s : AffineSubspace ℝ P) {x : P} (hx : x ∈ (s : Set P)) :
    x ∈ intrinsicInterior ℝ (s : Set P) := by
  -- Unfold the intrinsic interior inside the affine span, which is the affine subspace itself.
  rw [intrinsicInterior]
  refine ⟨⟨x, ?_⟩, ?_, rfl⟩
  · simpa [AffineSubspace.affineSpan_coe] using hx
  · have hpre :
        ((↑) : affineSpan ℝ (s : Set P) → P) ⁻¹' (s : Set P) = Set.univ := by
      ext y
      change (↑y ∈ (s : Set P)) ↔ True
      constructor
      · intro _
        trivial
      · intro _
        simpa [AffineSubspace.affineSpan_coe] using y.property
    rw [hpre]
    simp

/-- Helper for Theorem 12.2: the split objective never takes the value `-∞`. -/
private theorem splitObjective_ne_bot
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (xz : E × V) :
    composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz ≠ ⊥ := by
  rcases xz with ⟨x, z⟩
  -- Each summand avoids `⊥`, so the split objective does as well.
  simpa [composite_model_objective_apply, EReal.add_ne_bot_iff] using
    And.intro (h_problem.ne_bot x) (h_problem.g_proper.ne_bot z)

/-- Helper for Theorem 12.2: the split objective is finite exactly on
`effective_domain f ×ˢ effective_domain g`. -/
private theorem effectiveDomain_splitObjective
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    effective_domain (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) =
      effective_domain f ×ˢ effective_domain g := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Turn finiteness of the split sum into coordinatewise finiteness using the no-`⊥` owners.
  simp [effective_domain, lt_top_iff_ne_top, composite_model_objective_apply,
    EReal.add_ne_top_iff_ne_top₂, h_problem.ne_bot x, h_problem.g_proper.ne_bot z]

/-- Helper for Theorem 12.2: strong convexity of `f` and convexity of `g` make the split
objective convex on `E × V`. -/
private theorem splitObjective_convex
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    is_convex_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) := by
  have hf_convex_toReal :
      ConvexOn ℝ (effective_domain f) (fun x : E ↦ (f x).toReal) := by
    -- Strong convexity implies convexity of the real lift on the effective domain.
    exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
  have hf_convex : is_convex_function f := by
    -- Convert the domainwise convexity statement back to the project owner.
    rw [is_convex_function_iff_convexOn_toReal (fun x _ ↦ h_problem.ne_bot x)]
    exact hf_convex_toReal
  have hf_fst : is_convex_function (fun xz : E × V ↦ f xz.1) := by
    -- Pull the convexity of `f` back along the first-coordinate projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := f) hf_convex (LinearMap.fst ℝ E V) (0 : E)
  have hg_snd : is_convex_function (fun xz : E × V ↦ g xz.2) := by
    -- Pull the convexity of `g` back along the second-coordinate projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := g) h_problem.g_convex (LinearMap.snd ℝ E V) (0 : V)
  -- The split objective is the pointwise sum of the two coordinate pullbacks.
  simpa [composite_model_objective_eq_add] using
    (is_convex_function_pointwise_add
      hf_fst
      hg_snd
      (fun xz : E × V ↦ h_problem.ne_bot xz.1)
      (fun xz : E × V ↦ h_problem.g_proper.ne_bot xz.2))

/-- Helper for Theorem 12.2: the split objective is proper. -/
private theorem splitObjective_proper
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    IsProperExtendedRealFunction (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) := by
  rcases h_problem.effective_domain_nonempty with ⟨x₀, hx₀⟩
  rcases h_problem.g_proper.effective_domain_nonempty with ⟨z₀, hz₀⟩
  refine
    { ne_bot := splitObjective_ne_bot f g A h_problem
      effective_domain_nonempty := ?_ }
  refine ⟨(x₀, z₀), ?_⟩
  simpa [effectiveDomain_splitObjective f g A h_problem] using And.intro hx₀ hz₀

/-- Helper for Theorem 12.2: the Chapter 12 primal value is the infimum of the split objective
with infeasible pairs sent to `⊤`. -/
private theorem splitConstrainedPrimalValue_eq
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf
        (Set.range
            (constrained_problem_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (Set.univ.graphOn A))) := by
  -- First rewrite the Chapter 12 owner to the split infimum over graph-feasible pairs.
  rw [dual_based_proximal_gradient_primal_optimal_value_eq_split_infimum]
  -- Then compare the feasible-value image with the constrained-objective range.
  rw [show
      sInf
          (Set.image
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (Set.univ.graphOn A)) =
        sInf
          (Set.range
            (constrained_problem_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (Set.univ.graphOn A))) by
      apply le_antisymm
      · apply le_sInf
        rintro r ⟨xz, rfl⟩
        by_cases hxz : xz ∈ Set.univ.graphOn A
        · have hval :
              composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz =
                constrained_problem_objective
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (Set.univ.graphOn A) xz := by
            simpa using
              (constrained_problem_objective_of_mem
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                hxz).symm
          exact sInf_le ⟨xz, hxz, hval⟩
        · have htop :
              constrained_problem_objective
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (Set.univ.graphOn A) xz = ⊤ := by
            simpa using
              constrained_problem_objective_of_not_mem
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                hxz
          rw [htop]
          exact le_top
      · apply le_sInf
        rintro r ⟨xz, hxz, rfl⟩
        have hval :
              constrained_problem_objective
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (Set.univ.graphOn A) xz =
                composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz := by
          simpa using
            constrained_problem_objective_of_mem
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              hxz
        exact sInf_le ⟨xz, hval⟩]

/-- Helper for Theorem 12.2: the graph of a linear map is convex in the product space. -/
private theorem graphOn_convex
    (A : E →ₗ[ℝ] V) :
    Convex ℝ (Set.univ.graphOn A) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, z₁⟩
  rcases y with ⟨x₂, z₂⟩
  have hz₁ : A x₁ = z₁ := by
    simpa using hx
  have hz₂ : A x₂ = z₂ := by
    simpa using hy
  -- Linear combinations preserve the defining graph relation.
  simp [Set.mem_graphOn, hz₁, hz₂, map_add]

/-- Helper for Theorem 12.2: the indicator of the graph constraint is proper. -/
private theorem graphIndicator_proper
    (A : E →ₗ[ℝ] V) :
    IsProperExtendedRealFunction (extendedIndicator (Set.univ.graphOn A)) := by
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro xz
    by_cases hxz : xz ∈ Set.univ.graphOn A
    · simp [extendedIndicator, hxz]
    · simp [extendedIndicator, hxz]
  · refine ⟨(0, 0), ?_⟩
    simpa [effective_domain_extendedIndicator]

/-- Helper for Theorem 12.2: the graph indicator is convex because the graph of `A` is convex. -/
private theorem graphIndicator_convex
    (A : E →ₗ[ℝ] V) :
    is_convex_function (extendedIndicator (Set.univ.graphOn A)) := by
  have h_zero_convex : is_convex_function (0 : E × V → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (E × V))))
  have h_constrained_convex :
      is_convex_function
        (constrained_problem_objective (0 : E × V → EReal) (Set.univ.graphOn A)) := by
    exact is_convex_function_constrained_problem_objective h_zero_convex (graphOn_convex A)
  have hzero_ne_bot :
      ∀ xz ∉ Set.univ.graphOn A, (0 : EReal) ≠ ⊥ := by
    intro xz hxz
    simp
  -- Rewrite the constrained zero objective as `0 + δ_graph`, then cancel the zero summand.
  rw [constrained_problem_objective_eq_add_extendedIndicator
    (0 : E × V → EReal) (Set.univ.graphOn A) hzero_ne_bot] at h_constrained_convex
  simpa [composite_model_objective] using h_constrained_convex

/-- Helper for Theorem 12.2: the graph of a linear map is a cone. -/
private theorem graphOn_isCone
    (A : E →ₗ[ℝ] V) :
    IsCone (Set.univ.graphOn A) := by
  rw [isCone_iff_smul_mem]
  intro a ha x hx
  rcases x with ⟨x, z⟩
  have hz : A x = z := by
    simpa using hx
  -- Scaling a graph point preserves the relation `z = A x`.
  simp [Set.mem_graphOn, hz, map_smul]

/-- Helper for Theorem 12.2: the set-theoretic graph agrees with the carrier of the linear-map
graph submodule. -/
private theorem graphOn_eq_linearMap_graph
    (A : E →ₗ[ℝ] V) :
    Set.univ.graphOn A = (LinearMap.graph A : Set (E × V)) := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Compare the two graph presentations pointwise.
  simp [Set.mem_graphOn, LinearMap.mem_graph_iff, eq_comm]

/-- Helper for Theorem 12.2: the origin lies in the graph of `A`. -/
private theorem zero_mem_graphOn
    (A : E →ₗ[ℝ] V) :
    (0 : E × V) ∈ Set.univ.graphOn A := by
  simp [Set.mem_graphOn]

/-- Helper for Theorem 12.2: every graph-feasible pair lies in the intrinsic interior of the
graph constraint set. -/
private theorem memIntrinsicInterior_graphOn
    (A : E →ₗ[ℝ] V) {xz : E × V} (hxz : xz ∈ Set.univ.graphOn A) :
    xz ∈ intrinsicInterior ℝ (Set.univ.graphOn A) := by
  have hgraph_set :
      (LinearMap.graph A : Set (E × V)) =
        (((LinearMap.graph A).toAffineSubspace : AffineSubspace ℝ (E × V)) : Set (E × V)) := by
    -- The linear graph submodule and its associated affine subspace have the same carrier set.
    ext yz
    simp
  have hmem :
      xz ∈ (((LinearMap.graph A).toAffineSubspace : AffineSubspace ℝ (E × V)) : Set (E × V)) := by
    -- Rewrite the set-theoretic graph as the carrier of the linear graph submodule.
    simpa [graphOn_eq_linearMap_graph A, hgraph_set] using hxz
  -- Rewrite the target set to the affine-subspace carrier and then apply the affine-subspace API.
  rw [graphOn_eq_linearMap_graph A, hgraph_set]
  exact memIntrinsicInterior_affineSubspace ((LinearMap.graph A).toAffineSubspace) hmem

/-- Helper for Theorem 12.2: Assumption 12.1 provides a graph-feasible relative-interior witness
for the split formulation. -/
private theorem splitGraphQualificationWitness
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ xHat zHat,
      xHat ∈ intrinsicInterior ℝ (effective_domain f) ∧
        zHat ∈ intrinsicInterior ℝ (effective_domain g) ∧
          (xHat, zHat) ∈ Set.univ.graphOn A := by
  -- Repackage the source qualification witness as a point on the graph of `A`.
  rcases h_problem.exists_mem_intrinsicInterior_map_eq with
    ⟨xHat, hxHat, zHat, hzHat, hAz⟩
  refine ⟨xHat, zHat, hxHat, hzHat, ?_⟩
  simp [hAz]

/-- Helper for Theorem 12.2: the Chapter 4 split-graph qualification follows from the source
qualification witness. -/
private theorem splitGraphFenchelQualification_nonempty
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    (intrinsicInterior ℝ
        (effective_domain (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))) ∩
      intrinsicInterior ℝ
        (effective_domain (extendedIndicator (Set.univ.graphOn A)))).Nonempty := by
  rcases splitGraphQualificationWitness f g A h_problem with
    ⟨xHat, zHat, hxHat, hzHat, hgraph⟩
  refine ⟨(xHat, zHat), ?_⟩
  constructor
  · -- Place the witness in the product relative interior of the split effective domain.
    simpa [effectiveDomain_splitObjective f g A h_problem] using
      memIntrinsicInterior_prod hxHat hzHat
  · -- Rewrite the graph indicator domain to the graph itself and use the affine owner lemma.
    simpa [effective_domain_extendedIndicator] using
      memIntrinsicInterior_graphOn A hgraph

/-- Helper for Theorem 12.2: the generic perturbation value function
`d ↦ inf_u (f u + g (u + d))` used to reprove strong duality locally. -/
private noncomputable def localZeroCaseValue
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal) : W → EReal :=
  fun d ↦ sInf (Set.range fun u : W ↦ f u + g (u + d))

/-- Helper for Theorem 12.2: any feasible pair `(u, u + d)` places `d` in the effective domain of
the local perturbation value function. -/
private theorem mem_effectiveDomain_localZeroCaseValue_of_mem_domains
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal)
    {u d : W} (hu₁ : u ∈ effective_domain f) (hu₂ : u + d ∈ effective_domain g) :
    d ∈ effective_domain (localZeroCaseValue f g) := by
  rw [mem_effective_domain]
  have hu₁_top : f u ≠ ⊤ := lt_top_iff_ne_top.mp hu₁
  have hu₂_top : g (u + d) ≠ ⊤ := lt_top_iff_ne_top.mp hu₂
  -- Insert the concrete feasible witness and record that its value is finite.
  by_cases hbot₁ : f u = ⊥
  · exact lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) <| by simp [localZeroCaseValue, hbot₁]
  · by_cases hbot₂ : g (u + d) = ⊥
    · exact lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) <| by simp [localZeroCaseValue, hbot₂]
    · refine lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) ?_
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.add_ne_top_iff_ne_top₂ hbot₁ hbot₂).mpr
            ⟨hu₁_top, hu₂_top⟩

/-- Helper for Theorem 12.2: if both summands avoid `⊥`, then membership in the perturbation
effective domain is exactly the existence of a feasible finite pair. -/
private theorem mem_effectiveDomain_localZeroCaseValue_iff_exists
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal) (hf_ne_bot : ∀ x : W, f x ≠ ⊥) (hg_ne_bot : ∀ x : W, g x ≠ ⊥)
    {d : W} :
    d ∈ effective_domain (localZeroCaseValue f g) ↔
      ∃ u : W, u ∈ effective_domain f ∧ u + d ∈ effective_domain g := by
  constructor
  · intro hd
    rw [mem_effective_domain] at hd
    rcases exists_lt_of_csInf_lt (Set.range_nonempty (fun u : W ↦ f u + g (u + d))) hd with
      ⟨a, ⟨u, rfl⟩, hau⟩
    have hsum_ne_top : f u + g (u + d) ≠ ⊤ := lt_top_iff_ne_top.mp hau
    have hsplit :
        f u ≠ ⊤ ∧ g (u + d) ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top₂ (hf_ne_bot u) (hg_ne_bot (u + d))).mp hsum_ne_top
    exact ⟨u, lt_top_iff_ne_top.mpr hsplit.1, lt_top_iff_ne_top.mpr hsplit.2⟩
  · rintro ⟨u, hu₁, hu₂⟩
    exact mem_effectiveDomain_localZeroCaseValue_of_mem_domains f g hu₁ hu₂

/-- Helper for Theorem 12.2: partial minimization of a jointly convex kernel keeps the
perturbation value function convex. -/
private theorem localZeroCaseValue_isConvex
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal) (hf_ne_bot : ∀ x : W, f x ≠ ⊥) (hg_ne_bot : ∀ x : W, g x ≠ ⊥)
    (hf_convex : is_convex_function f) (hg_convex : is_convex_function g) :
    is_convex_function (localZeroCaseValue f g) := by
  let K : W × W → EReal := fun p ↦ f p.2 + g (p.2 + p.1)
  have hSecond : is_convex_function (fun p : W × W ↦ f p.2) := by
    -- Pull back `f` along the second projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        hf_convex
        (LinearMap.snd ℝ W W)
        (0 : W)
  have hSum : is_convex_function (fun p : W × W ↦ g (p.2 + p.1)) := by
    -- Pull back `g` along the addition map `(d, u) ↦ u + d`.
    simpa [add_comm] using
      is_convex_function_precompose_linearMap_add
        hg_convex
        (LinearMap.snd ℝ W W + LinearMap.fst ℝ W W)
        (0 : W)
  have hKernel : is_convex_function K := by
    -- Add the two jointly convex factors pointwise.
    simpa [K] using
      is_convex_function_pointwise_add
        hSecond
        hSum
        (fun p ↦ hf_ne_bot p.2)
        (fun p ↦ hg_ne_bot (p.2 + p.1))
  -- The perturbation owner is the partial infimum of that convex kernel.
  simpa [localZeroCaseValue, K] using
    partial_infimum_is_convex_function hKernel

/-- Helper for Theorem 12.2: evaluating the local perturbation value function at `0` recovers the
unsplit primal infimum. -/
private theorem localZeroCaseValue_zero_eq_primalValue
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal) :
    localZeroCaseValue f g (0 : W) = sInf (Set.range fun x : W ↦ f x + g x) := by
  -- The origin fiber identifies the perturbation value with the ordinary primal infimum.
  simp [localZeroCaseValue]

/-- Helper for Theorem 12.2: the common relative-interior qualification transports to the origin
of the local perturbation effective domain. -/
private theorem zero_mem_intrinsicInterior_effectiveDomain_localZeroCaseValue
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal)
    (hf_ne_bot : ∀ x : W, f x ≠ ⊥) (hg_ne_bot : ∀ x : W, g x ≠ ⊥)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f) ∩
        intrinsicInterior ℝ (effective_domain g)).Nonempty) :
    (0 : W) ∈ intrinsicInterior ℝ (effective_domain (localZeroCaseValue f g)) := by
  -- Translate the qualification witness into an interior neighborhood of the perturbation domain
  -- at the origin, exactly as in the standard zero-case proof.
  rcases hqual with ⟨x₀, hx₀₁, hx₀₂⟩
  have hxdom₁ : x₀ ∈ effective_domain f := intrinsicInterior_subset hx₀₁
  have hxdom₂ : x₀ ∈ effective_domain g := intrinsicInterior_subset hx₀₂
  let D : Set W := effective_domain (localZeroCaseValue f g)
  let P₁ : Submodule ℝ W := (affineSpan ℝ (effective_domain f)).direction
  let P₂ : Submodule ℝ W := (affineSpan ℝ (effective_domain g)).direction
  let U₁ : Set P₁ := {v : P₁ | x₀ + (v : W) ∈ effective_domain f}
  let U₂ : Set P₂ := {v : P₂ | x₀ + (v : W) ∈ effective_domain g}
  have hU₁_zero : (0 : P₁) ∈ interior U₁ := by
    -- Translate the first relative-interior point to an actual neighborhood at `0`.
    simpa [U₁, P₁] using translatedEffectiveDomainZero_mem_interior f x₀ hx₀₁
  have hU₂_zero : (0 : P₂) ∈ interior U₂ := by
    -- Repeat the same translation argument for the second effective domain.
    simpa [U₂, P₂] using translatedEffectiveDomainZero_mem_interior g x₀ hx₀₂
  let diffLinear : P₁ × P₂ →ₗ[ℝ] W :=
    { toFun := fun p ↦ (p.2 : W) - (p.1 : W)
      map_add' := by
        intro p q
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        simp [sub_eq_add_neg] }
  let W' : Submodule ℝ W := LinearMap.range diffLinear
  let diffToRange : P₁ × P₂ →ₗ[ℝ] W' := diffLinear.rangeRestrict
  let U : Set (P₁ × P₂) := U₁ ×ˢ U₂
  have hU_zero : (0 : P₁ × P₂) ∈ interior U := by
    -- The product of the translated neighborhoods is still an interior neighborhood of `0`.
    rw [show U = U₁ ×ˢ U₂ by rfl, interior_prod_eq]
    exact ⟨hU₁_zero, hU₂_zero⟩
  have hImage_subset :
      diffToRange '' U ⊆ ((↑) ⁻¹' D : Set W') := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩
    rcases hp with ⟨hp₁, hp₂⟩
    -- A pair of translated domain points yields a feasible witness for the fiber difference.
    refine
      mem_effectiveDomain_localZeroCaseValue_of_mem_domains f g
        (u := x₀ + (p.1 : W)) (d := (p.2 : W) - (p.1 : W)) ?_ ?_
    · simpa [U₁] using hp₁
    · simpa [U₂, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₂
  have hDiffOpen : IsOpenMap diffToRange :=
    diffToRange.isOpenMap_of_finiteDimensional (LinearMap.surjective_rangeRestrict diffLinear)
  let O : Set W' := diffToRange '' interior U
  have hO_zero : (0 : W') ∈ O := by
    -- The open-map image contains the origin because the source neighborhood contains the zero pair.
    refine ⟨0, hU_zero, ?_⟩
    simp [diffToRange, diffLinear]
  have hO_open : IsOpen O := by
    -- The image of the product neighborhood is open in the range subspace.
    exact hDiffOpen _ isOpen_interior
  have hO_subset : O ⊆ ((↑) ⁻¹' D : Set W') := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩
    exact hImage_subset ⟨p, interior_subset hp, rfl⟩
  have hW_zero : (0 : W') ∈ interior ((↑) ⁻¹' D : Set W') := by
    -- Push the open product neighborhood through the subtraction map.
    exact hO_open.mem_nhds hO_zero |> mem_interior_iff_mem_nhds.2 |> interior_mono hO_subset
  have hpreimage_span_top : Submodule.span ℝ (((↑) ⁻¹' D : Set W')) = ⊤ := by
    -- A nonempty interior neighborhood of `0` spans the whole range subspace.
    apply Submodule.eq_top_of_nonempty_interior'
    refine ⟨0, ?_⟩
    refine interior_mono ?_ hW_zero
    exact Submodule.subset_span
  have hDomain_subset_W' : D ⊆ (W' : Set W) := by
    intro d hd
    rcases (mem_effectiveDomain_localZeroCaseValue_iff_exists f g hf_ne_bot hg_ne_bot).1 hd with
      ⟨u, hu₁, hu₂⟩
    have hu₁_aff : u ∈ affineSpan ℝ (effective_domain f) :=
      subset_affineSpan ℝ (effective_domain f) hu₁
    have hx₀_aff₁ : x₀ ∈ affineSpan ℝ (effective_domain f) :=
      subset_affineSpan ℝ (effective_domain f) hxdom₁
    have hu₂_aff : u + d ∈ affineSpan ℝ (effective_domain g) :=
      subset_affineSpan ℝ (effective_domain g) hu₂
    have hx₀_aff₂ : x₀ ∈ affineSpan ℝ (effective_domain g) :=
      subset_affineSpan ℝ (effective_domain g) hxdom₂
    have hp₁_mem :
        u - x₀ ∈ (affineSpan ℝ (effective_domain f)).direction := by
      simpa [P₁] using
        (affineSpan ℝ (effective_domain f)).vsub_mem_direction hu₁_aff hx₀_aff₁
    have hp₂_mem :
        u + d - x₀ ∈ (affineSpan ℝ (effective_domain g)).direction := by
      simpa [P₂] using
        (affineSpan ℝ (effective_domain g)).vsub_mem_direction hu₂_aff hx₀_aff₂
    let p₁ : P₁ := ⟨u - x₀, hp₁_mem⟩
    let p₂ : P₂ := ⟨u + d - x₀, hp₂_mem⟩
    refine ⟨⟨p₁, p₂⟩, ?_⟩
    -- This witness decomposition places `d` in the subtraction-map range.
    simp [diffLinear, p₁, p₂, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have himage_preimage :
      (Submodule.subtype W') '' (((↑) ⁻¹' D : Set W')) = D := by
    ext d
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hd
      refine ⟨⟨d, hDomain_subset_W' hd⟩, hd, rfl⟩
  have hspan_D : Submodule.span ℝ D = W' := by
    -- Map the preimage span back through the subtype inclusion.
    calc
      Submodule.span ℝ D =
          Submodule.map (Submodule.subtype W') (Submodule.span ℝ (((↑) ⁻¹' D : Set W'))) := by
            rw [Submodule.map_span, himage_preimage]
      _ = Submodule.map (Submodule.subtype W') ⊤ := by rw [hpreimage_span_top]
      _ = W' := by simp
  have hzero_mem_D : (0 : W) ∈ D := by
    -- The qualification witness itself gives the zero difference.
    simpa [D] using
      (mem_effectiveDomain_localZeroCaseValue_of_mem_domains
        f g (u := x₀) (d := 0) hxdom₁ (by simpa using hxdom₂))
  have hD_le : affineSpan ℝ D ≤ W'.toAffineSubspace := by
    -- The domain already lies in the subtraction-map range.
    simpa [hspan_D] using (affineSpan_le_toAffineSubspace_span (k := ℝ) (s := D))
  have hW_le : W'.toAffineSubspace ≤ affineSpan ℝ D := by
    intro x hx
    have hvectorSpan_D :
        vectorSpan ℝ D = Submodule.span ℝ D := by
      simpa using
        (vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := D) hzero_mem_D)
    have hvec : x ∈ vectorSpan ℝ D := by
      rw [hvectorSpan_D, hspan_D]
      simpa [Submodule.mem_toAffineSubspace] using hx
    have hzero_aff : (0 : W) ∈ affineSpan ℝ D := mem_affineSpan ℝ hzero_mem_D
    -- Because `0 ∈ D`, vectors in the span of `D` are points of its affine hull.
    simpa using
      vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan (s := D) hzero_aff hvec
  have hspan_D_aff : affineSpan ℝ D = W'.toAffineSubspace :=
    le_antisymm hD_le hW_le
  -- Rewrite the intrinsic-interior ambient affine span using the range subspace and the open
  -- neighborhood already constructed there.
  rw [mem_intrinsicInterior, hspan_D_aff]
  refine ⟨⟨(0 : W), by simp [Submodule.mem_toAffineSubspace]⟩, ?_, rfl⟩
  simpa [D, Submodule.mem_toAffineSubspace] using hW_zero

/-- Helper for Theorem 12.2: every Fenchel dual objective value is bounded above by the zero-case
perturbation value at `0`. -/
private theorem fenchelDualProblemValue_le_localZeroCaseValue_zero
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g) :
    fenchel_dual_problem_value f g ≤ localZeroCaseValue f g (0 : W) := by
  rw [fenchel_dual_problem_value_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨y, rfl⟩
  rw [fenchel_dual_objective_eq_sInf_split_lagrangian f g hf_proper hg_proper y]
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  -- Evaluating the split infimum at the diagonal witness `(x, x)` recovers the zero fiber value.
  simpa [localZeroCaseValue, fenchel_split_lagrangian] using
    (sInf_le ⟨(x, x), rfl⟩ :
      sInf (Set.range fun xz : W × W ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) ≤
        fenchel_split_lagrangian f g x x y)

/-- Helper for Theorem 12.2: a subgradient of the zero-case perturbation value at the origin
produces a dual witness whose objective dominates that primal value. -/
private theorem localZeroCaseValue_le_fenchelDualObjective_of_mem_subdifferential_zero
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f g : W → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g)
    {η : Module.Dual ℝ W}
    (hη : η ∈ subdifferential (localZeroCaseValue f g) (0 : W)) :
    localZeroCaseValue f g (0 : W) ≤ fenchel_dual_objective f g (-η) := by
  have hf_ne_bot : ∀ x : W, f x ≠ ⊥ := hf_proper.ne_bot
  have hg_ne_bot : ∀ x : W, g x ≠ ⊥ := hg_proper.ne_bot
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hη
  rcases hη with ⟨_, hsupport⟩
  rw [fenchel_dual_objective_eq_sInf_split_lagrangian f g hf_proper hg_proper (-η)]
  refine le_sInf ?_
  rintro _ ⟨p, rfl⟩
  rcases p with ⟨x, z⟩
  dsimp
  by_cases hx : x ∈ effective_domain f
  · by_cases hz : z ∈ effective_domain g
    · let d : W := z - x
      have hzd : x + d ∈ effective_domain g := by
        simpa [d, sub_eq_add_neg, add_assoc] using hz
      have hd : d ∈ effective_domain (localZeroCaseValue f g) := by
        simpa [d, sub_eq_add_neg, add_assoc] using
          (mem_effectiveDomain_localZeroCaseValue_of_mem_domains f g hx hzd)
      have hsupport' :
          localZeroCaseValue f g d ≥ localZeroCaseValue f g (0 : W) + (η (d - 0) : EReal) :=
        hsupport d hd
      have hupper :
          localZeroCaseValue f g d ≤ f x + g z := by
        -- The feasible pair `(x, z)` gives an upper witness in the defining infimum.
        simpa [localZeroCaseValue, d, sub_eq_add_neg, add_assoc] using
          (sInf_le ⟨x, rfl⟩ :
            localZeroCaseValue f g d ≤ f x + g (x + d))
      have hcombined :
          localZeroCaseValue f g (0 : W) + (η (z - x) : EReal) ≤ f x + g z := by
        simpa [d] using hsupport'.trans hupper
      have hshift :
          localZeroCaseValue f g (0 : W) ≤ f x + g z - (η (z - x) : EReal) := by
        exact
          (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot (η (z - x))))
            (.inl (EReal.coe_ne_top (η (z - x))))).2
            hcombined
      have hneg_eval :
          ((-η) (z - x) : EReal) = -(η (z - x) : EReal) := by
        have hreal : (-η) (z - x) = -(η (z - x)) := by
          simp
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
      -- Rewrite the shifted bound into the split Lagrangian normalization at `-η`.
      calc
        localZeroCaseValue f g (0 : W) ≤ f x + g z - (η (z - x) : EReal) := hshift
        _ = f x + g z + (-(η (z - x) : EReal)) := by
          rw [sub_eq_add_neg]
        _ = f x + g z + ((-η) (z - x) : EReal) := by
          rw [hneg_eval]
        _ = fenchel_split_lagrangian f g x z (-η) := by
          symm
          rw [fenchel_split_lagrangian_apply, hneg_eval]
    · have hgz_top : g z = ⊤ := by
        refine le_antisymm le_top (not_lt.mp ?_)
        simpa [mem_effective_domain] using hz
      -- Outside the effective domain of `g`, the split Lagrangian is `⊤`.
      have htail_ne_bot : -((η (z - x) : EReal)) ≠ ⊥ := by
        intro hbot
        have htop : ((η (z - x) : EReal)) = ⊤ :=
          EReal.neg_eq_bot_iff.mp hbot
        exact EReal.coe_ne_top (η (z - x)) htop
      have hvalue_top : f x + g z + -((η (z - x) : EReal)) = ⊤ := by
        rw [hgz_top]
        rw [EReal.add_top_of_ne_bot (hf_ne_bot x)]
        rw [EReal.top_add_of_ne_bot htail_ne_bot]
      calc
        localZeroCaseValue f g (0 : W) ≤ ⊤ := le_top
        _ = f x + g z + -((η (z - x) : EReal)) := hvalue_top.symm
  · have hfx_top : f x = ⊤ := by
      refine le_antisymm le_top (not_lt.mp ?_)
      simpa [mem_effective_domain] using hx
    -- Outside the effective domain of `f`, the split Lagrangian is `⊤`.
    have htail_ne_bot : -((η (z - x) : EReal)) ≠ ⊥ := by
      intro hbot
      have htop : ((η (z - x) : EReal)) = ⊤ :=
        EReal.neg_eq_bot_iff.mp hbot
      exact EReal.coe_ne_top (η (z - x)) htop
    have hvalue_top : f x + g z + -((η (z - x) : EReal)) = ⊤ := by
      rw [hfx_top]
      rw [EReal.top_add_of_ne_bot (hg_ne_bot z)]
      rw [EReal.top_add_of_ne_bot htail_ne_bot]
    calc
      localZeroCaseValue f g (0 : W) ≤ ⊤ := le_top
      _ = f x + g z + -((η (z - x) : EReal)) := hvalue_top.symm

/-- Helper for Theorem 12.2: the split Fenchel pair on `E × V` has a local zero-case
perturbation owner. -/
private noncomputable def splitZeroCaseValue
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) : E × V → EReal :=
  localZeroCaseValue
    (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
    (extendedIndicator (Set.univ.graphOn A))

/-- Helper for Theorem 12.2: evaluating the split zero-case owner at `0` recovers the split
Fenchel primal infimum. -/
private theorem splitZeroCaseValue_zero_eqSplitFenchelPrimalInfimum
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) :
    splitZeroCaseValue f g A (0 : E × V) =
      sInf (Set.range
        (composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)))) := by
  -- Specialize the generic zero-case identity to the split objective plus graph indicator.
  simpa [splitZeroCaseValue, composite_model_objective_apply] using
    (localZeroCaseValue_zero_eq_primalValue
      (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
      (extendedIndicator (Set.univ.graphOn A)))

/-- Helper for Theorem 12.2: the split qualification witness puts `0` in the intrinsic interior of
the split zero-case effective domain. -/
private theorem splitZeroCaseOrigin_memIntrinsicInterior
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    (0 : E × V) ∈ intrinsicInterior ℝ (effective_domain (splitZeroCaseValue f g A)) := by
  have hF_ne_bot :
      ∀ xz : E × V, composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz ≠ ⊥ :=
    splitObjective_ne_bot f g A h_problem
  have hG_ne_bot :
      ∀ xz : E × V, extendedIndicator (Set.univ.graphOn A) xz ≠ ⊥ :=
    (graphIndicator_proper A).ne_bot
  -- Apply the generic intrinsic-interior argument to the split objective and graph indicator.
  simpa [splitZeroCaseValue] using
    zero_mem_intrinsicInterior_effectiveDomain_localZeroCaseValue
      (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
      (extendedIndicator (Set.univ.graphOn A))
      hF_ne_bot
      hG_ne_bot
      (splitGraphFenchelQualification_nonempty f g A h_problem)

/-- Helper for Theorem 12.2: the split Fenchel primal infimum equals the unrestricted split
Fenchel dual value by a local zero-case subgradient proof. -/
private theorem splitFenchelStrongDualityLocalAxiomClean
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    sInf (Set.range
      (composite_model_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A)))) =
      fenchel_dual_problem_value
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A)) := by
  have hF_ne_bot :
      ∀ xz : E × V, composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz ≠ ⊥ :=
    splitObjective_ne_bot f g A h_problem
  have hG_ne_bot :
      ∀ xz : E × V, extendedIndicator (Set.univ.graphOn A) xz ≠ ⊥ :=
    (graphIndicator_proper A).ne_bot
  have hψ_convex :
      is_convex_function (splitZeroCaseValue f g A) := by
    -- Convexity comes from partial minimization of the jointly convex split kernel.
    simpa [splitZeroCaseValue] using
      localZeroCaseValue_isConvex
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        hF_ne_bot
        hG_ne_bot
        (splitObjective_convex f g A h_problem)
        (graphIndicator_convex A)
  have hψ_ri :
      (0 : E × V) ∈ intrinsicInterior ℝ (effective_domain (splitZeroCaseValue f g A)) :=
    splitZeroCaseOrigin_memIntrinsicInterior f g A h_problem
  rcases subdifferential_nonempty_at_relativeInterior_point
      (splitZeroCaseValue f g A) (0 : E × V) hψ_convex hψ_ri with
    ⟨η, hη⟩
  have hlower :
      splitZeroCaseValue f g A (0 : E × V) ≤
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) := by
    -- The origin subgradient yields a single dual witness, hence a lower bound on the dual
    -- supremum.
    calc
      splitZeroCaseValue f g A (0 : E × V) ≤
          fenchel_dual_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A))
            (-η) := by
              exact
                localZeroCaseValue_le_fenchelDualObjective_of_mem_subdifferential_zero
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (extendedIndicator (Set.univ.graphOn A))
                  (splitObjective_proper f g A h_problem)
                  (graphIndicator_proper A)
                  (by simpa [splitZeroCaseValue] using hη)
      _ ≤
          fenchel_dual_problem_value
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A)) := by
              rw [fenchel_dual_problem_value_eq_sSup]
              exact le_sSup (Set.mem_range_self (-η))
  have hupper :
      fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) ≤
        splitZeroCaseValue f g A (0 : E × V) := by
    -- Test the split infimum at the diagonal witness to bound every dual value from above.
    simpa [splitZeroCaseValue] using
      fenchelDualProblemValue_le_localZeroCaseValue_zero
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        (splitObjective_proper f g A h_problem)
        (graphIndicator_proper A)
  have hzero_eq :
      splitZeroCaseValue f g A (0 : E × V) =
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) :=
    le_antisymm hlower hupper
  -- Replace the zero-case value by the split Fenchel primal infimum.
  simpa [splitZeroCaseValue_zero_eqSplitFenchelPrimalInfimum] using hzero_eq

/-- Helper for Theorem 12.2: the split Fenchel dual objective attains its supremum by the same
local zero-case subgradient witness. -/
private theorem splitFenchelDualAttainsLocalAxiomClean
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ ψ : Module.Dual ℝ (E × V),
      IsGreatest
        (Set.range
          (fenchel_dual_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A))))
        (fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          ψ) := by
  have hF_ne_bot :
      ∀ xz : E × V, composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz ≠ ⊥ :=
    splitObjective_ne_bot f g A h_problem
  have hG_ne_bot :
      ∀ xz : E × V, extendedIndicator (Set.univ.graphOn A) xz ≠ ⊥ :=
    (graphIndicator_proper A).ne_bot
  have hψ_convex :
      is_convex_function (splitZeroCaseValue f g A) := by
    -- Reuse the convexity of the split zero-case perturbation owner.
    simpa [splitZeroCaseValue] using
      localZeroCaseValue_isConvex
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        hF_ne_bot
        hG_ne_bot
        (splitObjective_convex f g A h_problem)
        (graphIndicator_convex A)
  have hψ_ri :
      (0 : E × V) ∈ intrinsicInterior ℝ (effective_domain (splitZeroCaseValue f g A)) :=
    splitZeroCaseOrigin_memIntrinsicInterior f g A h_problem
  rcases subdifferential_nonempty_at_relativeInterior_point
      (splitZeroCaseValue f g A) (0 : E × V) hψ_convex hψ_ri with
    ⟨η, hη⟩
  have hzero_eq :
      splitZeroCaseValue f g A (0 : E × V) =
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) := by
    -- Reuse the local strong-duality theorem to identify the zero-case value with the dual
    -- supremum.
    simpa [splitZeroCaseValue_zero_eqSplitFenchelPrimalInfimum] using
      splitFenchelStrongDualityLocalAxiomClean f g A h_problem
  have hdual_le_obj :
      fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) ≤
        fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (-η) := by
    -- The same subgradient witness attains the common optimal value.
    calc
      fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) =
        splitZeroCaseValue f g A (0 : E × V) := hzero_eq.symm
      _ ≤
          fenchel_dual_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A))
            (-η) := by
              exact
                localZeroCaseValue_le_fenchelDualObjective_of_mem_subdifferential_zero
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (extendedIndicator (Set.univ.graphOn A))
                  (splitObjective_proper f g A h_problem)
                  (graphIndicator_proper A)
                  (by simpa [splitZeroCaseValue] using hη)
  have hobj_le_dual :
      fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (-η) ≤
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) := by
    rw [fenchel_dual_problem_value_eq_sSup]
    exact le_sSup (Set.mem_range_self (-η))
  have hattain :
      fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) =
        fenchel_dual_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A))
          (-η) :=
    le_antisymm hdual_le_obj hobj_le_dual
  refine ⟨-η, ?_⟩
  refine ⟨Set.mem_range_self (-η), ?_⟩
  intro r hr
  rcases hr with ⟨ψ, rfl⟩
  -- Every split dual objective value is bounded above by the dual supremum, which `-η` attains.
  calc
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        ψ ≤
      fenchel_dual_problem_value
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A)) := by
          rw [fenchel_dual_problem_value_eq_sSup]
          exact le_sSup (Set.mem_range_self ψ)
    _ =
      fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        (-η) := hattain

/-- Helper for Theorem 12.2: the Chapter 12 primal value is the Chapter 4 primal infimum for the
split objective plus the graph indicator. -/
private theorem splitPrimalValue_eqFenchelPrimalInfimum
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf (Set.range
        (composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)))) := by
  have hconstrained_eq :
      constrained_problem_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (Set.univ.graphOn A) =
        composite_model_objective
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) := by
    -- Rewrite the constrained split objective as `splitObjective + δ_graph`.
    simpa [composite_model_objective_eq_add] using
      constrained_problem_objective_eq_add_extendedIndicator
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (Set.univ.graphOn A)
        (fun xz hxz ↦ splitObjective_ne_bot f g A h_problem xz)
  -- Substitute the canonical `splitObjective + δ_graph` owner into the normalized primal infimum.
  simpa [hconstrained_eq] using splitConstrainedPrimalValue_eq f g A

/-- Helper for Theorem 12.2: the graph-compatible dual vector attached to `y` annihilates
graph-feasible pairs `(x, A x)`. -/
private def graphDual
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) :
    Module.Dual ℝ (E × V) :=
  (A.dualMap y).comp (LinearMap.fst ℝ E V) -
    y.comp (LinearMap.snd ℝ E V)

/-- Helper for Theorem 12.2: evaluating the graph-compatible dual vector gives
`⟨Aᵀ y, x⟩ - ⟨y, z⟩`. -/
@[simp] private theorem graphDual_apply
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) (xz : E × V) :
    graphDual A y xz = ((A.dualMap y) xz.1 : ℝ) - y xz.2 := by
  -- Expand the product projections once so later graph identities simplify deterministically.
  simp [graphDual, sub_eq_add_neg]

/-- Helper for Theorem 12.2: the graph-compatible dual vector vanishes on the graph of `A`. -/
private theorem graphDual_graph_eq_zero
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) (x : E) :
    graphDual A y (x, A x) = 0 := by
  -- On a feasible split pair `(x, A x)`, the two pairing terms cancel exactly.
  simp [graphDual_apply]

/-- Helper for Theorem 12.2: the polar cone of the graph consists exactly of graph-compatible
dual vectors. -/
private theorem memPolarCone_graphOn_iff_exists_graphDual
    (A : E →ₗ[ℝ] V) (ψ : Module.Dual ℝ (E × V)) :
    ψ ∈ polar_cone (Set.univ.graphOn A) ↔ ∃ y : Module.Dual ℝ V, ψ = graphDual A y := by
  constructor
  · intro hψ
    have hψ_mem : ∀ x ∈ Set.univ.graphOn A, ψ x ≤ 0 :=
      (mem_polar_cone (Set.univ.graphOn A) ψ).1 hψ
    let y : Module.Dual ℝ V := -(ψ.comp (LinearMap.inr ℝ E V))
    refine ⟨y, ?_⟩
    apply LinearMap.ext
    intro xz
    rcases xz with ⟨x, z⟩
    have hgraph_mem : (x, A x) ∈ Set.univ.graphOn A := by
      simp
    have hneg_graph_mem : (-x, A (-x)) ∈ Set.univ.graphOn A := by
      simp
    have hgraph_le : ψ (x, A x) ≤ 0 := by
      exact hψ_mem (x, A x) hgraph_mem
    have hneg_graph : ψ (-x, A (-x)) ≤ 0 := by
      exact hψ_mem (-x, A (-x)) hneg_graph_mem
    have hneg_eval : ψ (-x, A (-x)) = -ψ (x, A x) := by
      calc
        ψ (-x, A (-x)) = ψ (-(x, A x)) := by simp
        _ = -ψ (x, A x) := by rw [map_neg]
    have hgraph_ge : 0 ≤ ψ (x, A x) := by
      have hneg : -(ψ (x, A x)) ≤ 0 := by
        rw [← hneg_eval]
        exact hneg_graph
      exact neg_nonpos.mp hneg
    have hgraph_eq : ψ (x, A x) = 0 := le_antisymm hgraph_le hgraph_ge
    have hsplit : (x, z) = (x, A x) + (0, z - A x) := by
      ext <;> simp
    -- Decompose an arbitrary pair into a graph component plus a vertical correction.
    calc
      ψ (x, z) = ψ (x, A x) + ψ (0, z - A x) := by
        rw [hsplit, map_add]
      _ = ψ (0, z - A x) := by simp [hgraph_eq]
      _ = ψ (0, z) - ψ (0, A x) := by
        simpa using map_sub ψ (0, z) (0, A x)
      _ = ((A.dualMap y) x : ℝ) - y z := by
        change ψ (0, z) - ψ (0, A x) = y (A x) - y z
        simp [y, sub_eq_add_neg, add_comm]
  · rintro ⟨y, rfl⟩
    rw [mem_polar_cone]
    intro x hx
    rcases x with ⟨u, z⟩
    have hz : A u = z := by
      simpa using hx
    -- A graph-compatible dual vector evaluates to zero on every graph-feasible pair.
    simp [graphDual_apply, hz]

/-- Helper for Theorem 12.2: negating an affine perturbation turns its infimum into the negative
Fenchel conjugate. -/
private theorem ereal_sInf_range_sub_pairing_eq_neg_conjugate
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (h : W → EReal) (η : Module.Dual ℝ W) :
    sInf (Set.range fun x : W ↦ h x - (η x : EReal)) = -conjugate_function h η := by
  have hrange :
      Set.range (fun x : W ↦ h x - (η x : EReal)) =
        -Set.range (fun x : W ↦ (η x : EReal) - h x) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      have hη_ne_bot : ((η x : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hη_ne_top : ((η x : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hraw :
          -(h x - (η x : EReal)) = -h x + (η x : EReal) := by
        exact EReal.neg_sub (Or.inr hη_ne_bot) (Or.inr hη_ne_top)
      have hneg : -(h x - (η x : EReal)) = ((η x : EReal) - h x) := by
        simpa [sub_eq_add_neg, add_comm] using hraw
      simpa using hneg.symm
    · rw [Set.mem_neg]
      rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hη_ne_bot : ((η x : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hη_ne_top : ((η x : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hraw :
          -(h x - (η x : EReal)) = -h x + (η x : EReal) := by
        exact EReal.neg_sub (Or.inr hη_ne_bot) (Or.inr hη_ne_top)
      have hneg : -(h x - (η x : EReal)) = ((η x : EReal) - h x) := by
        simpa [sub_eq_add_neg, add_comm] using hraw
      have hneg' : -(h x - (η x : EReal)) = -r := by
        calc
          -(h x - (η x : EReal)) = ((η x : EReal) - h x) := hneg
          _ = -r := by simpa using hx
      have hr' := congrArg Neg.neg hneg'
      simpa using hr'
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange]
  have hsInf_neg :
      sInf (-Set.range (fun x : W ↦ (η x : EReal) - h x)) =
        -sSup (Set.range fun x : W ↦ (η x : EReal) - h x) := by
    refine le_antisymm ?_ ?_
    · have hsSup :
          sSup (Set.range fun x : W ↦ (η x : EReal) - h x) ≤
            -sInf (-Set.range fun x : W ↦ (η x : EReal) - h x) := by
        refine sSup_le ?_
        intro x hx
        have hsInf :
            sInf (-Set.range fun x : W ↦ (η x : EReal) - h x) ≤ -x := by
          have hmem : -x ∈ -Set.range (fun x : W ↦ (η x : EReal) - h x) := by
            simpa [Set.mem_neg] using hx
          exact sInf_le hmem
        exact EReal.le_neg.mp hsInf
      exact EReal.le_neg.mpr hsSup
    · refine le_sInf ?_
      intro z hz
      refine EReal.neg_le.mpr ?_
      have hmem : -z ∈ Set.range (fun x : W ↦ (η x : EReal) - h x) := by
        simpa [Set.mem_neg] using hz
      exact le_sSup hmem
  rw [hsInf_neg, conjugate_function_apply]

/-- Helper for Theorem 12.2: negating the graph-compatible dual vector corresponds to negating the
underlying dual variable. -/
@[simp] private theorem graphDual_neg
    (A : E →ₗ[ℝ] V) (y : Module.Dual ℝ V) :
    graphDual A (-y) = -graphDual A y := by
  apply LinearMap.ext
  intro xz
  -- Expand both graph-dual evaluations pointwise and regroup the real terms.
  simp [graphDual_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.2: the support function of the graph constraint is exactly the indicator
of the graph-dual range. -/
private theorem supportFunction_graphOn_eqIndicator_graphDualRange
    (A : E →ₗ[ℝ] V) :
    support_function (Set.univ.graphOn A) =
      extendedIndicator (Set.range (graphDual A)) := by
  funext ψ
  have hpolar :
      ψ ∈ polar_cone (Set.univ.graphOn A) ↔ ψ ∈ Set.range (graphDual A) := by
    have hpolar_raw := memPolarCone_graphOn_iff_exists_graphDual A ψ
    constructor
    · intro hmem
      rcases hpolar_raw.mp hmem with ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact hpolar_raw.mpr ⟨y, hy.symm⟩
  have hsupport :
      support_function (Set.univ.graphOn A) ψ =
        extendedIndicator (polar_cone (Set.univ.graphOn A)) ψ := by
    simpa using
      congrArg (fun h : Module.Dual ℝ (E × V) → EReal ↦ h ψ)
        (support_function_eq_indicatorFunction_polarCone
          (Set.univ.graphOn A) (graphOn_isCone A) (zero_mem_graphOn A))
  by_cases hψ : ψ ∈ Set.range (graphDual A)
  · have hpolar_mem : ψ ∈ polar_cone (Set.univ.graphOn A) := hpolar.mpr hψ
    simpa [extendedIndicator, hψ, hpolar_mem] using hsupport
  · have hpolar_not_mem : ψ ∉ polar_cone (Set.univ.graphOn A) := by
      intro hmem
      exact hψ (hpolar.mp hmem)
    simpa [extendedIndicator, hψ, hpolar_not_mem] using hsupport

/-- Helper for Theorem 12.2: membership in the graph-dual range is invariant under negation. -/
private theorem neg_mem_graphDualRange_iff
    (A : E →ₗ[ℝ] V) (ψ : Module.Dual ℝ (E × V)) :
    -ψ ∈ Set.range (graphDual A) ↔ ψ ∈ Set.range (graphDual A) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    calc
      graphDual A (-y) = -graphDual A y := by simpa using graphDual_neg A y
      _ = ψ := by simpa [hy]
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    calc
      graphDual A (-y) = -graphDual A y := by simpa using graphDual_neg A y
      _ = -ψ := by simpa [hy]

/-- Helper for Theorem 12.2: evaluating the split objective minus `graphDual A y` is exactly the
Chapter 12 Lagrangian integrand. -/
private theorem splitObjective_sub_graphDual_eq_lagrangian
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (_h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : Module.Dual ℝ V) (xz : E × V) :
    composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz -
        ((graphDual A y) xz : EReal) =
      dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y := by
  rcases xz with ⟨x, z⟩
  -- Normalize the graph-dual pairing into the same affine split used by the Lagrangian owner.
  rw [dual_based_proximal_gradient_lagrangian_eq_affine_split, graphDual_apply,
    composite_model_objective_apply]
  have hs :
      -((((A.dualMap y) x - y z : ℝ) : EReal)) =
        -(((A.dualMap y) x : EReal)) + (y z : EReal) := by
    change (((-(((A.dualMap y) x - y z)) : ℝ)) : EReal) =
        (((-((A.dualMap y) x) + y z : ℝ)) : EReal)
    norm_num [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [sub_eq_add_neg, hs]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.2: the negative conjugate of the split objective on `graphDual A y`
matches the Chapter 12 dual objective. -/
private theorem negConjugate_splitObjective_graphDual_eqDualObjective
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : Module.Dual ℝ V) :
    -conjugate_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (graphDual A y) =
      dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  -- Rewrite the conjugate via the affine-perturbation infimum, then identify it with the
  -- Chapter 12 Lagrangian infimum formula.
  calc
    -conjugate_function (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (graphDual A y) =
        sInf (Set.range fun xz : E × V ↦
          composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) xz -
            ((graphDual A y) xz : EReal)) := by
          symm
          exact
            ereal_sInf_range_sub_pairing_eq_neg_conjugate
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (graphDual A y)
    _ =
        sInf (Set.range fun xz : E × V ↦
          dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) := by
          apply congrArg sInf
          ext r
          constructor
          · rintro ⟨xz, rfl⟩
            refine ⟨xz, ?_⟩
            simpa using splitObjective_sub_graphDual_eq_lagrangian f g A h_problem y xz
          · rintro ⟨xz, rfl⟩
            refine ⟨xz, ?_⟩
            simpa using splitObjective_sub_graphDual_eq_lagrangian f g A h_problem y xz
    _ = dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
      symm
      exact
        dual_based_proximal_gradient_lagrange_dual_objective_eq_sInf_lagrangian_formula
          f g A y h_problem.toIsProperExtendedRealFunction h_problem.g_proper

/-- Helper for Theorem 12.2: on the graph-dual range, the unrestricted Fenchel dual objective
agrees with the Chapter 12 dual objective. -/
private theorem splitGraphFenchelDualObjective_onGraphDual
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : Module.Dual ℝ V) :
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        (graphDual A y) =
      dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  -- Combine the split-objective conjugate bridge with the graph-support rewrite.
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function,
    supportFunction_graphOn_eqIndicator_graphDualRange A,
    negConjugate_splitObjective_graphDual_eqDualObjective f g A h_problem]
  have hneg_mem : -graphDual A y ∈ Set.range (graphDual A) := by
    refine ⟨-y, ?_⟩
    simpa using graphDual_neg A y
  simp [extendedIndicator, hneg_mem]

/-- Helper for Theorem 12.2: away from the graph-dual range, the unrestricted Fenchel dual
objective collapses to `-∞`. -/
private theorem splitGraphFenchelDualObjective_eqBot_of_notMemGraphDualRange
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)
    (ψ : Module.Dual ℝ (E × V))
    (hψ : ψ ∉ Set.range (graphDual A)) :
    fenchel_dual_objective
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A))
        ψ = ⊥ := by
  have hneg : -ψ ∉ Set.range (graphDual A) := by
    intro hmem
    exact hψ ((neg_mem_graphDualRange_iff A ψ).mp hmem)
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function,
    supportFunction_graphOn_eqIndicator_graphDualRange A]
  simp [extendedIndicator, hneg]

/-- Helper for Theorem 12.2: the unrestricted Fenchel dual value of the split graph formulation
is exactly the Chapter 12 dual problem value. -/
private theorem splitGraphFenchelDualProblemValue_eqLagrangeDualProblemValue
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    fenchel_dual_problem_value
        (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (extendedIndicator (Set.univ.graphOn A)) =
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  -- Compare the two suprema pointwise using the graph-dual on-range rewrite and the off-range
  -- collapse.
  rw [fenchel_dual_problem_value_eq_sSup, dual_based_proximal_gradient_lagrange_dual_problem_value]
  apply le_antisymm
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨ψ, rfl⟩
    by_cases hψ : ψ ∈ Set.range (graphDual A)
    · rcases hψ with ⟨y, rfl⟩
      rw [splitGraphFenchelDualObjective_onGraphDual f g A h_problem y]
      exact le_sSup ⟨y, rfl⟩
    · rw [splitGraphFenchelDualObjective_eqBot_of_notMemGraphDualRange f g A ψ hψ]
      exact bot_le
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    rw [← splitGraphFenchelDualObjective_onGraphDual f g A h_problem y]
    exact le_sSup ⟨graphDual A y, rfl⟩

/-- Helper for Theorem 12.2: the primal optimal value equals the Chapter 12 dual problem value. -/
private theorem dualBasedProximalGradientProblemStrongDualityLocal
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  -- Route correction: replace the contaminated public Chapter 4 value theorem with the local
  -- zero-case proof on the same split graph formulation, then rewrite the dual value back to the
  -- Chapter 12 owner.
  calc
    dual_based_proximal_gradient_primal_optimal_value f g A =
        sInf (Set.range
          (composite_model_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A)))) :=
      splitPrimalValue_eqFenchelPrimalInfimum f g A h_problem
    _ =
        fenchel_dual_problem_value
          (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
          (extendedIndicator (Set.univ.graphOn A)) :=
      splitFenchelStrongDualityLocalAxiomClean f g A h_problem
    _ = dual_based_proximal_gradient_lagrange_dual_problem_value f g A :=
      splitGraphFenchelDualProblemValue_eqLagrangeDualProblemValue f g A h_problem

/-- Helper for Theorem 12.2: the primal-space Chapter 12 dual objective is the canonical
dual-space owner evaluated at the Riesz image `toDualMap ℝ V y`. -/
private theorem primalDualObjective_eqDualOwner
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (y : V) :
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
      dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ V y) := by
  -- Rewrite the source-facing primal formula through the canonical dual-space owner.
  calc
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
        -dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V y) -
          dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V y) := by
          rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply,
            ← dual_based_proximal_gradient_dual_F_primal_apply (f := f) (A := A) (y := y),
            ← dual_based_proximal_gradient_dual_G_primal_apply (g := g) (y := y)]
    _ =
        dual_based_proximal_gradient_lagrange_dual_objective
          f g A (toDualMap ℝ V y) := by
          rw [dual_based_proximal_gradient_lagrange_dual_objective_apply,
            dual_based_proximal_gradient_dual_F_term_apply,
            dual_based_proximal_gradient_dual_G_term_apply]

/-- Helper for Theorem 12.2: every primal-space dual value is bounded above by the Chapter 12
dual problem value. -/
private theorem primalDualObjective_leDualProblemValue
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (y : V) :
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y ≤
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  -- Compare the primal-space value with the defining supremum of the canonical dual owner.
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value_eq_sSup]
  calc
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
        dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ V y) :=
      primalDualObjective_eqDualOwner f g A y
    _ ≤ sSup (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A)) := by
      exact le_sSup ⟨toDualMap ℝ V y, rfl⟩

/-- Helper for Theorem 12.2: Riesz representation transports the canonical dual-space value back
to the primal-space Chapter 12 dual objective. -/
private theorem primalDualObjective_eqDualOwner_ofDual
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (yDual : Module.Dual ℝ V) :
    let y : V := (toDual ℝ V).symm (LinearMap.toContinuousLinearMap yDual)
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
      dual_based_proximal_gradient_lagrange_dual_objective f g A yDual := by
  let y : V := (toDual ℝ V).symm (LinearMap.toContinuousLinearMap yDual)
  have hyDual_cont :
      (toDual ℝ V y : StrongDual ℝ V) = LinearMap.toContinuousLinearMap yDual := by
    exact LinearIsometryEquiv.apply_symm_apply (toDual ℝ V) (LinearMap.toContinuousLinearMap yDual)
  have hyDual :
      ((toDualMap ℝ V y : StrongDual ℝ V) : Module.Dual ℝ V) = yDual := by
    ext v
    change (toDual ℝ V y) v = yDual v
    simpa using congrArg (fun φ : StrongDual ℝ V ↦ φ v) hyDual_cont
  calc
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
        dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ V y) :=
      primalDualObjective_eqDualOwner f g A y
    _ = dual_based_proximal_gradient_lagrange_dual_objective f g A yDual := by
      rw [hyDual]

/-- Helper for Theorem 12.2: a maximizing split dual witness transports to a maximizing primal
dual vector in `V`. -/
private theorem graphDualGreatest_toPrimalExistsIsGreatest
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ y : V,
      IsGreatest
        (Set.range (dual_based_proximal_gradient_lagrange_dual_objective_primal f g A))
        (dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y) := by
  obtain ⟨ψStar, hψStarGreatest⟩ :=
    splitFenchelDualAttainsLocalAxiomClean f g A h_problem
  by_cases hψStar : ψStar ∈ Set.range (graphDual A)
  · rcases hψStar with ⟨yDual, hyDual⟩
    let y : V := (toDual ℝ V).symm (LinearMap.toContinuousLinearMap yDual)
    refine ⟨y, ?_⟩
    constructor
    · exact ⟨y, rfl⟩
    · rintro r ⟨yBar, rfl⟩
      have hsplit_le :
          fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A (toDualMap ℝ V yBar)) ≤
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              ψStar := by
        have hmem :
            fenchel_dual_objective
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                (extendedIndicator (Set.univ.graphOn A))
                (graphDual A (toDualMap ℝ V yBar)) ∈
              Set.range
                (fenchel_dual_objective
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (extendedIndicator (Set.univ.graphOn A))) := by
          exact ⟨graphDual A (toDualMap ℝ V yBar), rfl⟩
        exact hψStarGreatest.2 hmem
      have hleft :
          dual_based_proximal_gradient_lagrange_dual_objective_primal f g A yBar =
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A (toDualMap ℝ V yBar)) := by
        calc
          dual_based_proximal_gradient_lagrange_dual_objective_primal f g A yBar =
              dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ V yBar) :=
            primalDualObjective_eqDualOwner f g A yBar
          _ =
              fenchel_dual_objective
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                (extendedIndicator (Set.univ.graphOn A))
                (graphDual A (toDualMap ℝ V yBar)) := by
                  symm
                  exact splitGraphFenchelDualObjective_onGraphDual
                    f g A h_problem (toDualMap ℝ V yBar)
      have hright :
          fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              ψStar =
            dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y := by
        calc
          fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              ψStar =
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A yDual) := by
                rw [hyDual]
          _ = dual_based_proximal_gradient_lagrange_dual_objective f g A yDual := by
                exact splitGraphFenchelDualObjective_onGraphDual f g A h_problem yDual
          _ = dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y := by
                symm
                simpa [y] using primalDualObjective_eqDualOwner_ofDual f g A yDual
      calc
        dual_based_proximal_gradient_lagrange_dual_objective_primal f g A yBar =
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A (toDualMap ℝ V yBar)) := hleft
        _ ≤
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              ψStar := hsplit_le
        _ = dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y := hright
  · have hψStar_bot :
        fenchel_dual_objective
            (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
            (extendedIndicator (Set.univ.graphOn A))
            ψStar = ⊥ := by
      exact splitGraphFenchelDualObjective_eqBot_of_notMemGraphDualRange f g A ψStar hψStar
    have hall_bot :
        ∀ y : V, dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y = ⊥ := by
      intro y
      have hsplit_le :
          fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A (toDualMap ℝ V y)) ≤
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              ψStar := by
        have hmem :
            fenchel_dual_objective
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                (extendedIndicator (Set.univ.graphOn A))
                (graphDual A (toDualMap ℝ V y)) ∈
              Set.range
                (fenchel_dual_objective
                  (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                  (extendedIndicator (Set.univ.graphOn A))) := by
          exact ⟨graphDual A (toDualMap ℝ V y), rfl⟩
        exact hψStarGreatest.2 hmem
      have hsplit_bot :
          fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A (toDualMap ℝ V y)) = ⊥ := by
        exact le_bot_iff.mp <|
          calc
            fenchel_dual_objective
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                (extendedIndicator (Set.univ.graphOn A))
                (graphDual A (toDualMap ℝ V y)) ≤
              fenchel_dual_objective
                (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
                (extendedIndicator (Set.univ.graphOn A))
                ψStar := hsplit_le
            _ = ⊥ := hψStar_bot
      calc
        dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
            dual_based_proximal_gradient_lagrange_dual_objective f g A (toDualMap ℝ V y) :=
          primalDualObjective_eqDualOwner f g A y
        _ =
            fenchel_dual_objective
              (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
              (extendedIndicator (Set.univ.graphOn A))
              (graphDual A (toDualMap ℝ V y)) := by
                symm
                exact splitGraphFenchelDualObjective_onGraphDual f g A h_problem (toDualMap ℝ V y)
        _ = ⊥ := hsplit_bot
    refine ⟨0, ?_⟩
    constructor
    · exact ⟨0, rfl⟩
    · rintro r ⟨y, rfl⟩
      rw [hall_bot y, hall_bot 0]

/-- Helper for Theorem 12.2: the Chapter 12 dual problem value is finite. -/
private theorem dualBasedDualProblemValue_finite
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ r : ℝ, dual_based_proximal_gradient_lagrange_dual_problem_value f g A = (r : EReal) := by
  obtain ⟨xHat, hxHat, zHat, hzHat, hAz⟩ := h_problem.exists_mem_intrinsicInterior_map_eq
  have hxHat_eff : xHat ∈ effective_domain f := intrinsicInterior_subset hxHat
  have hzHat_eff : zHat ∈ effective_domain g := intrinsicInterior_subset hzHat
  have hpOpt_le :
      dual_based_proximal_gradient_primal_optimal_value f g A ≤
        composite_model_objective f (g ∘ A) xHat := by
    rw [dual_based_proximal_gradient_primal_optimal_value_eq_sInf]
    exact sInf_le ⟨xHat, rfl⟩
  have hprimal_val_ne_top :
      composite_model_objective f (g ∘ A) xHat ≠ ⊤ := by
    simpa [composite_model_objective_apply, Function.comp, hAz] using
      (ne_of_lt (EReal.add_lt_top (ne_of_lt hxHat_eff) (ne_of_lt hzHat_eff)))
  have hpOpt_ne_top :
      dual_based_proximal_gradient_primal_optimal_value f g A ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hpOpt_le (lt_top_iff_ne_top.mpr hprimal_val_ne_top))
  let hGproper :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g)
      h_problem.g_proper
      h_problem.g_convex
  rcases hGproper.effective_domain_nonempty with ⟨y0, hy0⟩
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ)
      (f := f)
      (A := A)
      h_problem.toIsProperExtendedRealFunction
      h_problem.f_closed
      h_problem.f_strongly_convex
      y0
  have hnegF_ne_bot : -((f∗) (A.adjoint y0)) ≠ ⊥ := by
    intro hbot
    have htop : (f∗) (A.adjoint y0) = ⊤ := by
      simpa using congrArg Neg.neg hbot
    exact hF_finite.2.ne htop
  have hGy_ne_top : (g∗) (-y0) ≠ ⊤ := by
    simpa [effective_domain] using (mem_effective_domain.mp hy0).ne
  have hnegG_ne_bot : -((g∗) (-y0)) ≠ ⊥ := by
    intro hbot
    have htop : (g∗) (-y0) = ⊤ := by
      simpa using congrArg Neg.neg hbot
    exact hGy_ne_top htop
  have hdualValue_ne_bot :
      dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y0 ≠ ⊥ := by
    rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, sub_eq_add_neg]
    exact EReal.add_ne_bot_iff.mpr ⟨hnegF_ne_bot, hnegG_ne_bot⟩
  have hqOpt_ne_bot :
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A ≠ ⊥ := by
    have hle :
        dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y0 ≤
          dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
      exact primalDualObjective_leDualProblemValue f g A y0
    intro hbot
    rw [hbot] at hle
    exact hdualValue_ne_bot (le_bot_iff.mp hle)
  have hqOpt_ne_top :
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A ≠ ⊤ := by
    rw [← dualBasedProximalGradientProblemStrongDualityLocal f g A h_problem]
    exact hpOpt_ne_top
  refine ⟨(dual_based_proximal_gradient_lagrange_dual_problem_value f g A).toReal, ?_⟩
  exact (EReal.coe_toReal hqOpt_ne_top hqOpt_ne_bot).symm

/-- Theorem 12.2 (1): under Assumption 12.1, the primal optimal value of
`min_x {f x + g (A x)}` equals the optimal value of the Chapter 12 Lagrange dual problem
`max_y {-f*(Aᵀ y) - g*(-y)}`. -/
theorem dual_based_proximal_gradient_problem_strong_duality
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  -- Route correction: realize the Chapter 12 pair as a split graph-constrained Fenchel problem,
  -- prove strong duality there, and transport the dual value back to the chapter owner.
  simpa using dualBasedProximalGradientProblemStrongDualityLocal f g A h_problem

/-- Theorem 12.2 (2): under Assumption 12.1, the textbook dual objective
`y ↦ -f*(Aᵀ y) - g*(-y)` on `V` attains its maximum. -/
theorem exists_isGreatest_dual_based_proximal_gradient_lagrange_dual_objective_primal
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ y : V,
      IsGreatest
        (Set.range (dual_based_proximal_gradient_lagrange_dual_objective_primal f g A))
        (dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y) := by
  -- Route correction: transport the local split-dual maximizer back through the graph-dual range
  -- bridge instead of using the contaminated public Chapter 4 attainment theorem.
  simpa using graphDualGreatest_toPrimalExistsIsGreatest f g A h_problem

end
