module

public import ReasLib.LinearAlgebra.Matrix.BlockIdentity
public import ReasLib.Optimization.BFGS.Trajectory
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Hermitian

public section

namespace BFGS

/-- Strict convexity makes the gradient pairing along every nontrivial chord positive. -/
private lemma inner_gradient_sub_pos_of_strictConvexOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E → ℝ) (h_differentiable : Differentiable ℝ F)
    (h_strictConvex : StrictConvexOn ℝ Set.univ F) {a b : E} (hab : a ≠ b) :
    0 < inner ℝ (gradient F b - gradient F a) (b - a) := by
  let φ : ℝ → ℝ := F ∘ AffineMap.lineMap a b
  have hφ_strict : StrictConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro r _ t _ hrt c d hc hd hcd
    have hline_ne : AffineMap.lineMap a b r ≠ AffineMap.lineMap a b t :=
      (AffineMap.lineMap_injective ℝ hab).ne hrt
    have hstrict := h_strictConvex.2 (Set.mem_univ _) (Set.mem_univ _)
      hline_ne hc hd hcd
    simpa only [φ, Function.comp_apply, Convex.combo_affine_apply hcd] using hstrict
  have hφ_differentiable : Differentiable ℝ φ :=
    h_differentiable.comp (AffineMap.lineMap a b).differentiable
  have hφ_deriv (t : ℝ) :
      deriv φ t = inner ℝ (gradient F (AffineMap.lineMap a b t)) (b - a) := by
    have houter := h_differentiable.differentiableAt
      (x := AffineMap.lineMap a b t) |>.hasGradientAt.hasFDerivAt
    have hline : HasDerivAt (AffineMap.lineMap a b) (b - a) t :=
      AffineMap.hasDerivAt_lineMap
    have hchain := houter.comp_hasDerivAt t hline
    rw [hchain.deriv]
    rfl
  have hmono := hφ_strict.strictMonoOn_deriv
    (fun t _ ↦ hφ_differentiable.differentiableAt)
    (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
  rw [hφ_deriv 0, hφ_deriv 1, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at hmono
  -- Subtract the two endpoint derivatives to recover the gradient-difference pairing.
  simpa only [inner_sub_left, sub_pos] using hmono

/-- A stationary point of a differentiable convex line restriction is an exact ray search. -/
private lemma isExact_of_inner_gradient_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E → ℝ) (h_differentiable : Differentiable ℝ F)
    (h_convex : ConvexOn ℝ Set.univ F) (x d : E) {β : ℝ} (hβ : 0 ≤ β)
    (hstationary : inner ℝ (gradient F (x + β • d)) d = 0) :
    LineSearch.IsExact F x d β := by
  let φ : ℝ → ℝ := F ∘ AffineMap.lineMap x (x + d)
  have hline_apply (t : ℝ) : AffineMap.lineMap x (x + d) t = x + t • d := by
    rw [AffineMap.lineMap_apply_module']
    module
  have hφ_eq : φ = fun t : ℝ ↦ F (x + t • d) := by
    funext t
    dsimp only [φ, Function.comp_apply]
    rw [hline_apply]
  have hφ_convex : ConvexOn ℝ Set.univ φ := by
    simpa only [Set.preimage_univ] using h_convex.comp_affineMap (AffineMap.lineMap x (x + d))
  have hφ_deriv : HasDerivAt φ (inner ℝ (gradient F (x + β • d)) d) β := by
    have houter := h_differentiable.differentiableAt
      (x := AffineMap.lineMap x (x + d) β) |>.hasGradientAt.hasFDerivAt
    have hline : HasDerivAt (AffineMap.lineMap x (x + d)) d β := by
      simpa only [add_sub_cancel_left] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := x + d) (x := β))
    have hchain := houter.comp_hasDerivAt β hline
    rw [hline_apply β] at hchain
    simpa only [InnerProductSpace.toDual_apply_apply] using hchain
  have hright : derivWithin φ (Set.Ioi β) β = 0 := by
    rw [hφ_deriv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi β), hstationary]
  have hmin_univ : IsMinOn φ Set.univ β :=
    hφ_convex.isMinOn_of_rightDeriv_eq_zero (by simp) hright
  refine LineSearch.isExact_iff F x d β |>.mpr ⟨hβ, ?_⟩
  have hmin_ray := hmin_univ.on_subset (Set.subset_univ (Set.Ici (0 : ℝ)))
  rwa [hφ_eq] at hmin_ray

/-- In a real two-dimensional inner-product subspace, common orthogonality and opposite
pairing signs determine a negative scalar multiple. -/
private lemma exists_neg_smul_of_common_orthogonal_of_finrank_eq_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) (h_dim : Module.finrank ℝ V = 2)
    {p u g t : E} (hpV : p ∈ V) (huV : u ∈ V) (hgV : g ∈ V)
    (hp : p ≠ 0) (hpu : inner ℝ p u = 0) (hpg : inner ℝ p g = 0)
    (hut : 0 < inner ℝ u t) (hgt : inner ℝ g t < 0) :
    ∃ β : ℝ, 0 < β ∧ u = (-β) • g := by
  -- Local instance justification (proof-local temporary data): the canonical
  -- orthogonal-collinearity theorem
  -- requires `Fact (Module.finrank ℝ V = 2)`, supplied by `h_dim`.
  letI : Fact (Module.finrank ℝ V = 2) := ⟨h_dim⟩
  let pV : V := ⟨p, hpV⟩
  let uV : V := ⟨u, huV⟩
  let gV : V := ⟨g, hgV⟩
  have hpV_ne : pV ≠ 0 := by
    intro hpV_zero
    apply hp
    exact congrArg Subtype.val hpV_zero
  have hgV_ne : gV ≠ 0 := by
    intro hgV_zero
    have hg_zero : g = 0 := congrArg Subtype.val hgV_zero
    rw [hg_zero, inner_zero_left] at hgt
    exact (lt_irrefl 0) hgt
  have hu_span : uV ∈ ℝ ∙ gV :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hpV_ne hgV_ne
      (by simpa only [pV, uV, Submodule.coe_inner])
      (by simpa only [pV, gV, Submodule.coe_inner])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu_span
  have hambient : c • g = u := congrArg Subtype.val hc
  have hpair : inner ℝ u t = c * inner ℝ g t := by
    rw [← hambient, inner_smul_left]
    simp only [conj_trivial]
  have hc_neg : c < 0 := by
    nlinarith
  refine ⟨-c, neg_pos.mpr hc_neg, ?_⟩
  rw [neg_neg]
  exact hambient.symm

/-- A positive-definite Hessian scaling relation identifies the corresponding search step. -/
private lemma eq_smul_searchDirection_of_toLpLin_eq_neg_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) {s g : EuclideanSpace ℝ ι}
    {β : ℝ} (hscale : Matrix.toLpLin 2 2 B s = (-β) • g) :
    s = β • searchDirection B g := by
  have hscale' : Matrix.mulVec B s.ofLp = (-β) • g.ofLp := by
    simpa only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_smul,
      WithLp.ofLp_neg] using congrArg WithLp.ofLp hscale
  apply (EuclideanSpace.equiv ι ℝ).injective
  apply Matrix.mulVec_injective_of_isUnit hB.isUnit
  rw [map_smul, Matrix.mulVec_smul, searchDirection_spec hB]
  simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, smul_neg, neg_smul,
    neg_neg] using hscale'

/-- The BFGS rank-two update acts through the old Hessian image and the two secant vectors. -/
private lemma update_toLpLin_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (s y z : EuclideanSpace ℝ ι) :
    Matrix.toLpLin 2 2 (update B s y) z =
      Matrix.toLpLin 2 2 B z -
          (dotProduct s.ofLp (Matrix.mulVec B s.ofLp))⁻¹ •
            (inner ℝ (Matrix.toLpLin 2 2 B z) s • Matrix.toLpLin 2 2 B s) +
        (dotProduct s.ofLp y.ofLp)⁻¹ • (inner ℝ z y • y) := by
  have hprod :
      Matrix.mulVec (B * Matrix.vecMulVec s.ofLp s.ofLp * B) z.ofLp =
        (dotProduct s.ofLp (Matrix.mulVec B z.ofLp)) • Matrix.mulVec B s.ofLp := by
    rw [← Matrix.mulVec_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec]
    simp only [op_smul_eq_smul]
  have hyprod : Matrix.mulVec (Matrix.vecMulVec y.ofLp y.ofLp) z.ofLp =
      (dotProduct y.ofLp z.ofLp) • y.ofLp := by
    rw [Matrix.vecMulVec_mulVec]
    simp only [op_smul_eq_smul]
  apply (EuclideanSpace.equiv ι ℝ).injective
  simp only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [BFGS.update_def, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, hprod,
    Matrix.smul_mulVec, hyprod]

/-- Updating by secant vectors in a subspace preserves identity action on its orthogonal block. -/
private lemma update_isBlockIdentityOn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} {V : Submodule ℝ (EuclideanSpace ℝ ι)}
    (hB : Matrix.IsBlockIdentityOn B V) {s y : EuclideanSpace ℝ ι}
    (hs : s ∈ V) (hy : y ∈ V) : Matrix.IsBlockIdentityOn (update B s y) V := by
  have hB_parts := Matrix.isBlockIdentityOn_iff B V |>.mp hB
  rw [Matrix.isBlockIdentityOn_iff]
  constructor
  · rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro z hz
    rw [update_toLpLin_apply]
    exact V.add_mem
      (V.sub_mem (hB_parts.1 hz) (V.smul_mem _ (V.smul_mem _ (hB_parts.1 hs))))
      (V.smul_mem _ (V.smul_mem _ hy))
  · intro z hz
    have hBz : Matrix.toLpLin 2 2 B z = z := hB_parts.2 z hz
    have hzs : inner ℝ z s = 0 := Submodule.inner_left_of_mem_orthogonal hs hz
    have hzy : inner ℝ z y = 0 := Submodule.inner_left_of_mem_orthogonal hy hz
    rw [update_toLpLin_apply, hBz, hzs, hzy]
    simp only [zero_smul, smul_zero, sub_zero, add_zero]

/-- A pairwise-distinct sequence satisfying the planar gradient, orthogonality, span,
and positive initial-step relations is an identity-initialized exact-line-search BFGS
trajectory whose Hessians act identically on the orthogonal complement. -/
theorem existsTrajectory_of_planarRelations {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (m β₀ : ℝ) (h_dim : Module.finrank ℝ V = 2) (h_differentiable : Differentiable ℝ F)
    (h_m : 0 < m) (h_strongConvex : StrongConvexOn Set.univ m F)
    (h_distinct : Function.Injective x) (h_point_mem : ∀ k, x k ∈ V)
    (h_gradient_mem : ∀ k, gradient F (x k) ∈ V)
    (h_orthogonal : ∀ k,
      inner ℝ (gradient F (x (k + 1))) (x (k + 1) - x k) = 0)
    (h_gradient_span : ∀ k, gradient F (x (k + 2)) ∈
      Submodule.span ℝ {gradient F (x (k + 1)) - gradient F (x k)})
    (h_gradient_ne : ∀ k, gradient F (x (k + 2)) ≠ 0)
    (h_beta : 0 < β₀)
    (h_initial : x 1 - x 0 = (-β₀) • gradient F (x 0)) :
    ∃ (B : ℕ → Matrix (Fin n) (Fin n) ℝ) (α : ℕ → ℝ),
      IsTrajectory F (1 : Matrix (Fin n) (Fin n) ℝ) x B α ∧
        ∀ k, Matrix.IsBlockIdentityOn (B k) V := by
  classical
  let g : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ gradient F (x k)
  let s : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ x (k + 1) - x k
  let y : ℕ → EuclideanSpace ℝ (Fin n) := fun k ↦ g (k + 1) - g k
  let B : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k ↦
    Nat.rec 1 (fun j Bj ↦ update Bj (s j) (y j)) k
  have hB_zero : B 0 = 1 := rfl
  have hB_succ (k : ℕ) : B (k + 1) = update (B k) (s k) (y k) := rfl
  have hs_mem (k : ℕ) : s k ∈ V := by
    exact V.sub_mem (h_point_mem (k + 1)) (h_point_mem k)
  have hy_mem (k : ℕ) : y k ∈ V := by
    exact V.sub_mem (h_gradient_mem (k + 1)) (h_gradient_mem k)
  have hs_ne (k : ℕ) : s k ≠ 0 := by
    intro hs_zero
    have hx_eq : x (k + 1) = x k := sub_eq_zero.mp hs_zero
    exact Nat.ne_of_gt (Nat.lt_succ_self k) (h_distinct hx_eq)
  have h_strictConvex : StrictConvexOn ℝ Set.univ F :=
    h_strongConvex.strictConvexOn h_m
  have h_convex : ConvexOn ℝ Set.univ F := h_strictConvex.convexOn
  have hcurvature (k : ℕ) : 0 < inner ℝ (y k) (s k) := by
    simpa only [g, s, y] using inner_gradient_sub_pos_of_strictConvexOn F
      h_differentiable h_strictConvex (h_distinct.ne (Nat.ne_of_lt (Nat.lt_succ_self k)))
  have hdot_curvature (k : ℕ) : 0 < dotProduct (s k).ofLp (y k).ofLp := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hcurvature k
  -- The source induction simultaneously preserves positivity, the block decomposition,
  -- and the signed scaling relation for the prescribed next displacement.
  have h_invariant (k : ℕ) :
      (B k).PosDef ∧ Matrix.IsBlockIdentityOn (B k) V ∧
        ∃ β : ℝ, 0 < β ∧ Matrix.toLpLin 2 2 (B k) (s k) = (-β) • g k := by
    induction k with
    | zero =>
        refine ⟨Matrix.PosDef.one, ?_, β₀, h_beta, ?_⟩
        · rw [hB_zero, Matrix.isBlockIdentityOn_iff, Matrix.toLpLin_one]
          exact ⟨by simp, fun z _ ↦ by simp⟩
        · rw [hB_zero, Matrix.toLpLin_one, LinearMap.id_apply]
          simpa only [s, g] using h_initial
    | succ k ih =>
        have hpos : (B (k + 1)).PosDef := by
          rw [hB_succ]
          exact update_posDef ih.1 (hdot_curvature k)
        have hblock : Matrix.IsBlockIdentityOn (B (k + 1)) V := by
          rw [hB_succ]
          exact update_isBlockIdentityOn ih.2.1 (hs_mem k) (hy_mem k)
        have hsecant : Matrix.toLpLin 2 2 (B (k + 1)) (s k) = y k := by
          apply (EuclideanSpace.equiv (Fin n) ℝ).injective
          simp only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv,
            Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
          rw [hB_succ]
          exact update_secant ih.1 (hdot_curvature k)
        have hy_orthogonal : inner ℝ (y k) (s (k + 1)) = 0 := by
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h_gradient_span k)
          have hc_ne : c ≠ 0 := by
            intro hc_zero
            rw [hc_zero, zero_smul] at hc
            exact h_gradient_ne k hc.symm
          have hscaled : inner ℝ (c • y k) (s (k + 1)) = 0 := by
            rw [hc]
            simpa only [g, s, y, Nat.add_assoc, Nat.reduceAdd] using h_orthogonal (k + 1)
          rw [inner_smul_left, conj_trivial] at hscaled
          exact (mul_eq_zero.mp hscaled).resolve_left hc_ne
        have hcommon_u :
            inner ℝ (s k) (Matrix.toLpLin 2 2 (B (k + 1)) (s (k + 1))) = 0 := by
          have hsymm := Matrix.isSymmetric_toEuclideanLin_iff.mpr hpos.isHermitian
          calc
            inner ℝ (s k) (Matrix.toLpLin 2 2 (B (k + 1)) (s (k + 1))) =
                inner ℝ (Matrix.toLpLin 2 2 (B (k + 1)) (s k)) (s (k + 1)) :=
              (hsymm (s k) (s (k + 1))).symm
            _ = inner ℝ (y k) (s (k + 1)) := by rw [hsecant]
            _ = 0 := hy_orthogonal
        have hcommon_g : inner ℝ (s k) (g (k + 1)) = 0 := by
          rw [real_inner_comm]
          simpa only [g, s] using h_orthogonal k
        have hu_mem : Matrix.toLpLin 2 2 (B (k + 1)) (s (k + 1)) ∈ V := by
          exact (Matrix.isBlockIdentityOn_iff (B (k + 1)) V |>.mp hblock).1
            (hs_mem (k + 1))
        have hu_pos :
            0 < inner ℝ (Matrix.toLpLin 2 2 (B (k + 1)) (s (k + 1))) (s (k + 1)) := by
          simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
            Matrix.toLpLin_apply] using quadraticDenominator_pos hpos (hs_ne (k + 1))
        have hg_neg : inner ℝ (g (k + 1)) (s (k + 1)) < 0 := by
          have hnext := hcurvature (k + 1)
          have hnext_orth : inner ℝ (g (k + 2)) (s (k + 1)) = 0 := by
            simpa only [g, s, Nat.add_assoc, Nat.reduceAdd] using h_orthogonal (k + 1)
          dsimp only [y] at hnext
          rw [inner_sub_left, hnext_orth, zero_sub] at hnext
          linarith
        obtain ⟨β, hβ, hscale⟩ :=
          exists_neg_smul_of_common_orthogonal_of_finrank_eq_two V h_dim
            (hs_mem k) hu_mem (h_gradient_mem (k + 1)) (hs_ne k)
            hcommon_u hcommon_g hu_pos hg_neg
        exact ⟨hpos, hblock, β, hβ, hscale⟩
  let α : ℕ → ℝ := fun k ↦ Classical.choose (h_invariant k).2.2
  have hα_pos (k : ℕ) : 0 < α k := Classical.choose_spec (h_invariant k).2.2 |>.1
  have hα_scale (k : ℕ) :
      Matrix.toLpLin 2 2 (B k) (s k) = (-α k) • g k :=
    Classical.choose_spec (h_invariant k).2.2 |>.2
  have hstep (k : ℕ) : s k = α k • searchDirection (B k) (g k) :=
    eq_smul_searchDirection_of_toLpLin_eq_neg_smul (h_invariant k).1 (hα_scale k)
  have hiterate (k : ℕ) :
      x (k + 1) = x k + α k • searchDirection (B k) (gradient F (x k)) := by
    calc
      x (k + 1) = x k + s k := by
        dsimp only [s]
        abel
      _ = x k + α k • searchDirection (B k) (gradient F (x k)) := by
        rw [hstep]
  have hexact (k : ℕ) :
      LineSearch.IsExact F (x k) (searchDirection (B k) (gradient F (x k))) (α k) := by
    have hstationary :
        inner ℝ (gradient F (x (k + 1)))
          (searchDirection (B k) (gradient F (x k))) = 0 := by
      have horth := h_orthogonal k
      rw [show x (k + 1) - x k = s k from rfl, hstep, inner_smul_right] at horth
      have hzero := (mul_eq_zero.mp horth).resolve_left (ne_of_gt (hα_pos k))
      simpa only [g] using hzero
    apply isExact_of_inner_gradient_eq_zero F h_differentiable h_convex
      (x k) (searchDirection (B k) (gradient F (x k))) (le_of_lt (hα_pos k))
    rw [← hiterate k]
    exact hstationary
  refine ⟨B, α, ?_, fun k ↦ (h_invariant k).2.1⟩
  -- The recursive equations and the established line-search facts now match the trajectory API.
  rw [isTrajectory_iff]
  exact ⟨hB_zero, h_differentiable, fun k ↦ (h_invariant k).1, hexact,
    hiterate, hB_succ⟩

end BFGS
