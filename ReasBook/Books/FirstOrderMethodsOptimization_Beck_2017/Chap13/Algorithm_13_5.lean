/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_31
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- `prompt_add/` is absent in this workspace, so the statement design is checked against the
nearby Chapter 13 owners. Domain sampling for Algorithm 13.5 uses:

- `polytope_quadratic_objective`, `polytope_quadratic_problem`, and
  `polytope_quadratic_feasible_set` from Definition 13.10 as the `core/canonical` quadratic
  model `f_q`, constrained problem `(13.32)`, and feasible polytope `Ω` on the canonical
  Chapter 13 owner `Fin n → ℝ`;
- `positiveDefiniteMatrices n` from Definition 1.31 as the canonical owner for the textbook
  regime `Q ∈ 𝕊_{++}^n`, used only in the bridge and optimality theorems that need the
  positive-definite quadratic geometry behind equation `(13.34)`;
- `unconstrained_problem_solutions` from Chapter 8 as the canonical owner for the finite
  vertex-index argmin set, together with `IsMinOn` for the corresponding minimizer
  characterization and the induced linearized conditional-gradient subproblem on
  `Ω = conv{a₁, …, a_l}`;
- `conditional_gradient_exact_line_search_stepsizes` from Definition 13.6 as the chapter owner
  for exact line search on a segment, with the clipped quadratic ratio from equation `(13.34)`
  treated below as a source-facing bridge into that owner rather than as a second owner;
- the project's set-valued one-step algorithm pattern from Algorithm 11.2 and Algorithm 13.1.

This item is `source-facing`: it chooses a minimizing vertex index, defines the search direction
and the exact-line-search scalar explicitly, and then either stops on the sign test
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` or updates to the next iterate. The helper owners below therefore use the
primitive matrix/point data already sufficient to define their formulas, while the
positive-definite and feasibility assumptions are kept only on the bridge and optimality theorems
that need them. The public API is therefore a small family of concrete helpers together with a
set-valued one-step owner, while optimality of the stopping branch is kept as a separate theorem
rather than primitive algorithmic data. The bridge/view `EuclideanSpace ℝ (Fin n) ≃ Fin n → ℝ`
is not exposed here: Algorithm 13.5 now lives directly on the chapter's quadratic owner type. -/

/-- The vertex-selection objective in Algorithm 13.5, namely
`i ↦ a_iᵀ (Q xᵏ + b)`, equivalently `i ↦ ⟪a_i, ∇ f_q(xᵏ)⟫` in the textbook
positive-definite quadratic setting. -/
def polytope_quadratic_vertex_linear_objective
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) : Fin l → ℝ :=
  fun i ↦ dotProduct (a i) (Q *ᵥ xk + b)

-- Proof sketch: unfold `polytope_quadratic_vertex_linear_objective`; evaluation at `i` is exactly
-- the displayed linearization value `a_iᵀ (Q xᵏ + b)`.
/-- Evaluating the vertex-selection objective at `i` gives `a_iᵀ (Q xᵏ + b)`. -/
@[simp] theorem polytope_quadratic_vertex_linear_objective_apply
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_vertex_linear_objective Q b a xk i =
      dotProduct (a i) (Q *ᵥ xk + b) :=
  rfl

/-- Every vertex `a_i` belongs to the feasible polytope `Ω = conv{a₁, …, a_l}`. -/
theorem polytope_quadratic_vertex_mem_feasible_set
    (a : Fin l → E) (i : Fin l) :
    a i ∈ polytope_quadratic_feasible_set a := by
  exact subset_convexHull ℝ (Set.range a) ⟨i, rfl⟩

-- Proof sketch: a linear functional attains the same minimum on a convex hull as on the
-- generating vertices. Therefore a minimizing vertex index produces a canonical `IsMinOn`
-- witness for the linearized subproblem over `Ω`.
/-- A minimizing vertex index in Algorithm 13.5 yields a canonical minimizer of the linearized
objective over the full feasible polytope `Ω = conv{a₁, …, a_l}`. -/
theorem polytope_quadratic_linearized_isMinOn_feasible_set_of_mem_vertex_argmin
    {Q : Matrix (Fin n) (Fin n) ℝ} {b : E} {a : Fin l → E} {xk : E} {i : Fin l}
    (hi :
      i ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xk)) :
    IsMinOn (fun y ↦ dotProduct y (Q *ᵥ xk + b)) (polytope_quadratic_feasible_set a) (a i) :=
  by
    -- Rewrite the discrete argmin certificate into pointwise bounds on every vertex.
    rw [isMinOn_iff]
    intro y hy
    let g : E := Q *ᵥ xk + b
    have hi' := mem_unconstrained_problem_solutions_iff_forall_le.mp hi
    have hverts : ∀ j : Fin l, dotProduct (a i) g ≤ dotProduct (a j) g := by
      intro j
      simpa [polytope_quadratic_vertex_linear_objective, g] using hi' j
    have hlin : IsLinearMap ℝ (fun z : E ↦ dotProduct z g) := by
      refine ⟨?_, ?_⟩
      · intro u v
        simp
      · intro c u
        simp
    -- The supporting halfspace is convex and contains every generating vertex, hence the hull.
    have hsubset :
        polytope_quadratic_feasible_set a ⊆ {z : E | dotProduct (a i) g ≤ dotProduct z g} := by
      refine convexHull_min ?_ (convex_halfSpace_ge hlin (dotProduct (a i) g))
      intro z hz
      rcases hz with ⟨j, rfl⟩
      simpa [g] using hverts j
    exact hsubset hy

/-- The search direction `dᵏ = a_{i_k} - xᵏ` from Algorithm 13.5. -/
def polytope_quadratic_conditional_gradient_direction
    (a : Fin l → E) (xk : E) (i : Fin l) : E :=
  a i - xk

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_direction`; the result is exactly
-- the difference `a_{i_k} - xᵏ`.
/-- Expanding the search direction gives `a_{i_k} - xᵏ`. -/
@[simp] theorem polytope_quadratic_conditional_gradient_direction_eq
    (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_conditional_gradient_direction a xk i = a i - xk :=
  rfl

/-- The stopping test in Algorithm 13.5 is the directional derivative
`(dᵏ)ᵀ (Q xᵏ + b)` along the chosen vertex direction, equivalently
`⟪dᵏ, ∇ f_q(xᵏ)⟫` in the positive-definite quadratic setting. -/
def polytope_quadratic_conditional_gradient_directional_derivative
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) : ℝ :=
  dotProduct (polytope_quadratic_conditional_gradient_direction a xk i)
    (Q *ᵥ xk + b)

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_directional_derivative`; this is
-- exactly `(dᵏ)ᵀ (Q xᵏ + b)`.
/-- Expanding the stopping test gives `(dᵏ)ᵀ (Q xᵏ + b)`. -/
@[simp] theorem polytope_quadratic_conditional_gradient_directional_derivative_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i =
      dotProduct (polytope_quadratic_conditional_gradient_direction a xk i)
        (Q *ᵥ xk + b) :=
  rfl

/-- The unclipped ratio from equation `(13.34)`,
`λ_k = -⟪dᵏ, ∇ f_q(xᵏ)⟫ / ((dᵏ)^T Q dᵏ)` attached to a matrix `Q`, current point `xᵏ`, and
direction `dᵏ`. On the nonterminal branch of Algorithm 13.5 in the positive-definite quadratic
regime, this is the exact-line-search candidate later clipped to `[0, 1]`. -/
def polytope_quadratic_exact_line_search_ratio
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (xk d : E) : ℝ :=
  -dotProduct d (Q *ᵥ xk + b) / dotProduct d (Q *ᵥ d)

-- Proof sketch: unfold `polytope_quadratic_exact_line_search_ratio`; the declaration is exactly
-- the quotient displayed in equation `(13.34)`.
/-- Expanding `polytope_quadratic_exact_line_search_ratio Q b xᵏ dᵏ` gives the scalar
`-⟪dᵏ, ∇ f_q(xᵏ)⟫ / ((dᵏ)^T Q dᵏ)`. -/
@[simp] theorem polytope_quadratic_exact_line_search_ratio_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (xk d : E) :
    polytope_quadratic_exact_line_search_ratio Q b xk d =
      -dotProduct d (Q *ᵥ xk + b) / dotProduct d (Q *ᵥ d) :=
  rfl

/-- The nonterminal-branch update formula `xᵏ + t_k dᵏ` from Algorithm 13.5, expressed using the
clipped ratio attached to the chosen vertex direction. In Algorithm 13.5 this formula is used on
the branch `⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0`, later specialized to feasible iterates and positive-definite
quadratic data. -/
def polytope_quadratic_conditional_gradient_update
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) : E :=
  let d := polytope_quadratic_conditional_gradient_direction a xk i
  xk + min (polytope_quadratic_exact_line_search_ratio Q b xk d) 1 • d

-- Proof sketch: unfold `polytope_quadratic_conditional_gradient_update`; it is definitionally the
-- update `xᵏ + t_k dᵏ` with `dᵏ = a_{i_k} - xᵏ` and `t_k = min {λ_k, 1}`.
/-- Expanding the nonterminal update gives `xᵏ + t_k dᵏ` with the exact-line-search stepsize
attached to the chosen direction `dᵏ = a_{i_k} - xᵏ`. -/
theorem polytope_quadratic_conditional_gradient_update_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) (xk : E) (i : Fin l) :
    polytope_quadratic_conditional_gradient_update Q b a xk i =
      let d := polytope_quadratic_conditional_gradient_direction a xk i
      xk + min (polytope_quadratic_exact_line_search_ratio Q b xk d) 1 • d :=
  rfl

/-- Helper for Algorithm 13.5: positive definiteness makes the quadratic cross term symmetric. -/
private lemma positiveDefinite_dotProduct_mulVec_swap
    {Q : positiveDefiniteMatrices n} (x y : E) :
    dotProduct x (Q *ᵥ y) = dotProduct y (Q *ᵥ x) := by
  -- Move the positive-definite matrix across the dot product using Hermitian symmetry.
  calc
    dotProduct x (Q *ᵥ y) = dotProduct (Q *ᵥ x) y :=
      dotProduct_mulVec_swap_of_isHermitian Q Q.2.isHermitian x y
    _ = dotProduct y (Q *ᵥ x) := by
      rw [dotProduct_comm]

/-- Helper for Algorithm 13.5: the quadratic objective restricts to a scalar quadratic along every
line through a point. -/
lemma polytope_quadratic_objective_add_smul_direction_eq
    {Q : positiveDefiniteMatrices n} {b x d : E} {t : ℝ} :
    polytope_quadratic_objective Q b (x + t • d) =
      polytope_quadratic_objective Q b x +
        t * dotProduct d (Q *ᵥ x + b) +
        ((t ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) := by
  have hquad :
      dotProduct (x + t • d) (Q *ᵥ (x + t • d)) =
        dotProduct x (Q *ᵥ x) +
          2 * t * dotProduct d (Q *ᵥ x) +
          t ^ (2 : ℕ) * dotProduct d (Q *ᵥ d) := by
    -- Expand the quadratic term and identify the two mixed terms via symmetry of `Q`.
    calc
      dotProduct (x + t • d) (Q *ᵥ (x + t • d))
          = dotProduct (x + t • d) (Q *ᵥ x + t • (Q *ᵥ d)) := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = dotProduct (x + t • d) (Q *ᵥ x) + dotProduct (x + t • d) (t • (Q *ᵥ d)) := by
            rw [dotProduct_add]
      _ = dotProduct x (Q *ᵥ x) + dotProduct (t • d) (Q *ᵥ x) +
            dotProduct (x + t • d) (t • (Q *ᵥ d)) := by
            rw [add_dotProduct]
      _ = dotProduct x (Q *ᵥ x) + t * dotProduct d (Q *ᵥ x) +
            dotProduct (x + t • d) (t • (Q *ᵥ d)) := by
            simp [smul_eq_mul]
      _ = dotProduct x (Q *ᵥ x) + t * dotProduct d (Q *ᵥ x) +
            t * dotProduct (x + t • d) (Q *ᵥ d) := by
            simp [smul_eq_mul]
      _ = dotProduct x (Q *ᵥ x) + t * dotProduct d (Q *ᵥ x) +
            t * (dotProduct x (Q *ᵥ d) + dotProduct (t • d) (Q *ᵥ d)) := by
            rw [add_dotProduct]
      _ = dotProduct x (Q *ᵥ x) + t * dotProduct d (Q *ᵥ x) +
            t * (dotProduct d (Q *ᵥ x) + t * dotProduct d (Q *ᵥ d)) := by
            simp [positiveDefinite_dotProduct_mulVec_swap, smul_eq_mul]
      _ = dotProduct x (Q *ᵥ x) +
            2 * t * dotProduct d (Q *ᵥ x) +
            t ^ (2 : ℕ) * dotProduct d (Q *ᵥ d) := by
            ring
  have hlin :
      dotProduct b (x + t • d) = dotProduct b x + t * dotProduct d b := by
    -- The affine term is linear along the same line.
    rw [dotProduct_add]
    simp [dotProduct_comm, smul_eq_mul]
  -- Combine the quadratic and affine expansions into the displayed scalar quadratic.
  rw [polytope_quadratic_objective_apply, polytope_quadratic_objective_apply, hquad, hlin]
  simp only [dotProduct_add, dotProduct_comm]
  ring

/-- Helper for Algorithm 13.5: clipping the exact quadratic ratio to `[0, 1]` minimizes the
scalar quadratic restriction on the unit interval. -/
private lemma clipped_quadratic_ratio_isMinOn_unit_interval
    {α κ : ℝ} (hκ : 0 < κ) (hratio : 0 ≤ -α / κ) :
    IsMinOn (fun t : ℝ ↦ t * α + ((t ^ (2 : ℕ)) / 2) * κ)
      (Set.Icc (0 : ℝ) 1) (min (-α / κ) 1) := by
  rw [isMinOn_iff]
  intro t ht
  let r : ℝ := -α / κ
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hratio
  have hquad_rewrite (u : ℝ) :
      u * α + ((u ^ (2 : ℕ)) / 2) * κ =
        ((κ / 2) * (u - r) ^ (2 : ℕ)) - (κ / 2) * r ^ (2 : ℕ) := by
    -- Complete the square around the unconstrained minimizer `r = -α / κ`.
    dsimp [r]
    field_simp [hκ.ne']
    ring
  by_cases hr_le_one : r ≤ 1
  · -- When `r ∈ [0, 1]`, the clipped point is the true quadratic minimizer.
    rw [min_eq_left hr_le_one, hquad_rewrite, hquad_rewrite]
    have hsq : 0 ≤ (t - r) ^ (2 : ℕ) := sq_nonneg (t - r)
    have _ : 0 ≤ min r 1 := le_min hr_nonneg zero_le_one
    nlinarith [hκ]
  · -- Otherwise the interval minimizer is the right endpoint `1`.
    have hr_one_lt : 1 < r := lt_of_not_ge hr_le_one
    rw [min_eq_right (le_of_lt hr_one_lt), hquad_rewrite, hquad_rewrite]
    have ht_le_r : t ≤ r := le_trans ht.2 (le_of_lt hr_one_lt)
    have h_left : 0 ≤ r - 1 := by
      nlinarith [hr_one_lt]
    have h_right : 0 ≤ r - t := by
      nlinarith [ht_le_r]
    have hmono : r - 1 ≤ r - t := by
      nlinarith [ht.2]
    have habs : |r - 1| ≤ |r - t| := by
      rw [abs_of_nonneg h_left, abs_of_nonneg h_right]
      exact hmono
    have hsq' : (r - 1) ^ (2 : ℕ) ≤ (r - t) ^ (2 : ℕ) := (sq_le_sq).2 habs
    have hsq : (r - 1) ^ (2 : ℕ) ≤ (t - r) ^ (2 : ℕ) := by
      have hEq : (r - t) ^ (2 : ℕ) = (t - r) ^ (2 : ℕ) := by
        ring
      rwa [← hEq]
    nlinarith [hκ]

-- Proof sketch: for a positive-definite quadratic objective, the one-dimensional restriction to
-- the segment from `xᵏ` to `a_{i_k}` is minimized on `[0, 1]` by the clipped ratio
-- `min {λ_k, 1}` from equation `(13.34)` once the Algorithm 13.5 update branch
-- `⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0` ensures that the unclipped ratio is nonnegative.
/-- On the nonterminal branch of Algorithm 13.5, where the chosen direction satisfies
`⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0`, the clipped ratio from equation `(13.34)` belongs to the canonical
Chapter 13 exact-line-search set on the segment from `xᵏ` to the chosen vertex `a_{i_k}`. This
is the `bridge/view` from the explicit quadratic ratio to the owner
`conditional_gradient_exact_line_search_stepsizes`. -/
theorem polytope_quadratic_ratio_clip_mem_conditional_gradient_exact_line_search_stepsizes
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E} {xk : E} {i : Fin l}
    (hderiv :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
    min
        (polytope_quadratic_exact_line_search_ratio Q b xk
          (polytope_quadratic_conditional_gradient_direction a xk i))
        1 ∈
      conditional_gradient_exact_line_search_stepsizes
        (polytope_quadratic_objective Q b).toEReal
        xk (a i) := by
  let d : E := polytope_quadratic_conditional_gradient_direction a xk i
  let α : ℝ := dotProduct d (Q *ᵥ xk + b)
  let κ : ℝ := dotProduct d (Q *ᵥ d)
  let τ : ℝ := min (polytope_quadratic_exact_line_search_ratio Q b xk d) 1
  have hd : d ≠ 0 := by
    -- A zero direction would force the directional derivative to vanish.
    intro hd
    have hd_sub : a i - xk = 0 := by
      simpa [d, polytope_quadratic_conditional_gradient_direction_eq] using hd
    have hd_eq : a i = xk := sub_eq_zero.mp hd_sub
    have hderiv_eq :
        polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i = 0 := by
      rw [polytope_quadratic_conditional_gradient_directional_derivative_eq,
        polytope_quadratic_conditional_gradient_direction_eq, hd_eq]
      simp
    linarith
  have hκ : 0 < κ := by
    simpa [κ, d] using Q.2.dotProduct_mulVec_pos hd
  have hratio_nonneg :
      0 ≤ polytope_quadratic_exact_line_search_ratio Q b xk d := by
    rw [polytope_quadratic_exact_line_search_ratio_eq]
    have hnum :
        0 ≤ -dotProduct d (Q *ᵥ xk + b) := by
      have hderiv_nonneg :
          0 ≤ -polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i := by
        linarith
      simpa [polytope_quadratic_conditional_gradient_directional_derivative_eq, d] using
        hderiv_nonneg
    exact div_nonneg hnum hκ.le
  have hscalar :
      IsMinOn (fun t : ℝ ↦ t * α + ((t ^ (2 : ℕ)) / 2) * κ) (Set.Icc (0 : ℝ) 1) τ := by
    -- The one-dimensional quadratic is minimized by the clipped exact-line-search ratio.
    simpa [τ, α, κ, polytope_quadratic_exact_line_search_ratio_eq] using
      clipped_quadratic_ratio_isMinOn_unit_interval hκ hratio_nonneg
  rw [mem_conditional_gradient_exact_line_search_stepsizes_iff]
  constructor
  · -- The clipped ratio lies in `[0, 1]`.
    constructor
    · exact le_min hratio_nonneg zero_le_one
    · exact min_le_right _ _
  · rw [isMinOn_iff] at hscalar ⊢
    intro s hs
    have hcompare := hscalar s hs
    have hcompare_shifted :
        polytope_quadratic_objective Q b xk + (τ * α + ((τ ^ (2 : ℕ)) / 2) * κ) ≤
          polytope_quadratic_objective Q b xk + (s * α + ((s ^ (2 : ℕ)) / 2) * κ) := by
      linarith
    have hcompare_ereal :
        ((polytope_quadratic_objective Q b xk + (τ * α + ((τ ^ (2 : ℕ)) / 2) * κ) : ℝ) : EReal) ≤
          ((polytope_quadratic_objective Q b xk + (s * α + ((s ^ (2 : ℕ)) / 2) * κ) : ℝ) :
            EReal) := by
      exact_mod_cast hcompare_shifted
    have hτ_eq :
        (polytope_quadratic_objective Q b).toEReal (xk + τ • (a i - xk)) =
          ((polytope_quadratic_objective Q b xk + (τ * α + ((τ ^ (2 : ℕ)) / 2) * κ) : ℝ) :
            EReal) := by
      -- Rewrite the segment objective at `τ` through the normalized quadratic line formula.
      calc
        (polytope_quadratic_objective Q b).toEReal (xk + τ • (a i - xk))
            = ((polytope_quadratic_objective Q b (xk + τ • d) : ℝ) : EReal) := by
                simp [Function.toEReal, d, polytope_quadratic_conditional_gradient_direction_eq]
        _ = ((polytope_quadratic_objective Q b xk +
              τ * dotProduct d (Q *ᵥ xk + b) +
              ((τ ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) : ℝ) : EReal) := by
                rw [polytope_quadratic_objective_add_smul_direction_eq
                  (Q := Q) (b := b) (x := xk) (d := d) (t := τ)]
        _ = ((polytope_quadratic_objective Q b xk + (τ * α + ((τ ^ (2 : ℕ)) / 2) * κ) : ℝ) :
              EReal) := by
                simp [α, κ, add_assoc]
    have hs_eq :
        (polytope_quadratic_objective Q b).toEReal (xk + s • (a i - xk)) =
          ((polytope_quadratic_objective Q b xk + (s * α + ((s ^ (2 : ℕ)) / 2) * κ) : ℝ) :
            EReal) := by
      -- The same normalization applies to every comparison point `s ∈ [0,1]`.
      calc
        (polytope_quadratic_objective Q b).toEReal (xk + s • (a i - xk))
            = ((polytope_quadratic_objective Q b (xk + s • d) : ℝ) : EReal) := by
                simp [Function.toEReal, d, polytope_quadratic_conditional_gradient_direction_eq]
        _ = ((polytope_quadratic_objective Q b xk +
              s * dotProduct d (Q *ᵥ xk + b) +
              ((s ^ (2 : ℕ)) / 2) * dotProduct d (Q *ᵥ d) : ℝ) : EReal) := by
                rw [polytope_quadratic_objective_add_smul_direction_eq
                  (Q := Q) (b := b) (x := xk) (d := d) (t := s)]
        _ = ((polytope_quadratic_objective Q b xk + (s * α + ((s ^ (2 : ℕ)) / 2) * κ) : ℝ) :
              EReal) := by
                simp [α, κ, add_assoc]
    rw [hτ_eq, hs_eq]
    exact hcompare_ereal

private theorem polytope_quadratic_exact_line_search_ratio_nonneg_of_neg_directional_derivative
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk : polytope_quadratic_feasible_set a} {i : Fin l}
    (hderiv :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
    0 ≤
      polytope_quadratic_exact_line_search_ratio Q b xk
        (polytope_quadratic_conditional_gradient_direction a xk i) := by
  let d := polytope_quadratic_conditional_gradient_direction a xk i
  have hd : d ≠ 0 := by
    intro hd
    have hd_sub : a i - (xk : E) = 0 := by
      simpa [d, polytope_quadratic_conditional_gradient_direction_eq] using hd
    have hd_eq : a i = (xk : E) := sub_eq_zero.mp hd_sub
    have hderiv_eq :
        polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i = 0 := by
      rw [polytope_quadratic_conditional_gradient_directional_derivative_eq,
        polytope_quadratic_conditional_gradient_direction_eq, hd_eq]
      simp
    have hnot :
        ¬ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0 := by
      rw [hderiv_eq]
      norm_num
    exact hnot hderiv
  have hden :
      0 < dotProduct d (Q *ᵥ d) := by
    simpa [d] using Q.2.dotProduct_mulVec_pos hd
  have hnum :
      0 ≤ -dotProduct d (Q *ᵥ (xk : E) + b) := by
    have hnum' :
        0 ≤
          -polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i := by
      linarith
    simpa [polytope_quadratic_conditional_gradient_directional_derivative_eq, d] using hnum'
  rw [polytope_quadratic_exact_line_search_ratio_eq]
  exact div_nonneg hnum hden.le

/-- On the nonterminal branch of Algorithm 13.5, the exact-line-search update remains in the
feasible polytope `Ω = conv{a₁, …, a_l}`. -/
theorem polytope_quadratic_conditional_gradient_update_mem_feasible_set
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk : polytope_quadratic_feasible_set a} {i : Fin l}
    (hderiv :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
    polytope_quadratic_conditional_gradient_update Q b a xk i ∈
      polytope_quadratic_feasible_set a := by
  let t :=
    min
      (polytope_quadratic_exact_line_search_ratio Q b xk
        (polytope_quadratic_conditional_gradient_direction a xk i))
      1
  have ht_nonneg : 0 ≤ t := by
    exact le_min
      (polytope_quadratic_exact_line_search_ratio_nonneg_of_neg_directional_derivative hderiv)
      zero_le_one
  have ht_le_one : t ≤ 1 := min_le_right _ _
  have hxk : (xk : E) ∈ polytope_quadratic_feasible_set a := xk.2
  have hai : a i ∈ polytope_quadratic_feasible_set a :=
    polytope_quadratic_vertex_mem_feasible_set a i
  have hcombo :
      (1 - t) • (xk : E) + t • a i ∈ polytope_quadratic_feasible_set a := by
    exact (convex_iff_add_mem.mp (convex_convexHull ℝ (Set.range a)))
      hxk hai (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
  have hupdate_eq :
      polytope_quadratic_conditional_gradient_update Q b a xk i =
        (1 - t) • (xk : E) + t • a i := by
    calc
      polytope_quadratic_conditional_gradient_update Q b a xk i
          = (xk : E) + t • (a i - (xk : E)) := by
              simp [polytope_quadratic_conditional_gradient_update, t,
                polytope_quadratic_conditional_gradient_direction_eq]
      _ = (1 - t) • (xk : E) + t • a i := by
            ext j
            change (xk : E) j + t * (a i j - (xk : E) j) =
              (1 - t) * (xk : E) j + t * a i j
            ring
  exact hupdate_eq ▸ hcombo

/-- The nonterminal branch of Algorithm 13.5 canonically produces the next feasible iterate as a
point of `Ω = conv{a₁, …, a_l}`. -/
def polytope_quadratic_conditional_gradient_next_iterate
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (xk : polytope_quadratic_feasible_set a) (i : Fin l)
    (hderiv :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
    polytope_quadratic_feasible_set a :=
  ⟨polytope_quadratic_conditional_gradient_update Q b a xk i,
    polytope_quadratic_conditional_gradient_update_mem_feasible_set hderiv⟩

/-- Coercing the canonical next feasible iterate from Algorithm 13.5 recovers the underlying
exact-line-search update `xᵏ + t_k dᵏ`. -/
@[simp] theorem polytope_quadratic_conditional_gradient_next_iterate_coe
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk : polytope_quadratic_feasible_set a} {i : Fin l}
    {hderiv :
      polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0} :
    ((polytope_quadratic_conditional_gradient_next_iterate Q b a xk i hderiv :
        polytope_quadratic_feasible_set a) : E) =
      polytope_quadratic_conditional_gradient_update Q b a xk i :=
  rfl

/-- Algorithm 13.5: the admissible next feasible iterates from `xᵏ` are obtained by choosing a
vertex index `i_k` minimizing `⟪a_i, ∇ f_q(xᵏ)⟫`, setting `dᵏ = a_{i_k} - xᵏ`, and then either
stopping when `⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0`, or updating by the exact-line-search step
`xᵏ⁺¹ = xᵏ + t_k dᵏ` with `t_k = min {λ_k, 1}`. -/
inductive polytope_quadratic_conditional_gradient_one_step
    (Q : positiveDefiniteMatrices n) (b : E) (a : Fin l → E)
    (xk : polytope_quadratic_feasible_set a) : polytope_quadratic_feasible_set a → Prop where
  | stop
      (i : Fin l)
      (hi :
        i ∈ unconstrained_problem_solutions
          (polytope_quadratic_vertex_linear_objective Q b a xk))
      (hderiv :
        0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i) :
      polytope_quadratic_conditional_gradient_one_step Q b a xk xk
  | update
      (i : Fin l)
      (hi :
        i ∈ unconstrained_problem_solutions
          (polytope_quadratic_vertex_linear_objective Q b a xk))
      (hderiv :
        polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
      polytope_quadratic_conditional_gradient_one_step Q b a xk
        (polytope_quadratic_conditional_gradient_next_iterate Q b a xk i hderiv)

-- Proof sketch: pattern match on the two constructors of
-- `polytope_quadratic_conditional_gradient_one_step`; the result is exactly the displayed
-- stop-or-update alternative on feasible iterates.
/-- A feasible iterate `xᵏ⁺¹` satisfies
`polytope_quadratic_conditional_gradient_one_step Q b a xᵏ xᵏ⁺¹` exactly when it arises from a
minimizing vertex index `i_k`, with either the stopping certificate
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` and `xᵏ⁺¹ = xᵏ`, or the nonterminal update
`xᵏ⁺¹ = xᵏ + t_k dᵏ`. -/
@[simp] theorem polytope_quadratic_conditional_gradient_one_step_iff
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk xNext : polytope_quadratic_feasible_set a} :
    polytope_quadratic_conditional_gradient_one_step Q b a xk xNext ↔
      ∃ i ∈
          unconstrained_problem_solutions
            (polytope_quadratic_vertex_linear_objective Q b a xk),
        ((0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i ∧
            xNext = xk) ∨
          ∃ hderiv :
            polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0,
            xNext =
              polytope_quadratic_conditional_gradient_next_iterate Q b a xk i hderiv) := by
  constructor
  · rintro (⟨i, hi, hderiv⟩ | ⟨i, hi, hderiv⟩)
    · exact ⟨i, hi, Or.inl ⟨hderiv, rfl⟩⟩
    · exact ⟨i, hi, Or.inr ⟨hderiv, rfl⟩⟩
  · rintro ⟨i, hi, hstop | hupdate⟩
    · rcases hstop with ⟨hderiv, rfl⟩
      exact polytope_quadratic_conditional_gradient_one_step.stop i hi hderiv
    · rcases hupdate with ⟨hderiv, rfl⟩
      exact polytope_quadratic_conditional_gradient_one_step.update i hi hderiv

/-- If the chosen minimizing vertex index satisfies the stopping test
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0`, then the stationary branch `xᵏ⁺¹ = xᵏ` is an admissible Algorithm 13.5
one-step outcome. -/
theorem self_polytope_quadratic_conditional_gradient_one_step_of_nonneg_directional_derivative
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk : polytope_quadratic_feasible_set a} {i : Fin l}
    (hi :
      i ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xk))
    (hderiv : 0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i) :
    polytope_quadratic_conditional_gradient_one_step Q b a xk xk := by
  exact polytope_quadratic_conditional_gradient_one_step.stop i hi hderiv

/-- If the chosen minimizing vertex index satisfies the nonterminal test
`⟪dᵏ, ∇ f_q(xᵏ)⟫ < 0`, then the exact-line-search update `xᵏ + t_k dᵏ` is an admissible
Algorithm 13.5 one-step outcome. -/
theorem polytope_quadratic_conditional_gradient_update_one_step
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E}
    {xk : polytope_quadratic_feasible_set a} {i : Fin l}
    (hi :
      i ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xk))
    (hderiv : polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i < 0) :
    polytope_quadratic_conditional_gradient_one_step Q b a xk
      (polytope_quadratic_conditional_gradient_next_iterate Q b a xk i hderiv) := by
  exact polytope_quadratic_conditional_gradient_one_step.update i hi hderiv

-- Proof sketch: from `hi`, the chosen vertex `a_i` minimizes the linearization over all vertices,
-- hence over the feasible polytope `Ω = conv{a₁, …, a_l}` by convexity of the linear
-- functional. The feasible hypothesis `hxk` upgrades the nonnegative directional derivative at
-- `dᵏ = a_i - xᵏ` to the first-order optimality condition for the convex quadratic objective on
-- `Ω`, which is exactly `IsMinOn` for the constrained problem `(13.32)`.
/-- If the minimizing vertex direction in Algorithm 13.5 satisfies the stopping test
`⟪dᵏ, ∇ f_q(xᵏ)⟫ ≥ 0` at a feasible point `xᵏ ∈ Ω`, then `xᵏ` solves the constrained quadratic
problem `(13.32)`. This is the optimality theorem attached to the stopping branch, not part of
the one-step data itself. -/
theorem polytope_quadratic_isMinOn_of_nonneg_directional_derivative
    {Q : positiveDefiniteMatrices n} {b : E} {a : Fin l → E} {xk : E} {i : Fin l}
    (hxk : xk ∈ polytope_quadratic_feasible_set a)
    (hi :
      i ∈ unconstrained_problem_solutions
        (polytope_quadratic_vertex_linear_objective Q b a xk))
    (hderiv : 0 ≤ polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i) :
    IsMinOn (polytope_quadratic_problem Q b a) Set.univ xk := by
  let g : E := Q *ᵥ xk + b
  have hlinMin :
      IsMinOn (fun y ↦ dotProduct y g) (polytope_quadratic_feasible_set a) (a i) :=
    polytope_quadratic_linearized_isMinOn_feasible_set_of_mem_vertex_argmin hi
  rw [isMinOn_iff] at hlinMin
  have hfirstOrder :
      ∀ {y : E}, y ∈ polytope_quadratic_feasible_set a →
        0 ≤ dotProduct (y - xk) g := by
    intro y hy
    -- Shift the minimizing-vertex inequality by `dotProduct xk g`.
    have hdir_le :
        polytope_quadratic_conditional_gradient_directional_derivative Q b a xk i ≤
          dotProduct (y - xk) g := by
      have hshift :
          dotProduct (a i) g - dotProduct xk g ≤ dotProduct y g - dotProduct xk g :=
        sub_le_sub_right (hlinMin y hy) (dotProduct xk g)
      simpa [g, polytope_quadratic_conditional_gradient_directional_derivative_eq,
        polytope_quadratic_conditional_gradient_direction_eq, dotProduct_sub,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
    exact le_trans hderiv hdir_le
  have hobjMin :
      ∀ {y : E}, y ∈ polytope_quadratic_feasible_set a →
        polytope_quadratic_objective Q b xk ≤ polytope_quadratic_objective Q b y := by
    intro y hy
    have hlinear_nonneg : 0 ≤ dotProduct (y - xk) g := hfirstOrder hy
    have hcurv_nonneg :
        0 ≤ ((1 : ℝ) ^ (2 : ℕ) / 2) * dotProduct (y - xk) (Q *ᵥ (y - xk)) := by
      have hpsd : 0 ≤ dotProduct (y - xk) (Q *ᵥ (y - xk)) :=
        Q.2.posSemidef.dotProduct_mulVec_nonneg (y - xk)
      nlinarith
    have hy_eq : y = xk + (1 : ℝ) • (y - xk) := by
      simp
    -- Evaluate the quadratic objective at `y` along the segment from `xk` in direction `y - xk`.
    rw [hy_eq, polytope_quadratic_objective_add_smul_direction_eq
      (Q := Q) (b := b) (x := xk) (d := y - xk) (t := (1 : ℝ))]
    nlinarith
  -- Split into feasible and infeasible comparison points for the constrained objective.
  rw [isMinOn_iff]
  intro y _
  by_cases hy : y ∈ polytope_quadratic_feasible_set a
  · simpa [polytope_quadratic_problem_of_mem Q b a hxk,
      polytope_quadratic_problem_of_mem Q b a hy] using
        (show ((polytope_quadratic_objective Q b xk : ℝ) : EReal) ≤
            ((polytope_quadratic_objective Q b y : ℝ) : EReal) by
          exact_mod_cast hobjMin hy)
  · rw [polytope_quadratic_problem_of_mem Q b a hxk,
      polytope_quadratic_problem_of_not_mem Q b a hy]
    simp

end
