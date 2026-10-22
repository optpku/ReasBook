/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Proposition_10_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Proposition 10.58 is `source-facing` in the chapter's smoothing API.

Domain sampling:
- `fista`, `fista_x`, `fista_t`, and `fista_y` from Algorithm 10.6 already own the exact
  initialization `x^0 = y^0 = x0`, `t_0 = 1` and the exact FISTA recursion;
- `fista_momentum_update` from Algorithm 10.13 is the canonical Chapter 10 owner of the scalar
  momentum formula;
- Proposition 10.56 already exports the regularizer-side assumptions needed to specialize the
  generic FISTA owners.

Source/core/bridge triage:
- `source-facing`: the S-FISTA specialization `s_fista` and its projected sequences
  `s_fista_x`, `s_fista_t`, and `s_fista_y`;
- `core/canonical`: the Chapter 10 owners `fista`, `fista_x`, `fista_t`, and `fista_y`;
- `bridge/view`: `IsSFISTAProblem.sFistaX`, which reuses the proposition-level problem data.

The only new concrete datum in this item is the constant curvature parameter
`L̃ = L_f + α / μ`; the algorithm itself should therefore remain a thin specialization of the
existing FISTA recursion rather than a bespoke auxiliary state owner. -/

/-- The effective curvature parameter `L_f + α / μ` used by S-FISTA is positive. -/
theorem s_fista_curvature_bound_pos (Lf : NNReal) (α μ : PosReal) :
    0 < (Lf : ℝ) + (α : ℝ) / (μ : ℝ) := by
  -- Split the bound into the nonnegative Lipschitz term and the positive smoothing term.
  have hLf : 0 ≤ (Lf : ℝ) := NNReal.coe_nonneg Lf
  have hdiv : 0 < (α : ℝ) / (μ : ℝ) := by
    exact div_pos (PosReal.coe_pos α) (PosReal.coe_pos μ)
  exact add_pos_of_nonneg_of_pos hLf hdiv

/-- The S-FISTA curvature parameter `L̃ = L_f + α / μ`. -/
def s_fista_curvature_bound (Lf : NNReal) (α μ : PosReal) : PosReal :=
  ⟨(Lf : ℝ) + (α : ℝ) / (μ : ℝ), s_fista_curvature_bound_pos Lf α μ⟩

/-- Coercing the S-FISTA curvature parameter to `ℝ` recovers the formula `L_f + α / μ`. -/
@[simp] theorem s_fista_curvature_bound_coe (Lf : NNReal) (α μ : PosReal) :
    ((s_fista_curvature_bound Lf α μ : PosReal) : ℝ) =
      (Lf : ℝ) + (α : ℝ) / (μ : ℝ) := by
  -- The coercion reads off the real value stored in the `PosReal` constructor.
  rfl

/-- S-FISTA is the Chapter 10 `fista` recursion specialized to the smoothed
smooth term `fun x ↦ f x + hμ x` and the constant curvature schedule
`fun _ ↦ s_fista_curvature_bound Lf α μ`, so it starts from `x^0 = y^0 = x0`, `t_0 = 1`, and
then follows the displayed prox, momentum, and extrapolation updates. -/
abbrev s_fista
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → FISTAState E :=
  fista (fun x ↦ f x + hμ x) g x0 (fun _ ↦ s_fista_curvature_bound Lf α μ)

/-- The S-FISTA primal iterates `x^k`. -/
abbrev s_fista_x
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → E :=
  fista_x (fun x ↦ f x + hμ x) g x0 (fun _ ↦ s_fista_curvature_bound Lf α μ)

/-- The S-FISTA momentum parameters `t_k`. -/
abbrev s_fista_t
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → ℝ :=
  fista_t (fun x ↦ f x + hμ x) g x0 (fun _ ↦ s_fista_curvature_bound Lf α μ)

/-- The S-FISTA extrapolated points `y^k`. -/
abbrev s_fista_y
    (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (Lf : NNReal) (α μ : PosReal) (x0 : E) :
    ℕ → E :=
  fista_y (fun x ↦ f x + hμ x) g x0 (fun _ ↦ s_fista_curvature_bound Lf α μ)

namespace IsSFISTAProblem

/-- Bridge/view: an `IsSFISTAProblem` supplies the regularizer side conditions needed to form the
S-FISTA primal iterates for any smoothing `h_μ`. -/
abbrev sFistaX
    {f h : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
    {Lf : NNReal} {α β : PosReal}
    (problem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hμ : E → ℝ) (μ : PosReal) (x0 : E) :
    ℕ → E :=
  @s_fista_x E _ _ _ f hμ g
    (instIsProperExtendedRealFunctionRightOfIsSFISTAProblem problem)
    (instFactLowerSemicontinuousRightOfIsSFISTAProblem problem)
    (instFactIsConvexFunctionRightOfIsSFISTAProblem problem)
    Lf α μ x0

end IsSFISTAProblem

section

variable (f hμ : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
variable (Lf : NNReal) (α μ : PosReal) (x0 : E)

/-- The S-FISTA primal sequence starts at the input point `x^0`. -/
@[simp] theorem s_fista_x_zero
    :
    s_fista_x f hμ g Lf α μ x0 0 = x0 := by
  -- This is the generic FISTA base case specialized to the smoothed objective and constant step.
  simp [s_fista_x]

/-- The initial S-FISTA momentum parameter is `t_0 = 1`. -/
@[simp] theorem s_fista_t_zero
    :
    s_fista_t f hμ g Lf α μ x0 0 = 1 := by
  -- The specialized momentum sequence inherits the generic FISTA initialization unchanged.
  simp [s_fista_t]

/-- The S-FISTA extrapolated sequence starts from `y^0 = x^0`. -/
@[simp] theorem s_fista_y_zero
    :
    s_fista_y f hμ g Lf α μ x0 0 = x0 := by
  -- The specialized extrapolated sequence inherits the generic FISTA initialization unchanged.
  simp [s_fista_y]

/-- At each iteration `k`, the next S-FISTA primal iterate is the proximal-gradient point for the
smoothed objective evaluated at `y^k`. -/
theorem s_fista_x_succ
    (k : ℕ) :
    s_fista_x f hμ g Lf α μ x0 (k + 1) =
      T[s_fista_curvature_bound Lf α μ; (fun y ↦ f y + hμ y), g]
        (s_fista_y f hμ g Lf α μ x0 k) := by
  -- This is the generic successor iterate formula at the smoothed objective and constant step.
  simpa [s_fista_x, s_fista_y] using
    (fista_x_succ (f := fun y ↦ f y + hμ y) (g := g) (x0 := x0)
      (L := fun _ ↦ s_fista_curvature_bound Lf α μ) k)

/-- At each iteration `k`, the S-FISTA momentum parameter satisfies the update
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`. -/
theorem s_fista_t_succ
    (k : ℕ) :
    s_fista_t f hμ g Lf α μ x0 (k + 1) =
      (1 + Real.sqrt (1 + 4 * (s_fista_t f hμ g Lf α μ x0 k) ^ (2 : ℕ))) / 2 := by
  -- Route through the owner theorem and then normalize the momentum update formula.
  simpa [s_fista_t, fista_momentum_update_eq] using
    (fista_t_succ (f := fun y ↦ f y + hμ y) (g := g) (x0 := x0)
      (L := fun _ ↦ s_fista_curvature_bound Lf α μ) k)

/-- Proposition 10.58: at each iteration `k`, the S-FISTA extrapolated point satisfies the update
`y^(k+1) = x^(k+1) + ((t_k - 1) / t_(k+1)) (x^(k+1) - x^k)`. -/
theorem s_fista_y_succ
    (k : ℕ) :
    s_fista_y f hμ g Lf α μ x0 (k + 1) =
      s_fista_x f hμ g Lf α μ x0 (k + 1) +
        ((s_fista_t f hμ g Lf α μ x0 k - 1) /
            s_fista_t f hμ g Lf α μ x0 (k + 1)) •
          (s_fista_x f hμ g Lf α μ x0 (k + 1) - s_fista_x f hμ g Lf α μ x0 k) := by
  -- The extrapolation coefficient is exactly the generic FISTA coefficient after specialization.
  simpa [s_fista_y, s_fista_x, s_fista_t] using
    (fista_y_succ (f := fun y ↦ f y + hμ y) (g := g) (x0 := x0)
      (L := fun _ ↦ s_fista_curvature_bound Lf α μ) k)

end

end
