module

public import ReasLib.Analysis.Calculus.Deriv.GlobalInverse
public import Mathlib.Topology.MetricSpace.Antilipschitz

public section

noncomputable section

open Set
open scoped NNReal

/-!
# Exterior identity and inverse adapters

These generic lemmas isolate the inverse bookkeeping used for cutoff maps.  The
forward map is assumed to be the identity outside a bounded interval; no
particular cutoff construction is exposed here.
-/

/-- A bijection whose forward map is the identity outside an absolute-radius
interval has the same exterior identity for `Function.invFun`. -/
theorem invFun_eq_self_of_bijective_of_eq_self_of_abs_ge
    {f : ℝ → ℝ} {R : ℝ} (hbij : Function.Bijective f)
    (houtside : ∀ x : ℝ, R ≤ |x| → f x = x)
    {y : ℝ} (hy : R ≤ |y|) :
    Function.invFun f y = y := by
  have hinv : f (Function.invFun f y) = y :=
    Function.rightInverse_invFun hbij.2 y
  apply hbij.1
  calc
    f (Function.invFun f y) = y := hinv
    _ = f y := (houtside y hy).symm

/-- Strict monotonicity plus surjectivity supplies the bijectivity needed by the
exterior inverse identity adapter. -/
theorem invFun_eq_self_of_strictMono_surjective_of_eq_self_of_abs_ge
    {f : ℝ → ℝ} {R : ℝ} (hmono : StrictMono f) (hsurj : Function.Surjective f)
    (houtside : ∀ x : ℝ, R ≤ |x| → f x = x)
    {y : ℝ} (hy : R ≤ |y|) :
    Function.invFun f y = y := by
  have hbij : Function.Bijective f := by
    constructor
    · exact hmono.injective
    · exact hsurj
  exact invFun_eq_self_of_bijective_of_eq_self_of_abs_ge hbij houtside hy

/-- An antilipschitz bijection has a reciprocal Lipschitz bound for its selected
right inverse `Function.invFun`. -/
theorem lipschitzWith_invFun_of_antilipschitz
    {α β : Type*} [Nonempty α] [PseudoMetricSpace α] [PseudoMetricSpace β]
    {f : α → β} {K : ℝ≥0} (hf : AntilipschitzWith K f)
    (hsurj : Function.Surjective f) :
    LipschitzWith K (Function.invFun f) := by
  exact hf.to_rightInverse (Function.rightInverse_invFun hsurj)

/-- If a bijective forward map is the identity outside `[-R, R]`, the support of
its inverse displacement is contained in that interval. -/
theorem support_invFun_sub_id_subset_Icc
    {f : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R) (hbij : Function.Bijective f)
    (houtside : ∀ x : ℝ, R ≤ |x| → f x = x) :
    Function.support (fun y : ℝ ↦ Function.invFun f y - y) ⊆ Set.Icc (-R) R := by
  intro y hySupport
  change Function.invFun f y - y ≠ 0 at hySupport
  by_contra hyIcc
  have hyOutside : R ≤ |y| := by
    rcases lt_or_ge y (-R) with hleft | hleft
    · have hyneg : y < 0 := hleft.trans_le (neg_nonpos.mpr hR)
      rw [abs_of_neg hyneg]
      linarith
    · have hright : R < y := by
        by_contra hnot
        have hyRight : y ≤ R := le_of_not_gt hnot
        exact hyIcc ⟨hleft, hyRight⟩
      rw [abs_of_nonneg (le_of_lt (hR.trans_lt hright))]
      exact le_of_lt hright
  have hinv := invFun_eq_self_of_bijective_of_eq_self_of_abs_ge hbij houtside hyOutside
  have hzero : Function.invFun f y - y = 0 := sub_eq_zero.mpr hinv
  exact hySupport hzero

end
