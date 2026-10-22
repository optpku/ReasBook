/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

namespace LinearEstimatingCertificate

/-- The source-facing denominator in Proposition 6.48, written directly as the shifted weight sum
`\sum_{k < t} a_{k+1}`. -/
def linearEstimatingWeightSum (a : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, a (k + 1)

/-- The source-facing estimating function in Proposition 6.48, written as the finite sum of the
weighted affine models at `x₀, …, x_{t-1}`. -/
def linearEstimatingFunction
    (Q : Set E) (a : ℕ → ℝ) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ) (xSeq : ℕ → Q)
    (t : ℕ) : Q → ℝ :=
  fun x ↦
    ∑ k ∈ Finset.range t,
      a (k + 1) *
        (f (xSeq k) + inner ℝ (gradF (xSeq k)) ((x : E) - (xSeq k : E)) + ψ x)

/-- The source-facing lower certificate in Proposition 6.48, obtained by normalizing the infimum
of the finite-sum estimating function by the shifted weight sum. -/
def linearEstimatingAccuracyCertificate
    (Q : Set E) (a : ℕ → ℝ) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ) (xSeq : ℕ → Q)
    (t : ℕ) : ℝ :=
  sInf (Set.range (linearEstimatingFunction Q a f gradF ψ xSeq t)) /
    linearEstimatingWeightSum a t

end LinearEstimatingCertificate

open LinearEstimatingCertificate

/- Proposition 6.48 lies in the chapter's averaged primal-dual gap / Fenchel-conjugacy domain.

Mandatory domain-style sampling before refinement:
- `Finset.centerMass`, the canonical owner for the averaged dual iterate `ν_t`;
- `linearEstimatingWeightSum`, `linearEstimatingWeightSum_def`, and
  `linearEstimatingAccuracyCertificate` in `Chap06/Definition_6_62`, the chapter owners for the
  shifted normalization factor and the source-facing certificate `\hat ℓ_t`;
- `fenchelConjugate` and `fenchelConjugate_apply` in `Chap06/Definition_6_1`, the chapter owner
  for `EReal`-valued Fenchel conjugates on the continuous dual;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing inner-product-space bridge
  built from `fenchelConjugate` via `innerₗ`;
- `StructuredObjectiveModel.adjointObjective_le_objective` in `Chap06/Proposition_6_4`, the
  chapter owner weak-duality pattern for primal/dual value functions.

Best owner abstraction:
- source-facing: Proposition 6.48's averaged-dual point
  `ν_t = (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (x_k))`, the source-facing
  certificate `\hat ℓ_t = linearEstimatingAccuracyCertificate ... t`, and the resulting gap
  bound;
- core/canonical: `Finset.centerMass`, `linearEstimatingAccuracyCertificate`,
  `linearEstimatingWeightSum`, `fenchelConjugate`, and `innerₗ`;
- bridge/view: the theorem-local dual value
  `ν ↦ inf_x (\bar f(x) + ⟪ν, u(x)⟫) - Φ*(ν)` written directly through `fenchelConjugate`.

Primitive data:
- the feasible set `Q`, certificate data `f`, `gradF`, `ψ`, `xSeq`, and `a`;
- the primal/dual data `barF`, `phi`, and `u`;
- the index `t` and error budget `Cv_t`.

Derived API:
- the source-facing theorem below.

Source/core/bridge triage:
- source-facing: `averaged_duality_gap_bound_of_lower_certificate`;
- core/canonical: `linearEstimatingAccuracyCertificate` and `fenchelConjugate`;
- bridge/view: evaluation at `innerₗ F νt`.

The previous version replaced the source-facing certificate `\hat ℓ_t` by a free scalar and
introduced a second public dual owner just to package the Fenchel formula. This refinement keeps
the actual Chapter 6 certificate on the theorem surface, deletes the duplicate owner, and uses
only theorem-local `let` bindings for the averaged dual point and the corresponding Fenchel dual
value. -/

-- Proof sketch: weak duality for the primal value `\bar f(x_t) + Φ(u(x_t))` and the dual
-- function `\bar g(ν) = inf_x (\bar f(x) + ⟪ν, u(x)⟫) - Φ*(ν)` gives
-- `0 ≤ \bar f(x_t) + Φ(u(x_t)) - \bar g(ν_t)`. The assumed lower bound
-- `\hat ℓ_t ≤ \bar g(ν_t)` then yields
-- `\bar f(x_t) + Φ(u(x_t)) - \bar g(ν_t) ≤ \bar f(x_t) + Φ(u(x_t)) - \hat ℓ_t`, and the
-- certificate
-- hypothesis bounds this by
-- `C_{v,t} / ∑_{k < t} a_{k+1}`.
/-- Helper for Proposition 6.48: evaluating the Fenchel conjugate at a test point `y` gives the
one-point inequality `⟪ν, y⟫ - Φ(y) ≤ Φ*(ν)`. -/
lemma pairing_sub_value_le_fenchelConjugate
    (phi : F → EReal) (ν y : F) :
    (((inner ℝ ν y : ℝ) : EReal) - phi y) ≤ fenchelConjugate phi (innerₗ F ν) := by
  -- Evaluate the supremum defining `Φ*` at the sample point `y`.
  rw [fenchelConjugate_apply]
  exact le_iSup (fun z : F ↦ (((innerₗ F ν) z : ℝ) : EReal) - phi z) y

section

variable {E' : Type u} {F' : Type v}
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

/-- Helper for Proposition 6.48: the Fenchel dual value at `ν` is bounded above by the primal
value at any test point `x`. -/
lemma dualObj_le_primal_value_at
    (barF : E' → EReal) (phi : F' → EReal) (u : E' → F') (ν : F') (x : E') :
    sInf (Set.range fun x' : E' ↦ barF x' + ((inner ℝ ν (u x') : ℝ) : EReal)) -
        fenchelConjugate phi (innerₗ F' ν) ≤
      barF x + phi (u x) := by
  let pairing : EReal := ((inner ℝ ν (u x) : ℝ) : EReal)
  -- Bound the infimum by evaluating the primal part at the current test point `x`.
  have hsInf :
      sInf (Set.range fun x' : E' ↦ barF x' + ((inner ℝ ν (u x') : ℝ) : EReal)) ≤
        barF x + pairing := by
    apply sInf_le
    refine ⟨x, ?_⟩
    dsimp [pairing]
  -- Evaluate the conjugate at the matched point `u x`.
  have hsample :
      pairing - phi (u x) ≤ fenchelConjugate phi (innerₗ F' ν) := by
    simpa [pairing] using pairing_sub_value_le_fenchelConjugate phi ν (u x)
  -- Subtract the same conjugate term from the infimum estimate.
  have hsInf_sub :
      sInf (Set.range fun x' : E' ↦ barF x' + ((inner ℝ ν (u x') : ℝ) : EReal)) -
          fenchelConjugate phi (innerₗ F' ν) ≤
        (barF x + pairing) - fenchelConjugate phi (innerₗ F' ν) := by
    exact EReal.sub_le_sub hsInf le_rfl
  -- Replace the conjugate by the sampled support value.
  have hreplace :
      (barF x + pairing) - fenchelConjugate phi (innerₗ F' ν) ≤
        (barF x + pairing) - (pairing - phi (u x)) := by
    exact EReal.sub_le_sub le_rfl hsample
  -- Cancel the finite pairing term to recover the primal value.
  have hcancel :
      (barF x + pairing) - (pairing - phi (u x)) = barF x + phi (u x) := by
    dsimp [pairing]
    rw [sub_eq_add_neg]
    rw [EReal.neg_sub (Or.inl (by simp)) (Or.inl (by simp))]
    have hpairing_cancel :
        (((inner ℝ ν (u x) : ℝ) : EReal) + -(((inner ℝ ν (u x) : ℝ) : EReal))) = 0 := by
      simpa [sub_eq_add_neg, add_assoc] using
        (EReal.add_sub_cancel_right (a := (0 : EReal)) (b := inner ℝ ν (u x)))
    rw [show
      barF x + ↑(inner ℝ ν (u x)) + (-↑(inner ℝ ν (u x)) + phi (u x)) =
        barF x + phi (u x) + (↑(inner ℝ ν (u x)) + -↑(inner ℝ ν (u x))) by
      ac_rfl]
    rw [hpairing_cancel, add_zero]
  exact hsInf_sub.trans <| hreplace.trans <| le_of_eq hcancel

end

/-- Helper for Proposition 6.48: a lower bound on the dual value turns into an upper bound on the
corresponding primal-dual gap. -/
lemma gap_upper_bound_of_dual_lower_bound
    {primal ell dual : EReal} (hell : ell ≤ dual) :
    primal - dual ≤ primal - ell := by
  -- Subtraction is antitone in its second argument.
  exact EReal.sub_le_sub le_rfl hell

/-- Proposition 6.48: let
`ν_t = (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (x_k))`.
If the Chapter 6 certificate `\hat ℓ_t = linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t`
is a lower bound for the dual value
`\bar g(ν_t) = inf_x (\bar f(x) + ⟪ν_t, u(x)⟫) - Φ*(ν_t)` and if the primal objective satisfies
`\bar f(x_t) + Φ(u(x_t)) - \hat ℓ_t ≤ C_{v,t} / linearEstimatingWeightSum a t`, then the
primal-dual gap at this averaged dual iterate lies in the canonical interval
`[0, C_{v,t} / linearEstimatingWeightSum a t]`. -/
theorem averaged_duality_gap_bound_of_lower_certificate
    (Q : Set E) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ)
    (barF : E → EReal) (phi : F → EReal) (u : E → F)
    (xSeq : ℕ → Q) (a : ℕ → ℝ) (t : ℕ) (Cv_t : ℝ)
    (hhatℓt :
      let νt := (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (xSeq k : E))
      let dualObj : F → EReal := fun ν ↦
        sInf (Set.range fun x : E ↦ barF x + ((inner ℝ ν (u x) : ℝ) : EReal)) -
          fenchelConjugate phi (innerₗ F ν)
      (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤ dualObj νt)
    (hcertificate :
      barF (xSeq t : E) + phi (u (xSeq t : E)) -
          (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤
        ((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal)) :
    let νt := (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (xSeq k : E))
    let dualObj : F → EReal := fun ν ↦
      sInf (Set.range fun x : E ↦ barF x + ((inner ℝ ν (u x) : ℝ) : EReal)) -
        fenchelConjugate phi (innerₗ F ν)
    barF (xSeq t : E) + phi (u (xSeq t : E)) - dualObj νt ∈
      Set.Icc 0 (((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal)) := by
  let νt := (Finset.range t).centerMass (fun k ↦ a (k + 1)) (fun k ↦ u (xSeq k : E))
  let dualObj : F → EReal := fun ν ↦
    sInf (Set.range fun x : E ↦ barF x + ((inner ℝ ν (u x) : ℝ) : EReal)) -
      fenchelConjugate phi (innerₗ F ν)
  let primal := barF (xSeq t : E) + phi (u (xSeq t : E))
  have hhatℓt' :
      (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤ dualObj νt := by
    simpa [νt, dualObj] using hhatℓt
  have hcertificate' :
      primal - (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤
        ((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal) := by
    simpa [primal] using hcertificate
  -- Weak duality at the averaged dual point is the source-proof lower bound on the gap.
  have hweak : dualObj νt ≤ primal := by
    dsimp [dualObj, primal, νt]
    exact dualObj_le_primal_value_at barF phi u _ _
  have hprimal_ne_bot : primal ≠ ⊥ := by
    intro hprimal_bot
    have hcert_bot :
        (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤ ⊥ :=
      by simpa [hprimal_bot] using hhatℓt'.trans hweak
    simp at hcert_bot
  have hdual_ne_top : dualObj νt ≠ ⊤ := by
    intro hdual_top
    have hprimal_top : primal = ⊤ := by
      simpa [hdual_top] using hweak
    have : ¬
        primal - (linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t : EReal) ≤
          ((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal) := by
      simp [hprimal_top]
    exact this hcertificate'
  have hlow : 0 ≤ primal - dualObj νt := by
    -- The certificate rules out the pathological `⊥`/`⊤` subtraction cases.
    rw [EReal.sub_nonneg (Or.inr hdual_ne_top) (Or.inl hprimal_ne_bot)]
    exact hweak
  have hup :
      primal - dualObj νt ≤ ((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal) := by
    -- Compare the exact gap to the certificate gap, then use the certificate bound.
    exact (gap_upper_bound_of_dual_lower_bound hhatℓt').trans hcertificate'
  have hgap :
      primal - dualObj νt ∈ Set.Icc 0 (((Cv_t / linearEstimatingWeightSum a t : ℝ) : EReal)) :=
    Set.mem_Icc.mpr ⟨hlow, hup⟩
  simpa [νt, dualObj, primal] using hgap
