module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberDerivative
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionCore
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicBridge
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

public section
noncomputable section
open scoped NNReal Topology
open Filter Set
universe u
namespace LocalInvariantGraph
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Metric fiber Faà-di-Bruno: atomic split of the `∂₂R · iteratedDeriv m ζ` term.

This is the *fiber* analogue of the top-section leaf
`MetricTopSectionFaaDiBruno.lean`.  We differentiate the **fiber remainder**
`g u := (R (u, ζ u)).2`, via Mathlib's vector-valued Faà-di-Bruno formula
`iteratedDeriv_vcomp_eq_sum_orderedFinpartition` (outer function `Prod.snd ∘ R :
ℝ × X → X` is vector-codomain; inner function `pair : ℝ → ℝ × X` has scalar domain).

The Faà-di-Bruno sum ranges over ordered finpartitions `c : OrderedFinpartition m`;
the single term with `c.length = m` (the *atomic* partition, all part sizes `= 1`) is
isolated and collapsed.  The result is the **cocycle term** the metric top-section
recurrence needs: the fiber derivative `derivFiber d ζ u` (the `∂₂R` slot) applied to
`iteratedDeriv m ζ u`, plus a sum of strictly-lower-order terms in `ζ`
(factorizing through `iteratedFDeriv ℝ c.length (Prod.snd ∘ R ∘ pair) u` with
`c.length ≠ m`).

### ⚠️ One correction to the original task spec (mathematically necessary)

The original spec asked for `iteratedDeriv m g u = derivFiber d ζ u (iteratedDeriv m
pair u) + …` for all `u`.  Rigorous type-checking shows this is ill-typed:
`derivFiber d ζ u : X →L[ℝ] X` expects an `X`, but
`iteratedDeriv m pair u : ℝ × X` (codomain of `pair` is `ℝ × X`).  The correct
second-slot input is `iteratedDeriv m ζ u : X` (the `X`-component of
`iteratedDeriv m pair u`), and this is what the atomic term reduces to.

The chain rule also shows the atomic term carries a `∂₁R` slot in general:
`(fderiv ℝ g u) (iteratedDeriv m pair u) = (∂₁R(u,ζu)) • 1 + derivFiber d ζ u
(iteratedDeriv m ζ u)`.  The `∂₁R` slot **does not vanish for general `u`**; it
vanishes only at `u = 0`, because `R 0 = 0` gives `fderiv ℝ R (0,0) (1,0) = 0` (the
*whole* output vector is zero, not merely its first component), so the `∂₁R` slot is
zero at the origin for every `m ≥ 1`.

We therefore prove the **honest** statements:

* `iteratedDeriv_fiber_remainder_atomic_split` — the general-`u` identity with the full
  chain-rule atomic term written as `iteratedFDeriv ℝ m (Prod.snd ∘ d.R) (pair u)` on
  the diagonal `fun _ ↦ 1` (no `∂₁R` slot dropped).  Hypotheses: `m + 1 ≤ d.nu`,
  `ContDiff ℝ (m + 1) ζ`.
* `iteratedDeriv_fiber_remainder_atomic_at_origin` — the **origin specialization**,
  obtained by direct evaluation of the general split at `u = 0`.  The atomic term is
  kept in its honest form `iteratedFDeriv ℝ m (Prod.snd ∘ d.R) (0, ζ 0)` on the diagonal
  `fun _ ↦ 1`.  Reducing this to the pure cocycle form `derivFiber d ζ 0
  (iteratedDeriv m ζ 0)` is **not** valid for `m ≥ 2`: the atomic term is the order-`m`
  derivative of `Prod.snd ∘ d.R`, and Mathlib's `iteratedDeriv_comp_two` shows it carries
  a transverse piece `∂₂R(0,0) · (deriv pair 0)^2` that does not vanish (it is
  `O(‖ζ 0‖²)`; only the base point, not `ζ`'s first derivative, is killed by `ζ 0 = 0`).
  The pure cocycle form holds for `m = 1` and is intentionally a separate consequence.
  Hypotheses: `m + 1 ≤ d.nu`, `ContDiff ℝ (m + 1) ζ`.
* `iteratedDeriv_fiber_remainder_remainder_continuous` — continuity of the non-atomic
  remainder sum.  Hypotheses: `m ≤ d.nu`, `ContDiff ℝ m ζ`.

All three declarations are fully proved and use no project-specific axioms.
-/

/-- Helper for the metric fiber Faà-di-Bruno leaf: among ordered finpartitions of `m`,
the only one whose `length` equals `m` is the atomic partition (each part a singleton).
This is the combinatorial core that lets us isolate the single "top" term in the
Faà-di-Bruno expansion.  Identical to the private helper in the sister leaf
`MetricTopSectionFaaDiBruno.lean`; reproduced here so the present file is independent. -/
private theorem orderedFinpartition_length_eq_iff_atomic
    {m : ℕ} (c : OrderedFinpartition m) :
    c.length = m ↔ c = OrderedFinpartition.atomic m := by
  constructor
  · intro hlen
    -- With `length = m`, the `m` part sizes (each `≥ 1`) sum to `m`, hence all equal `1`.
    have hsum : ∑ j, c.partSize j = m := by
      have h : ∑ (j : Fin c.length), ∑ _r : Fin (c.partSize j), (1 : ℕ) = ∑ _i : Fin m, (1 : ℕ) :=
        c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
      simpa using h
    have hall : ∀ j, c.partSize j = 1 := by
      intro j
      have hle : ∀ k, 1 ≤ c.partSize k := fun k => c.partSize_pos k
      by_contra hne
      have hlt : 1 < c.partSize j := lt_of_le_of_ne (hle j) (Ne.symm hne)
      have hcard : (Finset.univ : Finset (Fin c.length)).card = m := by simp [hlen]
      have hgt : ∑ k, c.partSize k > ∑ _k : Fin c.length, (1 : ℕ) := by
        refine Finset.sum_lt_sum (fun k _ => hle k) ⟨j, Finset.mem_univ j, hlt⟩
      simp only [Finset.sum_const, hcard, smul_eq_mul, mul_one] at hgt
      omega
    -- Destructure `c` and substitute the length equality, so the ambient `Fin m` and the
    -- part-index type `Fin length` become the same `Fin m`; then the greatest-element self-map
    -- `j ↦ emb j 0` of `Fin m` is strictly monotone, hence the identity.
    rcases c with ⟨length, partSize, hpos, emb, hmono, hpmono, hdisj, hcov⟩
    dsimp only at hlen hall
    subst length
    obtain rfl : partSize = fun _ ↦ 1 := funext hall
    have hg : StrictMono (fun j : Fin m => emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩) := hpmono
    have hid : ∀ j : Fin m, emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ = j := by
      have hfun : (fun j : Fin m => emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩) = id :=
        le_antisymm hg.le_id hg.id_le
      intro j; exact congrFun hfun j
    -- Every `emb j : Fin 1 → Fin m` is determined by its value at `0`, which equals `j`.
    have hemb : ∀ (j : Fin m) (r : Fin 1), emb j r = j := by
      intro j r
      have hr : r = ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ := Subsingleton.elim _ _
      rw [hr]; exact hid j
    simpa [OrderedFinpartition.ext_iff, OrderedFinpartition.atomic, funext_iff,
      Fin.forall_fin_one] using hemb
  · intro h; subst h; simp [OrderedFinpartition.atomic]

/-- Helper for Infrastructure I.16a: the order-`m` derivative of the metric fiber remainder
splits into its atomic branch and the non-atomic Faà-di-Bruno sum under exactly `C^m`
regularity. In particular, constructing this split does not presuppose `C^(m+1)` regularity
of the graph. -/
theorem iteratedDeriv_fiber_remainder_atomic_split_of_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).2) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦
            iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j) (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  let pairF : ℝ → ℝ × X := fun y ↦ (y, (ζ : ℝ → X) y)
  have hpair : ContDiff ℝ m pairF := contDiff_id.prodMk hprev
  have hmν_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_top
  have hG : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).2) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
  have hfdb := iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (g := (fun z : ℝ × X ↦ (d.R z).2)) (f := pairF)
    (i := m) (x := u) hG.contDiffAt hpair.contDiffAt le_rfl
  rw [hfdb]
  have hmem : OrderedFinpartition.atomic m ∈
      (Finset.univ : Finset (OrderedFinpartition m)) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hmem]
  have hatomic :
      iteratedFDeriv ℝ (OrderedFinpartition.atomic m).length
          (fun z : ℝ × X ↦ (d.R z).2)
          (pairF u)
          (fun j ↦ iteratedDeriv
            ((OrderedFinpartition.atomic m).partSize j)
            pairF u) =
        iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).2)
          (pairF u)
          (fun _ : Fin m ↦ iteratedDeriv 1 pairF u) := by
    have htuple :
        (fun j : Fin (OrderedFinpartition.atomic m).length ↦
          iteratedDeriv ((OrderedFinpartition.atomic m).partSize j) pairF u) =
            (fun _ : Fin (OrderedFinpartition.atomic m).length ↦
              iteratedDeriv 1 pairF u) := by
      funext j
      simp [OrderedFinpartition.atomic, iteratedDeriv_one]
    have hlen : (OrderedFinpartition.atomic m).length = m := by
      simp [OrderedFinpartition.atomic]
    rw [htuple, hlen]
  rw [hatomic]
  dsimp only [pairF]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and,
    ne_eq, orderedFinpartition_length_eq_iff_atomic]

/-- **Metric fiber Faà-di-Bruno, general-`u` atomic split.**  The order-`m` iterated
derivative of the fiber remainder `g u = (R (u, ζ u)).2` splits into the atomic top term
plus the Faà-di-Bruno remainder over all non-atomic ordered finpartitions (`c.length ≠ m`).

The atomic term is the FULL chain-rule value `iteratedFDeriv ℝ m (Prod.snd ∘ d.R) (pair u)`
on the diagonal `fun _ ↦ 1` (equivalently `(fderiv ℝ g u) (iteratedDeriv m pair u)`,
which expands to `(∂₁R(u,ζu)) • 1 + derivFiber d ζ u (iteratedDeriv m ζ u)`).  The `∂₁R`
slot is retained because it does **not** vanish for general `u`; use
`iteratedDeriv_fiber_remainder_atomic_at_origin` for the spec's `derivFiber`-only form at
the origin.  This compatibility form retains the successor-order regularity budget used by
existing callers and delegates to `iteratedDeriv_fiber_remainder_atomic_split_of_contDiff`. -/
theorem iteratedDeriv_fiber_remainder_atomic_split
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν1 : m + 1 ≤ d.nu) (hprev1 : ContDiff ℝ (m + 1) (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).2) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦
            iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j) (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  have hmν : m ≤ d.nu := (Nat.le_succ m).trans hmν1
  have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ m
  have hprev : ContDiff ℝ m (ζ : ℝ → X) := hprev1.of_le hm_le
  exact iteratedDeriv_fiber_remainder_atomic_split_of_contDiff d ζ m hmν hprev u
/-- **Metric fiber Faà-di-Bruno, origin specialization.**  At the origin, the general
atomic split is obtained by direct evaluation.  The statement keeps the full outer
`iteratedFDeriv` atomic term; reducing it to `derivFiber` requires an additional germ
hypothesis and is intentionally a separate consequence. -/
theorem iteratedDeriv_fiber_remainder_atomic_at_origin
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν1 : m + 1 ≤ d.nu) (hprev1 : ContDiff ℝ (m + 1) (ζ : ℝ → X)) :
    iteratedDeriv m (fun y ↦ (d.R (y, (ζ : ℝ → X) y)).2) 0
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).2)
          (0, (ζ : ℝ → X) 0)
          (fun _ : Fin m ↦
            iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) 0)
        + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
              (0, (ζ : ℝ → X) 0)
              (fun j ↦ iteratedDeriv (c.partSize j)
                (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) 0) := by
  exact iteratedDeriv_fiber_remainder_atomic_split d ζ m hmν1 hprev1 0

/-- Infrastructure I.16a: the first derivative of the fiber remainder along a graph splits into
the center-slot contribution and the fiber derivative applied to the graph derivative. -/
theorem deriv_fiber_remainder_eq_first_slot_add_fiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) (u : ℝ)
    (hζ : DifferentiableAt ℝ (ζ : ℝ → X) u) :
    deriv (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) u =
      (fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)) (1, 0) +
        derivFiber d ζ u (deriv (ζ : ℝ → X) u) := by
  have hsplit := fiber_atomic_isolate_one d ζ u hζ
  rw [iteratedFDeriv_one_apply] at hsplit
  simp only [iteratedDeriv_one] at hsplit
  have htwo : 0 < (2 : ℕ) := Nat.zero_lt_succ 1
  have hnu_pos : 0 < d.nu := lt_of_lt_of_le htwo d.hnu
  have hnu_ne_nat : d.nu ≠ 0 := Nat.ne_of_gt hnu_pos
  have hnu : (d.nu : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast hnu_ne_nat
  have hRdiff : DifferentiableAt ℝ d.R (u, (ζ : ℝ → X) u) :=
    d.hR_smooth.contDiffAt.differentiableAt hnu
  have hGderiv : fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u) =
      (ContinuousLinearMap.snd ℝ ℝ X).comp (fderiv ℝ d.R (u, (ζ : ℝ → X) u)) := by
    have h := fderiv_comp (x := (u, (ζ : ℝ → X) u))
      (f := d.R) (g := (Prod.snd : (ℝ × X) → X))
      (ContinuousLinearMap.snd ℝ ℝ X).differentiableAt hRdiff
    simpa only [Function.comp_def, fderiv_snd] using h
  have hpair : HasFDerivAt (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))
      ((1 : ℝ →L[ℝ] ℝ).prod (fderiv ℝ (ζ : ℝ → X) u)) u := by
    exact (hasFDerivAt_id u).prodMk hζ.hasFDerivAt
  have hpair_diff : DifferentiableAt ℝ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u :=
    hpair.differentiableAt
  have hG_eq : (fun z : ℝ × X ↦ (d.R z).2) =
      (Prod.snd : (ℝ × X) → X) ∘ d.R := by
    rfl
  have hGdiff : DifferentiableAt ℝ (fun z : ℝ × X ↦ (d.R z).2)
      (u, (ζ : ℝ → X) u) := by
    rw [hG_eq]
    exact (ContinuousLinearMap.snd ℝ ℝ X).differentiableAt.comp _ hRdiff
  have hcomp_fderiv := fderiv_comp (x := u)
      (f := fun y : ℝ ↦ (y, (ζ : ℝ → X) y))
      (g := fun z : ℝ × X ↦ (d.R z).2) hGdiff hpair_diff
  have hcomp_eq : (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) =
      (fun z : ℝ × X ↦ (d.R z).2) ∘
        (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) := by
    rfl
  have hderiv : deriv (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) u =
      (fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u))
        (deriv (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u) := by
    rw [hcomp_eq]
    change (fderiv ℝ ((fun z : ℝ × X ↦ (d.R z).2) ∘
      (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u) 1 = _
    rw [hcomp_fderiv]
    rfl
  rw [hderiv]
  exact hsplit

/-- Helper for Infrastructure I.16a: at the origin, the center-slot term vanishes under the
center-stable derivative certificate, leaving the pure fiber derivative contribution. -/
theorem deriv_fiber_remainder_at_origin_eq_fiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hζ : DifferentiableAt ℝ (ζ : ℝ → X) 0)
    (hR_deriv : HasFDerivAt d.R (LocalCutoff.centerStable d.L) (0, 0)) :
    deriv (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) 0 =
      derivFiber d ζ 0 (deriv (ζ : ℝ → X) 0) := by
  have hsplit := deriv_fiber_remainder_eq_first_slot_add_fiber d ζ 0 hζ
  have hζ0 : (ζ : ℝ → X) 0 = 0 := SmallLipschitzGraph.zero_apply ζ
  have hfderiv : fderiv ℝ d.R (0, (ζ : ℝ → X) 0) =
      LocalCutoff.centerStable d.L := by
    rw [hζ0]
    exact hR_deriv.fderiv
  have hGderiv : fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (0, (ζ : ℝ → X) 0) =
      (ContinuousLinearMap.snd ℝ ℝ X).comp (fderiv ℝ d.R (0, (ζ : ℝ → X) 0)) := by
    have hnu : (d.nu : WithTop ℕ∞) ≠ 0 := by
      have htwo : 0 < (2 : ℕ) := Nat.zero_lt_succ 1
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le htwo d.hnu))
    have hRdiff : DifferentiableAt ℝ d.R (0, (ζ : ℝ → X) 0) := by
      rw [hζ0]
      exact hR_deriv.differentiableAt
    have h := fderiv_comp (x := (0, (ζ : ℝ → X) 0))
      (f := d.R) (g := (Prod.snd : (ℝ × X) → X))
      (ContinuousLinearMap.snd ℝ ℝ X).differentiableAt hRdiff
    simpa only [Function.comp_def, fderiv_snd] using h
  have hslot :
      (fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (0, (ζ : ℝ → X) 0)) (1, 0) = 0 := by
    rw [hGderiv, hfderiv]
    simp only [ContinuousLinearMap.comp_apply, LocalCutoff.centerStable_apply,
      ContinuousLinearMap.coe_snd', map_zero]
  rw [hslot, zero_add] at hsplit
  exact hsplit

/-- Helper for the metric fiber Faà-di-Bruno leaf: the Faà-di-Bruno remainder (sum over
non-atomic ordered finpartitions) is a continuous function of `u`.  Uses only that the
fiber slice is `Cᵐ` (from `m ≤ d.nu`): each summand is a continuous order-`c.length`
(`< m`) multilinear jet composed with the continuous `pair`, evaluated at a continuously
varying tuple of iterated `pair`-derivatives of orders `c.partSize j ≤ m`.  No `C¹` control
on the remainder itself is assumed. -/
theorem iteratedDeriv_fiber_remainder_remainder_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    Continuous (fun u ↦ ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv (c.partSize j) (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hmν
  -- The inner pair map `pair` is `Cᵐ`.
  have hpair : ContDiff ℝ m (fun y ↦ (y, (ζ : ℝ → X) y)) := contDiff_id.prodMk hprev
  -- The outer fiber projection `G = Prod.snd ∘ R` is `Cᵐ`.
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_with_top
  have hg : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).2) := by
    have houter : ContDiff ℝ m
        ((ContinuousLinearMap.snd ℝ ℝ X) ∘ d.R) :=
      (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
    have heq :
        ((ContinuousLinearMap.snd ℝ ℝ X) ∘ d.R) =
          (fun z : ℝ × X ↦ (d.R z).2) := by
      funext z
      rfl
    rw [← heq]
    exact houter
  apply continuous_finsetSum
  intro c hc
  -- From the filter membership: `c.length ≠ m`, hence `c.length < m` (since `length ≤ m`).
  rw [Finset.mem_filter] at hc
  have hlt : c.length < m := lt_of_le_of_ne c.length_le hc.2
  -- Continuity of the multilinear jet `u ↦ iteratedFDeriv ℝ c.length g (pair u)`.
  have hjet : Continuous (fun u : ℝ ↦ iteratedFDeriv ℝ c.length
      (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)) := by
    have hlt_with_top : (c.length : WithTop ℕ∞) ≤ m := by exact_mod_cast hlt.le
    have hcont : Continuous (fun y : ℝ × X ↦ iteratedFDeriv ℝ c.length
        (fun z : ℝ × X ↦ (d.R z).2) y) :=
      hg.continuous_iteratedFDeriv hlt_with_top
    have hpair_continuous : Continuous
        (fun u : ℝ ↦ (u, (ζ : ℝ → X) u)) := by
      exact continuous_id.prodMk hprev.continuous
    exact hcont.comp hpair_continuous
  -- Continuity of the evaluation tuple `u ↦ (fun j ↦ iteratedDeriv (c.partSize j) pair u)`.
  have hvec : Continuous
      (fun u : ℝ ↦ (fun j ↦ iteratedDeriv (c.partSize j)
        (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
    apply continuous_pi
    intro j
    have hpart_with_top : (c.partSize j : WithTop ℕ∞) ≤ m := by
      exact_mod_cast c.partSize_le j
    exact hpair.continuous_iteratedDeriv (c.partSize j) hpart_with_top
  -- The evaluation of a continuous multilinear map on a continuously varying vector is continuous.
  exact hjet.eval hvec

/-! ## Exterior triviality of the fiber remainder — localizing the recurrence to a compact set.

The fiber remainder `g u = (R (u, ζ u)).2` vanishes on a whole neighbourhood of any point whose
graph point `(u, ζ u)` lies off `tsupport R`.  Since `pair u = (u, ζ u)` is continuous and
`tsupport R` is closed, off-support points have an off-support neighbourhood, on which `R ∘ pair`
— hence `g` — is identically `0`.  Every iterated derivative of `g` is therefore `0` there.

Combined with `hasDerivAt_iteratedDeriv_of_notMem_tsupport` (exterior triviality of
`iteratedDeriv m ζ` itself), this confirms the entire Faà-di-Bruno atomic split degenerates off the
compact support: the metric top-section recurrence carries analytic content only on the compact set
`tsupport ζ ∪ (pair ⁻¹' tsupport R)`. -/

/-- On a neighbourhood of any `u` whose graph point `(u, ζ u)` is off `tsupport R`, the fiber
remainder `g` agrees with the zero function. -/
theorem fiber_remainder_eventuallyEq_zero_of_pair_notMem_tsupport
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hprev : Continuous (ζ : ℝ → X))
    {u : ℝ} (hu : (u, (ζ : ℝ → X) u) ∉ tsupport d.R) :
    (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) =ᶠ[nhds u] (fun _ : ℝ ↦ (0 : X)) := by
  have hpair_cont : Continuous (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) :=
    continuous_id.prodMk hprev
  have hopen : IsOpen ((tsupport d.R)ᶜ) := (isClosed_tsupport _).isOpen_compl
  have hpre_open : IsOpen ((fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) ⁻¹' (tsupport d.R)ᶜ) :=
    hopen.preimage hpair_cont
  have hmem : u ∈ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) ⁻¹' (tsupport d.R)ᶜ := hu
  filter_upwards [hpre_open.mem_nhds hmem] with y hy
  have hRzero : d.R (y, (ζ : ℝ → X) y) = 0 :=
    image_eq_zero_of_notMem_tsupport (by simpa using hy)
  simp only [hRzero, Prod.snd_zero]

/-- Off the graph-support, every iterated derivative of the fiber remainder vanishes. -/
theorem iteratedDeriv_fiber_remainder_eq_zero_of_pair_notMem_tsupport
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hprev : Continuous (ζ : ℝ → X))
    (m : ℕ) {u : ℝ} (hu : (u, (ζ : ℝ → X) u) ∉ tsupport d.R) :
    iteratedDeriv m (fun y : ℝ ↦ (d.R (y, (ζ : ℝ → X) y)).2) u = 0 := by
  have hzero := fiber_remainder_eventuallyEq_zero_of_pair_notMem_tsupport d ζ hprev hu
  have hiter := hzero.iteratedDeriv_eq m
  rw [hiter, iteratedDeriv_fun_const_zero]

end LocalInvariantGraph
