module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicBridge
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

public section
noncomputable section
open scoped BigOperators NNReal Topology
open Filter Set
universe u
namespace LocalInvariantGraph
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## K1: the master differentiated identity via Faà-di-Bruno atomic isolation.

We apply Mathlib's scalar Faà-di-Bruno formula to the composition `ζ ∘ Φ`, where
`Φ := d.centerMap ζ : ℝ → ℝ` and `ζ : ℝ → X`.  The Faà-di-Bruno sum ranges over ordered
finpartitions `c : OrderedFinpartition m`; the single term with `c.length = m` (the *atomic*
partition, all part sizes `= 1`) is isolated and collapsed to `(deriv Φ u)^m • iteratedDeriv m ζ`,
while every other term has `c.length ≠ m` (equivalently `c.length < m`).

We chose the **collapsed** form for the atomic term: `(deriv Φ u) ^ m • iteratedDeriv m ζ (Φ u)`.
The remainder sum is exactly over `{c | c.length ≠ m}`.

The companion continuity fact for the remainder needs only that `ζ` and `Φ` are `Cᵐ`
(both supplied): each remainder summand is a continuous multilinear map `iteratedFDeriv ℝ c.length ζ`
of order `c.length < m` (continuous since `ζ` is `Cᵐ`), evaluated at a continuously varying tuple
whose entries are `iteratedDeriv (c.partSize j) Φ` with `c.partSize j ≤ m` (continuous since `Φ`
is `Cᵐ`).  No `C¹` control on the remainder itself is assumed.
-/

/-- Helper for Infrastructure I.16a: among ordered finpartitions of `m`, the only one whose `length`
equals `m` is the atomic partition (each part a singleton).  This is the combinatorial core
that lets us isolate the single "top" term in the Faà-di-Bruno expansion. -/
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
    have hid : ∀ j : Fin m,
        emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ =
          j := by
      have hfun : (fun j : Fin m => emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩) = id :=
        le_antisymm hg.le_id hg.id_le
      intro j
      exact congrFun hfun j
    -- Every `emb j : Fin 1 → Fin m` is determined by its value at `0`, which equals `j`.
    have hemb : ∀ (j : Fin m) (r : Fin 1), emb j r = j := by
      intro j r
      have hr : r = ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ := Subsingleton.elim _ _
      rw [hr]
      exact hid j
    simpa [OrderedFinpartition.ext_iff, OrderedFinpartition.atomic, funext_iff,
      Fin.forall_fin_one] using hemb
  · intro h
    subst h
    simp [OrderedFinpartition.atomic]

/-- Infrastructure I.16a: the order-`m` iterated derivative of the
composition `ζ ∘ (centerMap ζ)` splits into the isolated atomic top term
`(deriv Φ u)^m • iteratedDeriv m ζ (Φ u)` plus the Faà-di-Bruno remainder over all
non-atomic ordered finpartitions (`c.length ≠ m`). -/
theorem iteratedDeriv_zeta_comp_centerMap_atomic_split
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m ((ζ : ℝ → X) ∘ d.centerMap ζ) u
      = (deriv (d.centerMap ζ) u) ^ m • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)
        + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
              (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u) := by
  -- Smoothness of `Φ = centerMap ζ`.
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hΦ : ContDiff ℝ m (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ hmν_with_top hprev
  -- Faà-di-Bruno.
  have hfdb := iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (g := (ζ : ℝ → X)) (f := d.centerMap ζ) (i := m) (x := u)
    (hprev.contDiffAt) (hΦ.contDiffAt) le_rfl
  rw [hfdb]
  -- Split off the atomic term.
  have hmem : OrderedFinpartition.atomic m ∈ (Finset.univ : Finset (OrderedFinpartition m)) :=
    Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hmem]
  -- Identify the atomic summand and simplify it.
  have hatomic :
      iteratedFDeriv ℝ (OrderedFinpartition.atomic m).length (ζ : ℝ → X) (d.centerMap ζ u)
          (fun j ↦ iteratedDeriv ((OrderedFinpartition.atomic m).partSize j) (d.centerMap ζ) u)
        = (deriv (d.centerMap ζ) u) ^ m • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u) := by
    -- `atomic m` has `length = m` and every `partSize = 1`, so the tuple is `fun _ ↦ deriv Φ u`.
    have hlen : (OrderedFinpartition.atomic m).length = m := by
      simp [OrderedFinpartition.atomic]
    have htuple :
        (fun j : Fin (OrderedFinpartition.atomic m).length ↦
            iteratedDeriv ((OrderedFinpartition.atomic m).partSize j) (d.centerMap ζ) u)
          = fun _ ↦ deriv (d.centerMap ζ) u := by
      funext j
      simp [OrderedFinpartition.atomic, iteratedDeriv_one]
    -- Rewrite the multilinear map at the correct order via `hlen`.
    rw [htuple]
    -- Collapse via `map_smul_univ`: `w (fun _ ↦ (deriv Φ u) • 1) = (∏ deriv Φ u) • w (fun _ ↦ 1)`.
    have hscale :
        iteratedFDeriv ℝ (OrderedFinpartition.atomic m).length (ζ : ℝ → X) (d.centerMap ζ u)
            (fun _ ↦ deriv (d.centerMap ζ) u)
          = (deriv (d.centerMap ζ) u) ^ (OrderedFinpartition.atomic m).length •
              iteratedFDeriv ℝ (OrderedFinpartition.atomic m).length (ζ : ℝ → X) (d.centerMap ζ u)
                (fun _ ↦ (1 : ℝ)) := by
      have := (iteratedFDeriv ℝ (OrderedFinpartition.atomic m).length (ζ : ℝ → X)
        (d.centerMap ζ u)).map_smul_univ
        (fun _ : Fin (OrderedFinpartition.atomic m).length ↦ deriv (d.centerMap ζ) u)
        (fun _ ↦ (1 : ℝ))
      simpa using this
    rw [hscale, hlen]
    rw [iteratedDeriv_eq_iteratedFDeriv_ones (ζ : ℝ → X) m (d.centerMap ζ u)]
  rw [hatomic]
  -- The remaining sum over `univ.erase (atomic m)` equals the sum over `c.length ≠ m`.
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and,
    ne_eq, orderedFinpartition_length_eq_iff_atomic]

/-- Helper for Infrastructure I.16a: when the center-map derivative is nonzero, the atomic
Faà-di-Bruno split can be solved for the top iterated derivative of the graph. -/
theorem iteratedDeriv_zeta_comp_centerMap_solved_atomic
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ)
    (hderiv : deriv (d.centerMap ζ) u ≠ 0) :
    iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u) =
      (deriv (d.centerMap ζ) u)⁻¹ ^ m •
        (iteratedDeriv m ((ζ : ℝ → X) ∘ d.centerMap ζ) u -
          ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
              (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
  have hsplit := iteratedDeriv_zeta_comp_centerMap_atomic_split d ζ m hmν hprev u
  have hpow : (deriv (d.centerMap ζ) u)⁻¹ ^ m *
      (deriv (d.centerMap ζ) u) ^ m = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m hderiv)]
  calc
    iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u) =
        1 • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u) :=
      (one_smul ℝ _).symm
    _ = ((deriv (d.centerMap ζ) u)⁻¹ ^ m *
          (deriv (d.centerMap ζ) u) ^ m) •
        iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u) := by rw [hpow]
    _ = (deriv (d.centerMap ζ) u)⁻¹ ^ m •
        ((deriv (d.centerMap ζ) u) ^ m •
          iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)) := by rw [mul_smul]
    _ = (deriv (d.centerMap ζ) u)⁻¹ ^ m •
        (iteratedDeriv m ((ζ : ℝ → X) ∘ d.centerMap ζ) u -
          ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
              (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
      congr 1
      rw [hsplit]
      abel

/-- Helper for Infrastructure I.16a: the solved atomic split can be transported through the
fixed-graph equation, replacing `ζ ∘ centerMap` by the metric right-hand side. -/
theorem iteratedDeriv_fixedGraph_equation_solved_atomic
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ)
    (hderiv : deriv (d.centerMap ζ) u ≠ 0) :
    iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u) =
      (deriv (d.centerMap ζ) u)⁻¹ ^ m •
        (iteratedDeriv m (fun y ↦ d.L ((ζ : ℝ → X) y) +
            (d.R (y, (ζ : ℝ → X) y)).2) u -
          ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
              (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
  have hsolved := iteratedDeriv_zeta_comp_centerMap_solved_atomic
    d ζ m hmν hprev u hderiv
  have hfixedFunction :
      ((ζ : ℝ → X) ∘ d.centerMap ζ) =
        (fun y ↦ d.L ((ζ : ℝ → X) y) + (d.R (y, (ζ : ℝ → X) y)).2) := by
    funext y
    exact d.fixedGraph_equation ζ hfixed y
  have htransport := congrArg (fun f : ℝ → X ↦ iteratedDeriv m f u) hfixedFunction
  rw [htransport] at hsolved
  exact hsolved

/-- Helper for Infrastructure I.16a: the Faà-di-Bruno remainder (sum over non-atomic
ordered finpartitions) is a continuous function of `u`.  Uses only that `ζ` and `Φ = centerMap ζ`
are `Cᵐ`: each summand is a continuous order-`c.length` (`< m`) multilinear jet of `ζ` composed
with the continuous `Φ`, evaluated at a continuously varying tuple of iterated `Φ`-derivatives of
orders `c.partSize j ≤ m`. -/
theorem iteratedDeriv_zeta_comp_centerMap_remainder_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    Continuous (fun u ↦ ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
      iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
        (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hΦ : ContDiff ℝ m (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ hmν_with_top hprev
  apply continuous_finsetSum
  intro c hc
  -- From the filter membership: `c.length ≠ m`, hence `c.length < m` (since `length ≤ m`).
  rw [Finset.mem_filter] at hc
  have hlt : c.length < m := lt_of_le_of_ne c.length_le hc.2
  -- Continuity of the multilinear jet `u ↦ iteratedFDeriv ℝ c.length ζ (Φ u)`.
  have hjet : Continuous (fun u : ℝ ↦ iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)) := by
    have hlt_with_top : (c.length : WithTop ℕ∞) ≤ m := by
      exact_mod_cast hlt.le
    have hcont : Continuous (fun y : ℝ ↦ iteratedFDeriv ℝ c.length (ζ : ℝ → X) y) :=
      hprev.continuous_iteratedFDeriv hlt_with_top
    exact hcont.comp hΦ.continuous
  -- Continuity of the evaluation tuple `u ↦ (fun j ↦ iteratedDeriv (c.partSize j) Φ u)`.
  have hvec : Continuous
      (fun u : ℝ ↦ (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
    apply continuous_pi
    intro j
    have hpart_with_top : (c.partSize j : WithTop ℕ∞) ≤ m := by
      exact_mod_cast c.partSize_le j
    exact hΦ.continuous_iteratedDeriv (c.partSize j) hpart_with_top
  -- The evaluation of a continuous multilinear map on a continuously varying vector is continuous.
  exact hjet.eval hvec

/-- Helper for Infrastructure I.16a: every part of a non-singleton ordered finpartition has
size strictly below the size of the partitioned finite set. -/
private theorem orderedFinpartition_partSize_lt_of_length_ne_one
    {m : ℕ} (c : OrderedFinpartition m) (hlen : c.length ≠ 1) (j : Fin c.length) :
    c.partSize j < m := by
  have hlength : 1 < c.length := by
    have hjlt : j.val < c.length := j.isLt
    omega
  have hcard : 1 < Fintype.card (Fin c.length) := by
    simpa using hlength
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard j
  have hsum : ∑ i, c.partSize i = m := by
    have h : ∑ (i : Fin c.length), ∑ _r : Fin (c.partSize i), (1 : ℕ) =
        ∑ _i : Fin m, (1 : ℕ) :=
      c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
    simpa using h
  have hsum_erase :
      (∑ i ∈ Finset.univ.erase j, c.partSize i) + c.partSize j = m := by
    calc
      (∑ i ∈ Finset.univ.erase j, c.partSize i) + c.partSize j =
          ∑ i, c.partSize i := Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = m := hsum
  have hk_mem : k ∈ Finset.univ.erase j := by
    rw [Finset.mem_erase]
    exact ⟨hkj, Finset.mem_univ k⟩
  have hk_le : c.partSize k ≤ ∑ i ∈ Finset.univ.erase j, c.partSize i :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hk_mem
  have hk_pos : 0 < c.partSize k := c.partSize_pos k
  omega

/-- Helper for Infrastructure I.16a: a retained doubled-filter Faà-di-Bruno summand is
`C¹` when the outer map and inner curve are `C^m`.  Excluding the atomic and single-block
branches leaves one derivative for the outer jet and every inner jet. -/
private theorem orderedFinpartition_evaluation_contDiff_one
    {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : Z → Y) (f : ℝ → Z) {m : ℕ} (hm : 2 ≤ m)
    (hg : ContDiff ℝ m g) (hf : ContDiff ℝ m f)
    (c : OrderedFinpartition m) (hlenm : c.length ≠ m) (hlen1 : c.length ≠ 1) :
    ContDiff ℝ 1 (fun u ↦ iteratedFDeriv ℝ c.length g (f u)
      (fun j ↦ iteratedDeriv (c.partSize j) f u)) := by
  have hlength_lt : c.length < m := lt_of_le_of_ne c.length_le hlenm
  have houter_order_nat : 1 + c.length ≤ m := by
    omega
  have houter_order :
      (1 : WithTop ℕ∞) + (c.length : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast houter_order_nat
  have houter : ContDiff ℝ 1 (iteratedFDeriv ℝ c.length g) :=
    hg.iteratedFDeriv_right houter_order
  have hone_nat : 1 ≤ m := by
    omega
  have hone : (1 : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hone_nat
  have hf_one : ContDiff ℝ 1 f := hf.of_le hone
  have hjet : ContDiff ℝ 1
      (fun u ↦ iteratedFDeriv ℝ c.length g (f u)) :=
    houter.comp hf_one
  have hvec : ContDiff ℝ 1
      (fun u ↦ (fun j ↦ iteratedDeriv (c.partSize j) f u)) := by
    rw [contDiff_pi]
    intro j
    have hpart_lt : c.partSize j < m :=
      orderedFinpartition_partSize_lt_of_length_ne_one c hlen1 j
    have hpart_order_nat : c.partSize j + 1 ≤ m := by
      omega
    have hpart_order :
        ((c.partSize j + 1 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
      exact_mod_cast hpart_order_nat
    have hf_succ : ContDiff ℝ (c.partSize j + 1 : ℕ) f :=
      hf.of_le hpart_order
    exact (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf_succ).2
  have hevaluation : ContDiff ℝ 1
      (fun p : (Z [×c.length]→L[ℝ] Y) × (Fin c.length → Z) ↦ p.1 p.2) := by
    have heval : AnalyticOnNhd ℝ
        (fun p : (Z [×c.length]→L[ℝ] Y) × (Fin c.length → Z) ↦ p.1 p.2)
        (Set.univ : Set ((Z [×c.length]→L[ℝ] Y) × (Fin c.length → Z))) :=
      ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear
        (ContinuousLinearMap.id ℝ (Z [×c.length]→L[ℝ] Y))
        (s := Set.univ)
    exact heval.contDiff
  simpa only [Function.comp_def] using hevaluation.comp (hjet.prodMk hvec)

/-- Helper for Infrastructure I.16a: under exactly `C^r` regularity and `r ≥ 2`, the doubled-filter
residual from `ζ ∘ centerMap` in the reserved-top affine forcing is `C¹`. -/
theorem iteratedDeriv_zeta_comp_centerMap_length_one_residual_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {r : ℕ} (hr : 2 ≤ r) (hrν : r ≤ d.nu)
    (hprev : ContDiff ℝ r (ζ : ℝ → X)) :
    ContDiff ℝ 1 (fun u ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
        (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
  have hrν_with_top : (r : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hrν
  have hcenter : ContDiff ℝ r (d.centerMap ζ) :=
    centerMap_contDiff_of_prev d ζ hrν_with_top hprev
  apply ContDiff.sum
  intro c hc
  rw [Finset.mem_filter] at hc
  exact orderedFinpartition_evaluation_contDiff_one
    (ζ : ℝ → X) (d.centerMap ζ) hr hprev hcenter c hc.2.1 hc.2.2

/-- Helper for Infrastructure I.16a: the Faà-di-Bruno remainder has a uniform norm bound on
every compact set of center coordinates.  This is the boundedness interface needed before a
remainder term can be inserted into a bounded top-section operator. -/
theorem iteratedDeriv_zeta_comp_centerMap_remainder_norm_bound_on_compact
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X))
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ u ∈ K,
      ‖∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
        iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
          (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)‖ ≤ C := by
  let remainder : ℝ → X := fun u ↦
    ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
      iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
        (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)
  have hcontinuous : Continuous remainder := by
    simpa only [remainder] using
      iteratedDeriv_zeta_comp_centerMap_remainder_continuous d ζ m hmν hprev
  have hnorm : ContinuousOn (fun u ↦ ‖remainder u‖) K :=
    hcontinuous.continuousOn.norm
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  refine ⟨C, ?_⟩
  intro u hu
  have hbound := hC ⟨u, hu, rfl⟩
  simpa only [remainder] using hbound

/-- Helper for Infrastructure I.16a: the fixed-graph invariance equation transports the
Faà-di-Bruno atomic split from `ζ ∘ centerMap` to the differentiated metric right-hand side. -/
theorem iteratedDeriv_fixedGraph_equation_atomic_split
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m (fun y ↦ d.L ((ζ : ℝ → X) y) + (d.R (y, (ζ : ℝ → X) y)).2) u =
      (deriv (d.centerMap ζ) u) ^ m • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)
        + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
              (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u) := by
  have hfixedFunction :
      ((ζ : ℝ → X) ∘ d.centerMap ζ) =
        (fun y ↦ d.L ((ζ : ℝ → X) y) + (d.R (y, (ζ : ℝ → X) y)).2) := by
    funext y
    exact d.fixedGraph_equation ζ hfixed y
  have htransport := congrArg (fun f : ℝ → X ↦ iteratedDeriv m f u) hfixedFunction
  calc
    iteratedDeriv m (fun y ↦ d.L ((ζ : ℝ → X) y) + (d.R (y, (ζ : ℝ → X) y)).2) u =
        iteratedDeriv m ((ζ : ℝ → X) ∘ d.centerMap ζ) u := htransport.symm
    _ = (deriv (d.centerMap ζ) u) ^ m • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)
          + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
              iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
                (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u) :=
      iteratedDeriv_zeta_comp_centerMap_atomic_split d ζ m hmν hprev u

end LocalInvariantGraph
