module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberFaaDiBruno

/-!
## Length-1 partition extraction from the fiber Faà-di-Bruno remainder

The fiber remainder `g u = (R (u, ζ u)).2` has, for `m ≥ 2`, the order-`m` iterated derivative
split (`iteratedDeriv_fiber_remainder_atomic_split`) into

  `iteratedDeriv m g u = ATOMIC(m)  +  Σ_{c.length ≠ m} REMAINDER(c)`,

where `ATOMIC(m)` is the order-`m` derivative of `snd ∘ R` on the diagonal *first*-derivative jet
(and does **not** contain `W = iteratedDeriv m ζ`).  The value `W` sits in the single ordered
finpartition of length `1` (its unique part has size `m`), whose summand — via the order-one jet of
the pair map at `iteratedDeriv m pair u = (iteratedDeriv m id u, W u) = (0, W u)` (for `m ≥ 2`,
`iteratedDeriv m id = 0`) — collapses to the *fiber cocycle term* `derivFiber d ζ u (W u)`.

This leaf isolates that length-1 term from the remainder sum, giving the refined split needed by
the reserved-top-order recurrence: the `derivFiber · W` cocycle term is moved into the contraction
operator, and the leftover residual ranges over `c.length ∉ {1, m}`, i.e. finpartitions all of
whose part sizes are `≤ m − 1` — hence built from `C¹`-on-compacts lower-order jets.
-/

public section
noncomputable section
open scoped NNReal Topology
open Filter Set
universe u
namespace LocalInvariantGraph
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for Infrastructure I.16a: local copy of `iteratedDeriv_clm_comp_left` (reproduced to avoid importing the heavier secant
kernel leaf): the `m`-th iterated derivative of `L ∘ f` is `L` applied to the `m`-th derivative of
`f`, whenever `f` is `Cᵐ` at `u`. -/
private theorem iteratedDeriv_clm_comp_left'
    {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Z →L[ℝ] Y) (f : ℝ → Z) {m : ℕ} {u : ℝ} (hf : ContDiffAt ℝ m f u) :
    iteratedDeriv m (L ∘ f) u = L (iteratedDeriv m f u) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ m (L ∘ f) u) (fun _ ↦ 1) =
    L ((iteratedFDeriv ℝ m f u) (fun _ ↦ 1))
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left (g := L) (f := f) (x := u) hf (le_refl _)]
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rfl

/-- Helper for Infrastructure I.16a: a family indexed by `Fin 1` is pairwise disjoint on
distinct indices, since there are no distinct indices. -/
theorem finOne_pairwiseDisjoint
    {A : Type*} (s : Fin 1 → Set A) : PairwiseDisjoint Set.univ s := by
  intro i _ j _ hij
  exact (hij (Subsingleton.elim i j)).elim

/-- Helper for Infrastructure I.16a: the identity embedding of `Fin m` covers every point,
viewed as the sole part of a one-block ordered finpartition. -/
theorem singleBlock_id_cover (m : ℕ) :
    ∀ x : Fin m, ∃ i : Fin 1, x ∈ range (id : Fin m → Fin m) := by
  intro x
  refine ⟨0, x, ?_⟩
  rfl

/-- Helper for Infrastructure I.16a: the single-block ordered finpartition of `Fin m` (for `0 < m`): one part of size `m`, embedded
by the identity.  This is the unique ordered finpartition of `m` with `length = 1`. -/
@[expose] def singleBlock (m : ℕ) (hm : 0 < m) : OrderedFinpartition m where
  length := 1
  partSize _ := m
  partSize_pos _ := hm
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := finOne_pairwiseDisjoint _
  cover := singleBlock_id_cover m

/-- Helper for Infrastructure I.16a: `singleBlock m hm` has length one. -/
@[simp] theorem singleBlock_length (m : ℕ) (hm : 0 < m) : (singleBlock m hm).length = 1 := rfl

/-- Helper for Infrastructure I.16a: the unique part of `singleBlock m hm` has size `m`. -/
@[simp] theorem singleBlock_partSize (m : ℕ) (hm : 0 < m) (j : Fin 1) :
    (singleBlock m hm).partSize j = m := rfl

/-- Helper for Infrastructure I.16a: among ordered finpartitions of `m`, the only one whose
length equals `m` is the atomic partition (each part is a singleton). -/
private theorem orderedFinpartition_length_eq_iff_atomic
    {m : ℕ} (c : OrderedFinpartition m) :
    c.length = m ↔ c = OrderedFinpartition.atomic m := by
  constructor
  · intro hlen
    have hsum : ∑ j, c.partSize j = m := by
      have h : ∑ (j : Fin c.length), ∑ _r : Fin (c.partSize j), (1 : ℕ) =
          ∑ _i : Fin m, (1 : ℕ) := c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
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
    rcases c with ⟨length, partSize, hpos, emb, hmono, hpmono, hdisj, hcov⟩
    dsimp only at hlen hall
    subst length
    obtain rfl : partSize = fun _ ↦ 1 := funext hall
    have hg : StrictMono (fun j : Fin m =>
        emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩) := hpmono
    have hid : ∀ j : Fin m,
        emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩ = j := by
      have hfun : (fun j : Fin m =>
          emb j ⟨1 - 1, Nat.sub_one_lt_of_lt (hpos j)⟩) = id :=
        le_antisymm hg.le_id hg.id_le
      intro j
      exact congrFun hfun j
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

/-- Helper for Infrastructure I.16a: among ordered finpartitions of `m` (with `0 < m`), the only one whose `length` equals `1` is
`singleBlock`.  Mirrors `orderedFinpartition_length_eq_iff_atomic`. -/
theorem orderedFinpartition_length_eq_one_iff_singleBlock
    {m : ℕ} (hm : 0 < m) (c : OrderedFinpartition m) :
    c.length = 1 ↔ c = singleBlock m hm := by
  constructor
  · intro hlen
    -- With `length = 1`, the single part has size summing to `m`, hence `partSize 0 = m`.
    have hsum : ∑ j, c.partSize j = m := by
      have h : ∑ (j : Fin c.length), ∑ _r : Fin (c.partSize j), (1 : ℕ) = ∑ _i : Fin m, (1 : ℕ) :=
        c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
      simpa using h
    -- Over the single index, the sum is just `partSize` at that index, so `partSize · = m`.
    have hpart : ∀ j, c.partSize j = m := by
      have hone : (Finset.univ : Finset (Fin c.length)).card = 1 := by simp [hlen]
      -- `Fin c.length` is a singleton, so every index equals the summation index.
      have hsub : Subsingleton (Fin c.length) := by
        rw [hlen]
        infer_instance
      intro j
      have hsingle : ∑ k, c.partSize k = c.partSize j := by
        refine Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun k _ hk => ?_)
        exact absurd (Subsingleton.elim k j) hk
      omega
    -- Destructure and substitute the length equality.
    rcases c with ⟨length, partSize, hpos, emb, hmono, hpmono, hdisj, hcov⟩
    dsimp only at hlen hpart
    subst hlen
    obtain rfl : partSize = fun _ ↦ m := funext hpart
    -- Each `emb j : Fin m → Fin m` is a strictly-monotone self-map of `Fin m`, hence the identity.
    have hemb : ∀ (j : Fin 1) (r : Fin m), emb j r = ⟨r, r.2⟩ := by
      intro j r
      have hg : StrictMono (emb j) := hmono j
      have hfun : (emb j : Fin m → Fin m) = id := le_antisymm hg.le_id hg.id_le
      have := congrFun hfun r
      simpa using this
    simpa [OrderedFinpartition.ext_iff, singleBlock, funext_iff, Fin.forall_fin_one] using hemb
  · intro h
    subst h
    rfl

/-- Helper for Infrastructure I.16a: for `m ≥ 2`, the order-`m` iterated derivative of the pair map `pair y = (y, ζ y)` at `u` is
`(0, iteratedDeriv m ζ u)`: the first (`id`) component's `m`-th derivative vanishes for `m ≥ 2`. -/
theorem iteratedDeriv_pair_eq_of_two_le
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) {m : ℕ} (hm : 2 ≤ m) (u : ℝ)
    (hζm : ContDiffAt ℝ m (ζ : ℝ → X) u) :
    iteratedDeriv m (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u = (0, iteratedDeriv m (ζ : ℝ → X) u) := by
  set pairF : ℝ → ℝ × X := fun y ↦ (y, (ζ : ℝ → X) y) with hpairF
  have hpair_cd : ContDiffAt ℝ m pairF u := (contDiff_id.contDiffAt).prodMk hζm
  -- First component: `fst ∘ pair = id`, and `iteratedDeriv m id = 0` for `m ≥ 2`.
  have hfst : (iteratedDeriv m pairF u).1 = 0 := by
    have hcomp : iteratedDeriv m ((ContinuousLinearMap.fst ℝ ℝ X) ∘ pairF) u
        = (ContinuousLinearMap.fst ℝ ℝ X) (iteratedDeriv m pairF u) :=
      iteratedDeriv_clm_comp_left' (ContinuousLinearMap.fst ℝ ℝ X) pairF hpair_cd
    have hid : ((ContinuousLinearMap.fst ℝ ℝ X) ∘ pairF) = (id : ℝ → ℝ) := by
      funext y
      simp [hpairF]
    rw [hid] at hcomp
    have hzero : iteratedDeriv m (id : ℝ → ℝ) u = 0 := by
      rw [iteratedDeriv_id]
      have h0 : m ≠ 0 := by omega
      have h1 : m ≠ 1 := by omega
      simp [h0, h1]
    rw [hzero] at hcomp
    simpa using hcomp.symm
  -- Second component: `snd ∘ pair = ζ`.
  have hsnd : (iteratedDeriv m pairF u).2 = iteratedDeriv m (ζ : ℝ → X) u := by
    have hcomp : iteratedDeriv m ((ContinuousLinearMap.snd ℝ ℝ X) ∘ pairF) u
        = (ContinuousLinearMap.snd ℝ ℝ X) (iteratedDeriv m pairF u) :=
      iteratedDeriv_clm_comp_left' (ContinuousLinearMap.snd ℝ ℝ X) pairF hpair_cd
    have hζeq : ((ContinuousLinearMap.snd ℝ ℝ X) ∘ pairF) = (ζ : ℝ → X) := by
      funext y
      simp [hpairF]
    rw [hζeq] at hcomp
    simpa using hcomp.symm
  -- Reassemble the pair from its components.
  apply Prod.ext
  · simpa using hfst
  · simpa using hsnd

/-- Helper for Infrastructure I.16a: the Faà-di-Bruno summand attached to the single-block
finpartition `singleBlock m hm0` collapses to the fiber cocycle term
`derivFiber d ζ u (iteratedDeriv m ζ u)`, for `m ≥ 2`.  The order-one outer jet of
`snd ∘ R` is evaluated on `iteratedDeriv m pair u = (0, iteratedDeriv m ζ u)`, so its
second-slot contribution is exactly `derivFiber`. -/
theorem singleBlock_summand_eq_derivFiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hm0 : 0 < m) (u : ℝ)
    (hζm : ContDiffAt ℝ m (ζ : ℝ → X) u) :
    iteratedFDeriv ℝ (singleBlock m hm0).length (fun z : ℝ × X ↦ (d.R z).2)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv ((singleBlock m hm0).partSize j)
          (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
      = derivFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u) := by
  -- `singleBlock`'s `length` reduces to `1` and its single `partSize` to `m` (both by `@[expose]`
  -- defeq), so the goal is definitionally the order-one jet on the single order-`m` pair vector.
  show iteratedFDeriv ℝ 1 (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)
        (fun _ : Fin 1 ↦ iteratedDeriv m (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
      = derivFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u)
  rw [iteratedFDeriv_one_apply]
  -- The pair jet is `(0, W u)`.
  rw [iteratedDeriv_pair_eq_of_two_le d ζ hm u hζm]
  -- `fderiv (snd ∘ R) (pair u) (0, W u) = derivFiber d ζ u (W u)`.
  -- `fderiv (snd ∘ R) = snd ∘ fderiv R`; `derivFiber = snd ∘ fderiv R ∘ inr`; `inr (W u) = (0, W u)`.
  have hnu_ne : (d.nu : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two d.hnu))
  have hRdiff : DifferentiableAt ℝ d.R (u, (ζ : ℝ → X) u) :=
    d.hR_smooth.contDiffAt.differentiableAt hnu_ne
  have hGderiv : fderiv ℝ (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u) =
      (ContinuousLinearMap.snd ℝ ℝ X).comp (fderiv ℝ d.R (u, (ζ : ℝ → X) u)) := by
    have h := fderiv_comp (x := (u, (ζ : ℝ → X) u))
      (f := d.R) (g := (Prod.snd : (ℝ × X) → X))
      (ContinuousLinearMap.snd ℝ ℝ X).differentiableAt hRdiff
    simpa only [Function.comp_def, fderiv_snd] using h
  rw [hGderiv]
  -- `derivFiber d ζ u (W u) = (fderiv R (0, W u)).2` (via the exposed application lemma).
  rw [derivFiber_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']

/-- Helper for Infrastructure I.16a: the reserved-top-order split of the fiber remainder under
exactly `C^m` regularity.  For `m ≥ 2`, the order-`m` iterated derivative of
`u ↦ (d.R (u, ζ u)).2` is the sum of the atomic branch, the fiber cocycle applied to
`iteratedDeriv m ζ`, and the residual over ordered finpartitions of length neither `1` nor `m`.
Thus the residual depends only on jets of `ζ` of order at most `m - 1`. -/
theorem iteratedDeriv_fiber_remainder_length_one_split_of_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).2) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦ iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + derivFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u)
        + ∑ c ∈ (Finset.univ.filter
            (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j) (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  have hm0 : 0 < m := by omega
  have hζm : ContDiffAt ℝ m (ζ : ℝ → X) u := hprev.contDiffAt
  rw [iteratedDeriv_fiber_remainder_atomic_split_of_contDiff d ζ m hmν hprev u]
  set S : Finset (OrderedFinpartition m) :=
    Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m) with hS
  have hmemS : singleBlock m hm0 ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [singleBlock_length]
    omega
  rw [← Finset.add_sum_erase _ _ hmemS]
  rw [singleBlock_summand_eq_derivFiber d ζ hm hm0 u hζm]
  rw [add_assoc]
  have hset : S.erase (singleBlock m hm0)
      = Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1) := by
    ext c
    simp only [hS, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨hne, hlen⟩
      refine ⟨hlen, ?_⟩
      intro hone
      exact hne ((orderedFinpartition_length_eq_one_iff_singleBlock hm0 c).mp hone)
    · rintro ⟨hlenm, hlen1⟩
      refine ⟨?_, hlenm⟩
      intro heq
      subst heq
      rw [singleBlock_length] at hlen1
      exact hlen1 rfl
  rw [hset]

/-- Helper for Infrastructure I.16a: the stronger reserved-top-order split of the fiber remainder (`m ≥ 2`).  The order-`m` iterated
derivative of the fiber remainder `g u = (R (u, ζ u)).2` splits into

  `iteratedDeriv m g u = ATOMIC(m)  +  derivFiber d ζ u (iteratedDeriv m ζ u)  +  RESIDUAL(u)`,

where `ATOMIC(m) = iteratedFDeriv ℝ m (snd ∘ R) (pair u)` on the diagonal first-jet is `W`-free,
the middle term is the *fiber cocycle term* carrying `W = iteratedDeriv m ζ`, and `RESIDUAL(u)` is
the Faà-di-Bruno sum over ordered finpartitions of length **neither `1` nor `m`** — hence every
part has size `≤ m − 1`, so the residual is built purely from `≤ (m−1)`-order jets of `ζ`.  This is
the split the reserved-top-order recurrence needs: the `derivFiber · W` term moves into the
contracted operator, and only the `≤ (m−1)`-jet residual is left to bound by `η · |s|`. -/
theorem iteratedDeriv_fiber_remainder_length_one_split
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hmν1 : m + 1 ≤ d.nu) (hprev1 : ContDiff ℝ (m + 1) (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).2) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦ iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + derivFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u)
        + ∑ c ∈ (Finset.univ.filter
            (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j) (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  have hmν : m ≤ d.nu := by omega
  have hm_cast : (m : WithTop ℕ∞) ≤ (m + 1 : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ m
  have hprev : ContDiff ℝ m (ζ : ℝ → X) := hprev1.of_le hm_cast
  exact iteratedDeriv_fiber_remainder_length_one_split_of_contDiff d ζ hm hmν hprev u

/-- Helper for Infrastructure I.16a: the order-`m` derivative of the center-coordinate
remainder splits into its atomic branch and the non-atomic Faà-di-Bruno sum under exactly
`C^m` regularity. -/
theorem iteratedDeriv_center_remainder_atomic_split_of_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).1) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).1) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦
            iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j)
                (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  let pairF : ℝ → ℝ × X := fun y ↦ (y, (ζ : ℝ → X) y)
  have hpair : ContDiff ℝ m pairF := contDiff_id.prodMk hprev
  have hmν_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_top
  have hG : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).1) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).comp hR
  have hfdb := iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (g := (fun z : ℝ × X ↦ (d.R z).1)) (f := pairF)
    (i := m) (x := u) hG.contDiffAt hpair.contDiffAt le_rfl
  rw [hfdb]
  have hmem : OrderedFinpartition.atomic m ∈
      (Finset.univ : Finset (OrderedFinpartition m)) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hmem]
  have hatomic :
      iteratedFDeriv ℝ (OrderedFinpartition.atomic m).length
          (fun z : ℝ × X ↦ (d.R z).1)
          (pairF u)
          (fun j ↦ iteratedDeriv
            ((OrderedFinpartition.atomic m).partSize j)
            pairF u) =
        iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).1)
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
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  ext c
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and,
    ne_eq, orderedFinpartition_length_eq_iff_atomic]

/-- Helper for Infrastructure I.16a: for `m ≥ 2`, the center-coordinate Faà-di-Bruno
summand of the single-block ordered finpartition is `derivCenterFiber d ζ u` applied to
`iteratedDeriv m ζ u`. -/
theorem singleBlock_center_summand_eq_derivCenterFiber
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hm0 : 0 < m) (u : ℝ)
    (hζm : ContDiffAt ℝ m (ζ : ℝ → X) u) :
    iteratedFDeriv ℝ (singleBlock m hm0).length (fun z : ℝ × X ↦ (d.R z).1)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv ((singleBlock m hm0).partSize j)
          (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
      = derivCenterFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u) := by
  show iteratedFDeriv ℝ 1 (fun z : ℝ × X ↦ (d.R z).1) (u, (ζ : ℝ → X) u)
        (fun _ : Fin 1 ↦ iteratedDeriv m (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
      = derivCenterFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u)
  rw [iteratedFDeriv_one_apply]
  rw [iteratedDeriv_pair_eq_of_two_le d ζ hm u hζm]
  have hnu_ne : (d.nu : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two d.hnu))
  have hRdiff : DifferentiableAt ℝ d.R (u, (ζ : ℝ → X) u) :=
    d.hR_smooth.contDiffAt.differentiableAt hnu_ne
  have hGderiv : fderiv ℝ (fun z : ℝ × X ↦ (d.R z).1) (u, (ζ : ℝ → X) u) =
      (ContinuousLinearMap.fst ℝ ℝ X).comp (fderiv ℝ d.R (u, (ζ : ℝ → X) u)) := by
    have h := fderiv_comp (x := (u, (ζ : ℝ → X) u))
      (f := d.R) (g := (Prod.fst : (ℝ × X) → ℝ))
      (ContinuousLinearMap.fst ℝ ℝ X).differentiableAt hRdiff
    simpa only [Function.comp_def, fderiv_fst] using h
  rw [hGderiv]
  rw [derivCenterFiber_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']

/-- Helper for Infrastructure I.16a: under exactly `C^m` regularity and `m ≥ 2`, the
order-`m` derivative of the center-coordinate remainder is the sum of its atomic branch,
the center fiber cocycle on `iteratedDeriv m ζ`, and a residual involving only ordered
finpartitions of length neither `1` nor `m`. -/
theorem iteratedDeriv_center_remainder_length_one_split_of_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).1) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).1) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦ iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + derivCenterFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u)
        + ∑ c ∈ (Finset.univ.filter
            (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j)
                (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  have hm0 : 0 < m := by omega
  have hζm : ContDiffAt ℝ m (ζ : ℝ → X) u := hprev.contDiffAt
  rw [iteratedDeriv_center_remainder_atomic_split_of_contDiff d ζ m hmν hprev u]
  set S : Finset (OrderedFinpartition m) :=
    Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m) with hS
  have hmemS : singleBlock m hm0 ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [singleBlock_length]
    omega
  rw [← Finset.add_sum_erase _ _ hmemS]
  rw [singleBlock_center_summand_eq_derivCenterFiber d ζ hm hm0 u hζm]
  rw [add_assoc]
  have hset : S.erase (singleBlock m hm0)
      = Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1) := by
    ext c
    simp only [hS, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨hne, hlen⟩
      refine ⟨hlen, ?_⟩
      intro hone
      exact hne ((orderedFinpartition_length_eq_one_iff_singleBlock hm0 c).mp hone)
    · rintro ⟨hlenm, hlen1⟩
      refine ⟨?_, hlenm⟩
      intro heq
      subst heq
      rw [singleBlock_length] at hlen1
      exact hlen1 rfl
  rw [hset]

/-- Helper for Infrastructure I.16a: the stronger `C^(m+1)` center-coordinate
reserved-top-order split is a compatibility wrapper around
`iteratedDeriv_center_remainder_length_one_split_of_contDiff`. -/
theorem iteratedDeriv_center_remainder_length_one_split
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hmν1 : m + 1 ≤ d.nu)
    (hprev1 : ContDiff ℝ (m + 1) (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m
      ((fun z : ℝ × X ↦ (d.R z).1) ∘ (fun y : ℝ ↦ (y, (ζ : ℝ → X) y))) u
      = iteratedFDeriv ℝ m (fun z : ℝ × X ↦ (d.R z).1) (u, (ζ : ℝ → X) u)
          (fun _ : Fin m ↦ iteratedDeriv 1 (fun y : ℝ ↦ (y, (ζ : ℝ → X) y)) u)
        + derivCenterFiber d ζ u (iteratedDeriv m (ζ : ℝ → X) u)
        + ∑ c ∈ (Finset.univ.filter
            (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
            iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
              (u, (ζ : ℝ → X) u)
              (fun j ↦ iteratedDeriv (c.partSize j)
                (fun y ↦ (y, (ζ : ℝ → X) y)) u) := by
  have hmν : m ≤ d.nu := by omega
  have hm_cast : (m : WithTop ℕ∞) ≤ (m + 1 : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ m
  have hprev : ContDiff ℝ m (ζ : ℝ → X) := hprev1.of_le hm_cast
  exact iteratedDeriv_center_remainder_length_one_split_of_contDiff d ζ hm hmν hprev u

/-- Helper for Infrastructure I.16a: in a non-singleton ordered finpartition, every part has
size strictly below the size of the partitioned finite set. -/
theorem orderedFinpartition_partSize_lt_of_length_ne_one
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
`C¹` when the outer map and the inner curve are `C^m`.  The excluded atomic branch leaves one
derivative on the outer jet, while exclusion of the single-block branch leaves one derivative
on every inner jet. -/
private theorem orderedFinpartition_summand_contDiff_one
    {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : Z → Y) (pairF : ℝ → Z) {m : ℕ} (hm : 2 ≤ m)
    (hg : ContDiff ℝ m g) (hpair : ContDiff ℝ m pairF)
    (c : OrderedFinpartition m) (hlenm : c.length ≠ m) (hlen1 : c.length ≠ 1) :
    ContDiff ℝ 1 (fun u ↦ iteratedFDeriv ℝ c.length g (pairF u)
      (fun j ↦ iteratedDeriv (c.partSize j) pairF u)) := by
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
  have hpair_one : ContDiff ℝ 1 pairF := hpair.of_le hone
  have hjet : ContDiff ℝ 1
      (fun u ↦ iteratedFDeriv ℝ c.length g (pairF u)) :=
    houter.comp hpair_one
  have hvec : ContDiff ℝ 1
      (fun u ↦ (fun j ↦ iteratedDeriv (c.partSize j) pairF u)) := by
    rw [contDiff_pi]
    intro j
    have hpart_lt : c.partSize j < m :=
      orderedFinpartition_partSize_lt_of_length_ne_one c hlen1 j
    have hpart_order_nat : c.partSize j + 1 ≤ m := by
      omega
    have hpart_order :
        ((c.partSize j + 1 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
      exact_mod_cast hpart_order_nat
    have hpair_succ : ContDiff ℝ (c.partSize j + 1 : ℕ) pairF :=
      hpair.of_le hpart_order
    exact (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hpair_succ).2
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

/-- Helper for Infrastructure I.16a: under exactly `C^m` regularity and `m ≥ 2`, the
doubled-filter residual in the center-coordinate reserved-top-order split is `C¹`. -/
theorem iteratedDeriv_center_remainder_length_one_residual_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    ContDiff ℝ 1 (fun u ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv (c.partSize j)
          (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_with_top
  have hg : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).1) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).comp hR
  have hpair : ContDiff ℝ m (fun y ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  apply ContDiff.sum
  intro c hc
  rw [Finset.mem_filter] at hc
  exact orderedFinpartition_summand_contDiff_one
    (fun z : ℝ × X ↦ (d.R z).1) (fun y ↦ (y, (ζ : ℝ → X) y))
    hm hg hpair c hc.2.1 hc.2.2


/-- Helper for Infrastructure I.16a: the doubled-filter residual in the center-coordinate
reserved-top-order split is continuous.  Every retained ordered finpartition has length below
`m`, so its outer jet and all inner pair-map jets vary continuously under `ContDiff ℝ m ζ`. -/
theorem iteratedDeriv_center_remainder_length_one_residual_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    Continuous (fun u ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).1)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv (c.partSize j)
          (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_with_top
  have hg : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).1) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ X)).comp hR
  apply continuous_finsetSum
  intro c hc
  rw [Finset.mem_filter] at hc
  have hlt : c.length < m := lt_of_le_of_ne c.length_le hc.2.1
  have hjet : Continuous (fun u : ℝ ↦ iteratedFDeriv ℝ c.length
      (fun z : ℝ × X ↦ (d.R z).1) (u, (ζ : ℝ → X) u)) := by
    have hlt_with_top : (c.length : WithTop ℕ∞) ≤ m := by
      exact_mod_cast hlt.le
    have hcont : Continuous (fun y : ℝ × X ↦ iteratedFDeriv ℝ c.length
        (fun z : ℝ × X ↦ (d.R z).1) y) :=
      hg.continuous_iteratedFDeriv hlt_with_top
    have hpair_continuous : Continuous (fun u : ℝ ↦ (u, (ζ : ℝ → X) u)) :=
      continuous_id.prodMk hprev.continuous
    exact hcont.comp hpair_continuous
  have hvec : Continuous
      (fun u : ℝ ↦ (fun j ↦ iteratedDeriv (c.partSize j)
        (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
    apply continuous_pi
    intro j
    have hpart_with_top : (c.partSize j : WithTop ℕ∞) ≤ m := by
      exact_mod_cast c.partSize_le j
    have hpair : ContDiff ℝ m (fun y ↦ (y, (ζ : ℝ → X) y)) :=
      contDiff_id.prodMk hprev
    exact hpair.continuous_iteratedDeriv (c.partSize j) hpart_with_top
  exact hjet.eval hvec

/-- Helper for Infrastructure I.16a: under exactly `C^m` regularity and `m ≥ 2`, the
doubled-filter residual in the stable-coordinate reserved-top-order split is `C¹`. -/
theorem iteratedDeriv_fiber_remainder_length_one_residual_contDiff
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    {m : ℕ} (hm : 2 ≤ m) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    ContDiff ℝ 1 (fun u ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv (c.partSize j)
          (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_with_top
  have hg : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).2) :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
  have hpair : ContDiff ℝ m (fun y ↦ (y, (ζ : ℝ → X) y)) :=
    contDiff_id.prodMk hprev
  apply ContDiff.sum
  intro c hc
  rw [Finset.mem_filter] at hc
  exact orderedFinpartition_summand_contDiff_one
    (fun z : ℝ × X ↦ (d.R z).2) (fun y ↦ (y, (ζ : ℝ → X) y))
    hm hg hpair c hc.2.1 hc.2.2

/-- Helper for Infrastructure I.16a: the residual sum of `iteratedDeriv_fiber_remainder_length_one_split` (over ordered
finpartitions of length neither `1` nor `m`) is a continuous function of `u`.  Every such
finpartition has `length < m` (as in `iteratedDeriv_fiber_remainder_remainder_continuous`),
so the identical continuity argument applies to the doubled filter. -/
theorem iteratedDeriv_fiber_remainder_length_one_residual_continuous
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) :
    Continuous (fun u ↦ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition m ↦ c.length ≠ m ∧ c.length ≠ 1)),
      iteratedFDeriv ℝ c.length (fun z : ℝ × X ↦ (d.R z).2)
        (u, (ζ : ℝ → X) u)
        (fun j ↦ iteratedDeriv (c.partSize j) (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
  have hmν_with_top : (m : WithTop ℕ∞) ≤ d.nu := by exact_mod_cast hmν
  have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_with_top
  have hg : ContDiff ℝ m (fun z : ℝ × X ↦ (d.R z).2) := by
    have houter : ContDiff ℝ m ((ContinuousLinearMap.snd ℝ ℝ X) ∘ d.R) :=
      (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ X)).comp hR
    have heq : ((ContinuousLinearMap.snd ℝ ℝ X) ∘ d.R) = (fun z : ℝ × X ↦ (d.R z).2) := by
      funext z
      rfl
    rw [← heq]
    exact houter
  apply continuous_finsetSum
  intro c hc
  rw [Finset.mem_filter] at hc
  have hlt : c.length < m := lt_of_le_of_ne c.length_le hc.2.1
  have hjet : Continuous (fun u : ℝ ↦ iteratedFDeriv ℝ c.length
      (fun z : ℝ × X ↦ (d.R z).2) (u, (ζ : ℝ → X) u)) := by
    have hlt_with_top : (c.length : WithTop ℕ∞) ≤ m := by exact_mod_cast hlt.le
    have hcont : Continuous (fun y : ℝ × X ↦ iteratedFDeriv ℝ c.length
        (fun z : ℝ × X ↦ (d.R z).2) y) :=
      hg.continuous_iteratedFDeriv hlt_with_top
    have hpair_continuous : Continuous (fun u : ℝ ↦ (u, (ζ : ℝ → X) u)) :=
      continuous_id.prodMk hprev.continuous
    exact hcont.comp hpair_continuous
  have hvec : Continuous
      (fun u : ℝ ↦ (fun j ↦ iteratedDeriv (c.partSize j)
        (fun y ↦ (y, (ζ : ℝ → X) y)) u)) := by
    apply continuous_pi
    intro j
    have hpart_with_top : (c.partSize j : WithTop ℕ∞) ≤ m := by
      exact_mod_cast c.partSize_le j
    have hpair : ContDiff ℝ m (fun y ↦ (y, (ζ : ℝ → X) y)) := contDiff_id.prodMk hprev
    exact hpair.continuous_iteratedDeriv (c.partSize j) hpart_with_top
  exact hjet.eval hvec

end LocalInvariantGraph
