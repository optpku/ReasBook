module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.CompletePartialOrder
meta import Mathlib.Tactic.Attr.Register

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Order TopologicalSpace Topology
open scoped unitInterval

/- Domain-style sampling for Example 5.11.3:
- primary domain: Noetherian topological spaces and codimension of irreducible closed subsets;
- inspected owner declarations: `IrreducibleCloseds`, `coheight`, `NoetherianSpace`, and the
  chapter recall `Definition_5_11_1`;
- best owner abstraction: the source-facing example space should be the named type
  `TailTopologyUnitInterval`; the canonical owners `IrreducibleCloseds` and `coheight` should then
  be used directly on that space, without parallel codimension wrappers;
- primitive-vs-derived split: the only primitive data here is the carrier `[0, 1]` together with
  its tail topology; the bundled irreducible closed subset `{0}` and its codimension are derived
  API from the canonical owners.

Layer triage:
- `source-facing`: the example space `TailTopologyUnitInterval` and the codimension statement for
  the irreducible closed subset `{0}`;
- `core/canonical`: `IrreducibleCloseds`, `coheight`, and `NoetherianSpace`;
- `bridge/view`: the named irreducible closed subset `tailTopologyUnitIntervalZero`. -/

/-- The point set `[0, 1]` equipped with the tail topology from Example 5.11.3. -/
structure TailTopologyUnitInterval where
  val : I

namespace TailTopologyUnitInterval

instance : Coe TailTopologyUnitInterval ℝ where
  coe x := x.val

@[ext]
theorem ext {x y : TailTopologyUnitInterval} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simpa using h

instance : Zero TailTopologyUnitInterval := ⟨⟨0⟩⟩

@[simp] theorem coe_eq_zero {x : TailTopologyUnitInterval} : (x : ℝ) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    -- Equality in the ambient interval subtype reduces to equality of real coordinates.
    apply TailTopologyUnitInterval.ext
    change x.val = ⟨0, by constructor <;> norm_num⟩
    apply Subtype.ext
    simpa using hx
  · rintro rfl
    rfl

@[simp] theorem coe_zero : ((0 : TailTopologyUnitInterval) : ℝ) = 0 :=
  rfl

end TailTopologyUnitInterval

/-- The right endpoint of the `n`th closed initial segment `[0, 1 - 1 / (n + 1)]`. -/
noncomputable def tailCut (n : ℕ) : ℝ :=
  1 - 1 / (n + 1 : ℝ)

/-- The basic open tail `(1 - 1 / (n + 1), 1]` in the topology from Example 5.11.3. -/
private noncomputable def tailTopologyUnitIntervalBasicOpen (n : ℕ) : Set TailTopologyUnitInterval :=
  { x | tailCut n < x }

theorem tailCut_nonneg (n : ℕ) : 0 ≤ tailCut n := by
  -- Bound the reciprocal term by `1`, then rewrite the cutoff as a subtraction.
  dsimp [tailCut]
  have hle : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
    have hcast : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using one_div_le_one_div_of_le zero_lt_one hcast
  exact sub_nonneg.mpr hle

theorem tailCut_le_one (n : ℕ) : tailCut n ≤ 1 := by
  -- The cutoff is obtained by subtracting a nonnegative quantity from `1`.
  dsimp [tailCut]
  exact sub_le_self _ (by positivity)

theorem tailCut_lt_one (n : ℕ) : tailCut n < 1 := by
  -- The reciprocal term is strictly positive, so the cutoff stays below `1`.
  dsimp [tailCut]
  exact sub_lt_self _ (by positivity)

private theorem tailCut_strictMono : StrictMono tailCut := by
  intro n m hnm
  -- Increasing the index decreases the reciprocal term, hence increases the cutoff.
  dsimp [tailCut]
  have hdiv : (1 : ℝ) / (m + 1 : ℝ) < 1 / (n + 1 : ℝ) := by
    exact one_div_lt_one_div_of_lt (by positivity)
      (by exact_mod_cast Nat.succ_lt_succ hnm)
  linarith

theorem exists_tailCut_ge_of_ne_one (x : TailTopologyUnitInterval) (hx : (x : ℝ) ≠ 1) :
    ∃ n, (x : ℝ) ≤ tailCut n := by
  -- Since `x < 1`, some reciprocal `1 / (n + 1)` is smaller than the gap to `1`.
  have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.val.2.2 hx
  have hgap : 0 < 1 - (x : ℝ) := sub_pos.mpr hxlt
  rcases exists_nat_one_div_lt hgap with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  dsimp [tailCut]
  linarith

noncomputable def tailRankValue (x : TailTopologyUnitInterval) : ℕ∞ :=
  if hx : (x : ℝ) = 1 then ⊤ else Nat.find (exists_tailCut_ge_of_ne_one x hx)

noncomputable def tailRank (x : TailTopologyUnitInterval) : WithUpper ℕ∞ :=
  WithUpper.toUpper (tailRankValue x)

/-- The topology on `[0, 1]` from Example 5.11.3, realized as the topology induced from the
canonical upper topology on the stage order `ℕ∞`. -/
@[reducible] noncomputable instance : TopologicalSpace TailTopologyUnitInterval :=
  TopologicalSpace.induced tailRank inferInstance

private theorem tailRank_inducing : IsInducing tailRank :=
  ⟨rfl⟩

theorem tailRankValue_tailCut_lt_iff (x : TailTopologyUnitInterval) (n : ℕ) :
    tailCut n < (x : ℝ) ↔ (n : ℕ∞) < tailRankValue x := by
  by_cases hx : (x : ℝ) = 1
  · -- At the top point, every cutoff lies below `1`, so the rank is `⊤`.
    simp [tailRankValue, hx, tailCut_lt_one]
  · -- Away from `1`, the rank is the least cutoff index whose closed segment contains `x`.
    let m : ℕ := Nat.find (exists_tailCut_ge_of_ne_one x hx)
    have hm_spec : (x : ℝ) ≤ tailCut m := by
      dsimp [m]
      exact Nat.find_spec (exists_tailCut_ge_of_ne_one x hx)
    have hm_min : ∀ {k : ℕ}, (x : ℝ) ≤ tailCut k → m ≤ k := by
      intro k hk
      dsimp [m]
      exact Nat.find_min' (exists_tailCut_ge_of_ne_one x hx) hk
    have hcut : tailCut n < (x : ℝ) ↔ n < m := by
      constructor
      · intro hn
        by_contra hnm
        exact (not_lt_of_ge
          (hm_spec.trans (tailCut_strictMono.monotone (Nat.not_lt.mp hnm)))) hn
      · intro hnm
        by_contra hn
        exact Nat.not_lt_of_ge (hm_min (le_of_not_gt hn)) hnm
    simpa [tailRankValue, hx, m] using hcut

theorem tailRankValue_eq_zero_iff (x : TailTopologyUnitInterval) :
    tailRankValue x = 0 ↔ (x : ℝ) = 0 := by
  constructor
  · intro hx
    -- Rank zero means the first cutoff does not lie strictly below `x`.
    have hnot : ¬ tailCut 0 < (x : ℝ) := by
      intro hlt
      have hgt : (0 : ℕ∞) < tailRankValue x := (tailRankValue_tailCut_lt_iff x 0).1 hlt
      simp [hx] at hgt
    have hxnonneg : 0 ≤ (x : ℝ) := x.val.2.1
    have hxnotgt : ¬ 0 < (x : ℝ) := by
      simpa [tailCut] using hnot
    linarith
  · intro hx
    -- At `0`, the absence of a positive cutoff forces the rank to be exactly `0`.
    have hle : tailRankValue x ≤ 0 := by
      refine le_of_not_gt ?_
      intro hgt
      have hlt : tailCut 0 < (x : ℝ) := (tailRankValue_tailCut_lt_iff x 0).2 hgt
      simp [hx, tailCut] at hlt
    simpa using hle

private theorem tailTopologyUnitIntervalBasicOpen_eq_preimage (n : ℕ) :
    tailTopologyUnitIntervalBasicOpen n =
      tailRank ⁻¹' (((Set.Iic (WithUpper.toUpper (n : ℕ∞))) : Set (WithUpper ℕ∞))ᶜ) := by
  ext x
  simp [tailTopologyUnitIntervalBasicOpen, tailRank, tailRankValue_tailCut_lt_iff]

noncomputable def tailPoint (n : ℕ) : TailTopologyUnitInterval where
  val := ⟨tailCut n, tailCut_nonneg n, tailCut_le_one n⟩

@[simp] private theorem coe_tailPoint (n : ℕ) : ((tailPoint n : TailTopologyUnitInterval) : ℝ) = tailCut n :=
  rfl

@[simp] private theorem tailPoint_zero : tailPoint 0 = 0 := by
  -- The first sample point is the left endpoint of the interval.
  apply TailTopologyUnitInterval.ext
  apply Subtype.ext
  simp [tailPoint, tailCut]

theorem tailRankValue_tailPoint (n : ℕ) : tailRankValue (tailPoint n) = n := by
  have hx : ((tailPoint n : TailTopologyUnitInterval) : ℝ) ≠ 1 := by
    -- Sample points lie strictly below `1`, so the non-top branch of `tailRankValue` applies.
    simpa [coe_tailPoint] using (tailCut_lt_one n).ne
  have hfind : Nat.find (exists_tailCut_ge_of_ne_one (tailPoint n) hx) = n := by
    -- The point `tailPoint n` lies on the `n`th cutoff, and strict monotonicity forces minimality.
    apply le_antisymm
    · exact Nat.find_min' (exists_tailCut_ge_of_ne_one (tailPoint n) hx)
        (by simp [coe_tailPoint])
    · have hspec : tailCut n ≤ tailCut (Nat.find (exists_tailCut_ge_of_ne_one (tailPoint n) hx)) := by
        simpa [coe_tailPoint] using Nat.find_spec (exists_tailCut_ge_of_ne_one (tailPoint n) hx)
      by_contra hle
      have hlt : Nat.find (exists_tailCut_ge_of_ne_one (tailPoint n) hx) < n :=
        Nat.lt_of_not_ge hle
      exact (not_le_of_gt (tailCut_strictMono hlt)) hspec
  rw [tailRankValue, dif_neg hx]
  simpa using hfind

theorem tailTopologyUnitInterval_zero_isClosed :
    IsClosed ({(0 : TailTopologyUnitInterval)} : Set TailTopologyUnitInterval) := by
  -- The singleton `{0}` is the pullback of the closed initial segment `Iic 0` under the rank map.
  have hset :
      ({(0 : TailTopologyUnitInterval)} : Set TailTopologyUnitInterval) =
        tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (0 : ℕ∞))) := by
    ext x
    rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_Iic]
    simpa [tailRank, tailRankValue_eq_zero_iff] using
      (TailTopologyUnitInterval.coe_eq_zero (x := x)).symm
  rw [hset]
  exact isClosed_Iic.preimage tailRank_inducing.continuous

/-- The irreducible closed subset `{0}` of the tail-topology unit interval. -/
def tailTopologyUnitIntervalZero :
    IrreducibleCloseds TailTopologyUnitInterval :=
  ⟨{0}, isIrreducible_singleton, tailTopologyUnitInterval_zero_isClosed⟩

@[simp] theorem coe_tailTopologyUnitIntervalZero :
    (tailTopologyUnitIntervalZero : Set TailTopologyUnitInterval) = {0} :=
  rfl

private def tailPointClosure (n : ℕ) : IrreducibleCloseds TailTopologyUnitInterval :=
  ⟨closure ({tailPoint n} : Set TailTopologyUnitInterval), isIrreducible_singleton.closure,
    isClosed_closure⟩

private theorem coe_tailPointClosure (n : ℕ) :
    (tailPointClosure n : Set TailTopologyUnitInterval) =
      tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (n : ℕ∞))) := by
  -- Compute closures in the upper-topology model and pull them back along the inducing map.
  change closure ({tailPoint n} : Set TailTopologyUnitInterval) =
      tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (n : ℕ∞)))
  rw [Topology.IsInducing.closure_eq_preimage_closure_image tailRank_inducing, Set.image_singleton]
  rw [Topology.IsUpper.closure_singleton]
  simp [tailRank, tailRankValue_tailPoint]

private theorem tailPointClosure_zero :
    tailPointClosure 0 = tailTopologyUnitIntervalZero := by
  ext x
  simp [tailPointClosure, tailTopologyUnitIntervalZero, tailPoint_zero,
    tailTopologyUnitInterval_zero_isClosed.closure_eq]

/-- Helper for Example 5.11.3: the upper-topology space `WithUpper ℕ∞` is Noetherian because every
nonempty subset has a minimum, and any open containing that minimum contains the whole subset. -/
private theorem withUpper_enat_noetherian : NoetherianSpace (WithUpper ℕ∞) := by
  rw [TopologicalSpace.noetherianSpace_iff_isCompact]
  intro s
  rw [isCompact_iff_finite_subcover]
  intro ι U hUo hs
  have hwf : WellFounded ((· < ·) : WithUpper ℕ∞ → WithUpper ℕ∞ → Prop) := by
    simpa using (wellFounded_lt : WellFounded ((· < ·) : ℕ∞ → ℕ∞ → Prop))
  by_cases hsne : s.Nonempty
  · -- A minimum of `s` lies in some cover member, and upperness makes that member cover all of `s`.
    let m : WithUpper ℕ∞ := WellFounded.min hwf s hsne
    have hm_mem : m ∈ s := WellFounded.min_mem hwf s hsne
    rcases Set.mem_iUnion.1 (hs hm_mem) with ⟨i, him⟩
    refine ⟨({i} : Finset ι), ?_⟩
    intro x hx
    have hmx : m ≤ x := WellFounded.min_le hwf hx
    have hUpper : IsUpperSet (U i) := Topology.IsUpper.isUpperSet_of_isOpen (hUo i)
    have hxU : x ∈ U i := hUpper hmx him
    simp [hxU]
  · -- The empty set is compact with the empty finite subcover.
    refine ⟨(∅ : Finset ι), ?_⟩
    simp [Set.not_nonempty_iff_eq_empty.mp hsne]

/-- The tail-topology unit interval is a Noetherian topological space. -/
instance : NoetherianSpace TailTopologyUnitInterval := by
  have _ : NoetherianSpace (WithUpper ℕ∞) := withUpper_enat_noetherian
  -- Transfer Noetherianity along the inducing rank map.
  exact tailRank_inducing.noetherianSpace

private theorem tailPointClosure_strictMono : StrictMono tailPointClosure := by
  intro n m hnm
  -- The closure formula turns the sample closures into a strict chain of initial segments.
  show (tailPointClosure n : Set TailTopologyUnitInterval) ⊂
      (tailPointClosure m : Set TailTopologyUnitInterval)
  refine Set.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · intro x hx
    rw [coe_tailPointClosure] at hx ⊢
    have hx' : tailRank x ≤ WithUpper.toUpper (n : ℕ∞) := by
      simpa [Set.mem_preimage] using hx
    have hnm' : WithUpper.toUpper (n : ℕ∞) ≤ WithUpper.toUpper (m : ℕ∞) := by
      show (((n : ℕ∞) : WithUpper ℕ∞) ≤ (((m : ℕ∞) : WithUpper ℕ∞)))
      exact_mod_cast hnm.le
    change tailRank x ∈ Set.Iic (WithUpper.toUpper (m : ℕ∞))
    exact le_trans hx' hnm'
  · intro hEq
    have hm_mem : tailPoint m ∈ (tailPointClosure m : Set TailTopologyUnitInterval) := by
      rw [coe_tailPointClosure]
      simp [tailRank, tailRankValue_tailPoint]
    have hm_notmem : tailPoint m ∉ (tailPointClosure n : Set TailTopologyUnitInterval) := by
      rw [coe_tailPointClosure]
      simp [tailRank, tailRankValue_tailPoint, not_le_of_gt hnm]
    exact hm_notmem (hEq ▸ hm_mem)

/-- Example 5.11.3: in the topology on `[0, 1]` whose opens are `∅`, `[0, 1]`, and the tails
`(1 - 1 / n, 1]`, the irreducible closed subset `{0}` has infinite codimension. -/
theorem tailTopologyUnitInterval_zero_codimension_eq_top :
    coheight tailTopologyUnitIntervalZero = ⊤ := by
  -- The closures of the sample points form arbitrarily long strict chains above `{0}`.
  apply Order.coheight_eq_top_iff.mpr
  intro n
  refine ⟨(LTSeries.range n).map tailPointClosure tailPointClosure_strictMono, ?_, ?_⟩
  · simp [tailPointClosure_zero, LTSeries.head_map]
  · simp
