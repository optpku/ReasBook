/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Data.List.TFAE
import Mathlib.Topology.Semicontinuity.Lindelof
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_7

-- Declarations for this item will be appended below by the statement pipeline.

open Function Set
open scoped Topology

universe u

/-- The owner family `L(φ)` of supporting affine minorants of `φ` on `s`. -/
def supporting_affine_maps_on {E : Type u} [AddCommGroup E] [Module ℝ E]
    (s : Set E) (φ : E → ℝ) : Set (s → ℝ) :=
  {g | g ≤ s.restrict φ ∧ ∃ l : E →ₗ[ℝ] ℝ, ∃ c : ℝ, g = s.restrict l + const s c}

/-- Membership in `supporting_affine_maps_on s φ` is exactly the affine-minorant presentation by a
linear part and a constant term. -/
lemma mem_supporting_affine_maps_on_iff {E : Type u} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {φ : E → ℝ} {g : s → ℝ} :
    g ∈ supporting_affine_maps_on s φ ↔
      g ≤ s.restrict φ ∧ ∃ l : E →ₗ[ℝ] ℝ, ∃ c : ℝ, g = s.restrict l + const s c := by
  rfl

/-- Touching supporting affine minorants at every point force the owner family to be nonempty and
to recover `φ` as its pointwise supremum on `s`. -/
lemma supporting_affine_maps_nonempty_and_sSup_eq_of_forall_contact {E : Type u}
    [AddCommGroup E] [Module ℝ E] {s : Set E} {φ : E → ℝ}
    (hcontact : ∀ x₀ : s, ∃ g ∈ supporting_affine_maps_on s φ, g x₀ = φ x₀) :
    (supporting_affine_maps_on s φ).Nonempty ∧
      sSup (supporting_affine_maps_on s φ) = s.restrict φ := by
  have hne : (supporting_affine_maps_on s φ).Nonempty := by
    by_cases hs : Nonempty s
    · rcases hs with ⟨x⟩
      rcases hcontact x with ⟨g, hg, -⟩
      exact ⟨g, hg⟩
    · have hs_empty : IsEmpty s := not_nonempty_iff.mp hs
      refine ⟨s.restrict (0 : E →ₗ[ℝ] ℝ) + const s 0, ?_⟩
      refine mem_supporting_affine_maps_on_iff.2 ?_
      refine ⟨?_, 0, 0, rfl⟩
      intro x
      exact (hs_empty.false x).elim
  refine ⟨hne, ?_⟩
  ext x
  rw [sSup_apply_eq_sSup_image]
  apply le_antisymm
  · exact csSup_le (image_nonempty.mpr hne) fun z hz ↦ by
      rcases hz with ⟨g, hg, rfl⟩
      exact (mem_supporting_affine_maps_on_iff.mp hg).1 x
  · rcases hcontact x with ⟨g, hg, hx⟩
    simpa [hx] using
      le_csSup ((monotone_eval x).map_bddAbove
        ⟨s.restrict φ, fun f hf y ↦ (mem_supporting_affine_maps_on_iff.mp hf).1 y⟩)
        ⟨g, hg, rfl⟩

/-- Every member of the owner family is lower semicontinuous on the subtype. -/
lemma supporting_affine_map_lowerSemicontinuous {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {φ : E → ℝ} {g : s → ℝ}
    (hg : g ∈ supporting_affine_maps_on s φ) :
    LowerSemicontinuous g := by
  rcases mem_supporting_affine_maps_on_iff.mp hg with ⟨-, l, c, rfl⟩
  exact Continuous.lowerSemicontinuous
    (((LinearMap.continuous_of_finiteDimensional l).comp continuous_subtype_val).add
      continuous_const)

/-- From an `IsLUB` description of the owner family one can extract a countable supporting family
with the same supremum. -/
lemma exists_nat_supporting_affine_family_of_isLUB {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} [HereditarilyLindelofSpace s]
    {φ : E → ℝ} (hne : (supporting_affine_maps_on s φ).Nonempty)
    (hIsLUB : IsLUB (supporting_affine_maps_on s φ) (s.restrict φ)) :
    ∃ g : ℕ → s → ℝ, (∀ n : ℕ, g n ∈ supporting_affine_maps_on s φ) ∧
      ⨆ n, g n = s.restrict φ := by
  obtain ⟨F', hF'sub, hF'count, hF'lub⟩ :=
    exists_countable_lowerSemicontinuous_isLUB
      (fun f hf ↦ supporting_affine_map_lowerSemicontinuous hf) hIsLUB
  rcases hne with ⟨g₀, hg₀⟩
  let F'' : Set (s → ℝ) := insert g₀ F'
  have hF''count : F''.Countable := hF'count.insert g₀
  have hF''lub : IsLUB F'' (s.restrict φ) := by
    simpa [F'', sup_eq_right.2 (hIsLUB.1 hg₀)] using hF'lub.insert g₀
  have hF''nonempty : F''.Nonempty := ⟨g₀, by simp [F'']⟩
  obtain ⟨g, hg_range⟩ := hF''count.exists_eq_range hF''nonempty
  refine ⟨g, ?_, ?_⟩
  · intro n
    have hgn : g n ∈ F'' := by
      rw [hg_range]
      exact mem_range_self n
    rcases hgn with rfl | hgn
    · exact hg₀
    · exact hF'sub hgn
  · have hsSup_eq : sSup F'' = s.restrict φ := hF''lub.csSup_eq hF''nonempty
    rw [hg_range, sSup_range] at hsSup_eq
    exact hsSup_eq

/-- The partial pointwise maxima of a sequence of real-valued functions. -/
def partial_max {α : Type u} (g : ℕ → α → ℝ) : ℕ → α → ℝ
  | 0 => g 0
  | n + 1 => fun x ↦ max (partial_max g n x) (g (n + 1) x)

-- Proof sketch: unfold the recursive definition of `partial_max` at `0`.
/-- The zeroth partial maximum is the first function in the sequence. -/
theorem partial_max_zero {α : Type u} (g : ℕ → α → ℝ) :
    partial_max g 0 = g 0 := rfl

-- Proof sketch: unfold the recursive step of `partial_max` and read off the pointwise maximum. -/
/-- The successor step for `partial_max` adjoins one more function by taking the pointwise maximum.
-/
theorem partial_max_succ {α : Type u} (g : ℕ → α → ℝ) (n : ℕ) :
    partial_max g (n + 1) = fun x ↦ max (partial_max g n x) (g (n + 1) x) := rfl

/-- Helper for Corollary 7.8: a global supporting slope inequality on `I` produces a supporting
affine minorant touching `φ` at `x₀`, in the canonical owner family
`supporting_affine_maps_on I φ`. -/
-- Proof sketch: package the slope `t` as the linear map `t • 1`, then rewrite the
-- supporting-slope inequality in the owner membership shape.
lemma supporting_affine_map_of_supporting_slope {I : Set ℝ} {φ : ℝ → ℝ}
    (x₀ : I) (t : ℝ)
    (hslope : ∀ y ∈ I, φ x₀ + t * (y - x₀) ≤ φ y) :
    ∃ g ∈ supporting_affine_maps_on I φ, g x₀ = φ x₀ := by
  let l : ℝ →ₗ[ℝ] ℝ := t • 1
  let g : I → ℝ := Set.restrict I l + const I (φ x₀ - t * x₀)
  have hg : g ∈ supporting_affine_maps_on I φ := by
    refine mem_supporting_affine_maps_on_iff.2 ?_
    refine ⟨?_, l, φ x₀ - t * x₀, rfl⟩
    intro y
    change l y + (φ x₀ - t * x₀) ≤ φ y
    have hl : l y = t * y := by simp [l]
    rw [hl]
    linarith [hslope y y.2]
  refine ⟨g, hg, ?_⟩
  have hl : l x₀ = t * x₀ := by simp [l]
  change l x₀ + (φ x₀ - t * x₀) = φ x₀
  rw [hl]
  ring

/-- Helper for Corollary 7.8: convexity on an open interval yields a touching supporting affine
minorant at every point. -/
-- Route correction: use the canonical owner family `supporting_affine_maps_on I φ` for the public
-- contact statement and keep the affine `l, c` presentation internal to the membership bridge.
lemma forall_contact_of_convexOn {I : Set ℝ} (hI_open : IsOpen I) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ I φ) :
    ∀ x₀ : I, ∃ g ∈ supporting_affine_maps_on I φ, g x₀ = φ x₀ := by
  intro x₀
  have hx₀ : (x₀ : ℝ) ∈ interior I := by
    rw [hI_open.interior_eq]
    exact x₀.2
  have hslope_iff :
      (∀ y ∈ I, φ x₀ + derivWithin φ (Ioi (x₀ : ℝ)) x₀ * (y - x₀) ≤ φ y) ↔
        derivWithin φ (Ioi (x₀ : ℝ)) x₀ ∈
          Icc (derivWithin φ (Iio (x₀ : ℝ)) x₀) (derivWithin φ (Ioi (x₀ : ℝ)) x₀) :=
    convexOn_supportingSlope_iff hφ hx₀
  have hslope : ∀ y ∈ I, φ x₀ + derivWithin φ (Ioi (x₀ : ℝ)) x₀ * (y - x₀) ≤ φ y :=
    hslope_iff.2 ⟨hφ.leftDeriv_le_rightDeriv_of_mem_interior hx₀, le_rfl⟩
  exact supporting_affine_map_of_supporting_slope x₀
    (derivWithin φ (Ioi (x₀ : ℝ)) x₀) hslope

/- Helper for Corollary 7.8: every point admitting a touching affine minorant implies convexity on
`I`. -/
-- Proof sketch: at the barycenter `z = a x + b y`, choose a touching affine minorant; its affine
-- identity gives the convexity inequality after using that it lies below `φ` at `x` and `y`.
lemma convexOn_of_forall_contact {I : Set ℝ} (hI_convex : Convex ℝ I) {φ : ℝ → ℝ}
    (hcontact : ∀ x₀ : I, ∃ g ∈ supporting_affine_maps_on I φ, g x₀ = φ x₀) :
    ConvexOn ℝ I φ := by
  rw [ConvexOn]
  refine ⟨hI_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz_mem : a * x + b * y ∈ I := by
    simpa [smul_eq_mul] using hI_convex hx hy ha hb hab
  let z : I := ⟨a * x + b * y, hz_mem⟩
  rcases hcontact z with ⟨g, hg, hz⟩
  rcases mem_supporting_affine_maps_on_iff.mp hg with ⟨hminor, l, c, rfl⟩
  have hx_le : l x + c ≤ φ x := by simpa using hminor ⟨x, hx⟩
  have hy_le : l y + c ≤ φ y := by simpa using hminor ⟨y, hy⟩
  have h_aff : l (a * x + b * y) + c = a * (l x + c) + b * (l y + c) := by
    have hl : l (a * x + b * y) = a * l x + b * l y := by
      calc
        l (a * x + b * y) = l (a • x + b • y) := by simp [smul_eq_mul]
        _ = l (a • x) + l (b • y) := by rw [map_add]
        _ = a • l x + b • l y := by rw [map_smul, map_smul]
        _ = a * l x + b * l y := by simp [smul_eq_mul]
    have hc : c = a * c + b * c := by
      have hmul := congrArg (fun r : ℝ ↦ c * r) hab
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using hmul.symm
    have hsum : a * (l x + c) + b * (l y + c) = a * l x + b * l y + c := by
      calc
        a * (l x + c) + b * (l y + c) = a * l x + b * l y + (a * c + b * c) := by ring
        _ = a * l x + b * l y + c := by rw [← hc]
    calc
      l (a * x + b * y) + c = a * l x + b * l y + c := by rw [hl]
      _ = a * (l x + c) + b * (l y + c) := hsum.symm
  calc
    φ (a * x + b * y) = l (a * x + b * y) + c := by simpa [z] using hz.symm
    _ = a * (l x + c) + b * (l y + c) := h_aff
    _ ≤ a * φ x + b * φ y := by nlinarith

/-- Helper for Corollary 7.8: the partial maxima form a monotone real sequence at each point. -/
lemma partial_max_monotone {α : Type u} (g : ℕ → α → ℝ) (x : α) :
    Monotone (fun n ↦ partial_max g n x) := by
  refine monotone_nat_of_le_succ ?_
  intro n
  rw [partial_max_succ]
  exact le_max_left _ _

/-- Helper for Corollary 7.8: the `n`-th term of the family is bounded by the `n`-th partial
maximum. -/
lemma le_partial_max {α : Type u} (g : ℕ → α → ℝ) (x : α) :
    ∀ n, g n x ≤ partial_max g n x := by
  intro n
  induction n with
  | zero =>
      simp [partial_max_zero]
  | succ n ihn =>
      rw [partial_max_succ]
      exact le_max_right _ _

/-- Helper for Corollary 7.8: if a pointwise family is bounded above, then every partial maximum is
bounded above by its conditionally complete supremum. -/
lemma partial_max_le_iSup {α : Type u} (g : ℕ → α → ℝ) (x : α)
    (hbdd : BddAbove (Set.range (fun n ↦ g n x))) :
    ∀ n, partial_max g n x ≤ ⨆ m, g m x := by
  intro n
  induction n with
  | zero =>
      simpa [partial_max_zero] using le_ciSup hbdd 0
  | succ n ihn =>
      rw [partial_max_succ]
      exact max_le ihn (le_ciSup hbdd (n + 1))

/-- Helper for Corollary 7.8: the partial maxima converge pointwise to the supremum of the family.
-/
lemma partial_max_tendsto_iSup {α : Type u} (g : ℕ → α → ℝ) (x : α)
    (hbddg : BddAbove (Set.range (fun n ↦ g n x))) :
    Filter.Tendsto (fun n ↦ partial_max g n x) Filter.atTop (𝓝 (⨆ n, g n x)) := by
  have hmono : Monotone (fun n ↦ partial_max g n x) := partial_max_monotone g x
  have hbdd : BddAbove (Set.range (fun n ↦ partial_max g n x)) := by
    refine ⟨⨆ n, g n x, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact partial_max_le_iSup g x hbddg n
  have hlim : Filter.Tendsto (fun n ↦ partial_max g n x) Filter.atTop
      (𝓝 (⨆ n, partial_max g n x)) := tendsto_atTop_ciSup hmono hbdd
  have hiSup_eq : (⨆ n, partial_max g n x) = ⨆ n, g n x := by
    apply le_antisymm
    · exact ciSup_le fun n ↦ partial_max_le_iSup g x hbddg n
    · exact ciSup_le fun n ↦ (le_partial_max g x n).trans (le_ciSup hbdd n)
  simpa [hiSup_eq] using hlim

-- Proof sketch: use convexity on an open convex subset of `ℝ` to obtain continuity, hence lower
-- semicontinuity; then combine the source-facing contact theorem, the owner-style supremum bridge,
-- and the countable affine approximation argument written in the same owner shape as
-- `ConvexOn.real_sSup_of_nat_affine_eq`.
/-- Corollary 7.8: For a real-valued function on an open interval, the following are equivalent:
(i) `φ` is convex on `I`; (ii) every point of `I` admits a touching affine minorant;
(iii) the owner-style family of affine minorants is nonempty and has supremum `φ` on `I`;
(iv) `φ` is the pointwise limit of the partial maxima of a sequence of owner-style affine
minorants.
-/
theorem convex_on_tfae_supporting_affine_maps {I : Set ℝ} (hI_open : IsOpen I)
    (hI_convex : Convex ℝ I) (φ : ℝ → ℝ) :
    List.TFAE
      [ConvexOn ℝ I φ,
        ∀ x₀ : I, ∃ g ∈ supporting_affine_maps_on I φ, g x₀ = φ x₀,
        (supporting_affine_maps_on I φ).Nonempty ∧
          sSup (supporting_affine_maps_on I φ) = Set.restrict I φ,
        ∃ g : ℕ → I → ℝ,
          (∀ n, g n ∈ supporting_affine_maps_on I φ) ∧
            ∀ x : I, Filter.Tendsto (fun n ↦ partial_max g n x) Filter.atTop (𝓝 (φ x))] := by
  classical
  tfae_have 1 → 2 := by
    intro hφ
    exact forall_contact_of_convexOn hI_open hφ
  tfae_have 2 → 1 := by
    intro hcontact
    exact convexOn_of_forall_contact hI_convex hcontact
  tfae_have 2 → 3 := by
    intro hcontact
    exact supporting_affine_maps_nonempty_and_sSup_eq_of_forall_contact hcontact
  tfae_have 3 → 4 := by
    intro hsup
    have hIsLUB : IsLUB (supporting_affine_maps_on I φ) (Set.restrict I φ) := by
      rw [← hsup.2]
      refine isLUB_csSup hsup.1 ?_
      exact ⟨Set.restrict I φ, fun g hg y ↦ (mem_supporting_affine_maps_on_iff.mp hg).1 y⟩
    obtain ⟨g, hg, hgSup⟩ := exists_nat_supporting_affine_family_of_isLUB hsup.1 hIsLUB
    refine ⟨g, hg, ?_⟩
    intro x
    have hbddg : BddAbove (Set.range (fun n ↦ g n x)) := by
      refine ⟨φ x, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (mem_supporting_affine_maps_on_iff.mp (hg n)).1 x
    have hlim := partial_max_tendsto_iSup g x hbddg
    have hxSup : (⨆ n, g n x) = φ x := by
      simpa using congrFun hgSup x
    simpa [hxSup] using hlim
  tfae_have 4 → 3 := by
    intro hseq
    rcases hseq with ⟨g, hg, hconv⟩
    refine ⟨⟨g 0, hg 0⟩, ?_⟩
    ext x
    apply le_antisymm
    · rw [sSup_apply_eq_sSup_image]
      exact csSup_le (image_nonempty.mpr ⟨g 0, hg 0⟩) fun z hz ↦ by
        rcases hz with ⟨f, hf, rfl⟩
        exact (mem_supporting_affine_maps_on_iff.mp hf).1 x
    · have hEvalBdd : BddAbove (Function.eval x '' supporting_affine_maps_on I φ) := by
        refine ⟨φ x, ?_⟩
        rintro _ ⟨f, hf, rfl⟩
        exact (mem_supporting_affine_maps_on_iff.mp hf).1 x
      have hle_support : ∀ n, g n x ≤ sSup (supporting_affine_maps_on I φ) x := by
        intro n
        rw [sSup_apply_eq_sSup_image]
        exact le_csSup hEvalBdd ⟨g n, hg n, rfl⟩
      have hpartial_le : ∀ n, partial_max g n x ≤ sSup (supporting_affine_maps_on I φ) x := by
        intro n
        induction n with
        | zero =>
            simpa [partial_max_zero] using hle_support 0
        | succ n ihn =>
            rw [partial_max_succ]
            exact max_le ihn (hle_support (n + 1))
      have hsSup_tendsto :
          Filter.Tendsto (fun _ : ℕ ↦ sSup (supporting_affine_maps_on I φ) x) Filter.atTop
            (𝓝 (sSup (supporting_affine_maps_on I φ) x)) :=
        tendsto_const_nhds
      have hle := le_of_tendsto_of_tendsto' (hconv x) hsSup_tendsto hpartial_le
      simpa using hle
  tfae_have 3 → 1 := by
    intro hsup
    rw [ConvexOn]
    refine ⟨hI_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz_mem : a * x + b * y ∈ I := by
      simpa [smul_eq_mul] using hI_convex hx hy ha hb hab
    let z : I := ⟨a * x + b * y, hz_mem⟩
    have hz_eq : sSup (supporting_affine_maps_on I φ) z = φ (a * x + b * y) := by
      simpa [z] using congrFun hsup.2 z
    have hsSup_le : sSup (supporting_affine_maps_on I φ) z ≤ a * φ x + b * φ y := by
      rw [sSup_apply_eq_sSup_image]
      refine csSup_le (image_nonempty.mpr hsup.1) ?_
      rintro _ ⟨g, hg, rfl⟩
      rcases mem_supporting_affine_maps_on_iff.mp hg with ⟨hminor, l, c, rfl⟩
      have hx_le : l x + c ≤ φ x := by simpa using hminor ⟨x, hx⟩
      have hy_le : l y + c ≤ φ y := by simpa using hminor ⟨y, hy⟩
      have h_aff : l (a * x + b * y) + c = a * (l x + c) + b * (l y + c) := by
        have hl : l (a * x + b * y) = a * l x + b * l y := by
          calc
            l (a * x + b * y) = l (a • x + b • y) := by simp [smul_eq_mul]
            _ = l (a • x) + l (b • y) := by rw [map_add]
            _ = a • l x + b • l y := by rw [map_smul, map_smul]
            _ = a * l x + b * l y := by simp [smul_eq_mul]
        have hc : c = a * c + b * c := by
          have hmul := congrArg (fun r : ℝ ↦ c * r) hab
          simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using hmul.symm
        have hsum : a * (l x + c) + b * (l y + c) = a * l x + b * l y + c := by
          calc
            a * (l x + c) + b * (l y + c) = a * l x + b * l y + (a * c + b * c) := by ring
            _ = a * l x + b * l y + c := by rw [← hc]
        calc
          l (a * x + b * y) + c = a * l x + b * l y + c := by rw [hl]
          _ = a * (l x + c) + b * (l y + c) := hsum.symm
      have hineq : l (a * x + b * y) + c ≤ a * φ x + b * φ y := by
        rw [h_aff]
        nlinarith
      simpa [z] using hineq
    exact hz_eq.symm ▸ hsSup_le
  tfae_finish
