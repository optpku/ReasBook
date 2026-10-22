/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Remark_8_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Exercise_8_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

/-- Helper for Theorem 8.20: a frontier point of an interval is necessarily a one-sided endpoint,
so the whole interval lies either to its right or to its left. -/
lemma interval_frontier_subset_one_side {I : Set ℝ} (hI : Set.OrdConnected I) {c : ℝ}
    (hc : c ∈ frontier I) :
    I ⊆ Set.Ici c ∨ I ⊆ Set.Iic c := by
  classical
  by_cases h_right : I ⊆ Set.Ici c
  · exact Or.inl h_right
  · right
    intro x hx
    by_contra hxc
    have hcx : c < x := not_le.mp hxc
    rcases Set.not_subset.mp h_right with ⟨y, hyI, hy_not_mem⟩
    have hyc : y < c := not_le.mp hy_not_mem
    have hc_mem : c ∈ interior I := by
      -- Proof comment: points strictly between `y` and `x` lie in the interval, so the frontier
      -- point `c` would actually be interior if `I` crossed both sides of `c`.
      refine mem_interior_iff_mem_nhds.2 ?_
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hyc, hcx⟩) ?_
      intro z hz
      exact hI.out hyI hx ⟨hz.1.le, hz.2.le⟩
    exact hc.2 hc_mem

/-- Helper for Theorem 8.20: on the event where the conditional expectation hits a frontier point
of the interval, interval geometry forces the original random variable to equal that boundary value
almost surely. -/
lemma ae_eq_const_of_condExp_mem_frontier_interval
    {ℱ : MeasurableSpace Ω} {I : Set ℝ} {X : Ω → ℝ} (hℱ : ℱ ≤ mΩ)
    (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I) (hI : Set.OrdConnected I)
    {c : ℝ} (hc : c ∈ frontier I)
    (hA : MeasurableSet[ℱ] {ω | P[X | ℱ] ω = c}) :
    X =ᵐ[P.restrict {ω | P[X | ℱ] ω = c}] fun _ ↦ c := by
  let A : Set Ω := {ω | P[X | ℱ] ω = c}
  let Y : Ω → ℝ := P[X | ℱ]
  -- Proof comment: the interval can only sit on one side of a frontier point.
  rcases interval_frontier_subset_one_side hI hc with h_right | h_left
  · have h_nonneg : 0 ≤ᵐ[P.restrict A] fun ω ↦ X ω - c := by
      -- Proof comment: on the boundary event, the interval constraint puts `X` on the
      -- right-hand side of `c`.
      change ∀ᵐ ω ∂P.restrict A, 0 ≤ X ω - c
      rw [ae_restrict_iff' (hℱ _ hA)]
      filter_upwards [hXI] with ω hω hAω
      exact sub_nonneg.mpr (h_right hω)
    have h_int : Integrable (fun ω ↦ X ω - c) (P.restrict A) :=
      hX.restrict.sub (integrable_const c).restrict
    have hY_eq_c : Y =ᵐ[P.restrict A] fun _ ↦ c := by
      change ∀ᵐ ω ∂P.restrict A, Y ω = c
      rw [ae_restrict_iff' (hℱ _ hA)]
      exact Filter.Eventually.of_forall fun ω hω ↦ by simpa [A, Y] using hω
    have hcond :
        ∫ ω, Y ω ∂P.restrict A = ∫ ω, X ω ∂P.restrict A := by
      simpa [Y] using (setIntegral_condExp hℱ hX hA)
    have hzero : ∫ ω, (X ω - c) ∂P.restrict A = 0 := by
      -- Proof comment: the defining property of conditional expectation makes the centered
      -- variable have zero integral on the measurable event `A`.
      calc
        ∫ ω, (X ω - c) ∂P.restrict A
            = ∫ ω, X ω ∂P.restrict A - ∫ ω, c ∂P.restrict A := by
                simpa using
                  (integral_sub' hX.restrict (integrable_const c).restrict)
        _ = ∫ ω, Y ω ∂P.restrict A - ∫ ω, c ∂P.restrict A := by rw [← hcond]
        _ = 0 := by rw [integral_congr_ae hY_eq_c, sub_self]
    have h_ae_zero : (fun ω ↦ X ω - c) =ᵐ[P.restrict A] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).1 hzero
    filter_upwards [h_ae_zero] with ω hω
    have hω' : X ω - c = 0 := by simpa using hω
    linarith
  · have h_nonneg : 0 ≤ᵐ[P.restrict A] fun ω ↦ c - X ω := by
      -- Proof comment: in the complementary geometry branch, every interval point lies to the
      -- left of `c`.
      change ∀ᵐ ω ∂P.restrict A, 0 ≤ c - X ω
      rw [ae_restrict_iff' (hℱ _ hA)]
      filter_upwards [hXI] with ω hω hAω
      exact sub_nonneg.mpr (h_left hω)
    have h_int : Integrable (fun ω ↦ c - X ω) (P.restrict A) :=
      (integrable_const c).restrict.sub hX.restrict
    have hY_eq_c : Y =ᵐ[P.restrict A] fun _ ↦ c := by
      change ∀ᵐ ω ∂P.restrict A, Y ω = c
      rw [ae_restrict_iff' (hℱ _ hA)]
      exact Filter.Eventually.of_forall fun ω hω ↦ by simpa [A, Y] using hω
    have hcond :
        ∫ ω, Y ω ∂P.restrict A = ∫ ω, X ω ∂P.restrict A := by
      simpa [Y] using (setIntegral_condExp hℱ hX hA)
    have hzero : ∫ ω, (c - X ω) ∂P.restrict A = 0 := by
      calc
        ∫ ω, (c - X ω) ∂P.restrict A
            = ∫ ω, c ∂P.restrict A - ∫ ω, X ω ∂P.restrict A := by
                simpa using
                  (integral_sub' (integrable_const c).restrict hX.restrict)
        _ = ∫ ω, c ∂P.restrict A - ∫ ω, Y ω ∂P.restrict A := by rw [← hcond]
        _ = 0 := by rw [integral_congr_ae hY_eq_c, sub_self]
    have h_ae_zero : (fun ω ↦ c - X ω) =ᵐ[P.restrict A] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).1 hzero
    filter_upwards [h_ae_zero] with ω hω
    have hω' : c - X ω = 0 := by simpa using hω
    linarith

/-- Helper for Theorem 8.20: any affine lower bound for `φ` on `I` survives after applying
conditional expectation and then passing to the lower conditional expectation of `φ ∘ X`. -/
lemma affine_lower_bound_condExp_le_lowerCondExp
    {ℱ : MeasurableSpace Ω} {I : Set ℝ} {X : Ω → ℝ} {φ : ℝ → ℝ} (hℱ : ℱ ≤ mΩ)
    (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I) {a b : ℝ}
    (hminor : ∀ x ∈ I, a * x + b ≤ φ x) :
    (fun ω ↦ ((a * P[X | ℱ] ω + b : ℝ) : EReal)) ≤ᵐ[P] lowerCondExp P ℱ (φ ∘ X) := by
  let g : Ω → ℝ := fun ω ↦ a * X ω + b
  -- Proof comment: an affine minorant composed with `X` stays integrable because `X` is.
  have hg_int : Integrable g P := by
    simpa [g] using (hX.const_mul a).add (integrable_const b)
  -- Proof comment: the pointwise affine lower bound transfers directly along the almost-sure
  -- interval membership of `X`.
  have hg_minor : g ≤ᵐ[P] φ ∘ X := by
    filter_upwards [hXI] with ω hω
    exact hminor (X ω) hω
  -- Proof comment: monotonicity of `lowerCondExp` moves the affine lower bound through
  -- conditional expectation.
  have hg_mono : lowerCondExp P ℱ g ≤ᵐ[P] lowerCondExp P ℱ (φ ∘ X) :=
    @lowerCondExp_mono Ω mΩ P _ ℱ hℱ g (φ ∘ X) hg_int.neg_part hg_minor
  have hcond_g : lowerCondExp P ℱ g =ᵐ[P] fun ω ↦ (P[g | ℱ] ω : EReal) :=
    @lowerCondExp_ae_eq_condExp Ω mΩ P _ ℱ hℱ g hg_int
  -- Proof comment: for affine functions, ordinary conditional expectation is computed by
  -- linearity and the constant rule.
  have hlin : P[g | ℱ] =ᵐ[P] fun ω ↦ a * P[X | ℱ] ω + b := by
    calc
      P[g | ℱ] =ᵐ[P] P[fun ω ↦ a * X ω | ℱ] + P[fun _ : Ω ↦ b | ℱ] := by
        simpa [g] using
          (condExp_add (hX.const_mul a) (integrable_const b) ℱ :
            P[(fun ω ↦ a * X ω) + fun _ : Ω ↦ b | ℱ] =ᵐ[P]
              P[fun ω ↦ a * X ω | ℱ] + P[fun _ : Ω ↦ b | ℱ])
      _ =ᵐ[P] fun ω ↦ a * P[X | ℱ] ω + P[fun _ : Ω ↦ b | ℱ] ω := by
        simpa using (condExp_smul a X ℱ).add EventuallyEq.rfl
      _ =ᵐ[P] fun ω ↦ a * P[X | ℱ] ω + b := by
        simp [condExp_const hℱ b]
  have hcond_g' : lowerCondExp P ℱ g =ᵐ[P]
      fun ω ↦ ((a * P[X | ℱ] ω + b : ℝ) : EReal) := by
    filter_upwards [hcond_g, hlin] with ω hω₁ hω₂
    simpa [hω₂] using hω₁
  calc
    (fun ω ↦ ((a * P[X | ℱ] ω + b : ℝ) : EReal)) ≤ᵐ[P] lowerCondExp P ℱ g :=
      hcond_g'.symm.le
    _ ≤ᵐ[P] lowerCondExp P ℱ (φ ∘ X) := hg_mono

/-- Helper for Theorem 8.20: at an interior point of an interval, the right derivative of a convex
function defines an affine supporting line that minorizes the function on the whole interval. -/
lemma right_supporting_line_minorizes_on_interval
    {I : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ I φ) {q : ℝ} (hq : q ∈ interior I) :
    ∀ x ∈ I, φ q + derivWithin φ (Set.Ioi q) q * (x - q) ≤ φ x := by
  intro x hx
  by_cases hqx : x = q
  · -- Proof comment: at the contact point, the supporting line agrees with `φ` by construction.
    subst hqx
    simp
  rcases lt_or_gt_of_ne hqx with hxq | hqx
  · -- Proof comment: to the left of `q`, compare the secant slope with the left derivative, then
    -- bound that by the right derivative using convexity.
    have hslope : slope φ x q ≤ derivWithin φ (Set.Iio q) q :=
      hφ.slope_le_leftDeriv_of_mem_interior hx hq hxq
    have hderiv : derivWithin φ (Set.Iio q) q ≤ derivWithin φ (Set.Ioi q) q :=
      hφ.leftDeriv_le_rightDeriv_of_mem_interior hq
    have hmain : slope φ x q ≤ derivWithin φ (Set.Ioi q) q := hslope.trans hderiv
    have hqx_pos : 0 < q - x := sub_pos.mpr hxq
    rw [slope_def_field, div_le_iff₀ hqx_pos] at hmain
    linarith
  · -- Proof comment: to the right of `q`, the right derivative is bounded above by the secant
    -- slope, which rearranges to the desired affine lower bound.
    have hmain : derivWithin φ (Set.Ioi q) q ≤ slope φ q x :=
      hφ.rightDeriv_le_slope_of_mem_interior hq hx hqx
    have hqx_pos : 0 < x - q := sub_pos.mpr hqx
    rw [slope_def_field, le_div_iff₀ hqx_pos] at hmain
    linarith

/-- Helper for Theorem 8.20: the interior supporting-line family consists of the affine maps on
`interior I` obtained from the right-derivative supporting lines of `φ` at interior base points,
viewed as restricted functions on the subtype `interior I`. -/
def interior_supporting_line_family (I : Set ℝ) (φ : ℝ → ℝ) :
    Set (interior I → ℝ) :=
  {g | ∃ q : interior I, ∃ a : ℝ,
      g = (fun y : interior I ↦ φ q + a * ((y : ℝ) - (q : ℝ))) ∧
        ∀ x ∈ I, φ q + a * (x - (q : ℝ)) ≤ φ x}

/-- Helper for Theorem 8.20: each interior point of the interval contributes a restricted affine
supporting line that touches `φ` at that point. -/
lemma interior_supporting_line_restricted_contact
    {I : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ I φ) (q : interior I) :
    let g : interior I → ℝ :=
      fun y ↦ φ q + derivWithin φ (Set.Ioi q) q * ((y : ℝ) - (q : ℝ))
    g ∈ interior_supporting_line_family I φ ∧ g q = φ q := by
  let g : interior I → ℝ :=
    fun y ↦ φ q + derivWithin φ (Set.Ioi q) q * ((y : ℝ) - (q : ℝ))
  refine ⟨?_, ?_⟩
  · refine ⟨q, derivWithin φ (Set.Ioi q) q, rfl, ?_⟩
    intro x hx
    simpa using
      right_supporting_line_minorizes_on_interval hφ q.property x hx
  · simp

/-- Helper for Theorem 8.20: every restricted interior supporting line is lower semicontinuous on
the subtype `interior I`, because it is the restriction of an affine real map. -/
lemma interior_supporting_line_lowerSemicontinuous {I : Set ℝ} {φ : ℝ → ℝ}
    {g : interior I → ℝ} (hg : g ∈ interior_supporting_line_family I φ) :
    LowerSemicontinuous g := by
  rcases hg with ⟨q, a, rfl, -⟩
  -- Proof comment: once the affine witness is unpacked, continuity is immediate on the subtype.
  exact Continuous.lowerSemicontinuous <|
    continuous_const.add <|
      continuous_const.mul (continuous_subtype_val.sub continuous_const)

/-- Helper for Theorem 8.20: on the interior of the interval, the pointwise supremum of all
restricted supporting lines recovers `φ`. -/
lemma interior_supporting_line_family_sSup_eq {I : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ I φ) :
    sSup (interior_supporting_line_family I φ) = Set.restrict (interior I) φ := by
  ext x
  rw [sSup_apply_eq_sSup_image]
  let g : interior I → ℝ :=
    fun y ↦ φ x + derivWithin φ (Set.Ioi x) x * ((y : ℝ) - x)
  have hg_contact : g ∈ interior_supporting_line_family I φ ∧ g x = φ x := by
    simpa [g] using interior_supporting_line_restricted_contact hφ x
  have hEvalBdd : BddAbove (Function.eval x '' interior_supporting_line_family I φ) := by
    refine ⟨φ x, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    rcases hf with ⟨q, a, rfl, hminor⟩
    exact hminor x (interior_subset x.property)
  apply le_antisymm
  · -- Proof comment: every member of the support family minorizes `φ`, so the pointwise supremum
    -- cannot exceed `φ`.
    exact csSup_le ⟨g x, ⟨g, hg_contact.1, rfl⟩⟩ fun z hz ↦ by
      rcases hz with ⟨f, hf, rfl⟩
      rcases hf with ⟨q, a, rfl, hminor⟩
      exact hminor x (interior_subset x.property)
  · -- Proof comment: the supporting line based at `x` touches `φ` exactly at `x`, forcing the
    -- pointwise supremum to reach `φ x`.
    exact hg_contact.2.symm.le.trans <|
      le_csSup hEvalBdd ⟨g, hg_contact.1, rfl⟩

/-- Helper for Theorem 8.20: when `interior I` is nonempty, the full interior supporting-line
family admits a countable subfamily with the same pointwise supremum. -/
lemma exists_nat_interior_supporting_line_family {I : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ I φ) (hJ : Nonempty (interior I)) :
    ∃ g : ℕ → interior I → ℝ, (∀ n, g n ∈ interior_supporting_line_family I φ) ∧
      (⨆ n, g n) = Set.restrict (interior I) φ := by
  classical
  let F : Set (interior I → ℝ) := interior_supporting_line_family I φ
  have hF_nonempty : F.Nonempty := by
    rcases hJ with ⟨q⟩
    rcases interior_supporting_line_restricted_contact hφ q with ⟨hq, -⟩
    exact ⟨_, hq⟩
  have hF_bdd : BddAbove F := by
    refine ⟨Set.restrict (interior I) φ, ?_⟩
    intro f hf y
    rcases hf with ⟨q, a, rfl, hminor⟩
    exact hminor y (interior_subset y.property)
  have hIsLUB : IsLUB F (Set.restrict (interior I) φ) := by
    refine ⟨?_, ?_⟩
    · intro f hf y
      rcases hf with ⟨q, a, rfl, hminor⟩
      exact hminor y (interior_subset y.property)
    · intro u hu
      have hsSup_le : sSup F ≤ u := csSup_le hF_nonempty hu
      have hsSup_eq : sSup F = Set.restrict (interior I) φ := by
        simpa [F] using interior_supporting_line_family_sSup_eq hφ
      rwa [← hsSup_eq]
  obtain ⟨F', hF'sub, hF'count, hF'lub⟩ :=
    exists_countable_lowerSemicontinuous_isLUB
      (fun f hf ↦ interior_supporting_line_lowerSemicontinuous hf) hIsLUB
  rcases hF_nonempty with ⟨g₀, hg₀⟩
  let F'' : Set (interior I → ℝ) := insert g₀ F'
  have hF''count : F''.Countable := hF'count.insert g₀
  have hF''lub : IsLUB F'' (Set.restrict (interior I) φ) := by
    -- Proof comment: insert one known supporting line so that the enumerated family is visibly
    -- nonempty without changing the least upper bound.
    simpa [F'', sup_eq_right.2 (hIsLUB.1 hg₀)] using hF'lub.insert g₀
  have hF''nonempty : F''.Nonempty := ⟨g₀, by simp [F'']⟩
  obtain ⟨g, hg_range⟩ := hF''count.exists_eq_range hF''nonempty
  refine ⟨g, ?_, ?_⟩
  · intro n
    have hgn : g n ∈ F'' := by
      rw [hg_range]
      exact ⟨n, rfl⟩
    rcases hgn with rfl | hgn
    · exact hg₀
    · exact hF'sub hgn
  · have hsSup_eq : sSup F'' = Set.restrict (interior I) φ := hF''lub.csSup_eq hF''nonempty
    rw [hg_range, sSup_range] at hsSup_eq
    simpa using hsSup_eq

/-- Helper for Theorem 8.20: on the event where the conditional expectation lies in `interior I`,
the countable interior supporting-line family yields the Jensen lower bound. -/
lemma interior_event_jensen_from_countable_support_family
    {ℱ : MeasurableSpace Ω} {I : Set ℝ} {X : Ω → ℝ} {φ : ℝ → ℝ} (hℱ : ℱ ≤ mΩ)
    (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I)
    {g : ℕ → interior I → ℝ} (hg : ∀ n, g n ∈ interior_supporting_line_family I φ)
    (hgSup : (⨆ n, g n) = Set.restrict (interior I) φ) :
    (fun ω ↦ (φ (P[X | ℱ] ω) : EReal)) ≤ᵐ[P.restrict {ω | P[X | ℱ] ω ∈ interior I}]
      lowerCondExp P ℱ (φ ∘ X) := by
  let Y : Ω → ℝ := P[X | ℱ]
  let B : Set Ω := {ω | Y ω ∈ interior I}
  have hBℱ : MeasurableSet[ℱ] B := by
    -- Proof comment: the interior event is measurable because conditional expectation is strongly
    -- measurable and `interior I` is open.
    have hY_meas : Measurable Y := (stronglyMeasurable_condExp : StronglyMeasurable Y).measurable
    change MeasurableSet (Y ⁻¹' interior I)
    exact hY_meas isOpen_interior.measurableSet
  have hB : MeasurableSet[mΩ] B := hℱ _ hBℱ
  have h_lines :
      ∀ᵐ ω ∂P, ∀ n, ∀ hYωB : Y ω ∈ interior I,
        let xω : interior I := ⟨Y ω, hYωB⟩
        ((g n xω : ℝ) : EReal) ≤ lowerCondExp P ℱ (φ ∘ X) ω := by
    rw [ae_all_iff]
    intro n
    rcases hg n with ⟨q, a, hg_eq, hminor⟩
    have hminor_affine : ∀ x ∈ I, a * x + (φ q - a * q) ≤ φ x := by
      intro x hx
      have hx' := hminor x hx
      linarith
    have h_affine :
        (fun ω ↦ ((a * Y ω + (φ q - a * q) : ℝ) : EReal)) ≤ᵐ[P]
          lowerCondExp P ℱ (φ ∘ X) := by
      simpa [Y] using
        @affine_lower_bound_condExp_le_lowerCondExp Ω mΩ P _ ℱ I X φ
          hℱ hX hXI a (φ q - a * q) hminor_affine
    filter_upwards [h_affine] with ω hω hYωB
    let xω : interior I := ⟨Y ω, hYωB⟩
    have hrew : a * Y ω + (φ q - a * q) = φ q + a * ((xω : ℝ) - q) := by
      dsimp [xω]
      ring
    simpa [hg_eq, xω, hrew] using hω
  rw [Filter.EventuallyLE]
  change ∀ᵐ ω ∂P.restrict B, (φ (Y ω) : EReal) ≤ lowerCondExp P ℱ (φ ∘ X) ω
  have hae_le : ae (P.restrict B) ≤ ae P :=
    (Measure.absolutelyContinuous_restrict : P.restrict B ≪ P).ae_le
  have h_lines_restrict :
      ∀ᵐ ω ∂P.restrict B, ∀ n, ∀ hYωB : Y ω ∈ interior I,
        let xω : interior I := ⟨Y ω, hYωB⟩
        ((g n xω : ℝ) : EReal) ≤ lowerCondExp P ℱ (φ ∘ X) ω :=
    Filter.Eventually.filter_mono hae_le h_lines
  have h_memB : ∀ᵐ ω ∂P.restrict B, ω ∈ B := ae_restrict_mem hB
  filter_upwards [h_lines_restrict, h_memB] with ω hω_all hBω
  have hYωB : Y ω ∈ interior I := by
    simpa [B] using hBω
  let xω : interior I := ⟨Y ω, hYωB⟩
  have hgx_le : ∀ n, ((g n xω : ℝ) : EReal) ≤ lowerCondExp P ℱ (φ ∘ X) ω := by
    intro n
    simpa [xω] using hω_all n hYωB
  have hx_bdd : BddAbove (Set.range (fun n ↦ g n xω)) := by
    refine ⟨φ xω, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases hg n with ⟨q, a, hg_eq, hminor⟩
    simpa [hg_eq] using hminor xω (interior_subset xω.property)
  let f : ℕ → ℝ := fun n ↦ g n xω
  let fE : ℕ → EReal := fun n ↦ (f n : EReal)
  have hconv : Filter.Tendsto (fun n ↦ partialSups f n) Filter.atTop (nhds (φ xω)) := by
    have hxSup : (⨆ n, g n xω) = φ xω := by
      simpa using congrFun hgSup xω
    have hlim :
        Filter.Tendsto (fun n ↦ partialSups f n) Filter.atTop (nhds (⨆ n, partialSups f n)) :=
      tendsto_atTop_ciSup (partialSups_monotone f) ((bddAbove_range_partialSups).2 hx_bdd)
    have hiSup_eq : (⨆ n, partialSups f n) = ⨆ n, f n := ciSup_partialSups_eq hx_bdd
    simpa [f, hiSup_eq, hxSup] using hlim
  have hconvE :
      Filter.Tendsto (fun n ↦ ((partialSups f n : ℝ) : EReal)) Filter.atTop
        (nhds (φ xω : EReal)) :=
    EReal.tendsto_coe.2 hconv
  have hconst :
      Filter.Tendsto (fun _ : ℕ ↦ lowerCondExp P ℱ (φ ∘ X) ω) Filter.atTop
        (nhds (lowerCondExp P ℱ (φ ∘ X) ω)) := tendsto_const_nhds
  have hpartialSups_coe :
      ∀ n, ((partialSups f n : ℝ) : EReal) = partialSups fE n := by
    have hcoe_mono : Monotone (fun x : ℝ ↦ (x : EReal)) := EReal.coe_strictMono.monotone
    intro n
    induction n with
    | zero =>
        simp [f, fE, partialSups_zero]
    | succ n ihn =>
        have hsucc_f : partialSups f (n + 1) = partialSups f n ⊔ f (n + 1) := by
          simpa only [Order.succ_eq_add_one] using partialSups_succ f n
        have hsucc_fE : partialSups fE (n + 1) = partialSups fE n ⊔ fE (n + 1) := by
          simpa only [Order.succ_eq_add_one] using partialSups_succ fE n
        rw [hsucc_f, hsucc_fE]
        simpa [fE, ihn] using hcoe_mono.map_sup (partialSups f n) (f (n + 1))
  have hpartial_le :
      ∀ n, ((partialSups f n : ℝ) : EReal) ≤ lowerCondExp P ℱ (φ ∘ X) ω := by
    intro n
    rw [hpartialSups_coe n]
    exact partialSups_le fE n _ fun j _ ↦ by simpa [f, fE] using hgx_le j
  have hlimit_le := le_of_tendsto_of_tendsto' hconvE hconst hpartial_le
  simpa [Y, xω] using hlimit_le

/-- Helper for Theorem 8.20: on the event where the conditional expectation hits a frontier point
of the interval, the lower conditional expectation of `φ ∘ X` dominates the corresponding boundary
value `φ c`. -/
lemma lowerCondExp_ge_endpoint_value_on_condExp_eq_event
    {ℱ : MeasurableSpace Ω} {I : Set ℝ} {X : Ω → ℝ} {φ : ℝ → ℝ} (hℱ : ℱ ≤ mΩ)
    (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I)
    (hφXneg : Integrable (fun ω ↦ (φ (X ω))⁻) P) (hI : Set.OrdConnected I)
    {c : ℝ} (hc : c ∈ frontier I) :
    (fun _ ↦ (φ c : EReal)) ≤ᵐ[P.restrict {ω | P[X | ℱ] ω = c}]
      lowerCondExp P ℱ (φ ∘ X) := by
  let Y : Ω → ℝ := P[X | ℱ]
  let A : Set Ω := {ω | Y ω = c}
  have hY_meas : Measurable[ℱ] Y :=
    (stronglyMeasurable_condExp : StronglyMeasurable[ℱ] Y).measurable
  have hAℱ : MeasurableSet[ℱ] A := by
    change MeasurableSet[ℱ] (Y ⁻¹' {c})
    exact hY_meas isClosed_singleton.measurableSet
  have hA : MeasurableSet[mΩ] A := hℱ _ hAℱ
  have hXeq : X =ᵐ[P.restrict A] fun _ ↦ c :=
    @ae_eq_const_of_condExp_mem_frontier_interval Ω mΩ P _ ℱ I X
      hℱ hX hXI hI c hc hAℱ
  let g : Ω → ℝ :=
    A.indicator (fun _ ↦ φ c) + Aᶜ.indicator (fun ω ↦ -((φ (X ω))⁻))
  have hg_int : Integrable g P := by
    -- Proof comment: `g` is the sum of an indicator of a constant and the localized negative part
    -- of `φ ∘ X`, so both pieces are integrable.
    refine ((integrable_const (φ c)).indicator hA).add ?_
    exact hφXneg.neg.indicator hA.compl
  have hφ_restrict :
      (fun ω ↦ φ (X ω)) =ᵐ[P.restrict A] fun _ ↦ φ c := by
    filter_upwards [hXeq] with ω hω
    simp [hω]
  have hφ_on_A :
      A.indicator (fun ω ↦ φ (X ω)) =ᵐ[P] A.indicator (fun _ ↦ φ c) := by
    change ∀ᵐ ω ∂P.restrict A, φ (X ω) = φ c at hφ_restrict
    rw [ae_restrict_iff' hA] at hφ_restrict
    filter_upwards [hφ_restrict] with ω hω
    by_cases hωA : ω ∈ A
    · simp [hωA, hω hωA]
    · simp [hωA]
  have hg_le : g ≤ᵐ[P] φ ∘ X := by
    -- Proof comment: on `A` the function `g` agrees with the boundary value `φ c = φ (X)`, and
    -- off `A` it is the negative part lower bound `-(φ(X))⁻ ≤ φ(X)`.
    filter_upwards [hφ_on_A] with ω hω
    have hcompl_le :
        Aᶜ.indicator (fun ω ↦ -((φ (X ω))⁻)) ω ≤ Aᶜ.indicator (φ ∘ X) ω := by
      by_cases hωA : ω ∈ A
      · simp [hωA]
      · simp [hωA]
        by_cases hφω : 0 ≤ φ (X ω)
        · rw [negPart_eq_zero.2 hφω]
          linarith
        · rw [negPart_eq_neg.2 (le_of_not_ge hφω)]
          linarith
    calc
      g ω
          = A.indicator (fun _ ↦ φ c) ω + Aᶜ.indicator (fun ω ↦ -((φ (X ω))⁻)) ω := rfl
      _ ≤ A.indicator (φ ∘ X) ω + Aᶜ.indicator (φ ∘ X) ω := by
            exact add_le_add (by simpa using le_of_eq hω.symm) hcompl_le
      _ = φ (X ω) := by
            by_cases hωA : ω ∈ A
            · simp [hωA]
            · simp [hωA]
  have hmono :
      lowerCondExp P ℱ g ≤ᵐ[P] lowerCondExp P ℱ (φ ∘ X) :=
    @lowerCondExp_mono Ω mΩ P _ ℱ hℱ g (φ ∘ X) hg_int.neg_part hg_le
  have h_on_A : A.indicator g = A.indicator (fun _ ↦ φ c) := by
    funext ω
    by_cases hωA : ω ∈ A
    · simp [g, hωA]
    · simp [g, hωA]
  have hPg_indicator :
      A.indicator (P[g | ℱ]) =ᵐ[P] A.indicator (fun _ ↦ φ c) := by
    -- Proof comment: restricting `g` to the endpoint event removes the off-event term, so the
    -- conditional expectation of that restriction is the same constant on `A`.
    calc
      A.indicator (P[g | ℱ]) =ᵐ[P] P[A.indicator g | ℱ] := by
        exact (condExp_indicator hg_int hAℱ).symm
      _ = P[A.indicator (fun _ ↦ φ c) | ℱ] := by rw [h_on_A]
      _ =ᵐ[P] A.indicator (P[fun _ : Ω ↦ φ c | ℱ]) :=
        condExp_indicator (integrable_const (φ c)) hAℱ
      _ =ᵐ[P] A.indicator (fun _ ↦ φ c) := by
        simp [condExp_const hℱ (φ c)]
  have hPg_eq :
      P[g | ℱ] =ᵐ[P.restrict A] fun _ ↦ φ c := by
    change ∀ᵐ ω ∂P.restrict A, P[g | ℱ] ω = φ c
    rw [ae_restrict_iff' hA]
    rw [Filter.EventuallyEq] at hPg_indicator
    filter_upwards [hPg_indicator] with ω hω hωA
    simpa [hωA] using hω
  have hae_le : ae (P.restrict A) ≤ ae P :=
    (Measure.absolutelyContinuous_restrict : P.restrict A ≪ P).ae_le
  have hlow_g :
      lowerCondExp P ℱ g =ᵐ[P.restrict A] fun _ ↦ (φ c : EReal) := by
    have hlow :
        lowerCondExp P ℱ g =ᵐ[P] fun ω ↦ (P[g | ℱ] ω : EReal) :=
      @lowerCondExp_ae_eq_condExp Ω mΩ P _ ℱ hℱ g hg_int
    have hlowA :
        lowerCondExp P ℱ g =ᵐ[P.restrict A] fun ω ↦ (P[g | ℱ] ω : EReal) :=
      Filter.Eventually.filter_mono hae_le hlow
    have hPg_eqE :
        (fun ω ↦ (P[g | ℱ] ω : EReal)) =ᵐ[P.restrict A] fun _ ↦ (φ c : EReal) := by
      filter_upwards [hPg_eq] with ω hω
      simp [hω]
    exact hlowA.trans hPg_eqE
  have hmonoA :
      lowerCondExp P ℱ g ≤ᵐ[P.restrict A] lowerCondExp P ℱ (φ ∘ X) :=
    Filter.Eventually.filter_mono hae_le hmono
  calc
    (fun _ ↦ (φ c : EReal)) ≤ᵐ[P.restrict A] lowerCondExp P ℱ g := hlow_g.symm.le
    _ ≤ᵐ[P.restrict A] lowerCondExp P ℱ (φ ∘ X) := hmonoA

/-- Helper for Theorem 8.20: on the endpoint event `{P[X | ℱ] = c}`, the Jensen lower bound can
be rewritten directly in terms of `φ (P[X | ℱ])`. -/
lemma endpoint_event_jensen
    {ℱ : MeasurableSpace Ω} {I : Set ℝ} {X : Ω → ℝ} {φ : ℝ → ℝ} (hℱ : ℱ ≤ mΩ)
    (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I)
    (hφXneg : Integrable (fun ω ↦ (φ (X ω))⁻) P) (hI : Set.OrdConnected I)
    {c : ℝ} (hc : c ∈ frontier I) :
    (fun ω ↦ (φ (P[X | ℱ] ω) : EReal)) ≤ᵐ[P.restrict {ω | P[X | ℱ] ω = c}]
      lowerCondExp P ℱ (φ ∘ X) := by
  let Y : Ω → ℝ := P[X | ℱ]
  let A : Set Ω := {ω | Y ω = c}
  have hY_meas : Measurable[ℱ] Y :=
    (stronglyMeasurable_condExp : StronglyMeasurable[ℱ] Y).measurable
  have hAℱ : MeasurableSet[ℱ] A := by
    change MeasurableSet[ℱ] (Y ⁻¹' {c})
    exact hY_meas isClosed_singleton.measurableSet
  have hA : MeasurableSet[mΩ] A := hℱ _ hAℱ
  have hconst :
      (fun _ ↦ (φ c : EReal)) ≤ᵐ[P.restrict A] lowerCondExp P ℱ (φ ∘ X) :=
    @lowerCondExp_ge_endpoint_value_on_condExp_eq_event Ω mΩ P _ ℱ I X φ
      hℱ hX hXI hφXneg hI c hc
  have hY_eq :
      (fun ω ↦ (φ (Y ω) : EReal)) =ᵐ[P.restrict A] fun _ ↦ (φ c : EReal) := by
    change ∀ᵐ ω ∂P.restrict A, (φ (Y ω) : EReal) = (φ c : EReal)
    rw [ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall fun ω hω ↦ by
      have hYω : Y ω = c := by simpa [A] using hω
      simp [hYω]
  exact hY_eq.le.trans hconst

-- Proof sketch: use the supporting-line characterization of convex functions on an interval to
-- compare `φ` with its affine minorants, apply those affine bounds to `X`, then pass to
-- conditional expectations. The affine terms can be handled by linearity of conditional
-- expectation, while Remark 8.16 supplies the lower-integrable notion of conditional expectation
-- for `φ ∘ X`.
/-- Theorem 8.20: Jensen's inequality for conditional expectation. If `X` is an integrable
real-valued random variable taking values almost surely in a convex set `I`, `φ` is convex on
`I`, and `(φ ∘ X)⁻` is integrable, then `φ (P[X | ℱ])` is bounded above almost surely by the
lower conditional expectation of `φ ∘ X` from Remark 8.16. -/
theorem convex_comp_condExp_ae_le_lower_conditional_expectation
    {ℱ : MeasurableSpace Ω} {I : Set ℝ} {X : Ω → ℝ} {φ : ℝ → ℝ} (hℱ : ℱ ≤ mΩ)
    (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I) (hφ : ConvexOn ℝ I φ)
    (hφXneg : Integrable (fun ω ↦ (φ (X ω))⁻) P) :
    (fun ω ↦ (φ (P[X | ℱ] ω) : EReal)) ≤ᵐ[P] lowerCondExp P ℱ (φ ∘ X) := by
  let Y : Ω → ℝ := P[X | ℱ]
  let lhs : Ω → EReal := fun ω ↦ (φ (Y ω) : EReal)
  let rhs : Ω → EReal := lowerCondExp P ℱ (φ ∘ X)
  have hI : Set.OrdConnected I := hφ.1.ordConnected
  -- Proof comment: the first stable step is to place the conditional expectation back in the same
  -- interval as `X`.
  have hYI : ∀ᵐ ω ∂P, Y ω ∈ I :=
    @condExp_mem_interval_ae Ω mΩ P (inferInstance : IsFiniteMeasure P) ℱ hℱ I hI X hX hXI
  -- Proof comment: every affine supporting minorant on `I` already gives the desired lower bound
  -- after conditioning.
  have h_affine :
      ∀ a b : ℝ, (∀ x ∈ I, a * x + b ≤ φ x) →
        (fun ω ↦ ((a * Y ω + b : ℝ) : EReal)) ≤ᵐ[P] lowerCondExp P ℱ (φ ∘ X) := by
    intro a b hminor
    simpa [Y] using
      @affine_lower_bound_condExp_le_lowerCondExp Ω mΩ P _ ℱ I X φ
        hℱ hX hXI a b hminor
  -- Route correction: the fixed affine-minorant reduction is complete, and the supporting-line
  -- lemma is now proved locally. The interior branch is closed via a countable supporting-line
  -- family; only the frontier-event localization remains.
  let B : Set Ω := {ω | Y ω ∈ interior I}
  have h_interior :
      lhs ≤ᵐ[P.restrict B] rhs := by
    by_cases hJ : Nonempty (interior I)
    · obtain ⟨g, hg, hgSup⟩ := exists_nat_interior_supporting_line_family hφ hJ
      exact @interior_event_jensen_from_countable_support_family Ω mΩ P _ ℱ I X φ
        hℱ hX hXI g hg hgSup
    · have hB_empty : B = ∅ := by
        ext ω
        constructor
        · intro hω
          have hYω : Y ω ∈ interior I := by simpa [B] using hω
          exact (hJ ⟨⟨Y ω, hYω⟩⟩).elim
        · intro hω
          exact False.elim hω
      simp [hB_empty, Filter.EventuallyLE]
  have hY_meas : Measurable[ℱ] Y :=
    (stronglyMeasurable_condExp : StronglyMeasurable[ℱ] Y).measurable
  have hBℱ : MeasurableSet[ℱ] B := by
    change MeasurableSet[ℱ] (Y ⁻¹' interior I)
    exact hY_meas isOpen_interior.measurableSet
  have hB : MeasurableSet[mΩ] B := hℱ _ hBℱ
  have h_interior_imp : ∀ᵐ ω ∂P, Y ω ∈ interior I → lhs ω ≤ rhs ω := by
    -- Proof comment: rewrite the restricted interior estimate as a global implication on the
    -- interior event.
    change ∀ᵐ ω ∂P.restrict B, lhs ω ≤ rhs ω at h_interior
    rw [ae_restrict_iff' hB] at h_interior
    simpa [B, lhs, rhs, Filter.EventuallyLE] using h_interior
  have h_endpoint_imp :
      ∀ {c : ℝ}, c ∈ frontier I →
        ∀ᵐ ω ∂P, Y ω = c → lhs ω ≤ rhs ω := by
    intro c hc
    let A : Set Ω := {ω | Y ω = c}
    have hAℱ : MeasurableSet[ℱ] A := by
      change MeasurableSet[ℱ] (Y ⁻¹' {c})
      exact hY_meas isClosed_singleton.measurableSet
    have hA : MeasurableSet[mΩ] A := hℱ _ hAℱ
    have hAevent :
        lhs ≤ᵐ[P.restrict A] rhs :=
      @endpoint_event_jensen Ω mΩ P _ ℱ I X φ hℱ hX hXI hφXneg hI c hc
    change ∀ᵐ ω ∂P.restrict A, lhs ω ≤ rhs ω at hAevent
    rw [ae_restrict_iff' hA] at hAevent
    simpa [A, lhs, rhs, Y, Filter.EventuallyLE] using hAevent
  -- Proof comment: classify the interval shape and splice the interior estimate with the
  -- endpoint-event estimate(s) furnished by the boundary localization lemma.
  rcases hI.isPreconnected.mem_intervals with hIcc | hIco | hIoc | hIoo | hIci | hIoi | hIic |
      hIio | hIuniv | hIempty
  · let a : ℝ := sInf I
    let b : ℝ := sSup I
    have hab : a ≤ b := by
      by_contra hab
      have : ∀ᵐ ω ∂P, False := by
        filter_upwards [hYI] with ω hω
        have hy : Y ω ∈ Set.Icc a b := by
          rw [hIcc] at hω
          simpa [a, b] using hω
        exact (not_le_of_gt (lt_of_not_ge hab)) (hy.1.trans hy.2)
      have hbot : ae P = ⊥ := Filter.eventually_false_iff_eq_bot.mp this
      exact IsProbabilityMeasure.ae_neBot.ne hbot
    have ha_frontier : a ∈ frontier I := by
      rw [hIcc, frontier_Icc hab]
      simp [a, b]
    have hb_frontier : b ∈ frontier I := by
      rw [hIcc, frontier_Icc hab]
      simp [a, b]
    have hleft := h_endpoint_imp ha_frontier
    have hright := h_endpoint_imp hb_frontier
    filter_upwards [hYI, h_interior_imp, hleft, hright] with ω hω hωint hωa hωb
    have hy : Y ω ∈ Set.Icc a b := by
      rw [hIcc] at hω
      simpa [a, b] using hω
    by_cases hya : Y ω = a
    · exact hωa hya
    · by_cases hyb : Y ω = b
      · exact hωb hyb
      · exact hωint (by
          have ha_lt : a < Y ω := lt_of_le_of_ne hy.1 (by intro hEq; exact hya hEq.symm)
          have hy_lt_b : Y ω < b := lt_of_le_of_ne hy.2 hyb
          rw [hIcc, interior_Icc]
          simpa [a, b] using ⟨ha_lt, hy_lt_b⟩)
  · let a : ℝ := sInf I
    let b : ℝ := sSup I
    by_cases hab : a < b
    · have ha_frontier : a ∈ frontier I := by
        rw [hIco, frontier_Ico hab]
        simp [a, b]
      have hleft := h_endpoint_imp ha_frontier
      filter_upwards [hYI, h_interior_imp, hleft] with ω hω hωint hωa
      have hy : Y ω ∈ Set.Ico a b := by
        rw [hIco] at hω
        simpa [a, b] using hω
      by_cases hya : Y ω = a
      · exact hωa hya
      · exact hωint (by
          have ha_lt : a < Y ω := lt_of_le_of_ne hy.1 (by intro hEq; exact hya hEq.symm)
          rw [hIco, interior_Ico]
          simpa [a, b] using ⟨ha_lt, hy.2⟩)
    · filter_upwards [hYI] with ω hω
      have hy : Y ω ∈ Set.Ico a b := by
        rw [hIco] at hω
        simpa [a, b] using hω
      exact (hab (lt_of_le_of_lt hy.1 hy.2)).elim
  · let a : ℝ := sInf I
    let b : ℝ := sSup I
    by_cases hab : a < b
    · have hb_frontier : b ∈ frontier I := by
        rw [hIoc, frontier_Ioc hab]
        simp [a, b]
      have hright := h_endpoint_imp hb_frontier
      filter_upwards [hYI, h_interior_imp, hright] with ω hω hωint hωb
      have hy : Y ω ∈ Set.Ioc a b := by
        rw [hIoc] at hω
        simpa [a, b] using hω
      by_cases hyb : Y ω = b
      · exact hωb hyb
      · exact hωint (by
          have hy_lt_b : Y ω < b := lt_of_le_of_ne hy.2 hyb
          rw [hIoc, interior_Ioc]
          simpa [a, b] using ⟨hy.1, hy_lt_b⟩)
    · filter_upwards [hYI] with ω hω
      have hy : Y ω ∈ Set.Ioc a b := by
        rw [hIoc] at hω
        simpa [a, b] using hω
      exact (hab (lt_of_lt_of_le hy.1 hy.2)).elim
  · let a : ℝ := sInf I
    let b : ℝ := sSup I
    by_cases hab : a < b
    · filter_upwards [hYI, h_interior_imp] with ω hω hωint
      have hy : Y ω ∈ Set.Ioo a b := by
        rw [hIoo] at hω
        simpa [a, b] using hω
      exact hωint (by
        rw [hIoo, interior_Ioo]
        simpa [a, b] using hy)
    · filter_upwards [hYI] with ω hω
      have hy : Y ω ∈ Set.Ioo a b := by
        rw [hIoo] at hω
        simpa [a, b] using hω
      exact (hab (lt_trans hy.1 hy.2)).elim
  · let a : ℝ := sInf I
    have ha_frontier : a ∈ frontier I := by
      rw [hIci, frontier_Ici]
      simp [a]
    have hleft := h_endpoint_imp ha_frontier
    filter_upwards [hYI, h_interior_imp, hleft] with ω hω hωint hωa
    have hy : Y ω ∈ Set.Ici a := by
      rw [hIci] at hω
      simpa [a] using hω
    by_cases hya : Y ω = a
    · exact hωa hya
    · exact hωint (by
        have ha_lt : a < Y ω := lt_of_le_of_ne hy (by intro hEq; exact hya hEq.symm)
        rw [hIci, interior_Ici]
        simpa [a] using ha_lt)
  · filter_upwards [hYI, h_interior_imp] with ω hω hωint
    have hy : Y ω ∈ Set.Ioi (sInf I) := by
      rw [hIoi] at hω
      simpa using hω
    exact hωint (by
      rw [hIoi, interior_Ioi]
      simpa using hy)
  · let a : ℝ := sSup I
    have ha_frontier : a ∈ frontier I := by
      rw [hIic, frontier_Iic]
      simp [a]
    have hright := h_endpoint_imp ha_frontier
    filter_upwards [hYI, h_interior_imp, hright] with ω hω hωint hωa
    have hy : Y ω ∈ Set.Iic a := by
      rw [hIic] at hω
      simpa [a] using hω
    by_cases hya : Y ω = a
    · exact hωa hya
    · exact hωint (by
        have hy_lt_a : Y ω < a := lt_of_le_of_ne hy hya
        rw [hIic, interior_Iic]
        simpa [a] using hy_lt_a)
  · filter_upwards [hYI, h_interior_imp] with ω hω hωint
    have hy : Y ω ∈ Set.Iio (sSup I) := by
      rw [hIio] at hω
      simpa using hω
    exact hωint (by
      rw [hIio, interior_Iio]
      simpa using hy)
  · filter_upwards [h_interior_imp] with ω hωint
    simpa [hIuniv] using hωint (by simp [hIuniv])
  · filter_upwards [hYI] with ω hω
    exfalso
    rw [hIempty] at hω
    simp at hω
