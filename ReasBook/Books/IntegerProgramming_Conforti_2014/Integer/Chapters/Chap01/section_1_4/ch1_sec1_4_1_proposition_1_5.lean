/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; this statement
-- uses Mathlib's `convexHull ℝ` together with an explicit mixed-integer subset of `ℝ × ℝ`.

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: the mixed-integer strip
viewed as a subset of `ℝ × ℝ`. -/
private def integralFirstStrip (β : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) ∧ 0 ≤ p.2 ∧ p.1 - p.2 ≤ β}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: membership of an
integer-real pair in `integralFirstStrip β`. -/
private lemma intPair_mem_integralFirstStrip_iff
    {β : ℝ} {x : ℤ} {y : ℝ} :
    ((x : ℝ), y) ∈ integralFirstStrip β ↔ 0 ≤ y ∧ (x : ℝ) - y ≤ β := by
  -- The integrality condition is witnessed by the displayed integer `x`.
  simp only [integralFirstStrip, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨_, hy, hxy⟩
    exact ⟨hy, hxy⟩
  · rintro ⟨hy, hxy⟩
    exact ⟨⟨x, rfl⟩, hy, hxy⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: a feasible integer
first coordinate has enough nonnegative slack to satisfy the scaled floor gap inequality. -/
private lemma integerGap_mul_oneSubFract_le
    (β : ℝ) (z : ℤ) (y : ℝ)
    (hy : 0 ≤ y)
    (hzy : (z : ℝ) - y ≤ β) :
    ((z : ℝ) - (⌊β⌋ : ℝ)) * (1 - Int.fract β) ≤ y := by
  have hdenPos : 0 < 1 - Int.fract β := by
    linarith [Int.fract_lt_one β]
  by_cases hz : z ≤ ⌊β⌋
  · -- Below the floor, the scaled gap is nonpositive and hence bounded by `y`.
    have hzReal : (z : ℝ) ≤ (⌊β⌋ : ℝ) := by
      exact_mod_cast hz
    have hgapNonpos : (z : ℝ) - (⌊β⌋ : ℝ) ≤ 0 := by
      linarith
    have hscaledNonpos :
        ((z : ℝ) - (⌊β⌋ : ℝ)) * (1 - Int.fract β) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hgapNonpos hdenPos.le
    exact hscaledNonpos.trans hy
  · -- Above the floor, the integral gap is at least one and absorbs the fractional part.
    have hgapOne : (1 : ℝ) ≤ (z : ℝ) - (⌊β⌋ : ℝ) := by
      have hfloorSucc : ⌊β⌋ + 1 ≤ z :=
        Int.add_one_le_iff.mpr (lt_of_not_ge hz)
      have hfloorSuccReal : (⌊β⌋ : ℝ) + 1 ≤ (z : ℝ) := by
        exact_mod_cast hfloorSucc
      linarith
    have hfractProductNonneg :
        0 ≤ Int.fract β * ((z : ℝ) - (⌊β⌋ : ℝ) - 1) :=
      mul_nonneg (Int.fract_nonneg β) (sub_nonneg.mpr hgapOne)
    nlinarith [Int.floor_add_fract β]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: every point of
`integralFirstStrip β` satisfies the mixed-integer rounding inequality. -/
private lemma integralFirstStrip_cut_validOn
    (β : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ integralFirstStrip β) :
    p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) := by
  -- Replace the integral first coordinate by its witness and divide the scaled gap.
  rcases hp with ⟨⟨z, hz⟩, hy, hzy⟩
  rw [← hz] at hzy ⊢
  have hdenPos : 0 < 1 - Int.fract β := by
    linarith [Int.fract_lt_one β]
  have hscaled := integerGap_mul_oneSubFract_le β z p.2 hy hzy
  have hgapDiv :
      (z : ℝ) - (⌊β⌋ : ℝ) ≤ p.2 / (1 - Int.fract β) :=
    (le_div_iff₀ hdenPos).mpr hscaled
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: the three-inequality
relaxation of `mixedIntegerStrip β` is convex. -/
private lemma convex_mixedIntegerStripRelaxation (β : ℝ) :
    Convex ℝ
      {p : ℝ × ℝ |
        p.1 - p.2 ≤ β ∧
          p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) ∧
          0 ≤ p.2} := by
  -- Convex combinations preserve each of the three linear inequalities separately.
  rw [convex_iff_add_mem]
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpBase, hpCut, hpNonneg⟩
  rcases hq with ⟨hqBase, hqCut, hqNonneg⟩
  have hpBaseScaled := mul_le_mul_of_nonneg_left hpBase ha
  have hqBaseScaled := mul_le_mul_of_nonneg_left hqBase hb
  have hpCutScaled := mul_le_mul_of_nonneg_left hpCut ha
  have hqCutScaled := mul_le_mul_of_nonneg_left hqCut hb
  have hpNonnegScaled : 0 ≤ a * p.2 := mul_nonneg ha hpNonneg
  have hqNonnegScaled : 0 ≤ b * q.2 := mul_nonneg hb hqNonneg
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor
  · calc
      a * p.1 + b * q.1 - (a * p.2 + b * q.2) =
          a * (p.1 - p.2) + b * (q.1 - q.2) := by ring
      _ ≤ a * β + b * β := add_le_add hpBaseScaled hqBaseScaled
      _ = β := by rw [← add_mul, hab, one_mul]
  · constructor
    · calc
        a * p.1 + b * q.1 - (a * p.2 + b * q.2) / (1 - Int.fract β) =
            a * (p.1 - p.2 / (1 - Int.fract β)) +
              b * (q.1 - q.2 / (1 - Int.fract β)) := by ring
        _ ≤ a * (⌊β⌋ : ℝ) + b * (⌊β⌋ : ℝ) :=
          add_le_add hpCutScaled hqCutScaled
        _ = (⌊β⌋ : ℝ) := by rw [← add_mul, hab, one_mul]
    · exact add_nonneg hpNonnegScaled hqNonnegScaled

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: a point to the left of
`⌊β⌋` with nonnegative height lies in the convex hull of `mixedIntegerStrip β`. -/
private lemma mem_convexHull_mixedIntegerStrip_of_le_floor
    (β x y : ℝ)
    (hx : x ≤ (⌊β⌋ : ℝ))
    (hy : 0 ≤ y) :
    (x, y) ∈ convexHull ℝ (integralFirstStrip β) := by
  let t : ℝ := x - (⌈x⌉ : ℝ) + 1
  let left : ℝ × ℝ := (((⌈x⌉ - 1 : ℤ) : ℝ), y)
  let right : ℝ × ℝ := ((⌈x⌉ : ℝ), y)
  have hceilLeFloor : ⌈x⌉ ≤ ⌊β⌋ := Int.ceil_le.mpr hx
  have hceilLeFloorReal : (⌈x⌉ : ℝ) ≤ (⌊β⌋ : ℝ) := by
    exact_mod_cast hceilLeFloor
  have hfloorLe : (⌊β⌋ : ℝ) ≤ β := Int.floor_le β
  have hleftMem : left ∈ integralFirstStrip β := by
    -- Both adjacent ceiling integers are feasible because they do not exceed `⌊β⌋`.
    rw [intPair_mem_integralFirstStrip_iff]
    constructor
    · exact hy
    · norm_num
      linarith
  have hrightMem : right ∈ integralFirstStrip β := by
    rw [intPair_mem_integralFirstStrip_iff]
    constructor
    · exact hy
    · linarith
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    -- The ceiling inequalities place the interpolation parameter in `[0,1]`.
    constructor
    · dsimp only [t]
      linarith [Int.ceil_lt_add_one x]
    · dsimp only [t]
      linarith [Int.le_ceil x]
  have hline : AffineMap.lineMap left right t = (x, y) := by
    -- The affine line map recovers `x` in the first coordinate and keeps the height fixed.
    apply Prod.ext
    · simp only [AffineMap.lineMap_apply_module, left, right, Prod.smul_fst,
        Prod.fst_add, smul_eq_mul, Int.cast_sub, Int.cast_one]
      dsimp only [t]
      ring
    · simp only [AffineMap.lineMap_apply_module, left, right, Prod.smul_snd,
        Prod.snd_add, smul_eq_mul]
      ring
  have hsegment : AffineMap.lineMap left right t ∈ segment ℝ left right :=
    lineMap_mem_segment ℝ left right ht
  have hhull := segment_subset_convexHull hleftMem hrightMem hsegment
  rwa [hline] at hhull

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: a point above the MIR
facet between the adjacent integers `⌊β⌋` and `⌊β⌋ + 1` lies in the convex hull. -/
private lemma mem_convexHull_mixedIntegerStrip_of_floor_interval
    (β x y : ℝ)
    (hfloor : (⌊β⌋ : ℝ) ≤ x)
    (hceil : x ≤ (⌊β⌋ : ℝ) + 1)
    (hcut : x - y / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ)) :
    (x, y) ∈ convexHull ℝ (integralFirstStrip β) := by
  let d : ℝ := 1 - Int.fract β
  let t : ℝ := x - (⌊β⌋ : ℝ)
  let s : ℝ := y - d * t
  let left : ℝ × ℝ := ((⌊β⌋ : ℝ), s)
  let right : ℝ × ℝ := (((⌊β⌋ + 1 : ℤ) : ℝ), d + s)
  have hdPos : 0 < d := by
    dsimp only [d]
    linarith [Int.fract_lt_one β]
  have hscaled : (x - (⌊β⌋ : ℝ)) * d ≤ y := by
    apply (le_div_iff₀ hdPos).mp
    dsimp only [d]
    linarith
  have hs : 0 ≤ s := by
    dsimp only [s, t]
    rw [sub_nonneg]
    simpa only [mul_comm] using hscaled
  have hleftMem : left ∈ integralFirstStrip β := by
    -- The left endpoint has the nonnegative vertical slack `s` above the floor integer.
    rw [intPair_mem_integralFirstStrip_iff]
    constructor
    · exact hs
    · linarith [Int.floor_le β]
  have hrightMem : right ∈ integralFirstStrip β := by
    -- The right endpoint lies on the original strip boundary, shifted upward by `s`.
    rw [intPair_mem_integralFirstStrip_iff]
    constructor
    · exact add_nonneg hdPos.le hs
    · dsimp only [d]
      norm_num
      linarith [Int.floor_add_fract β]
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp only [t]
      linarith
    · dsimp only [t]
      linarith
  have hline : AffineMap.lineMap left right t = (x, y) := by
    -- Interpolation along the two translated breakpoints gives the original point.
    apply Prod.ext
    · simp only [AffineMap.lineMap_apply_module, left, right, Prod.smul_fst,
        Prod.fst_add, smul_eq_mul, Int.cast_add, Int.cast_one]
      dsimp only [t]
      ring
    · simp only [AffineMap.lineMap_apply_module, left, right, Prod.smul_snd,
        Prod.snd_add, smul_eq_mul]
      dsimp only [s, t]
      ring
  have hsegment : AffineMap.lineMap left right t ∈ segment ℝ left right :=
    lineMap_mem_segment ℝ left right ht
  have hhull := segment_subset_convexHull hleftMem hrightMem hsegment
  rwa [hline] at hhull

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: a point to the right of
`⌊β⌋ + 1` satisfying the original strip inequality lies in the convex hull. -/
private lemma mem_convexHull_mixedIntegerStrip_of_floor_add_one_le
    (β x y : ℝ)
    (hfloor : (⌊β⌋ : ℝ) + 1 ≤ x)
    (hbase : x - y ≤ β) :
    (x, y) ∈ convexHull ℝ (integralFirstStrip β) := by
  let t : ℝ := Int.fract x
  let left : ℝ × ℝ := ((⌊x⌋ : ℝ), y - Int.fract x)
  let right : ℝ × ℝ := (((⌊x⌋ + 1 : ℤ) : ℝ), y + 1 - Int.fract x)
  have hfloorCast : (((⌊β⌋ + 1 : ℤ) : ℝ)) ≤ x := by
    simpa only [Int.cast_add, Int.cast_one] using hfloor
  have hfloorInt : ⌊β⌋ + 1 ≤ ⌊x⌋ := Int.le_floor.mpr hfloorCast
  have hfloorReal : (⌊β⌋ : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by
    exact_mod_cast hfloorInt
  have hleftNonneg : 0 ≤ y - Int.fract x := by
    linarith [Int.floor_add_fract β, Int.floor_add_fract x, Int.fract_lt_one β]
  have hleftMem : left ∈ integralFirstStrip β := by
    -- Removing `fract x` from the height preserves the original strip slack exactly.
    rw [intPair_mem_integralFirstStrip_iff]
    constructor
    · exact hleftNonneg
    · linarith [Int.floor_add_fract x]
  have hrightMem : right ∈ integralFirstStrip β := by
    rw [intPair_mem_integralFirstStrip_iff]
    constructor
    · linarith
    · norm_num
      linarith [Int.floor_add_fract x]
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    -- Fractional parts are precisely the coefficients for adjacent-floor interpolation.
    constructor
    · exact Int.fract_nonneg x
    · exact (Int.fract_lt_one x).le
  have hline : AffineMap.lineMap left right t = (x, y) := by
    apply Prod.ext
    · simp only [AffineMap.lineMap_apply_module, left, right, Prod.smul_fst,
        Prod.fst_add, smul_eq_mul, Int.cast_add, Int.cast_one]
      dsimp only [t]
      calc
        (1 - Int.fract x) * (⌊x⌋ : ℝ) + Int.fract x * ((⌊x⌋ : ℝ) + 1) =
            (⌊x⌋ : ℝ) + Int.fract x := by ring
        _ = x := Int.floor_add_fract x
    · simp only [AffineMap.lineMap_apply_module, left, right, Prod.smul_snd,
        Prod.snd_add, smul_eq_mul]
      dsimp only [t]
      ring
  have hsegment : AffineMap.lineMap left right t ∈ segment ℝ left right :=
    lineMap_mem_segment ℝ left right ht
  have hhull := segment_subset_convexHull hleftMem hrightMem hsegment
  rwa [hline] at hhull

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean`: every point satisfying
the three relaxation inequalities belongs to `convexHull ℝ (mixedIntegerStrip β)`. -/
private lemma mixedIntegerStripRelaxation_subset_convexHull (β : ℝ) :
    {p : ℝ × ℝ |
        p.1 - p.2 ≤ β ∧
          p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) ∧
          0 ≤ p.2} ⊆
      convexHull ℝ (integralFirstStrip β) := by
  -- Split at the two consecutive integer breakpoints of the lower envelope.
  rintro ⟨x, y⟩ ⟨hbase, hcut, hy⟩
  by_cases hleft : x ≤ (⌊β⌋ : ℝ)
  · exact mem_convexHull_mixedIntegerStrip_of_le_floor β x y hleft hy
  · have hfloor : (⌊β⌋ : ℝ) ≤ x := le_of_not_ge hleft
    by_cases hright : (⌊β⌋ : ℝ) + 1 ≤ x
    · exact mem_convexHull_mixedIntegerStrip_of_floor_add_one_le β x y hright hbase
    · have hceil : x ≤ (⌊β⌋ : ℝ) + 1 := le_of_not_ge hright
      exact mem_convexHull_mixedIntegerStrip_of_floor_interval β x y hfloor hceil hcut

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_1_proposition_1_5.lean.
Proposition 1.5.
The convex hull of the mixed-integer set
`{(x, y) | x ∈ ℤ, y ≥ 0, x - y ≤ β}` is cut out by the original inequality, nonnegativity of
`y`, and the mixed-integer cut with `f = Int.fract β`. -/
theorem convexHull_mixed_integer_strip_eq
    (β : ℝ) :
    convexHull ℝ
        {p : ℝ × ℝ |
          p.1 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) ∧
            0 ≤ p.2 ∧
            p.1 - p.2 ≤ β} =
      {p : ℝ × ℝ |
        p.1 - p.2 ≤ β ∧
          p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) ∧
          0 ≤ p.2} := by
  have hsource :
      {p : ℝ × ℝ |
          p.1 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) ∧
            0 ≤ p.2 ∧
            p.1 - p.2 ≤ β} =
        integralFirstStrip β := by
    -- Put the displayed generators into the canonical strip form used by the prior lemmas.
    ext p
    rfl
  rw [hsource]
  apply Set.Subset.antisymm
  · -- Validity of both strip inequalities and convexity give the forward inclusion.
    refine convexHull_min ?_ (convex_mixedIntegerStripRelaxation β)
    intro p hp
    have hmem := hp
    exact ⟨hmem.2.2, integralFirstStrip_cut_validOn β hp, hmem.2.1⟩
  · -- The three-region interpolation lemma supplies the reverse inclusion.
    exact mixedIntegerStripRelaxation_subset_convexHull β
