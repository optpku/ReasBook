/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part17

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Theorem 35.8: in a convex slice, a `⊥` value at the end of a positive ray from a
finite base point propagates to every shorter positive point on that same ray. -/
lemma helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
    {k : ℕ}
    {g : (Fin k → ℝ) → EReal} {c d : Fin k → ℝ} {t : ℝ}
    (hConv : ConvexFunction g)
    (hcFinite : g c ≠ (⊤ : EReal) ∧ g c ≠ (⊥ : EReal))
    (ht : 0 < t) (ht_le_one : t ≤ 1)
    (hEndBot : g (c + d) = (⊥ : EReal)) :
    g (c + t • d) = (⊥ : EReal) := by
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt g c d) (Set.Ioi (0 : ℝ)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear g hConv c hcFinite).1 d |>.1
  have hquotOne :
      directionalDifferenceQuotientAt g c d 1 = (⊥ : EReal) := by
    -- At `t = 1`, the quotient numerator already has the terminal `⊥` value.
    simp [directionalDifferenceQuotientAt, hEndBot, div_eq_mul_inv]
  have hquotLe :
      directionalDifferenceQuotientAt g c d t ≤
        directionalDifferenceQuotientAt g c d 1 :=
    hmono ht (by simpa using zero_lt_one) ht_le_one
  have hquotT :
      directionalDifferenceQuotientAt g c d t = (⊥ : EReal) := by
    -- Monotonicity forces every earlier positive quotient to coincide with the terminal `⊥`.
    refine le_antisymm ?_ ?_
    · exact le_trans hquotLe (by rw [hquotOne])
    · exact (bot_le : (⊥ : EReal) ≤ directionalDifferenceQuotientAt g c d t)
  have hsub :
      g (c + t • d) - g c = (⊥ : EReal) := by
    -- Multiply the quotient identity back by the positive scalar `t`.
    have hmul :
        (((t : ℝ) : EReal) * directionalDifferenceQuotientAt g c d t) = (⊥ : EReal) := by
      rw [hquotT]
      simp [EReal.coe_mul_bot_of_pos ht]
    have hmul' :
        (((t : ℝ) : EReal) * ((((t⁻¹ : ℝ) : EReal) * (g (c + t • d) - g c)))) = (⊥ : EReal) := by
      simpa [directionalDifferenceQuotientAt, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hmul
    calc
      g (c + t • d) - g c =
          (((t : ℝ) : EReal) * ((((t⁻¹ : ℝ) : EReal) * (g (c + t • d) - g c)))) := by
            symm
            simpa using
              (section13_mul_mul_inv_cancel_pos_real (a := t) ht (z := g (c + t • d) - g c))
      _ = (⊥ : EReal) := hmul'
  by_cases htop : g (c + t • d) = (⊤ : EReal)
  · -- A `⊤` value cannot produce the `⊥` numerator against a finite base value.
    have : False := by
      rw [htop, EReal.top_sub hcFinite.1] at hsub
      simpa using hsub
    exact this.elim
  · by_cases hbot : g (c + t • d) = (⊥ : EReal)
    · exact hbot
    · -- Any remaining finite value also contradicts the `⊥` numerator.
      lift g (c + t • d) to ℝ using ⟨htop, hbot⟩ with rt hrt
      lift g c to ℝ using hcFinite with rc hrc
      have : (((rt - rc : ℝ)) : EReal) = (⊥ : EReal) := by
        simpa [hrt, hrc] using hsub
      exact (EReal.coe_ne_bot (rt - rc) this).elim

/-- Helper for Theorem 35.8: shrinking a reflected checkerboard in the second coordinate preserves
the same alternating `⊤/⊥` pattern. -/
lemma helperForTheorem_35_8_reflectedSecondSlice_checkerboard_shrinks_along_short_ray
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ} {x : Fin m → ℝ} {y : Fin n → ℝ} {t : ℝ}
    (hxFinite : K x v ≠ (⊤ : EReal) ∧ K x v ≠ (⊥ : EReal))
    (hxRefFinite :
      K (2 • u - x) v ≠ (⊤ : EReal) ∧ K (2 • u - x) v ≠ (⊥ : EReal))
    (hChecker :
      (K x y = (⊤ : EReal) ∧
          K (2 • u - x) y = (⊥ : EReal) ∧
          K (2 • u - x) (2 • v - y) = (⊤ : EReal) ∧
          K x (2 • v - y) = (⊥ : EReal)) ∨
        (K x y = (⊥ : EReal) ∧
          K (2 • u - x) y = (⊤ : EReal) ∧
          K (2 • u - x) (2 • v - y) = (⊥ : EReal) ∧
          K x (2 • v - y) = (⊤ : EReal)))
    (ht : 0 < t) (ht_le_one : t ≤ 1) :
    let yPlus : Fin n → ℝ := v + t • (y - v)
    let yMinus : Fin n → ℝ := v - t • (y - v)
    (K x yPlus = (⊤ : EReal) ∧
          K (2 • u - x) yPlus = (⊥ : EReal) ∧
          K (2 • u - x) yMinus = (⊤ : EReal) ∧
          K x yMinus = (⊥ : EReal)) ∨
        (K x yPlus = (⊥ : EReal) ∧
          K (2 • u - x) yPlus = (⊤ : EReal) ∧
          K (2 • u - x) yMinus = (⊥ : EReal) ∧
          K x yMinus = (⊤ : EReal)) := by
  let yPlus : Fin n → ℝ := v + t • (y - v)
  let yMinus : Fin n → ℝ := v - t • (y - v)
  have hyMinusEq : yMinus = v + t • ((2 • v - y) - v) := by
    -- The shrunk reflected point is the same short ray taken toward `2 • v - y`.
    ext j
    simp [yMinus, sub_eq_add_neg, two_smul]
    ring
  have hMid : (1 / 2 : ℝ) • yMinus + (1 / 2 : ℝ) • yPlus = v := by
    -- The two shrunken second-coordinate points stay symmetric around `v`.
    ext j
    simp [yPlus, yMinus, sub_eq_add_neg]
    ring
  rcases hChecker with hTop | hBot
  · rcases hTop with ⟨hxyTop, hxRefyBot, hxRefyRefTop, hxyRefBot⟩
    let gRef : (Fin n → ℝ) → EReal := K (2 • u - x)
    have hxRefyPlusBot : gRef yPlus = (⊥ : EReal) := by
      -- The `⊥` endpoint at `y` propagates down the short ray toward `v`.
      have hEndBot : gRef (v + (y - v)) = (⊥ : EReal) := by
        simpa [gRef] using hxRefyBot
      simpa [gRef, yPlus] using
        helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
          (g := gRef) (c := v) (d := y - v) (t := t)
          (hConv := hK.2 (2 • u - x)) (hcFinite := hxRefFinite) ht ht_le_one hEndBot
    let g : (Fin n → ℝ) → EReal := K x
    have hxyMinusBot : g yMinus = (⊥ : EReal) := by
      -- The reflected `⊥` endpoint contracts in the same way.
      have hEndBot : g (v + ((2 • v - y) - v)) = (⊥ : EReal) := by
        simpa [g, sub_eq_add_neg, two_smul] using hxyRefBot
      simpa [g, hyMinusEq] using
        helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
          (g := g) (c := v) (d := (2 • v - y) - v) (t := t)
          (hConv := hK.2 x) (hcFinite := hxFinite) ht ht_le_one hEndBot
    have hxyPlusTop : K x yPlus = (⊤ : EReal) := by
      -- Once the lower reflected corner is `⊥`, midpoint finiteness forces the opposite corner to
      -- stay `⊤`.
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := g) (x := yMinus) (y := yPlus) (m := v)
        (hConv := hK.2 x) (hMid := hMid) (hmNeBot := hxFinite.2) (hxBot := hxyMinusBot)
      simpa [g] using this
    have hxRefyMinusTop : K (2 • u - x) yMinus = (⊤ : EReal) := by
      -- The same midpoint argument on the reflected first-coordinate slice recovers the final
      -- `⊤` corner.
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := gRef) (x := yPlus) (y := yMinus) (m := v)
        (hConv := hK.2 (2 • u - x)) (hMid := by simpa [add_comm] using hMid)
        (hmNeBot := hxRefFinite.2) (hxBot := hxRefyPlusBot)
      simpa [gRef] using this
    exact Or.inl ⟨hxyPlusTop, by simpa [gRef] using hxRefyPlusBot, hxRefyMinusTop,
      by simpa [g] using hxyMinusBot⟩
  · rcases hBot with ⟨hxyBot, hxRefyTop, hxRefyRefBot, hxyRefTop⟩
    let g : (Fin n → ℝ) → EReal := K x
    have hxyPlusBot : g yPlus = (⊥ : EReal) := by
      -- In the bottom-corner branch the short ray starts from `K x y = ⊥`.
      have hEndBot : g (v + (y - v)) = (⊥ : EReal) := by
        simpa [g] using hxyBot
      simpa [g, yPlus] using
        helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
          (g := g) (c := v) (d := y - v) (t := t)
          (hConv := hK.2 x) (hcFinite := hxFinite) ht ht_le_one hEndBot
    let gRef : (Fin n → ℝ) → EReal := K (2 • u - x)
    have hxRefyMinusBot : gRef yMinus = (⊥ : EReal) := by
      -- The reflected bottom endpoint behaves symmetrically.
      have hEndBot : gRef (v + ((2 • v - y) - v)) = (⊥ : EReal) := by
        simpa [gRef, sub_eq_add_neg, two_smul] using hxRefyRefBot
      simpa [gRef, hyMinusEq] using
        helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
          (g := gRef) (c := v) (d := (2 • v - y) - v) (t := t)
          (hConv := hK.2 (2 • u - x)) (hcFinite := hxRefFinite) ht ht_le_one hEndBot
    have hxRefyPlusTop : K (2 • u - x) yPlus = (⊤ : EReal) := by
      -- Midpoint finiteness across the reflected pair recovers the top corner.
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := gRef) (x := yMinus) (y := yPlus) (m := v)
        (hConv := hK.2 (2 • u - x)) (hMid := hMid) (hmNeBot := hxRefFinite.2)
        (hxBot := hxRefyMinusBot)
      simpa [gRef] using this
    have hxyMinusTop : K x yMinus = (⊤ : EReal) := by
      -- The non-reflected slice closes the second branch in the same way.
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := g) (x := yPlus) (y := yMinus) (m := v)
        (hConv := hK.2 x) (hMid := by simpa [add_comm] using hMid)
        (hmNeBot := hxFinite.2) (hxBot := hxyPlusBot)
      simpa [g] using this
    exact Or.inr ⟨by simpa [g] using hxyPlusBot, hxRefyPlusTop,
      by simpa [gRef] using hxRefyMinusBot, hxyMinusTop⟩

/-- Helper for Theorem 35.8: shrinking a reflected checkerboard in the first coordinate preserves
the same alternating `⊤/⊥` pattern. -/
lemma helperForTheorem_35_8_reflectedFirstSlice_checkerboard_shrinks_along_short_ray
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {x : Fin m → ℝ} {yPlus yMinus : Fin n → ℝ} {s : ℝ}
    (hyPlusFinite : K u yPlus ≠ (⊤ : EReal) ∧ K u yPlus ≠ (⊥ : EReal))
    (hyMinusFinite : K u yMinus ≠ (⊤ : EReal) ∧ K u yMinus ≠ (⊥ : EReal))
    (hChecker :
      (K x yPlus = (⊤ : EReal) ∧
          K (2 • u - x) yPlus = (⊥ : EReal) ∧
          K (2 • u - x) yMinus = (⊤ : EReal) ∧
          K x yMinus = (⊥ : EReal)) ∨
        (K x yPlus = (⊥ : EReal) ∧
          K (2 • u - x) yPlus = (⊤ : EReal) ∧
          K (2 • u - x) yMinus = (⊥ : EReal) ∧
          K x yMinus = (⊤ : EReal)))
    (hs : 0 < s) (hs_le_one : s ≤ 1) :
    let xPlus : Fin m → ℝ := u + s • (x - u)
    let xMinus : Fin m → ℝ := u - s • (x - u)
    (K xPlus yPlus = (⊤ : EReal) ∧
          K xMinus yPlus = (⊥ : EReal) ∧
          K xMinus yMinus = (⊤ : EReal) ∧
          K xPlus yMinus = (⊥ : EReal)) ∨
        (K xPlus yPlus = (⊥ : EReal) ∧
          K xMinus yPlus = (⊤ : EReal) ∧
          K xMinus yMinus = (⊥ : EReal) ∧
          K xPlus yMinus = (⊤ : EReal)) := by
  let xPlus : Fin m → ℝ := u + s • (x - u)
  let xMinus : Fin m → ℝ := u - s • (x - u)
  have hxMinusEq : xMinus = u + s • ((2 • u - x) - u) := by
    -- The shrunk reflected first-coordinate point is the same short ray toward `2 • u - x`.
    ext i
    simp [xMinus, sub_eq_add_neg, two_smul]
    ring
  have hMid : (1 / 2 : ℝ) • xPlus + (1 / 2 : ℝ) • xMinus = u := by
    -- The two shrunken first-coordinate points stay symmetric around `u`.
    ext i
    simp [xPlus, xMinus, sub_eq_add_neg]
    ring
  rcases hChecker with hTop | hBot
  · rcases hTop with ⟨hxyPlusTop, hxRefyPlusBot, hxRefyMinusTop, hxyMinusBot⟩
    let gPlus : (Fin m → ℝ) → EReal := fun z => -K z yPlus
    have hxPlusTop : K xPlus yPlus = (⊤ : EReal) := by
      -- The top endpoint on the `yPlus` slice propagates inward through the reflected convex
      -- function `z ↦ -K z yPlus`.
      have hEndBot : gPlus (u + (x - u)) = (⊥ : EReal) := by
        simpa [gPlus] using hxyPlusTop
      have hxPlusBot :
          gPlus xPlus = (⊥ : EReal) := by
        simpa [gPlus, xPlus] using
          helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
            (g := gPlus) (c := u) (d := x - u) (t := s)
            (hConv := hK.1 yPlus)
            (hcFinite := by
              exact ⟨by simpa [gPlus] using hyPlusFinite.2, by simpa [gPlus] using hyPlusFinite.1⟩)
            hs hs_le_one hEndBot
      simpa [gPlus] using hxPlusBot
    have hxMinusBot : K xMinus yPlus = (⊥ : EReal) := by
      -- Midpoint finiteness across the `yPlus` slice recovers the opposite lower corner.
      have hxPlusBot : gPlus xPlus = (⊥ : EReal) := by
        simpa [gPlus] using hxPlusTop
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := gPlus) (x := xPlus) (y := xMinus) (m := u)
        (hConv := hK.1 yPlus) (hMid := hMid)
        (hmNeBot := by simpa [gPlus] using hyPlusFinite.1) (hxBot := hxPlusBot)
      simpa [gPlus] using this
    let gMinus : (Fin m → ℝ) → EReal := fun z => -K z yMinus
    have hxMinusTop : K xMinus yMinus = (⊤ : EReal) := by
      -- The reflected top endpoint on the `yMinus` slice contracts from `2 • u - x`.
      have hEndBot : gMinus (u + ((2 • u - x) - u)) = (⊥ : EReal) := by
        simpa [gMinus, sub_eq_add_neg, two_smul] using hxRefyMinusTop
      have hxMinusBot :
          gMinus xMinus = (⊥ : EReal) := by
        simpa [gMinus, hxMinusEq] using
          helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
            (g := gMinus) (c := u) (d := (2 • u - x) - u) (t := s)
            (hConv := hK.1 yMinus)
            (hcFinite := by
              exact ⟨by simpa [gMinus] using hyMinusFinite.2,
                by simpa [gMinus] using hyMinusFinite.1⟩)
            hs hs_le_one hEndBot
      simpa [gMinus] using hxMinusBot
    have hxPlusBot' : K xPlus yMinus = (⊥ : EReal) := by
      -- The midpoint argument closes the second row of the checkerboard.
      have hxMinusBot : gMinus xMinus = (⊥ : EReal) := by
        simpa [gMinus] using hxMinusTop
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := gMinus) (x := xMinus) (y := xPlus) (m := u)
        (hConv := hK.1 yMinus) (hMid := by simpa [add_comm] using hMid)
        (hmNeBot := by simpa [gMinus] using hyMinusFinite.1) (hxBot := hxMinusBot)
      simpa [gMinus] using this
    exact Or.inl ⟨hxPlusTop, hxMinusBot, hxMinusTop, hxPlusBot'⟩
  · rcases hBot with ⟨hxyPlusBot, hxRefyPlusTop, hxRefyMinusBot, hxyMinusTop⟩
    let gPlus : (Fin m → ℝ) → EReal := fun z => -K z yPlus
    have hxPlusBot : K xPlus yPlus = (⊥ : EReal) := by
      -- In the bottom-corner branch the reflected top endpoint now lies at `2 • u - x`.
      have hEndBot : gPlus (u + ((2 • u - x) - u)) = (⊥ : EReal) := by
        simpa [gPlus, sub_eq_add_neg, two_smul] using hxRefyPlusTop
      have hxMinusTop :
          gPlus xMinus = (⊥ : EReal) := by
        simpa [gPlus, hxMinusEq] using
          helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
            (g := gPlus) (c := u) (d := (2 • u - x) - u) (t := s)
            (hConv := hK.1 yPlus)
            (hcFinite := by
              exact ⟨by simpa [gPlus] using hyPlusFinite.2, by simpa [gPlus] using hyPlusFinite.1⟩)
            hs hs_le_one hEndBot
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := gPlus) (x := xMinus) (y := xPlus) (m := u)
        (hConv := hK.1 yPlus) (hMid := by simpa [add_comm] using hMid)
        (hmNeBot := by simpa [gPlus] using hyPlusFinite.1) (hxBot := hxMinusTop)
      simpa [gPlus] using this
    have hxMinusTop : K xMinus yPlus = (⊤ : EReal) := by
      -- The reflected top value itself already propagated to `xMinus`.
      let gPlus : (Fin m → ℝ) → EReal := fun z => -K z yPlus
      have hEndBot : gPlus (u + ((2 • u - x) - u)) = (⊥ : EReal) := by
        simpa [gPlus, sub_eq_add_neg, two_smul] using hxRefyPlusTop
      have hxMinusBot :
          gPlus xMinus = (⊥ : EReal) := by
        simpa [gPlus, hxMinusEq] using
          helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
            (g := gPlus) (c := u) (d := (2 • u - x) - u) (t := s)
            (hConv := hK.1 yPlus)
            (hcFinite := by
              exact ⟨by simpa [gPlus] using hyPlusFinite.2, by simpa [gPlus] using hyPlusFinite.1⟩)
            hs hs_le_one hEndBot
      simpa [gPlus] using hxMinusBot
    let gMinus : (Fin m → ℝ) → EReal := fun z => -K z yMinus
    have hxMinusBot : K xMinus yMinus = (⊥ : EReal) := by
      -- The `⊥` endpoint at `x` on the `yMinus` row propagates directly to `xPlus`.
      have hEndBot : gMinus (u + (x - u)) = (⊥ : EReal) := by
        simpa [gMinus] using hxyMinusTop
      have hxPlusBot :
          gMinus xPlus = (⊥ : EReal) := by
        simpa [gMinus, xPlus] using
          helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
            (g := gMinus) (c := u) (d := x - u) (t := s)
            (hConv := hK.1 yMinus)
            (hcFinite := by
              exact ⟨by simpa [gMinus] using hyMinusFinite.2,
                by simpa [gMinus] using hyMinusFinite.1⟩)
            hs hs_le_one hEndBot
      have := helperForTheorem_35_8_midpointFinite_leftBot_forces_rightTop
        (g := gMinus) (x := xPlus) (y := xMinus) (m := u)
        (hConv := hK.1 yMinus) (hMid := hMid)
        (hmNeBot := by simpa [gMinus] using hyMinusFinite.1) (hxBot := hxPlusBot)
      simpa [gMinus] using this
    have hxPlusTop : K xPlus yMinus = (⊤ : EReal) := by
      -- The same short-ray propagation on the `yMinus` row keeps the top corner on the near side.
      let gMinus : (Fin m → ℝ) → EReal := fun z => -K z yMinus
      have hEndBot : gMinus (u + (x - u)) = (⊥ : EReal) := by
        simpa [gMinus] using hxyMinusTop
      have hxPlusBot :
          gMinus xPlus = (⊥ : EReal) := by
        simpa [gMinus, xPlus] using
          helperForTheorem_35_8_convexSlice_bot_propagates_along_short_ray
            (g := gMinus) (c := u) (d := x - u) (t := s)
            (hConv := hK.1 yMinus)
            (hcFinite := by
              exact ⟨by simpa [gMinus] using hyMinusFinite.2,
                by simpa [gMinus] using hyMinusFinite.1⟩)
            hs hs_le_one hEndBot
      simpa [gMinus] using hxPlusBot
    exact Or.inr ⟨hxPlusBot, hxMinusTop, hxMinusBot, hxPlusTop⟩

/-- Helper for Theorem 35.8: sufficiently small reflected pairs stay inside the chosen slice
neighborhoods around `(u, v)`. -/
lemma helperForTheorem_35_8_small_reflected_pair_mem_slice_neighborhoods
    {m n : ℕ}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {x : Fin m → ℝ} {y : Fin n → ℝ}
    {C0 : Set (Fin m → ℝ)} {D0 : Set (Fin n → ℝ)}
    (hC0open : IsOpen C0) (huC0 : u ∈ C0)
    (hD0open : IsOpen D0) (hvD0 : v ∈ D0) :
    ∃ s t : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 < t ∧ t ≤ 1 ∧
        u + s • (x - u) ∈ C0 ∧
        u - s • (x - u) ∈ C0 ∧
        v + t • (y - v) ∈ D0 ∧
        v - t • (y - v) ∈ D0 := by
  rcases Metric.mem_nhds_iff.mp (hC0open.mem_nhds huC0) with ⟨εC, hεC, hBallC⟩
  rcases Metric.mem_nhds_iff.mp (hD0open.mem_nhds hvD0) with ⟨εD, hεD, hBallD⟩
  let s : ℝ := min 1 (εC / (2 * (‖x - u‖ + 1)))
  let t : ℝ := min 1 (εD / (2 * (‖y - v‖ + 1)))
  have hs_pos_raw : 0 < εC / (2 * (‖x - u‖ + 1)) := by
    positivity
  have ht_pos_raw : 0 < εD / (2 * (‖y - v‖ + 1)) := by
    positivity
  have hs_pos : 0 < s := by
    exact lt_min zero_lt_one hs_pos_raw
  have ht_pos : 0 < t := by
    exact lt_min zero_lt_one ht_pos_raw
  have hs_le_one : s ≤ 1 := min_le_left _ _
  have ht_le_one : t ≤ 1 := min_le_left _ _
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hxPlusMem : u + s • (x - u) ∈ C0 := by
    -- The explicit small parameter keeps the positive short-ray point inside the first slice ball.
    have hs_mul :
        s * (‖x - u‖ + 1) ≤ εC / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right (min_le_right 1 (εC / (2 * (‖x - u‖ + 1))))
          (by positivity : 0 ≤ ‖x - u‖ + 1)
      have hEq :
          (εC / (2 * (‖x - u‖ + 1))) * (‖x - u‖ + 1) = εC / 2 := by
        field_simp [show (‖x - u‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have hs_norm :
        ‖(u + s • (x - u)) - u‖ < εC := by
      calc
        ‖(u + s • (x - u)) - u‖ = ‖s • (x - u)‖ := by
          congr 1
          ext i
          simp [sub_eq_add_neg]
          ring
        _ = |s| * ‖x - u‖ := norm_smul s (x - u)
        _ = s * ‖x - u‖ := by simp [abs_of_nonneg hs_nonneg]
        _ ≤ s * (‖x - u‖ + 1) := by
          nlinarith [norm_nonneg (x - u), hs_nonneg]
        _ ≤ εC / 2 := hs_mul
        _ < εC := by linarith
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm] using hs_norm)
  have hxMinusMem : u - s • (x - u) ∈ C0 := by
    -- The reflected short-ray point has the same distance bound.
    have hs_mul :
        s * (‖x - u‖ + 1) ≤ εC / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right (min_le_right 1 (εC / (2 * (‖x - u‖ + 1))))
          (by positivity : 0 ≤ ‖x - u‖ + 1)
      have hEq :
          (εC / (2 * (‖x - u‖ + 1))) * (‖x - u‖ + 1) = εC / 2 := by
        field_simp [show (‖x - u‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have hs_norm :
        ‖(u - s • (x - u)) - u‖ < εC := by
      calc
        ‖(u - s • (x - u)) - u‖ = ‖-(s • (x - u))‖ := by
          simpa [sub_eq_add_neg]
        _ = ‖s • (x - u)‖ := by rw [norm_neg]
        _ = |s| * ‖x - u‖ := norm_smul s (x - u)
        _ = s * ‖x - u‖ := by simp [abs_of_nonneg hs_nonneg]
        _ ≤ s * (‖x - u‖ + 1) := by
          nlinarith [norm_nonneg (x - u), hs_nonneg]
        _ ≤ εC / 2 := hs_mul
        _ < εC := by linarith
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm] using hs_norm)
  have hyPlusMem : v + t • (y - v) ∈ D0 := by
    -- The same quantitative estimate works in the second coordinate.
    have ht_mul :
        t * (‖y - v‖ + 1) ≤ εD / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right (min_le_right 1 (εD / (2 * (‖y - v‖ + 1))))
          (by positivity : 0 ≤ ‖y - v‖ + 1)
      have hEq :
          (εD / (2 * (‖y - v‖ + 1))) * (‖y - v‖ + 1) = εD / 2 := by
        field_simp [show (‖y - v‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have ht_norm :
        ‖(v + t • (y - v)) - v‖ < εD := by
      calc
        ‖(v + t • (y - v)) - v‖ = ‖t • (y - v)‖ := by
          congr 1
          ext j
          simp [sub_eq_add_neg]
          ring
        _ = |t| * ‖y - v‖ := norm_smul t (y - v)
        _ = t * ‖y - v‖ := by simp [abs_of_nonneg ht_nonneg]
        _ ≤ t * (‖y - v‖ + 1) := by
          nlinarith [norm_nonneg (y - v), ht_nonneg]
        _ ≤ εD / 2 := ht_mul
        _ < εD := by linarith
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm] using ht_norm)
  have hyMinusMem : v - t • (y - v) ∈ D0 := by
    -- Reflection leaves the same norm estimate on the second-coordinate short ray.
    have ht_mul :
        t * (‖y - v‖ + 1) ≤ εD / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right (min_le_right 1 (εD / (2 * (‖y - v‖ + 1))))
          (by positivity : 0 ≤ ‖y - v‖ + 1)
      have hEq :
          (εD / (2 * (‖y - v‖ + 1))) * (‖y - v‖ + 1) = εD / 2 := by
        field_simp [show (‖y - v‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have ht_norm :
        ‖(v - t • (y - v)) - v‖ < εD := by
      calc
        ‖(v - t • (y - v)) - v‖ = ‖-(t • (y - v))‖ := by
          simpa [sub_eq_add_neg]
        _ = ‖t • (y - v)‖ := by rw [norm_neg]
        _ = |t| * ‖y - v‖ := norm_smul t (y - v)
        _ = t * ‖y - v‖ := by simp [abs_of_nonneg ht_nonneg]
        _ ≤ t * (‖y - v‖ + 1) := by
          nlinarith [norm_nonneg (y - v), ht_nonneg]
        _ ≤ εD / 2 := ht_mul
        _ < εD := by linarith
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm] using ht_norm)
  exact ⟨s, t, hs_pos, hs_le_one, ht_pos, ht_le_one, hxPlusMem, hxMinusMem, hyPlusMem,
    hyMinusMem⟩

/-- Helper for Theorem 35.8: the independent slice-neighborhood shrink parameters can be replaced
by a single common step that keeps both reflected pairs inside the chosen neighborhoods. -/
lemma helperForTheorem_35_8_common_small_reflected_pair_mem_slice_neighborhoods
    {m n : ℕ}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {x : Fin m → ℝ} {y : Fin n → ℝ}
    {C0 : Set (Fin m → ℝ)} {D0 : Set (Fin n → ℝ)}
    (hC0open : IsOpen C0) (huC0 : u ∈ C0)
    (hD0open : IsOpen D0) (hvD0 : v ∈ D0) :
    ∃ r : ℝ,
      0 < r ∧ r ≤ 1 ∧
        u + r • (x - u) ∈ C0 ∧
        u - r • (x - u) ∈ C0 ∧
        v + r • (y - v) ∈ D0 ∧
        v - r • (y - v) ∈ D0 := by
  rcases Metric.mem_nhds_iff.mp (hC0open.mem_nhds huC0) with ⟨εC, hεC, hBallC⟩
  rcases Metric.mem_nhds_iff.mp (hD0open.mem_nhds hvD0) with ⟨εD, hεD, hBallD⟩
  let r : ℝ := min 1 (min (εC / (2 * (‖x - u‖ + 1))) (εD / (2 * (‖y - v‖ + 1))))
  have hr_pos_rawC : 0 < εC / (2 * (‖x - u‖ + 1)) := by positivity
  have hr_pos_rawD : 0 < εD / (2 * (‖y - v‖ + 1)) := by positivity
  have hr_pos : 0 < r := by
    refine lt_min zero_lt_one ?_
    exact lt_min hr_pos_rawC hr_pos_rawD
  have hr_le_one : r ≤ 1 := min_le_left _ _
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_le_C : r ≤ εC / (2 * (‖x - u‖ + 1)) := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_D : r ≤ εD / (2 * (‖y - v‖ + 1)) := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hxPlusMem : u + r • (x - u) ∈ C0 := by
    -- The common short step keeps the first positive ray point inside the `u`-ball in `C0`.
    have hr_mul :
        r * (‖x - u‖ + 1) ≤ εC / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hr_le_C (by positivity : 0 ≤ ‖x - u‖ + 1)
      have hEq :
          (εC / (2 * (‖x - u‖ + 1))) * (‖x - u‖ + 1) = εC / 2 := by
        field_simp [show (‖x - u‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have hr_norm :
        ‖(u + r • (x - u)) - u‖ < εC := by
      calc
        ‖(u + r • (x - u)) - u‖ = ‖r • (x - u)‖ := by
          congr 1
          ext i
          simp [sub_eq_add_neg]
          ring
        _ = |r| * ‖x - u‖ := norm_smul r (x - u)
        _ = r * ‖x - u‖ := by simp [abs_of_nonneg hr_nonneg]
        _ ≤ r * (‖x - u‖ + 1) := by
          nlinarith [norm_nonneg (x - u), hr_nonneg]
        _ ≤ εC / 2 := hr_mul
        _ < εC := by linarith
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm] using hr_norm)
  have hxMinusMem : u - r • (x - u) ∈ C0 := by
    -- The reflected first-coordinate point satisfies the same norm estimate.
    have hr_mul :
        r * (‖x - u‖ + 1) ≤ εC / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hr_le_C (by positivity : 0 ≤ ‖x - u‖ + 1)
      have hEq :
          (εC / (2 * (‖x - u‖ + 1))) * (‖x - u‖ + 1) = εC / 2 := by
        field_simp [show (‖x - u‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have hr_norm :
        ‖(u - r • (x - u)) - u‖ < εC := by
      calc
        ‖(u - r • (x - u)) - u‖ = ‖-(r • (x - u))‖ := by
          simpa [sub_eq_add_neg]
        _ = ‖r • (x - u)‖ := by rw [norm_neg]
        _ = |r| * ‖x - u‖ := norm_smul r (x - u)
        _ = r * ‖x - u‖ := by simp [abs_of_nonneg hr_nonneg]
        _ ≤ r * (‖x - u‖ + 1) := by
          nlinarith [norm_nonneg (x - u), hr_nonneg]
        _ ≤ εC / 2 := hr_mul
        _ < εC := by linarith
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm] using hr_norm)
  have hyPlusMem : v + r • (y - v) ∈ D0 := by
    -- The same common step keeps the second positive ray point inside the `v`-ball in `D0`.
    have hr_mul :
        r * (‖y - v‖ + 1) ≤ εD / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hr_le_D (by positivity : 0 ≤ ‖y - v‖ + 1)
      have hEq :
          (εD / (2 * (‖y - v‖ + 1))) * (‖y - v‖ + 1) = εD / 2 := by
        field_simp [show (‖y - v‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have hr_norm :
        ‖(v + r • (y - v)) - v‖ < εD := by
      calc
        ‖(v + r • (y - v)) - v‖ = ‖r • (y - v)‖ := by
          congr 1
          ext j
          simp [sub_eq_add_neg]
          ring
        _ = |r| * ‖y - v‖ := norm_smul r (y - v)
        _ = r * ‖y - v‖ := by simp [abs_of_nonneg hr_nonneg]
        _ ≤ r * (‖y - v‖ + 1) := by
          nlinarith [norm_nonneg (y - v), hr_nonneg]
        _ ≤ εD / 2 := hr_mul
        _ < εD := by linarith
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm] using hr_norm)
  have hyMinusMem : v - r • (y - v) ∈ D0 := by
    -- Reflection preserves the same second-coordinate norm estimate.
    have hr_mul :
        r * (‖y - v‖ + 1) ≤ εD / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hr_le_D (by positivity : 0 ≤ ‖y - v‖ + 1)
      have hEq :
          (εD / (2 * (‖y - v‖ + 1))) * (‖y - v‖ + 1) = εD / 2 := by
        field_simp [show (‖y - v‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq] using hmul
    have hr_norm :
        ‖(v - r • (y - v)) - v‖ < εD := by
      calc
        ‖(v - r • (y - v)) - v‖ = ‖-(r • (y - v))‖ := by
          simpa [sub_eq_add_neg]
        _ = ‖r • (y - v)‖ := by rw [norm_neg]
        _ = |r| * ‖y - v‖ := norm_smul r (y - v)
        _ = r * ‖y - v‖ := by simp [abs_of_nonneg hr_nonneg]
        _ ≤ r * (‖y - v‖ + 1) := by
          nlinarith [norm_nonneg (y - v), hr_nonneg]
        _ ≤ εD / 2 := hr_mul
        _ < εD := by linarith
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm] using hr_norm)
  exact ⟨r, hr_pos, hr_le_one, hxPlusMem, hxMinusMem, hyPlusMem, hyMinusMem⟩

/-- Helper for Theorem 35.8: in a convex slice neighborhood, once one point on a ray from the
center is known to lie in the set, every shorter point on the same ray lies there as well. -/
lemma helperForTheorem_35_8_shorter_ray_mem_of_convex
    {k : ℕ}
    {C : Set (Fin k → ℝ)} {u d : Fin k → ℝ} {r s : ℝ}
    (hCconv : Convex ℝ C) (hu : u ∈ C) (hRay : u + r • d ∈ C)
    (hr_nonneg : 0 ≤ r) (hs_nonneg : 0 ≤ s) (hs_le : s ≤ r) :
    u + s • d ∈ C := by
  by_cases hr0 : r = 0
  · have hs0 : s = 0 := le_antisymm (by simpa [hr0] using hs_le) hs_nonneg
    -- If the longer ray point is just the center, the shorter point is also the center.
    simpa [hs0] using hu
  · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
    let t : ℝ := s / r
    have ht_nonneg : 0 ≤ t := by
      -- The reparameterization factor from the long step to the short step is nonnegative.
      exact div_nonneg hs_nonneg hr_nonneg
    have ht_le_one : t ≤ 1 := by
      -- The reparameterized step satisfies `t * r = s`, so `s ≤ r` becomes `t ≤ 1`.
      have hmul : t * r = s := by
        change (s / r) * r = s
        field_simp [hr0]
      nlinarith [hs_le, hmul, hr_pos]
    have hCombo : (1 - t) • u + t • (u + r • d) ∈ C := by
      -- Convexity keeps the entire segment from the center to the longer ray point inside `C`.
      refine hCconv hu hRay ?_ ?_ ?_
      · exact sub_nonneg.mpr ht_le_one
      · exact ht_nonneg
      · ring
    have hEq : (1 - t) • u + t • (u + r • d) = u + s • d := by
      -- This convex combination is exactly the shorter ray point.
      ext i
      simp [t, smul_add, Pi.add_apply, Pi.smul_apply]
      field_simp [hr0]
      ring
    rw [hEq] at hCombo
    exact hCombo

/-- Helper for Theorem 35.8: interior membership in the saddle effective domain yields an open
convex rectangle around `(u, v)` on which `K` stays finite. -/
lemma helperForTheorem_35_8_openConvexFiniteRectangle_of_jointInterior
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hInterior : (u, v) ∈ interior (saddleFunctionEffectiveDomain K)) :
    ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
      IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
      IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
          ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal) := by
  rcases
      helperForText_35_5_5_exists_ball_subset_effectiveDomain
        (K := K) (u := u) (v := v) hInterior with
    ⟨ε, hε, hBallSubset⟩
  let C : Set (Fin m → ℝ) := Metric.ball u ε
  let D : Set (Fin n → ℝ) := Metric.ball v ε
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The first coordinate neighborhood is the open ball around `u`.
    simpa [C] using isOpen_ball
  · -- The center belongs to its positive-radius ball.
    simpa [C, Metric.mem_ball] using hε
  · -- Balls are convex in Euclidean spaces.
    simpa [C] using convex_ball u ε
  · -- The second coordinate neighborhood is the matching ball around `v`.
    simpa [D] using isOpen_ball
  · -- Its center also belongs to the ball.
    simpa [D, Metric.mem_ball] using hε
  · -- This ball is convex as well.
    simpa [D] using convex_ball v ε
  · intro u' hu' v' hv'
    -- Combine the two coordinate ball conditions into membership in the product ball around `(u,v)`.
    have huDist : dist u' u < ε := by
      simpa [C, Metric.mem_ball] using hu'
    have hvDist : dist v' v < ε := by
      simpa [D, Metric.mem_ball] using hv'
    have hPairMem : (u', v') ∈ Metric.ball (u, v) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt huDist hvDist
    -- The product ball was chosen inside the effective domain.
    exact hBallSubset hPairMem

/-- Helper for Theorem 35.8: once the reflected checkerboard is shrunk with a common parameter,
its first corner is already an explicit mixed saddle secant quotient equal to `⊤` or `⊥`. -/
lemma helperForTheorem_35_8_checkerboardForcesInfiniteMixedQuotient_afterCommonShrink
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {x : Fin m → ℝ} {y : Fin n → ℝ}
    {r : ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hr : 0 < r)
    (hChecker :
      let xPlus : Fin m → ℝ := u + r • (x - u)
      let xMinus : Fin m → ℝ := u - r • (x - u)
      let yPlus : Fin n → ℝ := v + r • (y - v)
      let yMinus : Fin n → ℝ := v - r • (y - v)
      (K xPlus yPlus = (⊤ : EReal) ∧
            K xMinus yPlus = (⊥ : EReal) ∧
            K xMinus yMinus = (⊤ : EReal) ∧
            K xPlus yMinus = (⊥ : EReal)) ∨
          (K xPlus yPlus = (⊥ : EReal) ∧
            K xMinus yPlus = (⊤ : EReal) ∧
            K xMinus yMinus = (⊥ : EReal) ∧
            K xPlus yMinus = (⊤ : EReal))) :
    saddleDirectionalDifferenceQuotientAt K u v (x - u) (y - v) r = (⊤ : EReal) ∨
      saddleDirectionalDifferenceQuotientAt K u v (x - u) (y - v) r = (⊥ : EReal) := by
  let xPlus : Fin m → ℝ := u + r • (x - u)
  let yPlus : Fin n → ℝ := v + r • (y - v)
  rcases hChecker with hTop | hBot
  · -- In the top-corner branch the mixed secant numerator is immediately `⊤`.
    left
    have hInvPos : (0 : EReal) < (((r⁻¹ : ℝ)) : EReal) := by
      exact_mod_cast inv_pos.mpr hr
    calc
      saddleDirectionalDifferenceQuotientAt K u v (x - u) (y - v) r =
          ((K xPlus yPlus - K u v) / (r : EReal)) := by
            simp [saddleDirectionalDifferenceQuotientAt, xPlus, yPlus]
      _ = (⊤ : EReal) := by
        rw [hTop.1, EReal.top_sub hFinite.1, div_eq_mul_inv]
        simpa [EReal.coe_inv] using (EReal.top_mul_of_pos hInvPos)
  · -- In the bottom-corner branch the same quotient is `⊥`.
    right
    have hInvPos : (0 : EReal) < (((r⁻¹ : ℝ)) : EReal) := by
      exact_mod_cast inv_pos.mpr hr
    calc
      saddleDirectionalDifferenceQuotientAt K u v (x - u) (y - v) r =
          ((K xPlus yPlus - K u v) / (r : EReal)) := by
            simp [saddleDirectionalDifferenceQuotientAt, xPlus, yPlus]
      _ = (⊥ : EReal) := by
        have hNumBot : K xPlus yPlus - K u v = (⊥ : EReal) := by
          simp [xPlus, yPlus, hBot.1, hFinite.2]
        rw [hNumBot, div_eq_mul_inv, mul_comm]
        simpa [EReal.coe_inv] using (EReal.mul_bot_of_pos hInvPos)

/-- Helper for Theorem 35.8: once both the base value and the moved mixed corner are finite, the
corresponding mixed directional quotient at a positive step cannot be `⊤` or `⊥`. -/
lemma helperForTheorem_35_8_mixedQuotient_ne_top_or_bot_of_finiteMovedCorner
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uDir : Fin m → ℝ} {vDir : Fin n → ℝ}
    {r : ℝ}
    (hr : 0 < r)
    (hBase : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hMoved :
      K (u + r • uDir) (v + r • vDir) ≠ (⊤ : EReal) ∧
        K (u + r • uDir) (v + r • vDir) ≠ (⊥ : EReal)) :
    saddleDirectionalDifferenceQuotientAt K u v uDir vDir r ≠ (⊤ : EReal) ∧
      saddleDirectionalDifferenceQuotientAt K u v uDir vDir r ≠ (⊥ : EReal) := by
  let moved : EReal := K (u + r • uDir) (v + r • vDir)
  let base : EReal := K u v
  have hMoved' : moved ≠ (⊤ : EReal) ∧ moved ≠ (⊥ : EReal) := by
    simpa [moved] using hMoved
  have hBase' : base ≠ (⊤ : EReal) ∧ base ≠ (⊥ : EReal) := by
    simpa [base] using hBase
  rcases hMoved' with ⟨hMovedTop, hMovedBot⟩
  rcases hBase' with ⟨hBaseTop, hBaseBot⟩
  have hMovedReal : ((moved.toReal : ℝ) : EReal) = moved := by
    simpa using (EReal.coe_toReal hMovedTop hMovedBot)
  have hBaseReal : ((base.toReal : ℝ) : EReal) = base := by
    simpa using (EReal.coe_toReal hBaseTop hBaseBot)
  constructor
  · intro hTop
    have : ((((moved.toReal - base.toReal) / r : ℝ) : EReal)) = (⊤ : EReal) := by
      have hEq :
          saddleDirectionalDifferenceQuotientAt K u v uDir vDir r =
            ((((moved.toReal - base.toReal) / r : ℝ) : EReal)) := by
        change (moved - base) / (r : EReal) =
          ((((moved.toReal - base.toReal) / r : ℝ) : EReal))
        rw [← hMovedReal, ← hBaseReal]
        norm_num [EReal.coe_sub, hr.ne', EReal.coe_div]
      simpa [hEq] using hTop
    simp at this
  · intro hBot
    have : ((((moved.toReal - base.toReal) / r : ℝ) : EReal)) = (⊥ : EReal) := by
      have hEq :
          saddleDirectionalDifferenceQuotientAt K u v uDir vDir r =
            ((((moved.toReal - base.toReal) / r : ℝ) : EReal)) := by
        change (moved - base) / (r : EReal) =
          ((((moved.toReal - base.toReal) / r : ℝ) : EReal))
        rw [← hMovedReal, ← hBaseReal]
        norm_num [EReal.coe_sub, hr.ne', EReal.coe_div]
      simpa [hEq] using hBot
    simp at this

/-- Helper for Theorem 35.8: singleton slice data gives a uniform positive radius on which all
four reflected axis points along the directions `du` and `dv` stay finite. -/
lemma helperForTheorem_35_8_small_reflected_axis_finiteness_of_singletonSliceData
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (du : Fin m → ℝ) (dv : Fin n → ℝ)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar}) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t : ℝ, 0 < t → t < ρ →
        (K (u + t • du) v ≠ (⊤ : EReal) ∧ K (u + t • du) v ≠ (⊥ : EReal)) ∧
          (K (u - t • du) v ≠ (⊤ : EReal) ∧ K (u - t • du) v ≠ (⊥ : EReal)) ∧
            (K u (v + t • dv) ≠ (⊤ : EReal) ∧ K u (v + t • dv) ≠ (⊥ : EReal)) ∧
              (K u (v - t • dv) ≠ (⊤ : EReal) ∧ K u (v - t • dv) ≠ (⊥ : EReal)) := by
  rcases
      helperForTheorem_35_8_sliceFiniteNeighborhoods_of_singleton_partials
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFinite hFirstSingleton hSecondSingleton with
    ⟨C0, D0, hC0open, huC0, _hC0conv, hFirstFinite, hD0open, hvD0, _hD0conv, hSecondFinite⟩
  rcases Metric.mem_nhds_iff.mp (hC0open.mem_nhds huC0) with ⟨εC, hεC, hBallC⟩
  rcases Metric.mem_nhds_iff.mp (hD0open.mem_nhds hvD0) with ⟨εD, hεD, hBallD⟩
  let ρ : ℝ := min (εC / (‖du‖ + 1)) (εD / (‖dv‖ + 1))
  have hρpos : 0 < ρ := by
    -- Both coordinate radii stay positive after dividing by the positive norm bounds.
    refine lt_min ?_ ?_
    · positivity
    · positivity
  refine ⟨ρ, hρpos, ?_⟩
  intro t ht htρ
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  have htC : t < εC / (‖du‖ + 1) := lt_of_lt_of_le htρ (min_le_left _ _)
  have htD : t < εD / (‖dv‖ + 1) := lt_of_lt_of_le htρ (min_le_right _ _)
  have hPlusMemC : u + t • du ∈ C0 := by
    -- The positive first-coordinate step stays in the first slice ball.
    have htMulC : t * (‖du‖ + 1) < εC := by
      have hpos : 0 < ‖du‖ + 1 := by positivity
      have hmul := mul_lt_mul_of_pos_right htC hpos
      have hEq : (εC / (‖du‖ + 1)) * (‖du‖ + 1) = εC := by
        field_simp [show (‖du‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq, mul_comm, mul_left_comm, mul_assoc] using hmul
    have htNormC : ‖(u + t • du) - u‖ < εC := by
      calc
        ‖(u + t • du) - u‖ = ‖t • du‖ := by
          congr 1
          ext i
          simp [sub_eq_add_neg]
        _ = |t| * ‖du‖ := norm_smul t du
        _ = t * ‖du‖ := by simp [abs_of_nonneg ht_nonneg]
        _ ≤ t * (‖du‖ + 1) := by
          nlinarith [norm_nonneg du, ht_nonneg]
        _ < εC := by
          exact htMulC
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm] using htNormC)
  have hMinusMemC : u - t • du ∈ C0 := by
    -- Reflection across `u` keeps the same first-coordinate norm estimate.
    have htMulC : t * (‖du‖ + 1) < εC := by
      have hpos : 0 < ‖du‖ + 1 := by positivity
      have hmul := mul_lt_mul_of_pos_right htC hpos
      have hEq : (εC / (‖du‖ + 1)) * (‖du‖ + 1) = εC := by
        field_simp [show (‖du‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq, mul_comm, mul_left_comm, mul_assoc] using hmul
    have htNormC : ‖(u - t • du) - u‖ < εC := by
      calc
        ‖(u - t • du) - u‖ = ‖-(t • du)‖ := by
          simpa [sub_eq_add_neg]
        _ = ‖t • du‖ := by rw [norm_neg]
        _ = |t| * ‖du‖ := norm_smul t du
        _ = t * ‖du‖ := by simp [abs_of_nonneg ht_nonneg]
        _ ≤ t * (‖du‖ + 1) := by
          nlinarith [norm_nonneg du, ht_nonneg]
        _ < εC := by
          linarith
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm] using htNormC)
  have hPlusMemD : v + t • dv ∈ D0 := by
    -- The positive second-coordinate step stays in the second slice ball.
    have htMulD : t * (‖dv‖ + 1) < εD := by
      have hpos : 0 < ‖dv‖ + 1 := by positivity
      have hmul := mul_lt_mul_of_pos_right htD hpos
      have hEq : (εD / (‖dv‖ + 1)) * (‖dv‖ + 1) = εD := by
        field_simp [show (‖dv‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq, mul_comm, mul_left_comm, mul_assoc] using hmul
    have htNormD : ‖(v + t • dv) - v‖ < εD := by
      calc
        ‖(v + t • dv) - v‖ = ‖t • dv‖ := by
          congr 1
          ext j
          simp [sub_eq_add_neg]
        _ = |t| * ‖dv‖ := norm_smul t dv
        _ = t * ‖dv‖ := by simp [abs_of_nonneg ht_nonneg]
        _ ≤ t * (‖dv‖ + 1) := by
          nlinarith [norm_nonneg dv, ht_nonneg]
        _ < εD := by
          exact htMulD
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm] using htNormD)
  have hMinusMemD : v - t • dv ∈ D0 := by
    -- The reflected second-coordinate point obeys the same bound.
    have htMulD : t * (‖dv‖ + 1) < εD := by
      have hpos : 0 < ‖dv‖ + 1 := by positivity
      have hmul := mul_lt_mul_of_pos_right htD hpos
      have hEq : (εD / (‖dv‖ + 1)) * (‖dv‖ + 1) = εD := by
        field_simp [show (‖dv‖ + 1 : ℝ) ≠ 0 by positivity]
      simpa [hEq, mul_comm, mul_left_comm, mul_assoc] using hmul
    have htNormD : ‖(v - t • dv) - v‖ < εD := by
      calc
        ‖(v - t • dv) - v‖ = ‖-(t • dv)‖ := by
          simpa [sub_eq_add_neg]
        _ = ‖t • dv‖ := by rw [norm_neg]
        _ = |t| * ‖dv‖ := norm_smul t dv
        _ = t * ‖dv‖ := by simp [abs_of_nonneg ht_nonneg]
        _ ≤ t * (‖dv‖ + 1) := by
          nlinarith [norm_nonneg dv, ht_nonneg]
        _ < εD := by
          linarith
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm] using htNormD)
  exact ⟨hFirstFinite _ hPlusMemC, hFirstFinite _ hMinusMemC, hSecondFinite _ hPlusMemD,
    hSecondFinite _ hMinusMemD⟩



end Section35
end Chap07
