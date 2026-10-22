/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.51: disjointness of `C` and `D` forces `0` to lie outside the
Minkowski difference `C - D`. -/
private lemma zero_not_mem_sub_of_disjoint {C D : Set 𝓗} (hCD : Disjoint C D) :
    (0 : 𝓗) ∉ C - D := by
  intro h0
  rcases Set.mem_sub.mp h0 with ⟨c, hc, d, hd, hcd⟩
  have hEq : c = d := sub_eq_zero.mp hcd
  exact hCD.le_bot ⟨hc, hEq ▸ hd⟩

omit [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.51: a strict negative upper bound on `⟪z, u⟫` over `C - D` yields a
uniform positive margin between the support values on `C` and `D`. -/
private lemma pointwise_margin_of_sub_upper_bound {C D : Set 𝓗} {u : 𝓗} {ε : ℝ}
    (hbound : ∀ z ∈ C - D, ⟪z, u⟫_ℝ < -ε) :
    ∀ c ∈ C, ∀ d ∈ D, (⟪c, u⟫_ℝ : EReal) + ε ≤ (⟪d, u⟫_ℝ : EReal) := by
  intro c hc d hd
  have hmem : c - d ∈ C - D := Set.mem_sub.mpr ⟨c, hc, d, hd, rfl⟩
  have hlt : ⟪c - d, u⟫_ℝ < -ε := hbound (c - d) hmem
  have hle : ⟪c, u⟫_ℝ + ε ≤ ⟪d, u⟫_ℝ := by
    rw [inner_sub_left] at hlt
    linarith
  have hcast : (((⟪c, u⟫_ℝ + ε : ℝ) : EReal) ≤ (⟪d, u⟫_ℝ : EReal)) := by
    exact_mod_cast hle
  simpa [EReal.coe_add] using hcast

omit [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.51: a uniform positive inner-product margin forces strong separation in
the support-function formulation from Definition 3.49. -/
private lemma areStronglySeparated_of_uniform_inner_margin {C D : Set 𝓗} {u : 𝓗} {ε : ℝ}
    (hC : C.Nonempty) (hD : D.Nonempty) (hε : 0 < ε)
    (hmargin : ∀ c ∈ C, ∀ d ∈ D, (⟪c, u⟫_ℝ : EReal) + ε ≤ (⟪d, u⟫_ℝ : EReal)) :
    AreStronglySeparated C D := by
  have hu_ne : u ≠ 0 := by
    intro hu0
    obtain ⟨c, hc⟩ := hC
    obtain ⟨d, hd⟩ := hD
    have h : ((0 : ℝ) : EReal) + ε ≤ (0 : EReal) := by
      simpa [hu0] using hmargin c hc d hd
    have hε' : ((0 : ℝ) : EReal) < ε := by
      exact_mod_cast hε
    exact (not_le_of_gt hε') (by simpa using h)
  refine ⟨u, hu_ne, ?_⟩
  let S : Set EReal := (fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C
  let T : Set EReal := (fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D
  have hε_ne_top : ((ε : ℝ) : EReal) ≠ ⊤ := by simp
  have hε_ne_bot : ((ε : ℝ) : EReal) ≠ ⊥ := by simp
  have hnegε_ne_top : ((-ε : ℝ) : EReal) ≠ ⊤ := by simp
  have hsup_bound : sSup S ≤ sInf T - ε := by
    refine (isLUB_sSup S).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    refine (EReal.le_sub_iff_add_le (Or.inl hε_ne_bot) (Or.inl hε_ne_top)).2 ?_
    refine (isGLB_sInf T).2 ?_
    rintro _ ⟨d, hd, rfl⟩
    exact hmargin c hc d hd
  have hsup_margin : sSup S + ε ≤ sInf T := EReal.add_le_of_le_sub hsup_bound
  obtain ⟨c0, hc0⟩ := hC
  obtain ⟨d0, hd0⟩ := hD
  have hsSup_upper : sSup S ≤ (⟪d0, u⟫_ℝ : EReal) - ε := by
    refine (isLUB_sSup S).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact (EReal.le_sub_iff_add_le (Or.inl hε_ne_bot) (Or.inl hε_ne_top)).2 (hmargin c hc d0 hd0)
  have hinner_d0_ne_top : (⟪d0, u⟫_ℝ : EReal) ≠ ⊤ := by simp
  have hsSup_upper_ne_top : ((⟪d0, u⟫_ℝ : EReal) - ε) ≠ ⊤ := by
    have hfinite : (⟪d0, u⟫_ℝ : EReal) + (-ε : EReal) ≠ ⊤ :=
      EReal.add_ne_top hinner_d0_ne_top hnegε_ne_top
    simpa [sub_eq_add_neg] using hfinite
  have hsSup_ne_top : sSup S ≠ ⊤ :=
    ne_top_of_le_ne_top hsSup_upper_ne_top hsSup_upper
  have hsSup_ne_bot : sSup S ≠ ⊥ := by
    have : (⟪c0, u⟫_ℝ : EReal) ≤ sSup S := le_sSup ⟨c0, hc0, rfl⟩
    exact ne_bot_of_le_ne_bot (by simp) this
  have hsInf_lower : (⟪c0, u⟫_ℝ : EReal) + ε ≤ sInf T := by
    refine (isGLB_sInf T).2 ?_
    rintro _ ⟨d, hd, rfl⟩
    exact hmargin c0 hc0 d hd
  have hsInf_ne_top : sInf T ≠ ⊤ :=
    ne_top_of_le_ne_top hinner_d0_ne_top (sInf_le ⟨d0, hd0, rfl⟩)
  have hinner_c0_margin_ne_bot : (⟪c0, u⟫_ℝ : EReal) + ε ≠ ⊥ :=
    EReal.add_ne_bot_iff.2 ⟨by simp, hε_ne_bot⟩
  have hsInf_ne_bot : sInf T ≠ ⊥ :=
    ne_bot_of_le_ne_bot hinner_c0_margin_ne_bot hsInf_lower
  have hsSup_plus_ne_bot : sSup S + ε ≠ ⊥ :=
    EReal.add_ne_bot_iff.2 ⟨hsSup_ne_bot, hε_ne_bot⟩
  have h' : (sSup S + ε).toReal ≤ (sInf T).toReal :=
    EReal.toReal_le_toReal hsup_margin hsSup_plus_ne_bot hsInf_ne_top
  have hadd : (sSup S + ε).toReal = (sSup S).toReal + ε :=
    EReal.toReal_add hsSup_ne_top hsSup_ne_bot hε_ne_top hε_ne_bot
  have hreal : (sSup S).toReal + ε ≤ (sInf T).toReal := by
    simpa [hadd] using h'
  have hlt_real : (sSup S).toReal < (sInf T).toReal :=
    lt_of_lt_of_le (lt_add_of_pos_right _ hε) hreal
  rw [innerSupremumOn_eq_sSup_image, innerInfimumOn_eq_sInf_image]
  change sSup S < sInf T
  rw [← EReal.coe_toReal hsSup_ne_top hsSup_ne_bot, ← EReal.coe_toReal hsInf_ne_top hsInf_ne_bot]
  exact_mod_cast hlt_real

-- Proof sketch: the set `C - D` is a closed convex subset that does not contain `0`, since
-- `Disjoint C D` rules out writing `0 = c - d` with `c ∈ C` and `d ∈ D`. Apply the closed-point
-- strong separation theorem to `0` and `C - D`, then rewrite the resulting strict inequality on
-- `c - d` as a strict gap between the support functionals of `C` and `D`.
/-- Corollary 3.51: if nonempty subsets `C` and `D` of a real Hilbert space are disjoint and their
Minkowski difference `C - D` is closed and convex, then `C` and `D` are strongly separated. -/
theorem areStronglySeparated_of_disjoint_of_isClosed_of_convex_sub {C D : Set 𝓗}
    (hC : C.Nonempty) (hD : D.Nonempty) (hCD : Disjoint C D) (hclosed : IsClosed (C - D))
    (hconvex : Convex ℝ (C - D)) : AreStronglySeparated C D := by
  have h0not : (0 : 𝓗) ∉ C - D := zero_not_mem_sub_of_disjoint hCD
  obtain ⟨f, β, hsub, hβ0⟩ := geometric_hahn_banach_closed_point hconvex hclosed h0not
  let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
  let ε : ℝ := -β
  have hβ : β < 0 := by
    simpa using hβ0
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hbound : ∀ z ∈ C - D, ⟪z, u⟫_ℝ < -ε := by
    intro z hz
    have hz' : f z < β := hsub z hz
    have hz'' : ⟪u, z⟫_ℝ < -ε := by
      simpa [u, ε] using hz'
    simpa [real_inner_comm] using hz''
  exact areStronglySeparated_of_uniform_inner_margin hC hD hε
    (pointwise_margin_of_sub_upper_bound hbound)
