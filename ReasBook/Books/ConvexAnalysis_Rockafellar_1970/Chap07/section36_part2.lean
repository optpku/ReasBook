/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part1

section Chap07
section Section36

/-- Helper for Theorem 36.3: ambient saddle points are exactly subtype saddle points on
`dom₁ K × dom₂ K`, and the ambient point is forced into the projected domains. -/
lemma helperForTheorem_36_3_saddlePoint_transport
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hbdry : HasSaddleDomBoundaryBehavior K)
    (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀ ↔
      ∃ (hu₀ : u₀ ∈ saddleDom1 K) (hv₀ : v₀ ∈ saddleDom2 K),
        IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
          (fun u v => K u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩ :=
  by
    rcases hbdry with ⟨hDom1NE, hDom2NE, hBotStrip, hTopStrip⟩
    constructor
    · intro hs
      rcases hDom1NE with ⟨uC, huC⟩
      rcases hDom2NE with ⟨vD, hvD⟩
      rcases hs with ⟨hleft, hright⟩
      have hu₀ : u₀ ∈ saddleDom1 K := by
        by_contra hu₀
        -- If `u₀ ∉ dom₁ K`, then the center is forced to `⊥`, contradicting an in-domain row.
        have hCenterBot : K u₀ v₀ = (⊥ : EReal) := by
          have hle : K u₀ v₀ ≤ K u₀ vD := hright vD
          refine le_antisymm ?_ bot_le
          simpa [hBotStrip u₀ vD hu₀ hvD] using hle
        have hrowLt : (⊥ : EReal) < iInf (fun v : Fin n → ℝ => K uC v) := by
          simpa [saddleDom1] using huC
        have hrowLe : iInf (fun v : Fin n → ℝ => K uC v) ≤ K u₀ v₀ := by
          calc
            iInf (fun v : Fin n → ℝ => K uC v) ≤ K uC v₀ := iInf_le (fun v : Fin n → ℝ => K uC v) v₀
            _ ≤ K u₀ v₀ := hleft uC
        have hcontra : (⊥ : EReal) < (⊥ : EReal) := by
          exact lt_of_lt_of_le hrowLt (by simpa [hCenterBot] using hrowLe)
        exact (lt_irrefl (⊥ : EReal)) hcontra
      have hv₀ : v₀ ∈ saddleDom2 K := by
        by_contra hv₀
        -- If `v₀ ∉ dom₂ K`, then the center is forced to `⊤`, contradicting an in-domain column.
        have hCenterTop : K u₀ v₀ = (⊤ : EReal) := by
          have hge : K uC v₀ ≤ K u₀ v₀ := hleft uC
          refine le_antisymm le_top ?_
          simpa [hTopStrip uC v₀ huC hv₀] using hge
        have hcolLt : iSup (fun u : Fin m → ℝ => K u vD) < (⊤ : EReal) := by
          simpa [saddleDom2] using hvD
        have htopLe : (⊤ : EReal) ≤ iSup (fun u : Fin m → ℝ => K u vD) := by
          calc
            (⊤ : EReal) = K u₀ v₀ := hCenterTop.symm
            _ ≤ K u₀ vD := hright vD
            _ ≤ iSup (fun u : Fin m → ℝ => K u vD) :=
              le_iSup (fun u : Fin m → ℝ => K u vD) u₀
        exact (not_lt_of_ge htopLe) hcolLt
      refine ⟨hu₀, hv₀, ?_⟩
      refine ⟨?_, ?_⟩
      · intro u
        -- Once the center lies in `dom₁ K × dom₂ K`, the left saddle inequality restricts directly.
        simpa using hleft u.1
      · intro v
        -- The right saddle inequality restricts in the same way.
        simpa using hright v.1
    · rintro ⟨hu₀, hv₀, hs⟩
      rcases hs with ⟨hleft, hright⟩
      refine ⟨?_, ?_⟩
      · intro u
        by_cases hu : u ∈ saddleDom1 K
        · -- On-domain rows reduce to the subtype saddle inequality.
          simpa using hleft ⟨u, hu⟩
        · -- Off-domain rows contribute `⊥`, so the left inequality is automatic.
          calc
            K u v₀ = (⊥ : EReal) := hBotStrip u v₀ hu hv₀
            _ ≤ K u₀ v₀ := bot_le
      · intro v
        by_cases hv : v ∈ saddleDom2 K
        · -- On-domain columns reduce to the subtype saddle inequality.
          simpa using hright ⟨v, hv⟩
        · -- Off-domain columns contribute `⊤`, so the right inequality is automatic.
          calc
            K u₀ v₀ ≤ (⊤ : EReal) := le_top
            _ = K u₀ v := (hTopStrip u₀ v hu₀ hv).symm

-- Proof sketch: Use the domain-extension behavior of a closed proper concave-convex `K` to show
-- that values with `u ∉ dom₁ K` contribute `-∞` to `inf_v K(u,v)` and hence do not affect the
-- outer `sup_u`, while values with `v ∉ dom₂ K` contribute `+∞` to `sup_u K(u,v)` and hence do
-- not affect the outer `inf_v`. Transport saddle-value and saddle-point assertions by rewriting
-- the maximin/minimax expressions over `ℝ^m × ℝ^n` as the corresponding expressions over the
-- subtype domains `dom₁ K` and `dom₂ K`.
/-- Theorem 36.3: Let `K` be a closed proper concave-convex function on `ℝ^m × ℝ^n`, and let
`C = dom₁ K` and `D = dom₂ K`. Then restricting the maximin and minimax expressions to `C × D`
does not change their values, and the saddle-values and saddle-points of `K` with respect to
`ℝ^m × ℝ^n` agree with those with respect to `C × D`. -/
theorem maximin_minimax_and_saddle_restrict_to_saddleDom
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hK : IsClosedProperConcaveConvex K) :
    maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
        maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
          (fun u v => K u v) ∧
      minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
          minimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
            (fun u v => K u v) ∧
        (∀ x : EReal,
          IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K x ↔
            IsMinimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) x) ∧
          (∀ (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ),
            IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀ ↔
              ∃ (hu₀ : u₀ ∈ saddleDom1 K) (hv₀ : v₀ ∈ saddleDom2 K),
                IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                  (fun u v => K u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩) :=
  by
    have hbdry : HasSaddleDomBoundaryBehavior K := hK.1
    have hDom1NE : (saddleDom1 K).Nonempty := hbdry.1
    have hDom2NE : (saddleDom2 K).Nonempty := hbdry.2.1
    have hMax :
        maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
          maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
            (fun u v => K u v) :=
      helperForTheorem_36_3_maximin_eq_restrictedToSaddleDom
        (K := K) (hbdry := hbdry)
    have hMin :
        minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
          minimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
            (fun u v => K u v) :=
      helperForTheorem_36_3_minimax_eq_restrictedToSaddleDom
        (K := K) (hbdry := hbdry)
    have hSaddle :
        ∀ (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ),
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀ ↔
            ∃ (hu₀ : u₀ ∈ saddleDom1 K) (hv₀ : v₀ ∈ saddleDom2 K),
              IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                (fun u v => K u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩ :=
      fun u₀ v₀ =>
        helperForTheorem_36_3_saddlePoint_transport
          (K := K) (hbdry := hbdry) (u₀ := u₀) (v₀ := v₀)
    have hMinimax :
        ∀ x : EReal,
          IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K x ↔
            IsMinimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) x :=
      by
        intro x
        constructor
        · rintro ⟨_, _, hEq, hx⟩
          rcases hDom1NE with ⟨uC, huC⟩
          rcases hDom2NE with ⟨vD, hvD⟩
          -- Rewrite the two extremal values after restricting to `dom₁ K × dom₂ K`.
          refine ⟨⟨⟨uC, huC⟩⟩, ⟨⟨vD, hvD⟩⟩, ?_, ?_⟩
          · calc
              maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                  (fun u v => K u v) =
                  maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K := hMax.symm
              _ = minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K := hEq
              _ = minimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                    (fun u v => K u v) := hMin
          · calc
              x = maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K := hx
              _ = maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                    (fun u v => K u v) := hMax
        · rintro ⟨_, _, hEq, hx⟩
          -- The ambient function spaces are nonempty, so the predicate rewrites back directly.
          refine ⟨inferInstance, inferInstance, ?_, ?_⟩
          · calc
              maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
                  maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                    (fun u v => K u v) := hMax
              _ = minimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                    (fun u v => K u v) := hEq
              _ = minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K := hMin.symm
          · calc
              x = maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                    (fun u v => K u v) := hx
              _ = maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K := hMax.symm
    -- Combine the maximin/minimax rewrites with the saddle-point transport equivalence.
    exact ⟨hMax, hMin, hMinimax, hSaddle⟩

/-- The domain `dom K` of an extended-real saddle function `K(u,v)`, defined as the product
`dom₁ K × dom₂ K`. -/
noncomputable def saddleDom {U V : Type*} (K : U → V → EReal) : Set (U × V) :=
  saddleDom1 (U := U) (V := V) K ×ˢ saddleDom2 (U := U) (V := V) K

/-- Helper for Corollary 36.3.1: every saddle point lies in `dom K`, and its center value is
neither `-∞` nor `+∞`. -/
lemma helperForCorollary_36_3_1_saddlePoint_mem_dom_and_finiteCenter
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hK : IsClosedProperConcaveConvex K)
    {u₀ : Fin m → ℝ} {v₀ : Fin n → ℝ}
    (hsuv : IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀) :
    (u₀, v₀) ∈ saddleDom (U := (Fin m → ℝ)) (V := (Fin n → ℝ)) K ∧
      K u₀ v₀ ≠ (⊥ : EReal) ∧ K u₀ v₀ ≠ (⊤ : EReal) :=
  by
    rcases maximin_minimax_and_saddle_restrict_to_saddleDom (K := K) hK with
      ⟨_, _, _, hSaddle⟩
    rcases (hSaddle u₀ v₀).mp hsuv with ⟨hu₀, hv₀, hsSubtype⟩
    have hSubtypeData :=
      (isSaddlePoint_iff_maximinValue_eq_minimaxValue_and_attained
        (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
        (fun u v => K u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩).mp hsSubtype
    rcases hSubtypeData with ⟨hSubtypeMax, hSubtypeMin, hSubtypeEq, hCenterSubtype⟩
    have hRowRestr :
        iInf (fun v : Fin n → ℝ => K u₀ v) =
          iInf (fun v : {v // v ∈ saddleDom2 K} => K u₀ v) :=
      helperForTheorem_36_3_rowInf_eq_subtype_of_memSaddleDom1
        (K := K) (hbdry := hK.1) (u := u₀) hu₀
    have hColRestr :
        iSup (fun u : Fin m → ℝ => K u v₀) =
          iSup (fun u : {u // u ∈ saddleDom1 K} => K u v₀) :=
      helperForTheorem_36_3_colSup_eq_subtype_of_memSaddleDom2
        (K := K) (hbdry := hK.1) (v := v₀) hv₀
    -- Rewrite the subtype saddle row back to the ambient row.
    have hCenter_eq_rowInf :
        K u₀ v₀ = iInf (fun v : Fin n → ℝ => K u₀ v) := by
      calc
        K u₀ v₀ =
            maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) := hCenterSubtype
        _ = iInf (fun v : {v // v ∈ saddleDom2 K} => K u₀ v) := hSubtypeMax
        _ = iInf (fun v : Fin n → ℝ => K u₀ v) := hRowRestr.symm
    -- Rewrite the subtype saddle column back to the ambient column.
    have hCenter_eq_colSup :
        K u₀ v₀ = iSup (fun u : Fin m → ℝ => K u v₀) := by
      calc
        K u₀ v₀ =
            maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) := hCenterSubtype
        _ =
            minimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) := hSubtypeEq
        _ = iSup (fun u : {u // u ∈ saddleDom1 K} => K u v₀) := hSubtypeMin
        _ = iSup (fun u : Fin m → ℝ => K u v₀) := hColRestr.symm
    have hbot_lt_rowInf : (⊥ : EReal) < iInf (fun v : Fin n → ℝ => K u₀ v) := by
      simpa [saddleDom1] using hu₀
    have hcolSup_lt_top : iSup (fun u : Fin m → ℝ => K u v₀) < (⊤ : EReal) := by
      simpa [saddleDom2] using hv₀
    -- The domain conditions turn into strict bounds on the center value.
    have hbot_lt_center : (⊥ : EReal) < K u₀ v₀ := by
      simpa [hCenter_eq_rowInf] using hbot_lt_rowInf
    have hcenter_lt_top : K u₀ v₀ < (⊤ : EReal) := by
      simpa [hCenter_eq_colSup] using hcolSup_lt_top
    refine ⟨?_, ne_of_gt hbot_lt_center, ne_of_lt hcenter_lt_top⟩
    -- Membership in `dom K` is exactly membership in the two projected domains.
    simpa [saddleDom] using And.intro hu₀ hv₀

/-- Helper for Corollary 36.3.1: a saddle point furnishes a finite minimax value. -/
lemma helperForCorollary_36_3_1_exists_finite_minimaxValue_from_saddlePoint
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hK : IsClosedProperConcaveConvex K)
    (hs : ∃ u₀ v₀, IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀) :
    ∃ x : EReal,
      IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K x ∧
        x ≠ (⊥ : EReal) ∧ x ≠ (⊤ : EReal) :=
  by
    rcases hs with ⟨u₀, v₀, hsuv⟩
    have hFiniteCenter :=
      helperForCorollary_36_3_1_saddlePoint_mem_dom_and_finiteCenter
        (K := K) (hK := hK) hsuv
    rcases hFiniteCenter with ⟨_, hneBot, hneTop⟩
    have hSaddleData :=
      (isSaddlePoint_iff_maximinValue_eq_minimaxValue_and_attained
        (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀).mp hsuv
    rcases hSaddleData with ⟨_, _, hEq, hCenter⟩
    -- Lemma 36.2 packages the center value of a saddle point as the minimax value.
    refine ⟨K u₀ v₀, ?_, hneBot, hneTop⟩
    exact ⟨inferInstance, inferInstance, hEq, hCenter⟩

-- Proof sketch: Use Theorem 36.3 to reduce any saddle-point of `K` on `ℝ^m × ℝ^n` to a
-- saddle-point on `dom₁ K × dom₂ K`. Membership in `dom₁ K`/`dom₂ K` is then forced by the
-- definitions of these projected domains. Finally, use Lemma 36.2 to identify the saddle-value
-- with `K u₀ v₀` and rule out the values `±∞` under the closed/proper hypotheses.
/-- Corollary 36.3.1: Let `K` be a closed proper saddle-function on `ℝ^m × ℝ^n`.
If `K` has a saddle-point, then this saddle-point lies in `dom K`, and the saddle-value of `K`
is finite. -/
theorem saddlePoint_mem_dom_and_saddleValue_finite
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hK : IsClosedProperConcaveConvex K)
    (hs : ∃ u₀ v₀, IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀) :
    (∀ {u₀ : Fin m → ℝ} {v₀ : Fin n → ℝ},
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀ →
          (u₀, v₀) ∈ saddleDom (U := (Fin m → ℝ)) (V := (Fin n → ℝ)) K ∧
            K u₀ v₀ ≠ (⊥ : EReal) ∧ K u₀ v₀ ≠ (⊤ : EReal)) ∧
      (∃ x : EReal,
        IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K x ∧
          x ≠ (⊥ : EReal) ∧ x ≠ (⊤ : EReal)) :=
  by
    constructor
    · intro u₀ v₀ hsuv
      -- Theorem 36.3 puts every saddle point inside `dom K`, and Lemma 36.2 makes its value finite.
      exact helperForCorollary_36_3_1_saddlePoint_mem_dom_and_finiteCenter
        (K := K) (hK := hK) hsuv
    · -- Choosing one saddle point produces the finite minimax value promised by the corollary.
      exact helperForCorollary_36_3_1_exists_finite_minimaxValue_from_saddlePoint
        (K := K) (hK := hK) hs

/-- Two extended-real saddle functions `K` and `L` are *equivalent* if they have the same projected
domains `dom₁` and `dom₂`, satisfy the `±∞` boundary-value behavior on these domains, and agree on
`dom₁ × dom₂`. -/
def EquivalentSaddleFunctions {U V : Type*} (K L : U → V → EReal) : Prop :=
  HasSaddleDomBoundaryBehavior (U := U) (V := V) K ∧
    HasSaddleDomBoundaryBehavior (U := U) (V := V) L ∧
      saddleDom1 (U := U) (V := V) K = saddleDom1 (U := U) (V := V) L ∧
        saddleDom2 (U := U) (V := V) K = saddleDom2 (U := U) (V := V) L ∧
          ∀ u : U, ∀ v : V,
            u ∈ saddleDom1 (U := U) (V := V) K →
              v ∈ saddleDom2 (U := U) (V := V) K → K u v = L u v

/-- Helper for Theorem 36.4: on the common saddle domain, equivalent saddle-functions have the
same restricted kernel. -/
lemma helperForTheorem_36_4_restrictedKernel_eq_on_commonSaddleDom
    {m n : ℕ} {K L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hAgree :
      ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
        u ∈ saddleDom1 K → v ∈ saddleDom2 K → K u v = L u v) :
    (fun u : {u // u ∈ saddleDom1 K} => fun v : {v // v ∈ saddleDom2 K} => K u v) =
      (fun u : {u // u ∈ saddleDom1 K} => fun v : {v // v ∈ saddleDom2 K} => L u v) :=
  by
    -- On the common subtype domain, the two kernels agree pointwise by the defining hypothesis.
    funext u v
    exact hAgree u.1 v.1 u.2 v.2

/-- Helper for Theorem 36.4: for a saddle-function with the standard boundary behavior, the ambient
minimax-value predicate is equivalent to the minimax-value predicate on `dom₁ × dom₂`. -/
lemma helperForTheorem_36_4_isMinimaxValue_iff_restrictedToSaddleDom
    {m n : ℕ} (M : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hM : HasSaddleDomBoundaryBehavior M) (x : EReal) :
    IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M x ↔
      IsMinimaxValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
        (fun u v => M u v) x :=
  by
    have hDom1NE : (saddleDom1 M).Nonempty := hM.1
    have hDom2NE : (saddleDom2 M).Nonempty := hM.2.1
    have hMax :
        maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M =
          maximinValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
            (fun u v => M u v) :=
      helperForTheorem_36_3_maximin_eq_restrictedToSaddleDom (K := M) (hbdry := hM)
    have hMin :
        minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M =
          minimaxValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
            (fun u v => M u v) :=
      helperForTheorem_36_3_minimax_eq_restrictedToSaddleDom (K := M) (hbdry := hM)
    constructor
    · rintro ⟨_, _, hEq, hx⟩
      rcases hDom1NE with ⟨uM, huM⟩
      rcases hDom2NE with ⟨vM, hvM⟩
      -- Restrict the ambient maximin and minimax identities to the subtype domain.
      refine ⟨⟨uM, huM⟩, ⟨vM, hvM⟩, ?_, ?_⟩
      · calc
          maximinValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
              (fun u v => M u v) =
              maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M := hMax.symm
          _ = minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M := hEq
          _ = minimaxValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
                (fun u v => M u v) := hMin
      · calc
          x = maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M := hx
          _ = maximinValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
                (fun u v => M u v) := hMax
    · rintro ⟨_, _, hEq, hx⟩
      -- The ambient function spaces are nonempty, so the restricted statement lifts back directly.
      refine ⟨inferInstance, inferInstance, ?_, ?_⟩
      · calc
          maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M =
              maximinValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
                (fun u v => M u v) := hMax
          _ = minimaxValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
                (fun u v => M u v) := hEq
          _ = minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M := hMin.symm
      · calc
          x = maximinValue (C := {u // u ∈ saddleDom1 M}) (D := {v // v ∈ saddleDom2 M})
                (fun u v => M u v) := hx
          _ = maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) M := hMax.symm

/-- Helper for Theorem 36.4: on a fixed common subtype domain, equal restricted kernels have the
same saddle-point predicate. -/
lemma helperForTheorem_36_4_restrictedSaddlePoint_iff_of_restrictedKernel_eq
    {m n : ℕ} {K L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hEq :
      (fun u : {u // u ∈ saddleDom1 K} => fun v : {v // v ∈ saddleDom2 K} => K u v) =
        (fun u : {u // u ∈ saddleDom1 K} => fun v : {v // v ∈ saddleDom2 K} => L u v)) :
    ∀ (u₀ : {u // u ∈ saddleDom1 K}) (v₀ : {v // v ∈ saddleDom2 K}),
      IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
          (fun u v => K u v) u₀ v₀ ↔
        IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
          (fun u v => L u v) u₀ v₀ :=
  by
    intro u₀ v₀
    have hPoint :
        ∀ u : {u // u ∈ saddleDom1 K}, ∀ v : {v // v ∈ saddleDom2 K}, K u v = L u v := by
      intro u v
      exact congrFun (congrFun hEq u) v
    constructor
    · rintro ⟨hLeft, hRight⟩
      refine ⟨?_, ?_⟩
      · intro u
        -- Rewrite both endpoints of the left saddle inequality using the common restricted kernel.
        calc
          L u v₀ = K u v₀ := (hPoint u v₀).symm
          _ ≤ K u₀ v₀ := hLeft u
          _ = L u₀ v₀ := hPoint u₀ v₀
      · intro v
        -- Rewrite both endpoints of the right saddle inequality in the same way.
        calc
          L u₀ v₀ = K u₀ v₀ := (hPoint u₀ v₀).symm
          _ ≤ K u₀ v := hRight v
          _ = L u₀ v := hPoint u₀ v
    · rintro ⟨hLeft, hRight⟩
      refine ⟨?_, ?_⟩
      · intro u
        -- The reverse implication follows by the same pointwise rewrites.
        calc
          K u v₀ = L u v₀ := hPoint u v₀
          _ ≤ L u₀ v₀ := hLeft u
          _ = K u₀ v₀ := (hPoint u₀ v₀).symm
      · intro v
        calc
          K u₀ v₀ = L u₀ v₀ := hPoint u₀ v₀
          _ ≤ L u₀ v := hRight v
          _ = K u₀ v := (hPoint u₀ v).symm

/-- Helper for Theorem 36.4: changing only the subtype domain by equal sets does not change the
restricted minimax-value predicate. -/
lemma helperForTheorem_36_4_restrictedIsMinimaxValue_iff_of_domain_eq
    {m n : ℕ} (M : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    {S S' : Set (Fin m → ℝ)} {T T' : Set (Fin n → ℝ)}
    (hS : S = S') (hT : T = T') (x : EReal) :
    IsMinimaxValue (C := {u // u ∈ S}) (D := {v // v ∈ T}) (fun u v => M u v) x ↔
      IsMinimaxValue (C := {u // u ∈ S'}) (D := {v // v ∈ T'}) (fun u v => M u v) x :=
  by
    -- Once the two domain sets are identified, the restricted predicate is definitionally the same.
    cases hS
    cases hT
    rfl

/-- Helper for Theorem 36.4: changing only the subtype domain by equal sets does not change the
restricted existential saddle-point transport statement. -/
lemma helperForTheorem_36_4_restrictedSaddlePointExists_iff_of_domain_eq
    {m n : ℕ} (M : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    {S S' : Set (Fin m → ℝ)} {T T' : Set (Fin n → ℝ)}
    (hS : S = S') (hT : T = T') (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ) :
    (∃ (hu₀ : u₀ ∈ S) (hv₀ : v₀ ∈ T),
        IsSaddlePoint (C := {u // u ∈ S}) (D := {v // v ∈ T})
          (fun u v => M u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩) ↔
      (∃ (hu₀ : u₀ ∈ S') (hv₀ : v₀ ∈ T'),
        IsSaddlePoint (C := {u // u ∈ S'}) (D := {v // v ∈ T'})
          (fun u v => M u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩) :=
  by
    -- The witness package only depends on the subtype domains up to equality.
    cases hS
    cases hT
    rfl

-- Proof sketch: In the minimax setting, the maximin/minimax values and the saddle-point
-- inequalities depend only on the restriction of a saddle-function to `dom₁ × dom₂` together with
-- the forced boundary values `-∞` and `+∞` on the complementary “strips”. Transport these data
-- along `EquivalentSaddleFunctions` and conclude that the saddle-value predicate and the saddle
-- point predicate are preserved.
/-- Theorem 36.4: Equivalent saddle-functions on `ℝ^m × ℝ^n` have the same saddle-value and
saddle-points (if any). -/
theorem equivalentSaddleFunctions_saddleValue_and_saddlePoints
    {m n : ℕ} {K L : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hKL : EquivalentSaddleFunctions (U := (Fin m → ℝ)) (V := (Fin n → ℝ)) K L) :
    (∀ x : EReal,
        IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K x ↔
          IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L x) ∧
      (∀ (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ),
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀ ↔
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L u₀ v₀) :=
  by
    rcases hKL with ⟨hKbdry, hLbdry, hDom1, hDom2, hAgree⟩
    have hRestrictedEq :
        (fun u : {u // u ∈ saddleDom1 K} => fun v : {v // v ∈ saddleDom2 K} => K u v) =
          (fun u : {u // u ∈ saddleDom1 K} => fun v : {v // v ∈ saddleDom2 K} => L u v) :=
      helperForTheorem_36_4_restrictedKernel_eq_on_commonSaddleDom (K := K) (L := L) hAgree
    have hMinimaxK :
        ∀ x : EReal,
          IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K x ↔
            IsMinimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) x :=
      fun x =>
        helperForTheorem_36_4_isMinimaxValue_iff_restrictedToSaddleDom
          (M := K) (hM := hKbdry) (x := x)
    have hMinimaxL :
        ∀ x : EReal,
          IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L x ↔
            IsMinimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => L u v) x :=
      by
        intro x
        -- Rewrite `L`'s subtype domains to the common domains coming from `K`.
        exact
          (helperForTheorem_36_4_isMinimaxValue_iff_restrictedToSaddleDom
            (M := L) (hM := hLbdry) (x := x)).trans
            (helperForTheorem_36_4_restrictedIsMinimaxValue_iff_of_domain_eq
              (M := L) (S := saddleDom1 L) (S' := saddleDom1 K)
              (T := saddleDom2 L) (T' := saddleDom2 K)
              (hS := hDom1.symm) (hT := hDom2.symm) (x := x))
    have hRestrictedMinimax :
        ∀ x : EReal,
          IsMinimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) x ↔
            IsMinimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => L u v) x :=
      by
        intro x
        -- The restricted minimax predicate depends only on the common restricted kernel.
        simp [IsMinimaxValue, hRestrictedEq]
    have hSaddleK :
        ∀ (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ),
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u₀ v₀ ↔
            ∃ (hu₀ : u₀ ∈ saddleDom1 K) (hv₀ : v₀ ∈ saddleDom2 K),
              IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                (fun u v => K u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩ :=
      fun u₀ v₀ =>
        helperForTheorem_36_3_saddlePoint_transport
          (K := K) (hbdry := hKbdry) (u₀ := u₀) (v₀ := v₀)
    have hSaddleL :
        ∀ (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ),
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) L u₀ v₀ ↔
            ∃ (hu₀ : u₀ ∈ saddleDom1 K) (hv₀ : v₀ ∈ saddleDom2 K),
              IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
                (fun u v => L u v) ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩ :=
      by
        intro u₀ v₀
        -- Rewrite `L`'s transport statement onto the common subtype domains.
        exact
          (helperForTheorem_36_3_saddlePoint_transport
            (K := L) (hbdry := hLbdry) (u₀ := u₀) (v₀ := v₀)).trans
            (helperForTheorem_36_4_restrictedSaddlePointExists_iff_of_domain_eq
              (M := L) (S := saddleDom1 L) (S' := saddleDom1 K)
              (T := saddleDom2 L) (T' := saddleDom2 K)
              (hS := hDom1.symm) (hT := hDom2.symm) (u₀ := u₀) (v₀ := v₀))
    have hRestrictedSaddle :
        ∀ (u₀ : {u // u ∈ saddleDom1 K}) (v₀ : {v // v ∈ saddleDom2 K}),
          IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => K u v) u₀ v₀ ↔
            IsSaddlePoint (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
              (fun u v => L u v) u₀ v₀ :=
      helperForTheorem_36_4_restrictedSaddlePoint_iff_of_restrictedKernel_eq
        (K := K) (L := L) hRestrictedEq
    constructor
    · intro x
      -- Transport the minimax-value predicate through the common restricted kernel.
      exact (hMinimaxK x).trans <| (hRestrictedMinimax x).trans (hMinimaxL x).symm
    · intro u₀ v₀
      constructor
      · intro hsK
        rcases (hSaddleK u₀ v₀).mp hsK with ⟨hu₀, hv₀, hsRestricted⟩
        -- Move the restricted saddle-point witness across the common restricted kernel.
        refine (hSaddleL u₀ v₀).mpr ⟨hu₀, hv₀, ?_⟩
        exact (hRestrictedSaddle ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩).mp hsRestricted
      · intro hsL
        rcases (hSaddleL u₀ v₀).mp hsL with ⟨hu₀, hv₀, hsRestricted⟩
        -- The same witness transports back because the restricted kernels are equal.
        refine (hSaddleK u₀ v₀).mpr ⟨hu₀, hv₀, ?_⟩
        exact (hRestrictedSaddle ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩).mpr hsRestricted

end Section36
end Chap07
