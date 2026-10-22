/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.bifunction_inverse

section Chap07
section Section36

variable {C D : Type*}

/-- The value `α := sup_{u ∈ C} inf_{v ∈ D} K(u,v)` (the maximin value) for an extended-real function `K`. -/
noncomputable def maximinValue (K : C → D → EReal) : EReal :=
  iSup fun u : C => iInf fun v : D => K u v

/-- The value `β := inf_{v ∈ D} sup_{u ∈ C} K(u,v)` (the minimax value) for an extended-real function `K`. -/
noncomputable def minimaxValue (K : C → D → EReal) : EReal :=
  iInf fun v : D => iSup fun u : C => K u v

/-- Definition 36.0.1: For nonempty `C` and `D` and `K : C × D → [-∞, +∞]`, set
`α := sup_{u ∈ C} inf_{v ∈ D} K(u,v)` and `β := inf_{v ∈ D} sup_{u ∈ C} K(u,v)`;
if `α = β`, then this common value is called the minimax value (or saddle-value) of `K`. -/
def IsMinimaxValue (K : C → D → EReal) (x : EReal) : Prop :=
  Nonempty C ∧
    Nonempty D ∧
      maximinValue (C := C) (D := D) K = minimaxValue (C := C) (D := D) K ∧
        x = maximinValue (C := C) (D := D) K

-- Proof sketch: Use the order-theoretic inequality `⨆ u, ⨅ v, K u v ≤ ⨅ v, ⨆ u, K u v`
-- in the complete lattice `EReal`, which follows by comparing both sides against the family
-- of bounds `⨅ v, K u v ≤ ⨆ u, K u v` for each `u` and `v`.
/-- Lemma 36.1: If `K : C × D → [-∞, +∞]` is defined on a nonempty product set, then
`sup_u inf_v K(u,v) ≤ inf_v sup_u K(u,v)`. -/
lemma maximinValue_le_minimaxValue (K : C → D → EReal) (hC : Nonempty C) (hD : Nonempty D) :
    maximinValue (C := C) (D := D) K ≤ minimaxValue (C := C) (D := D) K :=
  by
    let _ : Nonempty C := hC
    let _ : Nonempty D := hD
    -- Compare the maximin value against the supremum profile at each fixed `v`.
    refine le_iInf ?_
    intro v
    -- For this fixed `v`, it is enough to bound each `u`-slice separately.
    refine iSup_le ?_
    intro u
    -- The inner infimum is bounded by the chosen value `K u v`, which is in turn
    -- bounded by the corresponding outer supremum.
    exact le_trans (iInf_le (fun w : D => K u w) v) (le_iSup (fun u' : C => K u' v) u)

/-- Definition 36.1.1: Let `C` and `D` be nonempty sets and `K : C × D → [-∞, +∞]`.
A pair `(u₀, v₀) ∈ C × D` is a saddle point of `K` (maximization in `u ∈ C` and minimization
in `v ∈ D`) if `K u v₀ ≤ K u₀ v₀ ≤ K u₀ v` for all `u : C` and `v : D`.
Equivalently, `v₀` minimizes `v ↦ K u₀ v` on `D` and `u₀` maximizes `u ↦ K u v₀` on `C`,
and if the extrema are attained then `K u₀ v₀` equals both the min and the max. -/
def IsSaddlePoint (K : C → D → EReal) (u₀ : C) (v₀ : D) : Prop :=
  (∀ u : C, K u v₀ ≤ K u₀ v₀) ∧ (∀ v : D, K u₀ v₀ ≤ K u₀ v)

-- Proof sketch: Unfold `IsSaddlePoint` and compare `K u₀ v₀` to the families
-- `iInf (K u ·)` and `iSup (K · v)` using monotonicity of `iSup`/`iInf`. For the
-- “only if” direction, show `maximinValue K = iInf (K u₀ ·)` and
-- `minimaxValue K = iSup (K · v₀)` by bounding each extremum above and below by
-- `K u₀ v₀`; for the converse, use the attainment equalities plus
-- `iInf_le`/`le_iSup` to recover the saddle inequalities.
/-- Helper for Lemma 36.2: at a saddle point, the `v`-infimum along the saddle row is the
center value `K u₀ v₀`. -/
lemma helperForLemma_36_2_rowInf_eq_centerValue
    (K : C → D → EReal) (u₀ : C) (v₀ : D)
    (hs : IsSaddlePoint (C := C) (D := D) K u₀ v₀) :
    iInf (fun v : D => K u₀ v) = K u₀ v₀ :=
  by
    rcases hs with ⟨_, hright⟩
    -- The saddle row is minimized at `v₀`, so the infimum equals the center value.
    refine le_antisymm ?_ ?_
    · exact iInf_le (fun v : D => K u₀ v) v₀
    · exact le_iInf hright

/-- Helper for Lemma 36.2: at a saddle point, the `u`-supremum along the saddle column is the
center value `K u₀ v₀`. -/
lemma helperForLemma_36_2_colSup_eq_centerValue
    (K : C → D → EReal) (u₀ : C) (v₀ : D)
    (hs : IsSaddlePoint (C := C) (D := D) K u₀ v₀) :
    iSup (fun u : C => K u v₀) = K u₀ v₀ :=
  by
    rcases hs with ⟨hleft, _⟩
    -- The saddle column is maximized at `u₀`, so the supremum equals the center value.
    refine le_antisymm ?_ ?_
    · exact iSup_le hleft
    · exact le_iSup (fun u : C => K u v₀) u₀

/-- Helper for Lemma 36.2: at a saddle point, the maximin value is attained at the saddle row
`u₀`. -/
lemma helperForLemma_36_2_maximin_eq_attainedRowInf
    (K : C → D → EReal) (u₀ : C) (v₀ : D)
    (hs : IsSaddlePoint (C := C) (D := D) K u₀ v₀) :
    maximinValue (C := C) (D := D) K = iInf (fun v : D => K u₀ v) :=
  by
    have hRow :
        iInf (fun v : D => K u₀ v) = K u₀ v₀ :=
      helperForLemma_36_2_rowInf_eq_centerValue (K := K) (u₀ := u₀) (v₀ := v₀) hs
    rcases hs with ⟨hleft, _⟩
    -- Compare the outer supremum against the row infimum at `u₀`.
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro u
      calc
        iInf (fun v : D => K u v) ≤ K u v₀ := iInf_le (fun v : D => K u v) v₀
        _ ≤ K u₀ v₀ := hleft u
        _ = iInf (fun v : D => K u₀ v) :=
          hRow.symm
    · exact le_iSup (fun u : C => iInf (fun v : D => K u v)) u₀

/-- Helper for Lemma 36.2: at a saddle point, the minimax value is attained at the saddle column
`v₀`. -/
lemma helperForLemma_36_2_minimax_eq_attainedColSup
    (K : C → D → EReal) (u₀ : C) (v₀ : D)
    (hs : IsSaddlePoint (C := C) (D := D) K u₀ v₀) :
    minimaxValue (C := C) (D := D) K = iSup (fun u : C => K u v₀) :=
  by
    have hCol :
        iSup (fun u : C => K u v₀) = K u₀ v₀ :=
      helperForLemma_36_2_colSup_eq_centerValue (K := K) (u₀ := u₀) (v₀ := v₀) hs
    rcases hs with ⟨_, hright⟩
    -- Compare the outer infimum against the column supremum at `v₀`.
    refine le_antisymm ?_ ?_
    · exact iInf_le (fun v : D => iSup (fun u : C => K u v)) v₀
    · refine le_iInf ?_
      intro v
      calc
        iSup (fun u : C => K u v₀) = K u₀ v₀ := hCol
        _ ≤ K u₀ v := hright v
        _ ≤ iSup (fun u : C => K u v) := le_iSup (fun u : C => K u v) u₀

/-- Lemma 36.2: Let `K : C × D → [-∞, +∞]` be an extended-real function on a nonempty
product `C × D`. A point `(u₀, v₀)` is a saddle-point of `K` (maximizing over `C` and
minimizing over `D`) if and only if the supremum in `sup_u inf_v K(u,v)` is attained
at `u₀`, the infimum in `inf_v sup_u K(u,v)` is attained at `v₀`, and these two
extrema are equal. If `(u₀, v₀)` is a saddle-point, the saddle-value of `K` is
`K u₀ v₀`. -/
lemma isSaddlePoint_iff_maximinValue_eq_minimaxValue_and_attained
    (K : C → D → EReal) (u₀ : C) (v₀ : D) :
    IsSaddlePoint (C := C) (D := D) K u₀ v₀ ↔
      (maximinValue (C := C) (D := D) K = iInf fun v : D => K u₀ v) ∧
      (minimaxValue (C := C) (D := D) K = iSup fun u : C => K u v₀) ∧
      maximinValue (C := C) (D := D) K = minimaxValue (C := C) (D := D) K ∧
      K u₀ v₀ = maximinValue (C := C) (D := D) K :=
  by
    constructor
    · intro hs
      -- First identify the saddle row and saddle column extrema with the center value.
      have hRow :
          iInf (fun v : D => K u₀ v) = K u₀ v₀ :=
        helperForLemma_36_2_rowInf_eq_centerValue (K := K) (u₀ := u₀) (v₀ := v₀) hs
      have hCol :
          iSup (fun u : C => K u v₀) = K u₀ v₀ :=
        helperForLemma_36_2_colSup_eq_centerValue (K := K) (u₀ := u₀) (v₀ := v₀) hs
      -- Then show the global maximin and minimax values are attained at `(u₀, v₀)`.
      have hMax :
          maximinValue (C := C) (D := D) K = iInf (fun v : D => K u₀ v) :=
        helperForLemma_36_2_maximin_eq_attainedRowInf (K := K) (u₀ := u₀) (v₀ := v₀) hs
      have hMin :
          minimaxValue (C := C) (D := D) K = iSup (fun u : C => K u v₀) :=
        helperForLemma_36_2_minimax_eq_attainedColSup (K := K) (u₀ := u₀) (v₀ := v₀) hs
      refine ⟨hMax, hMin, ?_, ?_⟩
      · -- Both extrema equal the common center value `K u₀ v₀`.
        calc
          maximinValue (C := C) (D := D) K = iInf (fun v : D => K u₀ v) := hMax
          _ = K u₀ v₀ := hRow
          _ = iSup (fun u : C => K u v₀) := hCol.symm
          _ = minimaxValue (C := C) (D := D) K := hMin.symm
      · -- The saddle value itself is the common maximin value.
        calc
          K u₀ v₀ = iInf (fun v : D => K u₀ v) := hRow.symm
          _ = maximinValue (C := C) (D := D) K := hMax.symm
    · rintro ⟨hMax, hMin, hEq, hCenter⟩
      refine ⟨?_, ?_⟩
      · intro u
        -- Rewrite through the attained minimax value to recover the left saddle inequality.
        calc
          K u v₀ ≤ iSup (fun u' : C => K u' v₀) := le_iSup (fun u' : C => K u' v₀) u
          _ = minimaxValue (C := C) (D := D) K := hMin.symm
          _ = maximinValue (C := C) (D := D) K := hEq.symm
          _ = K u₀ v₀ := hCenter.symm
      · intro v
        -- Rewrite through the attained maximin value to recover the right saddle inequality.
        calc
          K u₀ v₀ = maximinValue (C := C) (D := D) K := hCenter
          _ = iInf (fun v' : D => K u₀ v') := hMax
          _ ≤ K u₀ v := iInf_le (fun v' : D => K u₀ v') v

attribute [local instance] Classical.propDecidable

/-- A `±∞`-extension of a real-valued function `K` defined on a nonempty product `C × D` of
subsets of ambient spaces: it agrees with `K` on `C × D`, equals `+∞` on `C × (Dᶜ)`,
equals `-∞` on `(Cᶜ) × D`, and takes a chosen fallback value outside `C ∪ D`. -/
noncomputable def pmInfExtension
    {U V : Type*} (C : Set U) (D : Set V) (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (z : EReal := 0) : U → V → EReal :=
  fun u v =>
    if hu : u ∈ C then
      if hv : v ∈ D then (K ⟨u, hu⟩ ⟨v, hv⟩ : EReal) else ⊤
    else
      if v ∈ D then ⊥ else z

/-- A `±∞`-extension of a real-valued function `K` on `C × D` where the value on
`(Cᶜ) × (Dᶜ)` is allowed to be an arbitrary function `Z` of `(u,v)`. -/
noncomputable def pmInfExtensionWith
    {U V : Type*} (C : Set U) (D : Set V) (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : U → V → EReal) : U → V → EReal :=
  fun u v =>
    if hu : u ∈ C then
      if hv : v ∈ D then (K ⟨u, hu⟩ ⟨v, hv⟩ : EReal) else ⊤
    else
      if v ∈ D then ⊥ else Z u v

-- Proof sketch: Split into cases `u ∈ C`/`u ∉ C` and `v ∈ D`/`v ∉ D`. For the inf/sup
-- identities, show that the `+∞` and `-∞` branches do not affect the relevant extremum,
-- using nonemptiness of `C` and `D` to force the `-∞` (resp. `+∞`) value when outside.
-- Then identify the maximin/minimax expressions over ambient spaces with those over
-- the subtypes `C` and `D`, and transport saddle-value/saddle-point assertions via the
-- already-defined `IsMinimaxValue` and `IsSaddlePoint`.
/-- Helper for Proposition 36.2.1: when `u ∈ C`, the ambient row infimum of the
`±∞`-extension agrees with the subtype row infimum over `D`. -/
lemma helperForProposition_36_2_1_rowInf_eq_subtype_of_mem
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (hu : u ∈ C) :
    (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
      iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal) :=
  by
    -- On-domain rows only differ from the subtype family by extra `⊤` values off `D`.
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro v
      simpa [pmInfExtensionWith, hu, v.property] using
        (iInf_le
          (fun w : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u w) v.1)
    · refine le_iInf ?_
      intro v
      by_cases hv : v ∈ D
      · calc
          (iInf fun w : {v // v ∈ D} => (K ⟨u, hu⟩ w : EReal)) ≤
              (K ⟨u, hu⟩ ⟨v, hv⟩ : EReal) :=
            iInf_le (fun w : {v // v ∈ D} => (K ⟨u, hu⟩ w : EReal)) ⟨v, hv⟩
          _ = pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v := by
            simp [pmInfExtensionWith, hu, hv]
      · have htop :
            (iInf fun w : {v // v ∈ D} => (K ⟨u, hu⟩ w : EReal)) ≤ (⊤ : EReal) :=
          le_top
        simpa [pmInfExtensionWith, hu, hv] using htop

/-- Helper for Proposition 36.2.1: when `u ∉ C`, the ambient row infimum of the
`±∞`-extension is forced to be `-∞`. -/
lemma helperForProposition_36_2_1_rowInf_eq_bot_of_not_mem
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hD : D.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (hu : u ∉ C) :
    (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
      (⊥ : EReal) :=
  by
    rcases hD with ⟨vD, hvD⟩
    -- A single in-domain column already has value `⊥`, so the whole infimum is `⊥`.
    refine le_antisymm ?_ bot_le
    calc
      (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) ≤
          pmInfExtensionWith (C := C) (D := D) K (Z := Z) u vD :=
        iInf_le
          (fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) vD
      _ = ⊥ := by
        simp [pmInfExtensionWith, hu, hvD]

/-- Helper for Proposition 36.2.1: package the row-infimum formula, its finiteness
from above, and the `u ∉ C` boundary behavior. -/
lemma helperForProposition_36_2_1_rowInf_package
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hD : D.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) :
    (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
        (if hu : u ∈ C then
            iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)
          else ⊥) ∧
      (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) <
          (⊤ : EReal) ∧
      (u ∉ C →
        (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
          ⊥) :=
  by
    by_cases hu : u ∈ C
    · have hEq :
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
            iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal) :=
        helperForProposition_36_2_1_rowInf_eq_subtype_of_mem
          (C := C) (D := D) (K := K) (Z := Z) (u := u) hu
      rcases hD with ⟨vD, hvD⟩
      have hLt :
          (iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)) < (⊤ : EReal) :=
        by
          -- A finite witness from `D` keeps the subtype infimum strictly below `⊤`.
          calc
            (iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)) ≤
                (K ⟨u, hu⟩ ⟨vD, hvD⟩ : EReal) :=
              iInf_le (fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)) ⟨vD, hvD⟩
            _ < ⊤ := by simp
      refine ⟨?_, ?_, ?_⟩
      · simpa [hu] using hEq
      · calc
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal) := hEq
          _ < ⊤ := hLt
      · intro huNot
        contradiction
    · have hEq :
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
            (⊥ : EReal) :=
        helperForProposition_36_2_1_rowInf_eq_bot_of_not_mem
          (C := C) (D := D) (hD := hD) (K := K) (Z := Z) (u := u) hu
      refine ⟨?_, ?_, ?_⟩
      · simpa [hu] using hEq
      · simpa [hEq]
      · intro _
        exact hEq

/-- Helper for Proposition 36.2.1: when `v ∈ D`, the ambient column supremum of the
`±∞`-extension agrees with the subtype column supremum over `C`. -/
lemma helperForProposition_36_2_1_colSup_eq_subtype_of_mem
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (v : Fin n → ℝ) (hv : v ∈ D) :
    (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
      iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal) :=
  by
    -- On-domain columns only differ from the subtype family by extra `⊥` values off `C`.
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro u
      by_cases hu : u ∈ C
      · calc
          pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v = (K ⟨u, hu⟩ ⟨v, hv⟩ : EReal) := by
            simp [pmInfExtensionWith, hu, hv]
          _ ≤ iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal) :=
            le_iSup (fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal)) ⟨u, hu⟩
      · have hbot : (⊥ : EReal) ≤ iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal) :=
          bot_le
        simpa [pmInfExtensionWith, hu, hv] using hbot
    · refine iSup_le ?_
      intro u
      calc
        (K u ⟨v, hv⟩ : EReal) = pmInfExtensionWith (C := C) (D := D) K (Z := Z) u.1 v := by
          simp [pmInfExtensionWith, u.2, hv]
        _ ≤ iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v :=
          le_iSup (fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) u.1

/-- Helper for Proposition 36.2.1: when `v ∉ D`, the ambient column supremum of the
`±∞`-extension is forced to be `+∞`. -/
lemma helperForProposition_36_2_1_colSup_eq_top_of_not_mem
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hC : C.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (v : Fin n → ℝ) (hv : v ∉ D) :
    (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
      (⊤ : EReal) :=
  by
    rcases hC with ⟨uC, huC⟩
    -- A single in-domain row already has value `⊤`, so the whole supremum is `⊤`.
    refine le_antisymm le_top ?_
    calc
      (⊤ : EReal) = pmInfExtensionWith (C := C) (D := D) K (Z := Z) uC v := by
        simp [pmInfExtensionWith, huC, hv]
      _ ≤ iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v :=
        le_iSup (fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) uC

/-- Helper for Proposition 36.2.1: package the column-supremum formula, its finiteness
from below, and the `v ∉ D` boundary behavior. -/
lemma helperForProposition_36_2_1_colSup_package
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hC : C.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (v : Fin n → ℝ) :
    (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
        (if hv : v ∈ D then
            iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal)
          else ⊤) ∧
      (⊥ : EReal) <
          (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) ∧
      (v ∉ D →
        (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
          ⊤) :=
  by
    by_cases hv : v ∈ D
    · have hEq :
          (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
            iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal) :=
        helperForProposition_36_2_1_colSup_eq_subtype_of_mem
          (C := C) (D := D) (K := K) (Z := Z) (v := v) hv
      rcases hC with ⟨uC, huC⟩
      have hLt :
          (⊥ : EReal) < iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal) :=
        by
          -- A finite witness from `C` keeps the subtype supremum strictly above `⊥`.
          exact lt_of_lt_of_le (by simp)
            (le_iSup (fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal)) ⟨uC, huC⟩)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hv] using hEq
      · calc
          (⊥ : EReal) < iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal) := hLt
          _ = (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) := by
            simpa using hEq.symm
      · intro hvNot
        contradiction
    · have hEq :
          (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
            (⊤ : EReal) :=
        helperForProposition_36_2_1_colSup_eq_top_of_not_mem
          (C := C) (D := D) (hC := hC) (K := K) (Z := Z) (v := v) hv
      refine ⟨?_, ?_, ?_⟩
      · simpa [hv] using hEq
      · simpa [hEq]
      · intro _
        exact hEq

/-- Helper for Proposition 36.2.1: the outer `u`-supremum of the ambient row infima
coincides with the subtype maximin expression over `C × D`. -/
lemma helperForProposition_36_2_1_maximin_eq_subtype
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hD : D.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (iSup fun u : Fin m → ℝ =>
        iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
      (iSup fun u : {u // u ∈ C} => iInf fun v : {v // v ∈ D} => (K u v : EReal)) :=
  by
    -- Outside `C`, the row-infimum is `⊥`, so only the on-domain rows contribute.
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro u
      by_cases hu : u ∈ C
      · calc
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              (iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)) :=
            helperForProposition_36_2_1_rowInf_eq_subtype_of_mem
              (C := C) (D := D) (K := K) (Z := Z) (u := u) hu
          _ ≤ iSup fun u : {u // u ∈ C} => iInf fun v : {v // v ∈ D} => (K u v : EReal) :=
            le_iSup (fun u : {u // u ∈ C} => iInf fun v : {v // v ∈ D} => (K u v : EReal))
              ⟨u, hu⟩
      · calc
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              (⊥ : EReal) :=
            helperForProposition_36_2_1_rowInf_eq_bot_of_not_mem
              (C := C) (D := D) (hD := hD) (K := K) (Z := Z) (u := u) hu
          _ ≤ iSup fun u : {u // u ∈ C} => iInf fun v : {v // v ∈ D} => (K u v : EReal) :=
            bot_le
    · refine iSup_le ?_
      intro u
      calc
        (iInf fun v : {v // v ∈ D} => (K u v : EReal)) =
            (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u.1 v) := by
          simpa using
            (helperForProposition_36_2_1_rowInf_eq_subtype_of_mem
              (C := C) (D := D) (K := K) (Z := Z) (u := u.1) u.2).symm
        _ ≤ iSup fun u : Fin m → ℝ =>
              iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v :=
          le_iSup
            (fun u : Fin m → ℝ =>
              iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v)
            u.1

/-- Helper for Proposition 36.2.1: the outer `v`-infimum of the ambient column suprema
coincides with the subtype minimax expression over `C × D`. -/
lemma helperForProposition_36_2_1_minimax_eq_subtype
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hC : C.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (iInf fun v : Fin n → ℝ =>
        iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
      (iInf fun v : {v // v ∈ D} => iSup fun u : {u // u ∈ C} => (K u v : EReal)) :=
  by
    -- Outside `D`, the column-supremum is `⊤`, so only the on-domain columns contribute.
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro v
      calc
        (iInf fun v : Fin n → ℝ =>
            iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) ≤
            (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v.1) :=
          iInf_le
            (fun v : Fin n → ℝ =>
              iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v)
            v.1
        _ = iSup fun u : {u // u ∈ C} => (K u v : EReal) := by
          simpa using
            helperForProposition_36_2_1_colSup_eq_subtype_of_mem
              (C := C) (D := D) (K := K) (Z := Z) (v := v.1) v.2
    · refine le_iInf ?_
      intro v
      by_cases hv : v ∈ D
      · calc
          (iInf fun v : {v // v ∈ D} => iSup fun u : {u // u ∈ C} => (K u v : EReal)) ≤
              (iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal)) :=
            iInf_le (fun v : {v // v ∈ D} => iSup fun u : {u // u ∈ C} => (K u v : EReal))
              ⟨v, hv⟩
          _ = (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) := by
            simpa using
              (helperForProposition_36_2_1_colSup_eq_subtype_of_mem
                (C := C) (D := D) (K := K) (Z := Z) (v := v) hv).symm
      · calc
          (iInf fun v : {v // v ∈ D} => iSup fun u : {u // u ∈ C} => (K u v : EReal)) ≤
              (⊤ : EReal) :=
            le_top
          _ = (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) := by
            simpa using
              (helperForProposition_36_2_1_colSup_eq_top_of_not_mem
                (C := C) (D := D) (hC := hC) (K := K) (Z := Z) (v := v) hv).symm

/-- Helper for Proposition 36.2.1: an ambient saddle point for the `±∞`-extension is
exactly a subtype saddle point on `C × D`, and the ambient point is forced into `C × D`. -/
lemma helperForProposition_36_2_1_saddlePoint_transport
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ)) (hC : C.Nonempty) (hD : D.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ)
    (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) u₀ v₀ ↔
      ∃ (hu₀ : u₀ ∈ C) (hv₀ : v₀ ∈ D),
        IsSaddlePoint (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal))
          ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩ :=
  by
    constructor
    · intro hs
      rcases hC with ⟨uC, huC⟩
      rcases hD with ⟨vD, hvD⟩
      rcases hs with ⟨hleft, hright⟩
      have hu₀ : u₀ ∈ C := by
        by_contra hu₀
        -- If `u₀ ∉ C`, evaluating the right saddle inequality at `vD ∈ D` forces the center to be `⊥`.
        have hCenterBot :
            pmInfExtensionWith (C := C) (D := D) K (Z := Z) u₀ v₀ = (⊥ : EReal) :=
          by
            have hle :
                pmInfExtensionWith (C := C) (D := D) K (Z := Z) u₀ v₀ ≤
                  pmInfExtensionWith (C := C) (D := D) K (Z := Z) u₀ vD :=
              hright vD
            have hbot :
                pmInfExtensionWith (C := C) (D := D) K (Z := Z) u₀ vD = (⊥ : EReal) := by
              simp [pmInfExtensionWith, hu₀, hvD]
            exact le_bot_iff.mp (hbot ▸ hle)
        by_cases hv₀ : v₀ ∈ D
        · have hleft' := hleft uC
          rw [hCenterBot] at hleft'
          simp [pmInfExtensionWith, huC, hv₀] at hleft'
        · have hleft' := hleft uC
          rw [hCenterBot] at hleft'
          simp [pmInfExtensionWith, huC, hv₀] at hleft'
      have hv₀ : v₀ ∈ D := by
        by_contra hv₀
        -- If `v₀ ∉ D`, evaluating the left saddle inequality at `uC ∈ C` forces the center to be `⊤`.
        have hCenterTop :
            pmInfExtensionWith (C := C) (D := D) K (Z := Z) u₀ v₀ = (⊤ : EReal) :=
          by
            have hge :
                pmInfExtensionWith (C := C) (D := D) K (Z := Z) uC v₀ ≤
                  pmInfExtensionWith (C := C) (D := D) K (Z := Z) u₀ v₀ :=
              hleft uC
            have htop :
                pmInfExtensionWith (C := C) (D := D) K (Z := Z) uC v₀ = (⊤ : EReal) := by
              simp [pmInfExtensionWith, huC, hv₀]
            exact top_le_iff.mp (htop ▸ hge)
        have hright' := hright vD
        rw [hCenterTop] at hright'
        simp [pmInfExtensionWith, hu₀, hvD] at hright'
      refine ⟨hu₀, hv₀, ?_⟩
      refine ⟨?_, ?_⟩
      · intro u
        -- Once the center is known to lie in `C × D`, the left saddle inequality restricts verbatim.
        have hleft' := hleft u.1
        simpa [pmInfExtensionWith, hu₀, hv₀, u.2] using hleft'
      · intro v
        -- The right saddle inequality restricts in the same way.
        have hright' := hright v.1
        simpa [pmInfExtensionWith, hu₀, hv₀, v.2] using hright'
    · rintro ⟨hu₀, hv₀, hs⟩
      rcases hs with ⟨hleft, hright⟩
      refine ⟨?_, ?_⟩
      · intro u
        by_cases hu : u ∈ C
        · -- On-domain rows reduce to the subtype saddle inequality.
          have hleft' := hleft ⟨u, hu⟩
          simpa [pmInfExtensionWith, hu, hu₀, hv₀] using hleft'
        · -- Off-domain rows contribute `⊥`, so the left inequality is automatic.
          simp [pmInfExtensionWith, hu, hu₀, hv₀]
      · intro v
        by_cases hv : v ∈ D
        · -- On-domain columns reduce to the subtype saddle inequality.
          have hright' := hright ⟨v, hv⟩
          simpa [pmInfExtensionWith, hu₀, hv, hv₀] using hright'
        · -- Off-domain columns contribute `⊤`, so the right inequality is automatic.
          simp [pmInfExtensionWith, hu₀, hv₀, hv]

/-- Proposition 36.2.1: (`±∞`-extension from `C × D` to `ℝ^m × ℝ^n`.)
Let `C ⊆ ℝ^m` and `D ⊆ ℝ^n` be nonempty and let `K : C × D → ℝ`. Define an extension
`K̄ : ℝ^m × ℝ^n → [-∞, +∞]` by setting `K̄ = K` on `C × D`, `K̄ = +∞` on `C × (Dᶜ)`,
`K̄ = -∞` on `(Cᶜ) × D`, and choosing an arbitrary value (depending on `(u,v)`) on
`(Cᶜ) × (Dᶜ)`. Then:
(1) `inf_v K̄(u,v) = inf_{v ∈ D} K(u,v) < +∞`, with value `-∞` when `u ∉ C`;
(2) `sup_u K̄(u,v) = sup_{u ∈ C} K(u,v) > -∞`, with value `+∞` when `v ∉ D`;
(3) consequently the maximin/minimax values computed on `ℝ^m × ℝ^n` coincide with those
computed on `C × D`, and `K̄` has a saddle-value (resp. saddle-point) w.r.t. `ℝ^m × ℝ^n`
iff `K` has one w.r.t. `C × D` (with coinciding values/points). -/
theorem pmInfExtension_inf_sup_and_saddle_equivalences
    {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (K : {u // u ∈ C} → {v // v ∈ D} → ℝ) (Z : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (∀ u : Fin m → ℝ,
        (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
            (if hu : u ∈ C then
                iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)
              else ⊥) ∧
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) <
              (⊤ : EReal) ∧
          (u ∉ C →
            (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              ⊥)) ∧
      (∀ v : Fin n → ℝ,
        (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
            (if hv : v ∈ D then
                iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal)
              else ⊤) ∧
          (⊥ : EReal) <
              (iSup fun u : Fin m → ℝ =>
                pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) ∧
          (v ∉ D →
            (iSup fun u : Fin m → ℝ =>
                pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              ⊤)) ∧
      (iSup fun u : Fin m → ℝ =>
          iInf fun v : Fin n → ℝ =>
            pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
          (iSup fun u : {u // u ∈ C} => iInf fun v : {v // v ∈ D} => (K u v : EReal)) ∧
      (iInf fun v : Fin n → ℝ =>
          iSup fun u : Fin m → ℝ =>
            pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
          (iInf fun v : {v // v ∈ D} => iSup fun u : {u // u ∈ C} => (K u v : EReal)) ∧
      (∀ x : EReal,
        IsMinimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
              (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) x ↔
          IsMinimaxValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) x) ∧
      (∀ (u₀ : Fin m → ℝ) (v₀ : Fin n → ℝ),
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
              (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) u₀ v₀ ↔
          ∃ (hu₀ : u₀ ∈ C) (hv₀ : v₀ ∈ D),
            IsSaddlePoint (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal))
              ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩) :=
  by
    -- Assemble the row/column packages first, then rewrite the outer maximin/minimax expressions.
    have hRow :
        ∀ u : Fin m → ℝ,
          (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              (if hu : u ∈ C then
                  iInf fun v : {v // v ∈ D} => (K ⟨u, hu⟩ v : EReal)
                else ⊥) ∧
            (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) <
                (⊤ : EReal) ∧
            (u ∉ C →
              (iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
                ⊥) :=
      fun u => helperForProposition_36_2_1_rowInf_package
        (C := C) (D := D) (hD := hD) (K := K) (Z := Z) u
    have hCol :
        ∀ v : Fin n → ℝ,
          (iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
              (if hv : v ∈ D then
                  iSup fun u : {u // u ∈ C} => (K u ⟨v, hv⟩ : EReal)
                else ⊤) ∧
            (⊥ : EReal) <
                (iSup fun u : Fin m → ℝ =>
                  pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) ∧
            (v ∉ D →
              (iSup fun u : Fin m → ℝ =>
                  pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
                ⊤) :=
      fun v => helperForProposition_36_2_1_colSup_package
        (C := C) (D := D) (hC := hC) (K := K) (Z := Z) v
    have hMax :
        (iSup fun u : Fin m → ℝ =>
            iInf fun v : Fin n → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
          (iSup fun u : {u // u ∈ C} => iInf fun v : {v // v ∈ D} => (K u v : EReal)) :=
      helperForProposition_36_2_1_maximin_eq_subtype
        (C := C) (D := D) (hD := hD) (K := K) (Z := Z)
    have hMin :
        (iInf fun v : Fin n → ℝ =>
            iSup fun u : Fin m → ℝ => pmInfExtensionWith (C := C) (D := D) K (Z := Z) u v) =
          (iInf fun v : {v // v ∈ D} => iSup fun u : {u // u ∈ C} => (K u v : EReal)) :=
      helperForProposition_36_2_1_minimax_eq_subtype
        (C := C) (D := D) (hC := hC) (K := K) (Z := Z)
    refine ⟨hRow, hCol, hMax, hMin, ?_, ?_⟩
    · intro x
      -- The minimax-value predicate only changes by rewriting maximin/minimax along `hMax` and `hMin`.
      constructor
      · rintro ⟨_, _, hEq, hx⟩
        rcases hC with ⟨uC, huC⟩
        rcases hD with ⟨vD, hvD⟩
        refine ⟨⟨⟨uC, huC⟩⟩, ⟨⟨vD, hvD⟩⟩, ?_, ?_⟩
        · calc
            maximinValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) =
                maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
                  (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) := by
                  simpa [maximinValue] using hMax.symm
            _ = minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
                  (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) := hEq
            _ = minimaxValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) := by
                  simpa [minimaxValue] using hMin
        · calc
            x = maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
                  (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) := hx
            _ = maximinValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) := by
                  simpa [maximinValue] using hMax
      · rintro ⟨_, _, hEq, hx⟩
        refine ⟨inferInstance, inferInstance, ?_, ?_⟩
        · calc
            maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
                (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) =
                maximinValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) := by
                  simpa [maximinValue] using hMax
            _ = minimaxValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) := hEq
            _ = minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
                  (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) := by
                  simpa [minimaxValue] using hMin.symm
        · calc
            x = maximinValue (C := {u // u ∈ C}) (D := {v // v ∈ D}) (fun u v => (K u v : EReal)) := hx
            _ = maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
                  (pmInfExtensionWith (C := C) (D := D) K (Z := Z)) := by
                  simpa [maximinValue] using hMax.symm
    · intro u₀ v₀
      -- Saddle points transport exactly once the center is known to lie in `C × D`.
      exact helperForProposition_36_2_1_saddlePoint_transport
        (C := C) (D := D) (hC := hC) (hD := hD) (K := K) (Z := Z) u₀ v₀

/-- The first domain `dom₁ K` of an extended-real saddle function `K(u,v)`, defined as the set of
points `u` where `inf_v K(u,v) > -∞`. -/
noncomputable def saddleDom1 {U V : Type*} (K : U → V → EReal) : Set U :=
  {u | (⊥ : EReal) < iInf fun v : V => K u v}

/-- The second domain `dom₂ K` of an extended-real saddle function `K(u,v)`, defined as the set of
points `v` where `sup_u K(u,v) < +∞`. -/
noncomputable def saddleDom2 {U V : Type*} (K : U → V → EReal) : Set V :=
  {v | (iSup fun u : U => K u v) < (⊤ : EReal)}

/-- A bundled hypothesis package expressing the *domain boundary behavior* expected of an
extended-real saddle function `K` used in minimax problems: the projected domains `dom₁ K` and
`dom₂ K` are nonempty, `K(u,v) = -∞` on `(dom₁ K)ᶜ × dom₂ K`, and `K(u,v) = +∞` on
`dom₁ K × (dom₂ K)ᶜ`. -/
def HasSaddleDomBoundaryBehavior {U V : Type*} (K : U → V → EReal) : Prop :=
  (saddleDom1 (U := U) (V := V) K).Nonempty ∧
    (saddleDom2 (U := U) (V := V) K).Nonempty ∧
      (∀ u : U, ∀ v : V,
          u ∉ saddleDom1 (U := U) (V := V) K → v ∈ saddleDom2 (U := U) (V := V) K →
            K u v = (⊥ : EReal)) ∧
        (∀ u : U, ∀ v : V,
          u ∈ saddleDom1 (U := U) (V := V) K → v ∉ saddleDom2 (U := U) (V := V) K →
            K u v = (⊤ : EReal))

/-- The core concavity/convexity/closedness/properness content of the textbook hypothesis
“closed proper concave-convex”, separated from the `±∞` boundary-value behavior. -/
def IsClosedProperConcaveConvexCore {U V : Type*}
    [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] (K : U → V → EReal) : Prop :=
  (∀ v, v ∈ saddleDom2 (U := U) (V := V) K →
      IsClosed {p : U × ℝ | (p.2 : EReal) ≤ K p.1 v}) ∧
    (∀ v, v ∈ saddleDom2 (U := U) (V := V) K →
      Convex ℝ {p : U × ℝ | (p.2 : EReal) ≤ K p.1 v}) ∧
      (∀ v, v ∈ saddleDom2 (U := U) (V := V) K → ∃ u : U, (⊥ : EReal) < K u v) ∧
        (∀ u, u ∈ saddleDom1 (U := U) (V := V) K →
          IsClosed {p : V × ℝ | K u p.1 ≤ (p.2 : EReal)}) ∧
          (∀ u, u ∈ saddleDom1 (U := U) (V := V) K →
            Convex ℝ {p : V × ℝ | K u p.1 ≤ (p.2 : EReal)}) ∧
            (∀ u, u ∈ saddleDom1 (U := U) (V := V) K → ∃ v : V, K u v < (⊤ : EReal))

/-- The book-level hypothesis that an extended-real function `K(u,v)` is a *closed proper
concave-convex saddle function* (Rockafellar, Theorem 36.3 context).

This predicate is intentionally separated from `HasSaddleDomBoundaryBehavior`: the latter captures
the `±∞` boundary values on complements of `dom₁ K` and `dom₂ K`, while this predicate is meant to
also include the concavity/convexity and closedness/properness content of the textbook notion. -/
def IsClosedProperConcaveConvex {U V : Type*}
    [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] (K : U → V → EReal) : Prop :=
  HasSaddleDomBoundaryBehavior (U := U) (V := V) K ∧ IsClosedProperConcaveConvexCore (U := U) (V := V) K

/-- Helper for Theorem 36.3: on a row indexed by `u ∈ dom₁ K`, restricting the infimum to
`dom₂ K` does not change its value. -/
lemma helperForTheorem_36_3_rowInf_eq_subtype_of_memSaddleDom1
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hbdry : HasSaddleDomBoundaryBehavior K)
    (u : Fin m → ℝ) (hu : u ∈ saddleDom1 K) :
    iInf (fun v : Fin n → ℝ => K u v) =
      iInf (fun v : {v // v ∈ saddleDom2 K} => K u v) :=
  by
    rcases hbdry with ⟨_, _, _, hTopStrip⟩
    -- Off-domain columns contribute only `⊤`, so the row infimum is unchanged.
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro v
      simpa using (iInf_le (fun w : Fin n → ℝ => K u w) v.1)
    · refine le_iInf ?_
      intro v
      by_cases hv : v ∈ saddleDom2 K
      · simpa using
          (iInf_le (fun w : {v // v ∈ saddleDom2 K} => K u w) ⟨v, hv⟩)
      · have hleTop : (iInf fun w : {v // v ∈ saddleDom2 K} => K u w) ≤ (⊤ : EReal) := le_top
        simpa [hTopStrip u v hu hv] using hleTop

/-- Helper for Theorem 36.3: outside `dom₁ K`, the row infimum is exactly `-∞`. -/
lemma helperForTheorem_36_3_rowInf_eq_bot_of_not_memSaddleDom1
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (hu : u ∉ saddleDom1 K) :
    iInf (fun v : Fin n → ℝ => K u v) = (⊥ : EReal) :=
  by
    -- Negating the definition of `dom₁ K` forces the row infimum down to `⊥`.
    have hle : iInf (fun v : Fin n → ℝ => K u v) ≤ (⊥ : EReal) := by
      have hnot : ¬ ((⊥ : EReal) < iInf (fun v : Fin n → ℝ => K u v)) := by
        simpa [saddleDom1] using hu
      exact not_lt.mp hnot
    exact le_antisymm hle bot_le

/-- Helper for Theorem 36.3: on a column indexed by `v ∈ dom₂ K`, restricting the supremum to
`dom₁ K` does not change its value. -/
lemma helperForTheorem_36_3_colSup_eq_subtype_of_memSaddleDom2
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hbdry : HasSaddleDomBoundaryBehavior K)
    (v : Fin n → ℝ) (hv : v ∈ saddleDom2 K) :
    iSup (fun u : Fin m → ℝ => K u v) =
      iSup (fun u : {u // u ∈ saddleDom1 K} => K u v) :=
  by
    rcases hbdry with ⟨_, _, hBotStrip, _⟩
    -- Off-domain rows contribute only `⊥`, so the column supremum is unchanged.
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro u
      by_cases hu : u ∈ saddleDom1 K
      · simpa using
          (le_iSup (fun w : {u // u ∈ saddleDom1 K} => K w v) ⟨u, hu⟩)
      · have hbotLe : (⊥ : EReal) ≤ iSup (fun w : {u // u ∈ saddleDom1 K} => K w v) := bot_le
        simpa [hBotStrip u v hu hv] using hbotLe
    · refine iSup_le ?_
      intro u
      exact le_iSup (fun w : Fin m → ℝ => K w v) u.1

/-- Helper for Theorem 36.3: outside `dom₂ K`, the column supremum is exactly `+∞`. -/
lemma helperForTheorem_36_3_colSup_eq_top_of_not_memSaddleDom2
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (v : Fin n → ℝ) (hv : v ∉ saddleDom2 K) :
    iSup (fun u : Fin m → ℝ => K u v) = (⊤ : EReal) :=
  by
    -- Negating the definition of `dom₂ K` forces the column supremum up to `⊤`.
    have hge : (⊤ : EReal) ≤ iSup (fun u : Fin m → ℝ => K u v) := by
      have hnot : ¬ (iSup (fun u : Fin m → ℝ => K u v) < (⊤ : EReal)) := by
        simpa [saddleDom2] using hv
      exact not_lt.mp hnot
    exact le_antisymm le_top hge

/-- Helper for Theorem 36.3: restricting the maximin expression from `ℝ^m × ℝ^n` to
`dom₁ K × dom₂ K` does not change its value. -/
lemma helperForTheorem_36_3_maximin_eq_restrictedToSaddleDom
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hbdry : HasSaddleDomBoundaryBehavior K) :
    maximinValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
      maximinValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
        (fun u v => K u v) :=
  by
    unfold maximinValue
    -- Outside `dom₁ K`, the row infimum is `⊥`, so only rows in `dom₁ K` matter.
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro u
      by_cases hu : u ∈ saddleDom1 K
      · calc
          (iInf fun v : Fin n → ℝ => K u v) =
              iInf (fun v : {v // v ∈ saddleDom2 K} => K u v) :=
            helperForTheorem_36_3_rowInf_eq_subtype_of_memSaddleDom1
              (K := K) (hbdry := hbdry) (u := u) hu
          _ ≤ iSup (fun w : {u // u ∈ saddleDom1 K} =>
                iInf (fun v : {v // v ∈ saddleDom2 K} => K w v)) :=
            le_iSup
              (fun w : {u // u ∈ saddleDom1 K} =>
                iInf (fun v : {v // v ∈ saddleDom2 K} => K w v))
              ⟨u, hu⟩
      · calc
          (iInf fun v : Fin n → ℝ => K u v) = (⊥ : EReal) :=
            helperForTheorem_36_3_rowInf_eq_bot_of_not_memSaddleDom1
              (K := K) (u := u) hu
          _ ≤ iSup (fun w : {u // u ∈ saddleDom1 K} =>
                iInf (fun v : {v // v ∈ saddleDom2 K} => K w v)) := bot_le
    · refine iSup_le ?_
      intro u
      calc
        (iInf fun v : {v // v ∈ saddleDom2 K} => K u v) =
            iInf (fun v : Fin n → ℝ => K u.1 v) := by
          simpa using
            (helperForTheorem_36_3_rowInf_eq_subtype_of_memSaddleDom1
              (K := K) (hbdry := hbdry) (u := u.1) u.2).symm
        _ ≤ iSup (fun w : Fin m → ℝ => iInf (fun v : Fin n → ℝ => K w v)) :=
          le_iSup (fun w : Fin m → ℝ => iInf (fun v : Fin n → ℝ => K w v)) u.1

/-- Helper for Theorem 36.3: restricting the minimax expression from `ℝ^m × ℝ^n` to
`dom₁ K × dom₂ K` does not change its value. -/
lemma helperForTheorem_36_3_minimax_eq_restrictedToSaddleDom
    {m n : ℕ} (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hbdry : HasSaddleDomBoundaryBehavior K) :
    minimaxValue (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K =
      minimaxValue (C := {u // u ∈ saddleDom1 K}) (D := {v // v ∈ saddleDom2 K})
        (fun u v => K u v) :=
  by
    unfold minimaxValue
    -- Outside `dom₂ K`, the column supremum is `⊤`, so only columns in `dom₂ K` matter.
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro v
      calc
        (iInf fun w : Fin n → ℝ => iSup (fun u : Fin m → ℝ => K u w)) ≤
            iSup (fun u : Fin m → ℝ => K u v.1) :=
          iInf_le (fun w : Fin n → ℝ => iSup (fun u : Fin m → ℝ => K u w)) v.1
        _ = iSup (fun u : {u // u ∈ saddleDom1 K} => K u v) := by
          simpa using
            helperForTheorem_36_3_colSup_eq_subtype_of_memSaddleDom2
              (K := K) (hbdry := hbdry) (v := v.1) v.2
    · refine le_iInf ?_
      intro v
      by_cases hv : v ∈ saddleDom2 K
      · calc
          (iInf fun w : {v // v ∈ saddleDom2 K} =>
              iSup (fun u : {u // u ∈ saddleDom1 K} => K u w)) ≤
            iSup (fun u : {u // u ∈ saddleDom1 K} => K u v) :=
            iInf_le
              (fun w : {v // v ∈ saddleDom2 K} =>
                iSup (fun u : {u // u ∈ saddleDom1 K} => K u w))
              ⟨v, hv⟩
        _ = iSup (fun u : Fin m → ℝ => K u v) := by
          simpa using
            (helperForTheorem_36_3_colSup_eq_subtype_of_memSaddleDom2
              (K := K) (hbdry := hbdry) (v := v) hv).symm
      · calc
          (iInf fun w : {v // v ∈ saddleDom2 K} =>
              iSup (fun u : {u // u ∈ saddleDom1 K} => K u w)) ≤ (⊤ : EReal) := le_top
          _ = iSup (fun u : Fin m → ℝ => K u v) := by
            simpa using
              (helperForTheorem_36_3_colSup_eq_top_of_not_memSaddleDom2
                (K := K) (v := v) hv).symm

end Section36
end Chap07
