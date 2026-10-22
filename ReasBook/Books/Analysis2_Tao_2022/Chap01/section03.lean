/-
Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap01
section Section03

variable {X : Type*} [MetricSpace X]

/-- Definition 1.15 (Relative topology). Let `(X,d)` be a metric space and let `Y`
be a subset of `X`. The induced metric subspace on `Y` is the metric space `(Y, d`
restricted to `Y x Y`). A subset `E` of `Y` is relatively open in `Y` if for every
`y` in `E` there exists `r > 0` such that `{z in Y | dist y z < r}` is contained in
`E`. A subset `E` of `Y` is relatively closed in `Y` if it is closed in the induced
metric space, equivalently if `Y \ E` is relatively open in `Y`. Used in Proposition 1.18. -/
abbrev inducedMetricSubspace (Y : Set X) := {x : X // Y x}

/-- A subset `E` of `Y` is relatively open in `Y` if it is open in the metric
subspace induced on `Y`. Used in Proposition 1.18. -/
def IsRelOpen (Y E : Set X) : Prop :=
  And (Set.Subset E Y)
    (IsOpen (Set.preimage (Subtype.val : {x // Y x} -> X) E))

/-- A subset `E` of `Y` is relatively closed in `Y` if it is closed in the metric
subspace induced on `Y`. Used in Proposition 1.18. -/
def IsRelClosed (Y E : Set X) : Prop :=
  And (Set.Subset E Y)
    (IsClosed (Set.preimage (Subtype.val : {x // Y x} -> X) E))

omit [MetricSpace X] in
/-- Helper for Proposition 1.18: preimage of an intersection with `Y` under the
subtype inclusion equals the preimage of the first set. -/
lemma helperForProposition_1_18_preimage_inter_eq {Y V : Set X} :
    Set.preimage (Subtype.val : {x // Y x} → X) (Set.inter V Y) =
      Set.preimage (Subtype.val : {x // Y x} → X) V := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact And.intro hx x.property

omit [MetricSpace X] in
/-- Helper for Proposition 1.18: recover `E = V ∩ Y` from equality of preimages. -/
lemma helperForProposition_1_18_eq_inter_of_preimage_eq {Y E V : Set X}
    (hEY : E ⊆ Y)
    (hpre :
      Set.preimage (Subtype.val : {x // Y x} → X) V =
        Set.preimage (Subtype.val : {x // Y x} → X) E) :
    E = Set.inter V Y := by
  ext x
  constructor
  · intro hxE
    have hxY : x ∈ Y := hEY hxE
    have hxPreE :
        (⟨x, hxY⟩ : {x // Y x}) ∈
          Set.preimage (Subtype.val : {x // Y x} → X) E := by
      simpa using hxE
    have hxPreV :
        (⟨x, hxY⟩ : {x // Y x}) ∈
          Set.preimage (Subtype.val : {x // Y x} → X) V := by
      simpa [hpre] using hxPreE
    have hxV : x ∈ V := by
      simpa using hxPreV
    exact And.intro hxV hxY
  · intro hx
    have hxY : x ∈ Y := hx.2
    have hxPreV :
        (⟨x, hxY⟩ : {x // Y x}) ∈
          Set.preimage (Subtype.val : {x // Y x} → X) V := by
      simpa using hx.1
    have hxPreE :
        (⟨x, hxY⟩ : {x // Y x}) ∈
          Set.preimage (Subtype.val : {x // Y x} → X) E := by
      simpa [hpre] using hxPreV
    simpa using hxPreE

/-- Proposition 1.18. Let `(X,d)` be a metric space, let `Y` be a subset of `X`,
and let `E` be a subset of `Y`. (a) `E` is open in the subspace metric space on
`Y` iff there exists an open set `V` in `X` such that `E = Set.inter V Y`. (b)
`E` is closed in the subspace metric space on `Y` iff there exists a closed set
`K` in `X` such that `E = Set.inter K Y`. -/
theorem relOpen_relClosed_iff_eq_inter {Y E : Set X} :
    (IsRelOpen Y E ↔ ∃ V : Set X, IsOpen V ∧ E = Set.inter V Y) ∧
      (IsRelClosed Y E ↔ ∃ K : Set X, IsClosed K ∧ E = Set.inter K Y) := by
  constructor
  · constructor
    · intro hRelOpen
      rcases hRelOpen with ⟨hEY, hOpen⟩
      rcases isOpen_induced_iff.mp hOpen with ⟨V, hVopen, hpre⟩
      refine ⟨V, hVopen, ?_⟩
      exact
        helperForProposition_1_18_eq_inter_of_preimage_eq (Y := Y) (E := E) (V := V) hEY hpre
    · intro hExists
      rcases hExists with ⟨V, hVopen, hE⟩
      have hEY : E ⊆ Y := by
        intro x hx
        have hx' : x ∈ Set.inter V Y := by
          simpa [hE] using hx
        exact hx'.2
      have hOpenPreV :
          IsOpen (Set.preimage (Subtype.val : {x // Y x} → X) V) :=
        hVopen.preimage continuous_subtype_val
      have hPre :
          Set.preimage (Subtype.val : {x // Y x} → X) E =
            Set.preimage (Subtype.val : {x // Y x} → X) V := by
        calc
          Set.preimage (Subtype.val : {x // Y x} → X) E =
              Set.preimage (Subtype.val : {x // Y x} → X) (Set.inter V Y) := by
            simp [hE]
          _ = Set.preimage (Subtype.val : {x // Y x} → X) V := by
            simpa using (helperForProposition_1_18_preimage_inter_eq (Y := Y) (V := V))
      have hOpenPreE :
          IsOpen (Set.preimage (Subtype.val : {x // Y x} → X) E) := by
        simpa [hPre] using hOpenPreV
      exact And.intro hEY hOpenPreE
  · constructor
    · intro hRelClosed
      rcases hRelClosed with ⟨hEY, hClosed⟩
      rcases isClosed_induced_iff.mp hClosed with ⟨K, hKclosed, hpre⟩
      refine ⟨K, hKclosed, ?_⟩
      exact
        helperForProposition_1_18_eq_inter_of_preimage_eq (Y := Y) (E := E) (V := K) hEY hpre
    · intro hExists
      rcases hExists with ⟨K, hKclosed, hE⟩
      have hEY : E ⊆ Y := by
        intro x hx
        have hx' : x ∈ Set.inter K Y := by
          simpa [hE] using hx
        exact hx'.2
      have hClosedPreK :
          IsClosed (Set.preimage (Subtype.val : {x // Y x} → X) K) :=
        hKclosed.preimage continuous_subtype_val
      have hPre :
          Set.preimage (Subtype.val : {x // Y x} → X) E =
            Set.preimage (Subtype.val : {x // Y x} → X) K := by
        calc
          Set.preimage (Subtype.val : {x // Y x} → X) E =
              Set.preimage (Subtype.val : {x // Y x} → X) (Set.inter K Y) := by
            simp [hE]
          _ = Set.preimage (Subtype.val : {x // Y x} → X) K := by
            simpa using (helperForProposition_1_18_preimage_inter_eq (Y := Y) (V := K))
      have hClosedPreE :
          IsClosed (Set.preimage (Subtype.val : {x // Y x} → X) E) := by
        simpa [hPre] using hClosedPreK
      exact And.intro hEY hClosedPreE

/-- Part (a) for Proposition 1.18: relative openness in `Y` iff `E = Set.inter V Y`
for some open `V` in `X`. -/
lemma isRelOpen_iff_eq_inter {Y E : Set X} :
    IsRelOpen Y E ↔ ∃ V : Set X, IsOpen V ∧ E = Set.inter V Y := by
  simpa using (relOpen_relClosed_iff_eq_inter (Y := Y) (E := E)).1

/-- Part (b): relative closedness in `Y` iff `E = Set.inter K Y` for some closed
`K` in `X`. Used in Proposition 1.18. -/
lemma isRelClosed_iff_eq_inter {Y E : Set X} :
    IsRelClosed Y E ↔ ∃ K : Set X, IsClosed K ∧ E = Set.inter K Y := by
  simpa using (relOpen_relClosed_iff_eq_inter (Y := Y) (E := E)).2

end Section03
end Chap01
