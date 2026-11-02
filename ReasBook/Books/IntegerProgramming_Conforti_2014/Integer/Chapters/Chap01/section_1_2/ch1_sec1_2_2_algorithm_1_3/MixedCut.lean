import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_2_definition_1_9

open scoped Matrix

variable {n p : ℕ}

/-- A cutting plane `α x + γ y ≤ β` for a mixed-integer problem in `n` integer and `p`
continuous variables. -/
structure MixedCut (n p : ℕ) where
  xCoeff : Fin n → ℝ
  yCoeff : Fin p → ℝ
  rhs : ℝ

namespace MixedCut

/-- The left-hand side `α x + γ y` of a mixed cut evaluated at a mixed point. -/
@[expose] def eval (cut : MixedCut n p) (xy : MixedRealPoint n p) : ℝ :=
  cut.xCoeff ⬝ᵥ xy.1 + cut.yCoeff ⬝ᵥ xy.2

/-- Unfolding equation for `cut.eval xy`. -/
theorem eval_def (cut : MixedCut n p) (xy : MixedRealPoint n p) :
    cut.eval xy = cut.xCoeff ⬝ᵥ xy.1 + cut.yCoeff ⬝ᵥ xy.2 :=
  rfl

/-- The cut inequality is valid on the mixed feasible set `S`. -/
@[expose] def validFor (cut : MixedCut n p) (S : Set (MixedRealPoint n p)) : Prop :=
  is_valid_inequality ((Fin.appendEquiv n p) '' S) (Fin.append cut.xCoeff cut.yCoeff) cut.rhs

/-- `cut.validFor S` unfolds to validity of the flattened inequality on `S`. -/
theorem validFor_iff {cut : MixedCut n p} {S : Set (MixedRealPoint n p)} :
    cut.validFor S ↔
      is_valid_inequality ((Fin.appendEquiv n p) '' S) (Fin.append cut.xCoeff cut.yCoeff) cut.rhs :=
  Iff.rfl

/-- `cut.cutsAt S xy0` means that `cut` is a Definition 1.9 cutting plane for `S` at `xy0`. -/
@[expose] def cutsAt
    (cut : MixedCut n p)
    (S : Set (MixedRealPoint n p))
    (xy0 : MixedRealPoint n p) : Prop :=
  isCuttingPlaneAt S xy0 cut.xCoeff cut.yCoeff cut.rhs

/-- `cut.cutsAt S xy0` unfolds to validity on `S` together with strict violation at `xy0`. -/
theorem cutsAt_iff
    {cut : MixedCut n p}
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p} :
    cut.cutsAt S xy0 ↔ cut.validFor S ∧ cut.rhs < cut.eval xy0 := by
  constructor
  · intro hcut
    exact ⟨hcut.valid, by simpa [MixedCut.eval] using hcut.cutsOff⟩
  · rintro ⟨hvalid, hcutsOff⟩
    exact isCuttingPlaneAt.ofConditions S xy0 cut.xCoeff cut.yCoeff cut.rhs hvalid <|
      by simpa [MixedCut.eval] using hcutsOff

/-- A mixed cut that cuts at `xy0` is valid on `S`. -/
theorem cutsAt_valid
    {cut : MixedCut n p}
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p}
    (hcut : cut.cutsAt S xy0) :
    cut.validFor S :=
  hcut.valid

/-- A mixed cut that cuts at `xy0` is strictly violated by `xy0`. -/
theorem cutsAt_cutsOff
    {cut : MixedCut n p}
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p}
    (hcut : cut.cutsAt S xy0) :
    cut.rhs < cut.eval xy0 := by
  simpa [MixedCut.eval] using hcut.cutsOff

/-- A mixed cut that cuts at `xy0` excludes `xy0` from the feasible set `S`. -/
theorem cutsAt_not_mem
    {cut : MixedCut n p}
    {S : Set (MixedRealPoint n p)}
    {xy0 : MixedRealPoint n p}
    (hcut : cut.cutsAt S xy0) :
    xy0 ∉ S :=
  isCuttingPlaneAt.not_mem hcut

/-- The halfspace cut out by the inequality `α x + γ y ≤ β`. -/
@[expose] def halfspace (cut : MixedCut n p) : Set (MixedRealPoint n p) :=
  {xy | cut.eval xy ≤ cut.rhs}

/-- Membership in `cut.halfspace` means satisfaction of the cut inequality. -/
theorem mem_halfspace_iff {cut : MixedCut n p} {xy : MixedRealPoint n p} :
    xy ∈ cut.halfspace ↔ cut.eval xy ≤ cut.rhs :=
  Iff.rfl

/-- The mixed point `xy` satisfies the cut inequality `α x + γ y ≤ β`. -/
@[expose] def satisfied (cut : MixedCut n p) (xy : MixedRealPoint n p) : Prop :=
  xy ∈ cut.halfspace

/-- `cut.satisfied xy` unfolds to the scalar inequality `cut.eval xy ≤ cut.rhs`. -/
theorem satisfied_iff {cut : MixedCut n p} {xy : MixedRealPoint n p} :
    cut.satisfied xy ↔ cut.eval xy ≤ cut.rhs :=
  Iff.rfl

end MixedCut
