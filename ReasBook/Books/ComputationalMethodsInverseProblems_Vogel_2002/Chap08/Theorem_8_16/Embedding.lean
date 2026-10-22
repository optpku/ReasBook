/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.EmbeddingBounds
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}
variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

namespace BVCompactness

/-- The underlying `L¹(Ω)` representative of a Chapter 8 `BV(Ω)` element belongs to
`Lᵖ(Ω)` whenever `p` lies between `1` and the critical exponent. -/
theorem toLp_memLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p ≤ criticalExponent d)
    (u : BV Ω) :
    MeasureTheory.MemLp u.toL1 p (domainMeasure Ω) := by
  by_cases h1 : d = 1
  · subst h1
    -- Route correction: in one dimension, descend from the exact endpoint `L∞` owner.
    have hp_top : p ≤ (⊤ : ENNReal) := by
      simpa [criticalExponent_one] using hp
    exact (endpointExponentEstimate (Ω := Ω) hΩ u).mono_exponent hp_top
  · have h1d : 1 < d := lt_of_le_of_ne hd (by simpa [eq_comm] using h1)
    -- Away from `d = 1`, descend from the exact critical exponent owner.
    exact (criticalExponentEstimate (d := d) (Ω := Ω) h1d hΩ u).mono_exponent hp

/-- The canonical BV-to-`Lᵖ(Ω)` embedding from Theorem 8.16. Its underlying
almost-everywhere class is exactly the `L¹(Ω)` representative `u.toL1`. -/
def toLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p ≤ criticalExponent d) :
    BV Ω → MeasureTheory.Lp ℝ p (domainMeasure Ω) :=
  fun u ↦ MeasureTheory.MemLp.toLp u.toL1 (toLp_memLp hd hΩ hp u)

/-- `BVCompactness.toLp` preserves the underlying almost-everywhere class. -/
@[simp] theorem toLp_toAEEqFun
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p ≤ criticalExponent d)
    (u : BV Ω) :
    ((toLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u :
        MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
  apply MeasureTheory.AEEqFun.ext
  simpa [toLp] using MeasureTheory.MemLp.coeFn_toLp (toLp_memLp hd hΩ hp u)

/-- The strict-subcritical BV-to-`Lᵖ(Ω)` embedding used in Theorem 8.16 (1). -/
def toSubcriticalLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d) :
    BV Ω → MeasureTheory.Lp ℝ p (domainMeasure Ω) :=
  toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp)

/-- `BVCompactness.toSubcriticalLp` preserves the underlying almost-everywhere
class. -/
@[simp] theorem toSubcriticalLp_toAEEqFun
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (u : BV Ω) :
    ((toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u :
        MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
  change
    ((toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) u :
        MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ)
  exact toLp_toAEEqFun (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) u

/-- The canonical set-valued `BV(Ω) → Lᵖ(Ω)` image surface for Theorem 8.16. -/
@[expose] def lpImage
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p ≤ criticalExponent d)
    (S : Set (BV Ω)) :
    Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)) :=
  toLp hd hΩ hp '' S

/-- Helper for Theorem 8.16: the canonical `BV(Ω) → Lᵖ(Ω)` image surface is monotone in the
source set. -/
theorem lpImage_mono
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p ≤ criticalExponent d)
    {S T : Set (BV Ω)}
    (hST : S ⊆ T) :
    lpImage (d := d) (Ω := Ω) (p := p) hd hΩ hp S ⊆
      lpImage (d := d) (Ω := Ω) (p := p) hd hΩ hp T := by
  intro y hy
  -- Unpack the public image surface once, then push the source membership through `hST`.
  rcases hy with ⟨u, hu, rfl⟩
  exact ⟨u, hST hu, rfl⟩

/-- The strict-subcritical `BV(Ω) → Lᵖ(Ω)` image surface from Theorem 8.16 (1). -/
@[expose] def subcriticalLpImage
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (S : Set (BV Ω)) :
    Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)) :=
  lpImage hd hΩ (le_of_lt hp) S

/-- Helper for Theorem 8.16: the strict-subcritical image surface is monotone in the source set. -/
theorem subcriticalLpImage_mono
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    {S T : Set (BV Ω)}
    (hST : S ⊆ T) :
    subcriticalLpImage (d := d) (Ω := Ω) (p := p) hd hΩ hp S ⊆
      subcriticalLpImage (d := d) (Ω := Ω) (p := p) hd hΩ hp T := by
  -- Reuse the canonical `lpImage` monotonicity theorem at the exposed strict-subcritical surface.
  simpa [subcriticalLpImage] using
    lpImage_mono (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) hST

/-- The critical `L^(criticalExponent d)(Ω)` space, with the positive-dimension
lower bound carried by the explicit proof `hd`. -/
abbrev criticalLpSpace
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    [MeasureTheory.IsFiniteMeasure (domainMeasure U)]
    (hd : 1 ≤ d) :=
  let _ := hd
  MeasureTheory.Lp ℝ (criticalExponent d) (domainMeasure U)

/-- The critical `L^(criticalExponent d)(Ω)` space inherits the usual normed-group
structure from `Lᵖ(Ω)` once `hd : 1 ≤ d` is fixed. -/
instance instNormedAddCommGroupCriticalLpSpace
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    [MeasureTheory.IsFiniteMeasure (domainMeasure U)]
    (hd : 1 ≤ d) :
    NormedAddCommGroup (criticalLpSpace U hd) :=
  -- Local instance justification (proof-local temporary datum): this reusable
  -- owner instance is defined by transporting the canonical `Lp` structure
  -- along the source-facing lower-bound witness `hd`.
  letI : Fact (1 ≤ criticalExponent d) := factOneLeCriticalExponent hd
  inferInstance

/-- The critical `L^(criticalExponent d)(Ω)` space inherits the usual normed-space
structure from `Lᵖ(Ω)` once `hd : 1 ≤ d` is fixed. -/
instance instNormedSpaceCriticalLpSpace
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    [MeasureTheory.IsFiniteMeasure (domainMeasure U)]
    (hd : 1 ≤ d) :
    NormedSpace ℝ (criticalLpSpace U hd) :=
  -- Local instance justification (proof-local temporary datum): this reusable
  -- owner instance is defined by transporting the canonical `Lp` structure
  -- along the source-facing lower-bound witness `hd`.
  letI : Fact (1 ≤ criticalExponent d) := factOneLeCriticalExponent hd
  inferInstance

/-- The critical BV-to-`L^(criticalExponent d)(Ω)` embedding used in
Theorem 8.16 (2). -/
def toCriticalLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    BV Ω → criticalLpSpace Ω hd :=
  let _ : Fact (1 ≤ criticalExponent d) := factOneLeCriticalExponent hd
  toLp (d := d) (Ω := Ω) (p := criticalExponent d) hd hΩ le_rfl

/-- `BVCompactness.toCriticalLp` preserves the underlying almost-everywhere
class. -/
@[simp] theorem toCriticalLp_toAEEqFun
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (u : BV Ω) :
    ((toCriticalLp (d := d) (Ω := Ω) hd hΩ u : criticalLpSpace Ω hd) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
  let _ : Fact (1 ≤ criticalExponent d) := factOneLeCriticalExponent hd
  change
    ((toLp (d := d) (Ω := Ω) (p := criticalExponent d) hd hΩ le_rfl u :
        MeasureTheory.Lp ℝ (criticalExponent d) (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ)
  exact toLp_toAEEqFun (d := d) (Ω := Ω) (p := criticalExponent d) hd hΩ le_rfl u

/-- The weak image of the critical BV-to-`L^(criticalExponent d)(Ω)` embedding
from Theorem 8.16 (2). -/
@[expose] def criticalWeakImage
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (S : Set (BV Ω)) :
    Set (WeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))) :=
  toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
    (toCriticalLp (Nat.le_of_lt h1d) hΩ '' S)

/-- Helper for Theorem 8.16: the critical weak image surface is monotone in the source set. -/
theorem criticalWeakImage_mono
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    {S T : Set (BV Ω)}
    (hST : S ⊆ T) :
    criticalWeakImage (d := d) (Ω := Ω) h1d hΩ S ⊆
      criticalWeakImage (d := d) (Ω := Ω) h1d hΩ T := by
  intro y hy
  -- Unpack the nested image definition once and reuse the same witness on the larger source set.
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨u, hu, rfl⟩
  exact ⟨toCriticalLp (d := d) (Ω := Ω) (Nat.le_of_lt h1d) hΩ u, ⟨u, hST hu, rfl⟩, rfl⟩

/-- The one-dimensional BV-to-`L∞(Ω)` embedding used in Theorem 8.16 (3). -/
def toEndpointLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1)))) :
    BV Ω → MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω) :=
  toLp (d := 1) (Ω := Ω) (p := ⊤) (show 1 ≤ (1 : ℕ) from le_rfl) hΩ
    (show (⊤ : ENNReal) ≤ criticalExponent 1 by rw [criticalExponent_one])

/-- `BVCompactness.toEndpointLp` preserves the underlying almost-everywhere
class. -/
@[simp] theorem toEndpointLp_toAEEqFun
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (u : BV Ω) :
    ((toEndpointLp (Ω := Ω) hΩ u : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ) := by
  change
    ((toLp (d := 1) (Ω := Ω) (p := ⊤) (show 1 ≤ (1 : ℕ) from le_rfl) hΩ
        (show (⊤ : ENNReal) ≤ criticalExponent 1 by rw [criticalExponent_one]) u :
        MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ)
  exact
    toLp_toAEEqFun (d := 1) (Ω := Ω) (p := ⊤) (show 1 ≤ (1 : ℕ) from le_rfl) hΩ
      (show (⊤ : ENNReal) ≤ criticalExponent 1 by rw [criticalExponent_one]) u

/-- The canonical `L∞(Ω) → (L¹(Ω))'` pairing map used for the one-dimensional
weak-* endpoint. -/
def endpointWeakStarOfLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω)) :
    WeakDual ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :=
    StrongDual.toWeakDual
      ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure Ω) (⊤ : ENNReal) (1 : ENNReal)
        f)

/-- `endpointWeakStarOfLp` evaluates by the canonical `L∞`-`L¹` pairing. -/
@[simp] theorem endpointWeakStarOfLp_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω))
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    endpointWeakStarOfLp u f =
      ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure Ω) (⊤ : ENNReal) (1 : ENNReal)
        u) f := by
  simp [endpointWeakStarOfLp]

/-- The weak-* image of the one-dimensional endpoint embedding from Theorem 8.16 (3). -/
@[expose] def endpointWeakStarImage
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (S : Set (BV Ω)) :
    Set (WeakDual ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) :=
  endpointWeakStarOfLp '' (toEndpointLp hΩ '' S)

/-- Helper for Theorem 8.16: the one-dimensional weak-* image surface is monotone in the source
set. -/
theorem endpointWeakStarImage_mono
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    {S T : Set (BV Ω)}
    (hST : S ⊆ T) :
    endpointWeakStarImage (Ω := Ω) hΩ S ⊆ endpointWeakStarImage (Ω := Ω) hΩ T := by
  intro y hy
  -- The endpoint surface is another nested image, so the same witness transport closes it.
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨u, hu, rfl⟩
  exact ⟨toEndpointLp (Ω := Ω) hΩ u, ⟨u, hST hu, rfl⟩, rfl⟩

end BVCompactness

end VariationalRegularization
