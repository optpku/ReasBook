/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u v w

/- Definition 12.20 is organized in three layers.

- `source-facing`: conditional independence of a family of sub-`σ`-algebras is the finite-event
  factorization property below.
- `core/canonical`: under `StandardBorelSpace Ω`, this source-facing notion is equivalent to the
  owner abstraction `ProbabilityTheory.iCondIndep`.
- `bridge/view`: conditional independence of random variables is obtained by applying the
  sub-`σ`-algebra notion to the generated `σ`-algebras `σ(X i) = MeasurableSpace.comap (X i)`.
-/

variable {Ω : Type u} {ι : Type v} {E : Type w}

variable [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

noncomputable section

local notation "AmbientMeasure" => @Measure Ω mΩ

/-- Definition 12.20: a family of sub-`σ`-algebras is conditionally independent given `m` if the
conditional probability of every finite intersection of events measurable in the corresponding
sub-`σ`-algebras factors as the product of the conditional probabilities of the individual
events. -/
def IsConditionallyIndependent
    (m : MeasurableSpace Ω) (𝓖 : ι → MeasurableSpace Ω) (μ : AmbientMeasure)
    [IsFiniteMeasure μ] : Prop :=
  m ≤ mΩ ∧
    (∀ i, 𝓖 i ≤ mΩ) ∧
    ∀ (s : Finset ι) {A : ι → Set Ω}, (∀ i, i ∈ s → MeasurableSet[𝓖 i] (A i)) →
      μ⟦⋂ i ∈ s, A i | m⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦A i | m⟧

/-- A family of `E`-valued random variables is conditionally independent given `m` if each
coordinate is measurable and the generated sub-`σ`-algebras `σ(X i)` are conditionally
independent given `m`. -/
def IsConditionallyIndependentFun
    (m : MeasurableSpace Ω) (X : ι → Ω → E) (μ : AmbientMeasure) [IsFiniteMeasure μ] : Prop :=
  letI : MeasurableSpace Ω := mΩ
  (∀ i, Measurable (X i)) ∧
    IsConditionallyIndependent m (fun i ↦ MeasurableSpace.comap (X i) inferInstance) μ

/-- A family of `E`-valued random variables is conditionally identically distributed given the
sub-`σ`-algebra `m` if every coordinate is measurable and the conditional probabilities
`μ⟦X i ⁻¹' s | m⟧` agree almost surely for every measurable set `s`. -/
def IsConditionallyIdentDistrib
    (m : MeasurableSpace Ω) (X : ι → Ω → E) (μ : AmbientMeasure) [IsFiniteMeasure μ] : Prop :=
  letI : MeasurableSpace Ω := mΩ
  m ≤ mΩ ∧
    (∀ i, Measurable (X i)) ∧
    ∀ i j s, MeasurableSet s → μ⟦X i ⁻¹' s | m⟧ =ᵐ[μ] μ⟦X j ⁻¹' s | m⟧

/-- A family of `E`-valued random variables is conditionally i.i.d. given the sub-`σ`-algebra `m`
if it is conditionally independent given `m` and all of its conditional distributions given `m`
agree almost surely on measurable sets. -/
def IsConditionallyIID
    (m : MeasurableSpace Ω) (X : ι → Ω → E) (μ : AmbientMeasure) [IsFiniteMeasure μ] : Prop :=
  letI : MeasurableSpace Ω := mΩ
  IsConditionallyIndependentFun m X μ ∧ IsConditionallyIdentDistrib m X μ

section Basic

variable {m : MeasurableSpace Ω} {𝓖 : ι → MeasurableSpace Ω} {X : ι → Ω → E}
variable {μ : AmbientMeasure} [IsFiniteMeasure μ]

namespace IsConditionallyIndependent

/-- In a conditionally independent family of sub-`σ`-algebras, every finite intersection event
has factorizing conditional probability. -/
theorem condProb_biInter_ae_eq_prod
    (h𝓖 : IsConditionallyIndependent m 𝓖 μ)
    (s : Finset ι) {A : ι → Set Ω} (hA : ∀ i, i ∈ s → MeasurableSet[𝓖 i] (A i)) :
    μ⟦⋂ i ∈ s, A i | m⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦A i | m⟧ :=
  h𝓖.2.2 s hA

/-- In a source-facing conditionally independent family, the conditioning `σ`-algebra is a
sub-`σ`-algebra of the ambient one. -/
theorem le_ambient
    (h𝓖 : IsConditionallyIndependent m 𝓖 μ) :
    m ≤ mΩ :=
  h𝓖.1

/-- In a source-facing conditionally independent family, each `𝓖 i` is a sub-`σ`-algebra of the
ambient one. -/
theorem le_ambient_right
    (h𝓖 : IsConditionallyIndependent m 𝓖 μ) (i : ι) :
    𝓖 i ≤ mΩ :=
  h𝓖.2.1 i

end IsConditionallyIndependent

namespace IsConditionallyIndependentFun

/-- In a conditionally independent family of random variables, each coordinate is measurable. -/
theorem measurable
    (hX : IsConditionallyIndependentFun m X μ) (i : ι) :
    Measurable (X i) :=
  hX.1 i

/-- In a conditionally independent family of random variables, the conditioning `σ`-algebra is a
sub-`σ`-algebra of the ambient one. -/
theorem le_ambient
    (hX : IsConditionallyIndependentFun m X μ) :
    m ≤ mΩ :=
  hX.2.1

/-- The random-variable formulation is the generated-sub-`σ`-algebra specialization of the
source-facing sub-`σ`-algebra notion. -/
theorem isConditionallyIndependent
    (hX : IsConditionallyIndependentFun m X μ) :
    IsConditionallyIndependent m (fun i ↦ MeasurableSpace.comap (X i) inferInstance) μ :=
  hX.2

/-- In a conditionally independent family of random variables, the conditional probability of
every finite joint event factors as the product of the coordinate conditional probabilities. -/
theorem condProb_preimage_biInter_ae_eq_prod
    (hX : IsConditionallyIndependentFun m X μ)
    (s : Finset ι) {t : ι → Set E} (ht : ∀ i, i ∈ s → MeasurableSet (t i)) :
    μ⟦⋂ i ∈ s, X i ⁻¹' t i | m⟧ =ᵐ[μ] ∏ i ∈ s, μ⟦X i ⁻¹' t i | m⟧ :=
  hX.isConditionallyIndependent s (fun i hi ↦ ⟨t i, ht i hi, rfl⟩)

end IsConditionallyIndependentFun

namespace IsConditionallyIdentDistrib

/-- In a conditionally identically distributed family, each coordinate is measurable. -/
theorem measurable
    (hX : IsConditionallyIdentDistrib m X μ) (i : ι) :
    Measurable (X i) :=
  hX.2.1 i

/-- In a conditionally identically distributed family, the conditioning `σ`-algebra is a
sub-`σ`-algebra of the ambient one. -/
theorem le_ambient
    (hX : IsConditionallyIdentDistrib m X μ) :
    m ≤ mΩ :=
  hX.1

/-- In a conditionally identically distributed family, the conditional probabilities of the
measurable events `{X i ∈ s}` and `{X j ∈ s}` agree almost surely for every measurable set `s`. -/
theorem condProb_preimage_ae_eq
    (hX : IsConditionallyIdentDistrib m X μ)
    (i j : ι) {s : Set E} (hs : MeasurableSet s) :
    μ⟦X i ⁻¹' s | m⟧ =ᵐ[μ] μ⟦X j ⁻¹' s | m⟧ :=
  hX.2.2 i j s hs

end IsConditionallyIdentDistrib

namespace IsConditionallyIID

/-- In a conditionally i.i.d. family, each coordinate is measurable. -/
theorem measurable
    (hX : IsConditionallyIID m X μ) (i : ι) :
    Measurable (X i) :=
  hX.1.measurable i

/-- In a conditionally i.i.d. family, the conditioning `σ`-algebra is a sub-`σ`-algebra of the
ambient one. -/
theorem le_ambient
    (hX : IsConditionallyIID m X μ) :
    m ≤ mΩ :=
  hX.1.2.1

/-- Forgetting the identical-distribution half of conditional i.i.d. leaves conditional
independence. -/
theorem isConditionallyIndependentFun
    (hX : IsConditionallyIID m X μ) :
    IsConditionallyIndependentFun m X μ :=
  hX.1

/-- Forgetting the independence half of conditional i.i.d. leaves conditional identical
distribution. -/
theorem isConditionallyIdentDistrib
    (hX : IsConditionallyIID m X μ) :
    IsConditionallyIdentDistrib m X μ :=
  hX.2

end IsConditionallyIID

end Basic

section StandardBorel

variable [StandardBorelSpace Ω]
variable {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
variable {𝓖 : ι → MeasurableSpace Ω} (h𝓖m : ∀ i, 𝓖 i ≤ mΩ)
variable {X : ι → Ω → E} {μ : AmbientMeasure} [IsFiniteMeasure μ]

namespace IsConditionallyIndependent

/-- Under the standard-Borel hypothesis on `Ω`, the source-facing conditional independence of a
family of sub-`σ`-algebras is equivalent to mathlib's owner abstraction
`ProbabilityTheory.iCondIndep`. -/
theorem isConditionallyIndependent_iff_iCondIndep :
    IsConditionallyIndependent m 𝓖 μ ↔ iCondIndep m hm 𝓖 μ :=
  ⟨fun h ↦ (iCondIndep_iff 𝓖 h𝓖m μ).2 h.2.2,
    fun h ↦ ⟨hm, h𝓖m, (iCondIndep_iff 𝓖 h𝓖m μ).1 h⟩⟩

/-- Bridge/view: a source-facing conditionally independent family of sub-`σ`-algebras yields
mathlib's owner abstraction `ProbabilityTheory.iCondIndep`. -/
theorem iCondIndep
    (h𝓖 : IsConditionallyIndependent m 𝓖 μ) :
    iCondIndep m hm 𝓖 μ :=
  (isConditionallyIndependent_iff_iCondIndep hm h𝓖m).1 h𝓖

end IsConditionallyIndependent

namespace IsConditionallyIndependentFun

/-- Under `StandardBorelSpace Ω`, the random-variable companion is equivalent to the owner
abstraction `ProbabilityTheory.iCondIndepFun`. -/
theorem isConditionallyIndependentFun_iff_measurable_iCondIndepFun :
    IsConditionallyIndependentFun m X μ ↔
      (∀ i, Measurable[mΩ] (X i)) ∧ iCondIndepFun m hm X μ :=
  ⟨fun hX ↦
      ⟨hX.1,
        (iCondIndepFun_iff_iCondIndep (fun _ : ι ↦ inferInstance) X μ).2 <|
          (isConditionallyIndependent_iff_iCondIndep hm (fun i ↦ (hX.1 i).comap_le)).1 hX.2⟩,
    fun hX ↦
      ⟨hX.1,
        (isConditionallyIndependent_iff_iCondIndep hm (fun i ↦ (hX.1 i).comap_le)).2 <|
          (iCondIndepFun_iff_iCondIndep (fun _ : ι ↦ inferInstance) X μ).1 hX.2⟩⟩

/-- Bridge/view: a source-facing conditionally independent family of random variables yields the
owner abstraction `ProbabilityTheory.iCondIndepFun`. -/
theorem iCondIndepFun
    (hX : IsConditionallyIndependentFun m X μ) :
    iCondIndepFun m hm X μ :=
  (isConditionallyIndependentFun_iff_measurable_iCondIndepFun hm).1 hX |>.2

/-- Bridge/view: the same source-facing conditional independence hypothesis also yields owner-level
conditional independence of the generated sub-`σ`-algebras. -/
theorem iCondIndep
    (hX : IsConditionallyIndependentFun m X μ) :
    iCondIndep m hm (fun i ↦ MeasurableSpace.comap (X i) inferInstance) μ :=
  (iCondIndepFun_iff_iCondIndep (fun _ : ι ↦ inferInstance) X μ).1 (hX.iCondIndepFun hm)

end IsConditionallyIndependentFun

namespace IsConditionallyIID

/-- A conditionally i.i.d. family is conditionally independent in mathlib's owner sense. -/
theorem iCondIndepFun
    (hX : IsConditionallyIID m X μ) :
    iCondIndepFun m hm X μ :=
  hX.1.iCondIndepFun hm

/-- A conditionally i.i.d. family is conditionally independent at the level of the generated
sub-`σ`-algebras. -/
theorem iCondIndep
    (hX : IsConditionallyIID m X μ) :
    iCondIndep m hm (fun i ↦ MeasurableSpace.comap (X i) inferInstance) μ :=
  hX.1.iCondIndep hm

end IsConditionallyIID

end StandardBorel
