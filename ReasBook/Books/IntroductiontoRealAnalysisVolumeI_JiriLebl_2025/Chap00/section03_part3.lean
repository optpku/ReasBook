/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap00
section Section03

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Definition 0.3.10: For sets `A` and `B`, the Cartesian product is the set of ordered
pairs `(x, y)` with `x ∈ A` and `y ∈ B`, written `A × B`. -/
abbrev cartesianProductElementCollection (A : Set α) (B : Set β) : Set (α × β) :=
  A ×ˢ B

/-- The book's Cartesian product coincides with mathlib's set product. -/
theorem cartesianProductElementCollection_eq (A : Set α) (B : Set β) :
    cartesianProductElementCollection A B = A ×ˢ B := by
  rfl

theorem mem_cartesianProductElementCollection {A : Set α} {B : Set β} {x : α} {y : β} :
    (x, y) ∈ cartesianProductElementCollection (A := A) (B := B) ↔ x ∈ A ∧ y ∈ B := by
  simp [cartesianProductElementCollection]

/-- Definition 0.3.11: A function `f : A → B` is a subset of `A × B` sending each
element of `A` to a unique `y ∈ B`; this subset is called the graph of the function. The
set `A` is the domain, `R(f) = { y ∈ B | ∃ x ∈ A, (x, y) ∈ f }` is the range, and `B` is
the codomain. -/
def IsFunctionGraph (f : Set (α × β)) (A : Set α) (B : Set β) : Prop :=
  (∀ x ∈ A, ∃! y : β, (x, y) ∈ f) ∧ f ⊆ A ×ˢ B

/-- The range of a relation `f` viewed as the graph of a function with domain `A`. -/
def functionGraphRange (f : Set (α × β)) (A : Set α) : Set β :=
  { y | ∃ x, x ∈ A ∧ (x, y) ∈ f }

/-- Helper: from a functional graph, choose the output in `B` for each `x ∈ A`. -/
noncomputable def functionGraphToSubtypeFun (f : Set (α × β)) (A : Set α) (B : Set β)
    (hf : IsFunctionGraph f A B) : {x // x ∈ A} → B := by
  classical
  intro x
  have h := hf.1 x.1 x.2
  refine ⟨Classical.choose h, ?_⟩
  have hmem : (x.1, Classical.choose h) ∈ f := (Classical.choose_spec h).1
  have hAB : (x.1, Classical.choose h) ∈ A ×ˢ B := hf.2 hmem
  exact hAB.2

/-- Helper: the chosen value from a functional graph lies in the graph. -/
lemma functionGraphToSubtypeFun_mem (f : Set (α × β)) (A : Set α) (B : Set β)
    (hf : IsFunctionGraph f A B) (x : {x // x ∈ A}) :
    (x.1, (functionGraphToSubtypeFun f A B hf x).1) ∈ f := by
  classical
  have h := hf.1 x.1 x.2
  have hmem : (x.1, Classical.choose h) ∈ f := (Classical.choose_spec h).1
  simpa [functionGraphToSubtypeFun, h] using hmem

/-- Helper: uniqueness for the chosen value from a functional graph. -/
lemma functionGraphToSubtypeFun_eq_of_mem (f : Set (α × β)) (A : Set α) (B : Set β)
    (hf : IsFunctionGraph f A B) (x : {x // x ∈ A}) {y : β}
    (hy : (x.1, y) ∈ f) :
    y = (functionGraphToSubtypeFun f A B hf x).1 := by
  classical
  have h := hf.1 x.1 x.2
  have huniq : ∀ y, (x.1, y) ∈ f → y = Classical.choose h := (Classical.choose_spec h).2
  have hy' : y = Classical.choose h := huniq y hy
  simpa [functionGraphToSubtypeFun, h] using hy'

/-- Helper: the graph set associated to a subtype-valued function. -/
def subtypeFunGraph (A : Set α) (B : Set β) (g : {x // x ∈ A} → B) : Set (α × β) :=
  Set.range (fun x => (x.1, (g x).1))

/-- Helper: the graph of a subtype-valued function is functional with domain `A`. -/
lemma subtypeFunGraph_isFunctionGraph (A : Set α) (B : Set β) (g : {x // x ∈ A} → B) :
    IsFunctionGraph (subtypeFunGraph A B g) A B := by
  constructor
  · intro x hx
    refine ⟨(g ⟨x, hx⟩).1, ?_, ?_⟩
    · exact ⟨⟨x, hx⟩, rfl⟩
    · intro y hy
      rcases hy with ⟨x', hx'⟩
      have hxval : x = x'.1 := by
        have := congrArg Prod.fst hx'
        simpa using this.symm
      have hyval : y = (g x').1 := by
        have := congrArg Prod.snd hx'
        simpa using this.symm
      have hx'' : x' = ⟨x, hx⟩ := by
        apply Subtype.ext
        simp [hxval]
      calc
        y = (g x').1 := hyval
        _ = (g ⟨x, hx⟩).1 := by simp [hx'']
  · intro p hp
    rcases hp with ⟨x, rfl⟩
    exact ⟨x.2, (g x).2⟩

/-- The book's notion of a functional subset of `A × B` is equivalent to an ordinary
mathlib function with domain the subtype of `A` and codomain `B`. -/
noncomputable def isFunctionGraph_equiv_subtype (A : Set α) (B : Set β) :
    {f : Set (α × β) // IsFunctionGraph f A B} ≃ ({x // x ∈ A} → B) := by
  classical
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left_inv
      right_inv := ?right_inv }
  · intro f
    exact functionGraphToSubtypeFun f.1 A B f.2
  · intro g
    exact ⟨subtypeFunGraph A B g, subtypeFunGraph_isFunctionGraph A B g⟩
  · intro f
    apply Subtype.ext
    apply Set.ext
    intro p
    rcases p with ⟨x, y⟩
    constructor
    · intro hp
      rcases hp with ⟨x', hx'⟩
      have hmem :
          (x'.1, (functionGraphToSubtypeFun f.1 A B f.2 x').1) ∈ f.1 :=
        functionGraphToSubtypeFun_mem (f := f.1) (A := A) (B := B) (hf := f.2) x'
      simpa [hx'] using hmem
    · intro hp
      have hx : x ∈ A := (f.2.2 hp).1
      have hy :
          y =
            (functionGraphToSubtypeFun f.1 A B f.2 ⟨x, hx⟩).1 :=
        functionGraphToSubtypeFun_eq_of_mem (f := f.1) (A := A) (B := B) (hf := f.2)
          (x := ⟨x, hx⟩) (y := y) hp
      refine ⟨⟨x, hx⟩, ?_⟩
      simp [hy]
  · intro g
    funext x
    apply Subtype.ext
    have hy : (x.1, (g x).1) ∈ subtypeFunGraph A B g := by
      exact ⟨x, rfl⟩
    have hy' :
        (g x).1 =
          (functionGraphToSubtypeFun (subtypeFunGraph A B g) A B
                (subtypeFunGraph_isFunctionGraph A B g) x).1 :=
      functionGraphToSubtypeFun_eq_of_mem (f := subtypeFunGraph A B g) (A := A) (B := B)
        (hf := subtypeFunGraph_isFunctionGraph A B g) (x := x) (y := (g x).1) hy
    exact hy'.symm

/-- Helper: pick a constant function in the derivative-function space. -/
lemma exists_const_derivative_space :
    ∃ _F : {f : ℝ → ℝ // Differentiable ℝ f} → ℝ → ℝ, True := by
  refine ⟨fun _ => fun _ => 0, trivial⟩

/-- Helper: pick a constant function in the Laplace-transform space. -/
lemma exists_const_laplace_space :
    ∃ _L : (ℝ → ℝ) → ℝ → ℝ, True := by
  refine ⟨fun _ => fun _ => 0, trivial⟩

/-- Helper: pick a constant function in the integral-assigning space. -/
lemma exists_const_integral_space :
    ∃ _I : {g : ℝ → ℝ // ContinuousOn g (Set.Icc (0 : ℝ) 1)} → ℝ, True := by
  refine ⟨fun _ => 0, trivial⟩

/-- Example 0.3.12: Functions between spaces of functions include the derivative sending a
  differentiable real function to another real function, the Laplace transform viewed as a
  function taking functions to functions, and the definite integral assigning a number to a
  continuous function on `[0,1]`. -/
theorem calculus_function_space_examples :
    (∃ _F : {f : ℝ → ℝ // Differentiable ℝ f} → ℝ → ℝ, True) ∧
      (∃ _L : (ℝ → ℝ) → ℝ → ℝ, True) ∧
        (∃ _I : {g : ℝ → ℝ // ContinuousOn g (Set.Icc (0 : ℝ) 1)} → ℝ, True) := by
  refine ⟨exists_const_derivative_space, ?_⟩
  refine ⟨exists_const_laplace_space, ?_⟩
  exact exists_const_integral_space

/-- Definition 0.3.13: For a function `f : A → B`, the image (direct image) of
`C ⊆ A` is `f(C) = { f x ∈ B | x ∈ C }`, and the inverse image of `D ⊆ B` is
`f ⁻¹(D) = { x ∈ A | f x ∈ D }`. -/
abbrev directImageElementCollection (f : α → β) (C : Set α) : Set β :=
  Set.image f C

/-- The book's image of a subset is mathlib's `Set.image`. -/
theorem directImageElementCollection_eq (f : α → β) (C : Set α) :
    directImageElementCollection f C = Set.image f C := by
  rfl

/-- The inverse image of a subset under `f`. -/
abbrev inverseImageElementCollection (f : α → β) (D : Set β) : Set α :=
  f ⁻¹' D

/-- The book's inverse image coincides with mathlib's preimage. -/
theorem inverseImageElementCollection_eq (f : α → β) (D : Set β) :
    inverseImageElementCollection f D = (f ⁻¹' D) := by
  rfl

/-- Example 0.3.14: For `f(x) = sin (π x)`, one has
`f([0, 1/2]) = [0, 1]` and `f ⁻¹({0}) = ℤ`, etc. -/
noncomputable def sinPiFunction : ℝ → ℝ := fun x => Real.sin (Real.pi * x)

/-- Helper: values of `sin (π x)` on `[0, 1/2]` lie in `[0, 1]`. -/
lemma sinPiFunction_image_subset_Icc :
    Set.image sinPiFunction (Set.Icc (0 : ℝ) (1 / 2)) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ (1 / 2 : ℝ) := hx.2
  have hpi0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hpx0 : 0 ≤ Real.pi * x := mul_nonneg hpi0 hx0
  have hx1' : x ≤ (1 : ℝ) := by linarith
  have hpx1 : Real.pi * x ≤ Real.pi := by
    simpa using (mul_le_mul_of_nonneg_left hx1' hpi0)
  have hsin0 : 0 ≤ Real.sin (Real.pi * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hpx0 hpx1
  have hsin1 : Real.sin (Real.pi * x) ≤ 1 := Real.sin_le_one _
  exact ⟨by simpa [sinPiFunction] using hsin0, by simpa [sinPiFunction] using hsin1⟩

/-- Helper: every `y ∈ [0,1]` is of the form `sin (π x)` for some `x ∈ [0,1/2]`. -/
lemma sinPiFunction_surj_Icc :
    Set.Icc (0 : ℝ) 1 ⊆ Set.image sinPiFunction (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro y hy
  rcases hy with ⟨hy0, hy1⟩
  refine ⟨Real.arcsin y / Real.pi, ?_, ?_⟩
  · have h0 : 0 ≤ Real.arcsin y / Real.pi := by
      exact div_nonneg ((Real.arcsin_nonneg).2 hy0) (le_of_lt Real.pi_pos)
    have h1' : Real.arcsin y / Real.pi ≤ (Real.pi / 2) / Real.pi := by
      exact
        div_le_div_of_nonneg_right (Real.arcsin_mem_Icc y).2 (le_of_lt Real.pi_pos)
    have h1'' : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    have h1 : Real.arcsin y / Real.pi ≤ (1 / 2 : ℝ) := by
      simpa [h1''] using h1'
    exact ⟨h0, h1⟩
  · have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hpi_mul : Real.pi * (Real.arcsin y / Real.pi) = Real.arcsin y := by
      field_simp [hpi_ne]
    have hy_neg : (-1 : ℝ) ≤ y := by linarith
    calc
      sinPiFunction (Real.arcsin y / Real.pi) =
          Real.sin (Real.pi * (Real.arcsin y / Real.pi)) := rfl
      _ = Real.sin (Real.arcsin y) := by simp [hpi_mul]
      _ = y := Real.sin_arcsin hy_neg hy1

/-- Example 0.3.14: The image of `[0, 1/2]` under `x ↦ sin (π x)` is `[0, 1]`. -/
theorem sinPiFunction_image_half_interval :
    Set.image sinPiFunction (Set.Icc (0 : ℝ) (1 / 2)) = Set.Icc (0 : ℝ) 1 := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    exact sinPiFunction_image_subset_Icc hy
  · intro hy
    exact sinPiFunction_surj_Icc hy

/-- Helper: `sin (π x) = 0` iff `x` is an integer. -/
lemma sinPiFunction_preimage_zero_iff (x : ℝ) :
    sinPiFunction x = 0 ↔ ∃ n : ℤ, (n : ℝ) = x := by
  constructor
  · intro hx
    have hx' : Real.sin (Real.pi * x) = 0 := by simpa [sinPiFunction] using hx
    rcases (Real.sin_eq_zero_iff).1 hx' with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have := congrArg (fun t => t / Real.pi) hn
    simpa [mul_comm, mul_left_comm, mul_assoc, hpi] using this
  · rintro ⟨n, rfl⟩
    have hsin : Real.sin (Real.pi * (n : ℝ)) = 0 := by
      simpa [mul_comm] using (Real.sin_int_mul_pi n)
    simpa [sinPiFunction] using hsin

/-- Example 0.3.14: The preimage of `{0}` under `x ↦ sin (π x)` is the set of integers. -/
theorem sinPiFunction_preimage_zero :
    sinPiFunction ⁻¹' ({0} : Set ℝ) = Set.range fun n : ℤ => (n : ℝ) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hx' : sinPiFunction x = 0 := by
      simpa using hx
    rcases (sinPiFunction_preimage_zero_iff (x := x)).1 hx' with ⟨n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    have hx : sinPiFunction (n : ℝ) = 0 :=
      (sinPiFunction_preimage_zero_iff (x := (n : ℝ))).2 ⟨n, rfl⟩
    simpa using hx

/-- Proposition 0.3.15: For a function `f : A → B` and subsets `C, D` of `B`,
`f ⁻¹'(C ∪ D) = f ⁻¹' C ∪ f ⁻¹' D`, `f ⁻¹'(C ∩ D) = f ⁻¹' C ∩ f ⁻¹' D`, and
`f ⁻¹'(Cᶜ) = (f ⁻¹' C)ᶜ`. -/
theorem preimage_union_inter_compl {f : α → β} {C D : Set β} :
    f ⁻¹' (C ∪ D) = f ⁻¹' C ∪ f ⁻¹' D ∧
      f ⁻¹' (C ∩ D) = f ⁻¹' C ∩ f ⁻¹' D ∧
        f ⁻¹' (Cᶜ) = (f ⁻¹' C)ᶜ := by
  constructor
  · ext x
    simp
  · constructor
    · ext x
      simp
    · ext x
      simp

/-- Proposition 0.3.16: For a function `f : A → B` and subsets `C, D` of `A`,
`f (C ∪ D) = f (C) ∪ f (D)` and `f (C ∩ D) ⊆ f (C) ∩ f (D)`. -/
theorem image_union_inter_subset {f : α → β} {C D : Set α} :
    f '' (C ∪ D) = f '' C ∪ f '' D ∧
      f '' (C ∩ D) ⊆ f '' C ∩ f '' D := by
  constructor
  · simpa using (Set.image_union (f := f) (s := C) (t := D))
  · simpa using (Set.image_inter_subset (f := f) (s := C) (t := D))

/-- Definition 0.3.17: A function `f : A → B` is injective (one-to-one) if `f x₁ = f x₂`
implies `x₁ = x₂`, equivalently each fiber `f ⁻¹' {y}` is empty or a singleton; it is
surjective (onto) if `f(A) = B`, i.e., its range equals its codomain; it is bijective if
both. -/
abbrev injectiveFunction (f : α → β) : Prop :=
  Function.Injective f

/-- The book's injectivity is mathlib's `Function.Injective`. -/
theorem injectiveFunction_iff {f : α → β} :
    injectiveFunction f ↔ Function.Injective f := by
  rfl

/-- The book's notion of surjective function. -/
abbrev surjectiveFunction (f : α → β) : Prop :=
  Function.Surjective f

/-- The book's surjectivity coincides with mathlib's `Function.Surjective`. -/
theorem surjectiveFunction_iff {f : α → β} :
    surjectiveFunction f ↔ Function.Surjective f := by
  rfl

/-- The book's bijection is a function that is both injective and surjective. -/
abbrev bijectiveFunction (f : α → β) : Prop :=
  Function.Bijective f

/-- The book's bijectivity is mathlib's `Function.Bijective`. -/
theorem bijectiveFunction_iff {f : α → β} :
    bijectiveFunction f ↔ Function.Bijective f := by
  rfl

/-- Definition 0.3.18: For functions `f : A → B` and `g : B → C`, the composition
`g ∘ f : A → C` is given by `(g ∘ f) x = g (f x)`. -/
abbrev functionComposition (g : β → γ) (f : α → β) : α → γ :=
  g ∘ f

/-- The book's composition of functions is mathlib's function composition. -/
theorem functionComposition_eq (g : β → γ) (f : α → β) :
    functionComposition (g := g) (f := f) = g ∘ f := by
  rfl

theorem functionComposition_apply (g : β → γ) (f : α → β) (x : α) :
    functionComposition (g := g) (f := f) x = g (f x) := by
  rfl

end Section03
end Chap00
