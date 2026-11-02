module

public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-- A polynomial-time map records an explicit function, a running-time function with a polynomial
bound in the input encoding size, and a polynomial bound for the encoding size of its output. -/
structure PolynomialTimeMap
    (α : Type)
    (β : Type)
    (inputEncodingSize : α → ℕ)
    (outputEncodingSize : β → ℕ) where
  toFun : α → β
  runtime : α → ℕ
  timeBound : Polynomial ℕ
  runtime_le : ∀ a : α, runtime a ≤ timeBound.eval (inputEncodingSize a)
  outputSizeBound : Polynomial ℕ
  outputSize_le : ∀ a : α, outputEncodingSize (toFun a) ≤ outputSizeBound.eval (inputEncodingSize a)

namespace PolynomialTimeMap

/-- Helper for Definition 1.18: evaluation of a natural-coefficient polynomial is monotone on
`ℕ`. -/
private lemma polynomialEvalNatMonotone (p : Polynomial ℕ) :
    Monotone p.eval := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro q r hq hr x y hxy
    -- Monotonicity is preserved under polynomial addition.
    simpa [Polynomial.eval_add] using add_le_add (hq hxy) (hr hxy)
  · intro n a x y hxy
    -- A monomial is monotone because powers and multiplication are monotone on `ℕ`.
    simpa [Polynomial.eval_monomial, Nat.mul_comm] using
      mul_le_mul_left (pow_le_pow_left' hxy n) a

/-- The runtime bound used by `PolynomialTimeMap.comp`. -/
theorem compRuntimeLe
    {α β γ : Type}
    {inputEncodingSize : α → ℕ}
    {middleEncodingSize : β → ℕ}
    {outputEncodingSize : γ → ℕ}
    (f : PolynomialTimeMap β γ middleEncodingSize outputEncodingSize)
    (g : PolynomialTimeMap α β inputEncodingSize middleEncodingSize) :
    ∀ a : α,
      g.runtime a + f.runtime (g.toFun a) ≤
        (g.timeBound + f.timeBound.comp g.outputSizeBound).eval (inputEncodingSize a) := by
  intro a
  -- Extract the component runtime and output-size bounds that drive the composition estimate.
  have hgRuntime := g.runtime_le a
  have hfRuntime := f.runtime_le (g.toFun a)
  have hgOutput := g.outputSize_le a
  have hfTimeMonotone :
      f.timeBound.eval (middleEncodingSize (g.toFun a)) ≤
        f.timeBound.eval (g.outputSizeBound.eval (inputEncodingSize a)) :=
    polynomialEvalNatMonotone f.timeBound hgOutput
  -- Combine the two runtime bounds and then rewrite the target into the composed polynomial form.
  calc
    g.runtime a + f.runtime (g.toFun a) ≤
        g.timeBound.eval (inputEncodingSize a) +
          f.timeBound.eval (middleEncodingSize (g.toFun a)) := by
      exact add_le_add hgRuntime hfRuntime
    _ ≤ g.timeBound.eval (inputEncodingSize a) +
        f.timeBound.eval (g.outputSizeBound.eval (inputEncodingSize a)) := by
      simpa using
        add_le_add_left hfTimeMonotone (g.timeBound.eval (inputEncodingSize a))
    _ = (g.timeBound + f.timeBound.comp g.outputSizeBound).eval (inputEncodingSize a) := by
      rw [Polynomial.eval_add, Polynomial.eval_comp]

/-- The output-size bound used by `PolynomialTimeMap.comp`. -/
theorem compOutputSizeLe
    {α β γ : Type}
    {inputEncodingSize : α → ℕ}
    {middleEncodingSize : β → ℕ}
    {outputEncodingSize : γ → ℕ}
    (f : PolynomialTimeMap β γ middleEncodingSize outputEncodingSize)
    (g : PolynomialTimeMap α β inputEncodingSize middleEncodingSize) :
    ∀ a : α,
      outputEncodingSize (f.toFun (g.toFun a)) ≤
        (f.outputSizeBound.comp g.outputSizeBound).eval (inputEncodingSize a) := by
  intro a
  -- Extract the inner output-size bound and transport it through the outer polynomial bound.
  have hfOutput := f.outputSize_le (g.toFun a)
  have hgOutput := g.outputSize_le a
  have hfOutputMonotone :
      f.outputSizeBound.eval (middleEncodingSize (g.toFun a)) ≤
        f.outputSizeBound.eval (g.outputSizeBound.eval (inputEncodingSize a)) :=
    polynomialEvalNatMonotone f.outputSizeBound hgOutput
  -- Normalize the composed polynomial and close by transitivity.
  calc
    outputEncodingSize (f.toFun (g.toFun a)) ≤
        f.outputSizeBound.eval (middleEncodingSize (g.toFun a)) := by
      exact hfOutput
    _ ≤ f.outputSizeBound.eval (g.outputSizeBound.eval (inputEncodingSize a)) := by
      exact hfOutputMonotone
    _ = (f.outputSizeBound.comp g.outputSizeBound).eval (inputEncodingSize a) := by
      rw [Polynomial.eval_comp]

/-- Compose two polynomial-time maps, with the expected composed runtime and output-size bounds.
-/
noncomputable def comp
    {α β γ : Type}
    {inputEncodingSize : α → ℕ}
    {middleEncodingSize : β → ℕ}
    {outputEncodingSize : γ → ℕ}
    (f : PolynomialTimeMap β γ middleEncodingSize outputEncodingSize)
    (g : PolynomialTimeMap α β inputEncodingSize middleEncodingSize) :
    PolynomialTimeMap α γ inputEncodingSize outputEncodingSize where
  toFun := fun a ↦ f.toFun (g.toFun a)
  runtime := fun a ↦ g.runtime a + f.runtime (g.toFun a)
  timeBound := g.timeBound + f.timeBound.comp g.outputSizeBound
  runtime_le := compRuntimeLe f g
  outputSizeBound := f.outputSizeBound.comp g.outputSizeBound
  outputSize_le := compOutputSizeLe f g

/-- Evaluating the composed polynomial-time map agrees with ordinary function composition. -/
theorem comp_apply
    {α β γ : Type}
    {inputEncodingSize : α → ℕ}
    {middleEncodingSize : β → ℕ}
    {outputEncodingSize : γ → ℕ}
    (f : PolynomialTimeMap β γ middleEncodingSize outputEncodingSize)
    (g : PolynomialTimeMap α β inputEncodingSize middleEncodingSize)
    (a : α) :
    (comp f g).toFun a = f.toFun (g.toFun a) := by
  -- The composed map was defined by ordinary function composition on `toFun`.
  rfl

end PolynomialTimeMap
