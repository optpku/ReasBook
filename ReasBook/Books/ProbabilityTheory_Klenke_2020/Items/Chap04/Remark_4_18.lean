/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

variable {α : Type u} [MeasurableSpace α]

/-- The real `ℒ^p(μ)` space viewed as the submodule of functions with finite `p`-seminorm. -/
def mem_lp_submodule (p : ENNReal) (μ : Measure α) : Submodule ℝ (α → ℝ) where
  carrier := fun f : α → ℝ ↦ MemLp f p μ
  zero_mem' := MemLp.zero
  add_mem' := fun hf hg ↦ MemLp.add hf hg
  smul_mem' := fun c _ hf ↦ MemLp.const_smul hf c

/-- Membership in `mem_lp_submodule p μ` is exactly the `MemLp` condition. -/
lemma memLp_of_mem_lp_submodule {p : ENNReal} {μ : Measure α} (f : mem_lp_submodule p μ) :
    MemLp (f : α → ℝ) p μ :=
  f.2

/-- Remark 4.18: for `1 ≤ p`, the real-valued `L^p` seminorm defines a seminorm on
`ℒ^p(μ)`, represented here by the submodule of functions with `MemLp`. -/
def lp_seminorm_on_mem_lp (p : ENNReal) (μ : Measure α) (hp : 1 ≤ p) :
    Seminorm ℝ (mem_lp_submodule p μ) :=
  Seminorm.of
    (fun f ↦ lpNorm (f : α → ℝ) p μ)
    (fun f g ↦
      show lpNorm ((f : α → ℝ) + (g : α → ℝ)) p μ ≤
          lpNorm (f : α → ℝ) p μ + lpNorm (g : α → ℝ) p μ from
        lpNorm_add_le (memLp_of_mem_lp_submodule f) hp)
    (fun c f ↦ lpNorm_const_smul c (f : α → ℝ) μ)

/-- Evaluating `lp_seminorm_on_mem_lp` is the usual real-valued `L^p` seminorm. -/
lemma lp_seminorm_on_mem_lp_apply {p : ENNReal} {μ : Measure α} (hp : 1 ≤ p)
    (f : mem_lp_submodule p μ) :
    lp_seminorm_on_mem_lp p μ hp f = lpNorm (f : α → ℝ) p μ :=
  rfl
