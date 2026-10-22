/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*}
variable [∀ i, NormedAddCommGroup (E i)]

/- Remark 6.7 is `bridge/view`: the source rewrites the separable proximal-operator identity from
Theorem 6.6 into textbook tuple notation once each coordinate proximal set is known to be a
singleton. Domain sampling in this file family identifies the owner abstraction as the Chapter 6
pair `separableSum` on `PiLp (2 : ENNReal) E` and the set-valued proximal mapping `prox[...]`;
`EuclideanSpace ℝ ι` is only the textbook specialization obtained by taking every `E i = ℝ`. This
item therefore records only the singleton rewrite on that owner surface and does not introduce a
parallel single-valued proximal-map API. As in Theorem 6.6, the no-`⊥` hypothesis is essential:
without it, one coordinate summand can force the summed proximal objective to `⊥` while leaving
the other coordinates unconstrained, so the product proximal set need not be a singleton even when
the coordinatewise singleton statement is written down. -/

-- Proof sketch: rewrite `prox[separableSum f] x` using the owner theorem
-- `prox_separableSum_eq_coordinatewise`. The forward direction updates a single coordinate of `y`
-- and uses singletonity of the product proximal set to recover equality in that coordinate; the
-- reverse direction is extensionality on `PiLp`.
/-- Remark 6.7: for a separable function on a finite `L²` product, the set-valued proximal
identity from Theorem 6.6 is equivalent to the singleton statement that the proximal point at `x`
is the point whose `i`-th coordinate is the proximal point of the `i`-th summand `f i` at `x i`.
Specializing to `E i = ℝ`, this gives the textbook vector formula on `EuclideanSpace ℝ ι`, and
for `ι = Fin n` it is `prox_f(x) = (prox_{f_i}(x_i))_{i=1}^n`. -/
theorem prox_separableSum_eq_singleton_iff_coordinatewise
    (f : ∀ i, E i → EReal) (hf_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (x y : PiLp (2 : ENNReal) E) :
    prox[PiLp.separableSum f] x = {y} ↔
      ∀ i : ι, prox[f i] (x i) = {y i} := by
  classical
  rw [prox_separableSum_eq_coordinatewise f hf_proper x]
  constructor
  · intro h i
    have hy : ∀ j : ι, y j ∈ prox[f j] (x j) := by
      intro j
      have : y ∈ ({y} : Set (PiLp (2 : ENNReal) E)) := by simp
      rw [← h] at this
      exact this j
    ext u
    constructor
    · intro hu
      let z : PiLp (2 : ENNReal) E := WithLp.toLp 2 (Function.update (fun j ↦ y j) i u)
      have hz : z ∈ ({v : PiLp (2 : ENNReal) E | ∀ j, v j ∈ prox[f j] (x j)} : Set _) := by
        intro j
        by_cases hj : j = i
        · subst hj
          simpa [z, Function.update] using hu
        · simpa [z, Function.update, hj] using hy j
      have hz' : z = y := by
        have : z ∈ ({y} : Set (PiLp (2 : ENNReal) E)) := by rw [← h]; exact hz
        simpa using this
      have : z i = y i := congrArg (fun v : PiLp (2 : ENNReal) E ↦ v i) hz'
      simpa [z, Function.update] using this
    · intro hu
      rw [hu]
      exact hy i
  · intro h
    ext z
    constructor
    · intro hz
      have hz_eq : z = y := by
        ext i
        have : z i ∈ prox[f i] (x i) := hz i
        simpa [h i] using this
      simpa [hz_eq]
    · intro hz
      rw [Set.mem_singleton_iff.mp hz]
      intro i
      simpa [h i]

end
