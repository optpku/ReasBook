/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19

public section

/-!
Exercise 7.15. Missing-source-decomposition blocker.

The source asks for separate `O(1)` bounds on the second and third terms on the
right-hand side of equation `(7.72)`. In the current repository snapshot,
`Book.Ch7.Prop_7_19` formalizes only the combined `s = -1` conclusion
`S_{p,j}^{-1}(n, h) + log h = O(1)` together with the underlying
`KernelMoment` integrand, series, and improper integral owners.

Because the exact `(7.72)` decomposition and its named second and third
right-hand-side terms are not yet exported as source-facing Chapter 7 API, this
file stays a conservative check-only blocker rather than asserting two guessed
exercise-specific theorems.
-/

/- Exercise 7.15. Main labeled blocker entry.

The current repository snapshot does not yet expose the precise decomposition
`(7.72)` whose second and third terms this exercise asks to bound separately.
Accordingly, no source-facing theorem is introduced here. The `#check` entries
below record the existing Chapter 7 owners that an eventual faithful
formalization should reuse: the infinite quadrature series, the kernel moment
integrand, and the available combined `s = -1` `O(1)` estimate from Proposition
7.19. -/

#check KernelMoment.quadratureSeries

#check KernelMoment.integrand

#check KernelMoment.quadratureApproxNegOne_isBigO

end
