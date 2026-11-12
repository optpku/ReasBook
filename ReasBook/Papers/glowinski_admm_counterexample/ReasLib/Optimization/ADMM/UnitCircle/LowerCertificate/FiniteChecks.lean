/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.CachedPowers

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

/-- Assemble small independently checked coefficient batches into an exact list identity. -/
theorem list_eq_of_getD {α : Type} (p q : List α) (default : α) (n : ℕ)
    (hp : p.length = n) (hq : q.length = n)
    (h : ∀ i : Fin n, p.getD i default = q.getD i default) : p = q := by
  apply List.ext_getElem (hp.trans hq.symm)
  intro i hip hiq
  have hi : i < n := by omega
  have he := h ⟨i, hi⟩
  rw [← List.getElem_eq_getD default, ← List.getElem_eq_getD default] at he
  exact he

end ADMM.UnitCircle.LowerCertificate
