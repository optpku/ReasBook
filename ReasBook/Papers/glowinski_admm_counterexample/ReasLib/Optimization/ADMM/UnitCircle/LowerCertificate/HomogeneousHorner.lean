/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerEncoding

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.IntegerEncoding

open scoped BigOperators

/-- Homogeneous Horner evaluation retains the current denominator power in a
second state component. The fold uses a linear number of ring operations. -/
def homogeneousState {R : Type*} [CommRing R] (u s : R) (p : List R) : R × R :=
  p.foldr (fun a r ↦ (a * r.2 + u * r.1, s * r.2)) (0, 1)

def homogeneousHorner {R : Type*} [CommRing R] (u s : R) (p : List R) : R :=
  (homogeneousState u s p).1

@[simp] theorem homogeneousState_nil {R : Type*} [CommRing R] (u s : R) :
    homogeneousState u s [] = (0, 1) := rfl

@[simp] theorem homogeneousHorner_nil {R : Type*} [CommRing R] (u s : R) :
    homogeneousHorner u s [] = 0 := rfl

theorem homogeneousState_snd {R : Type*} [CommRing R] (u s : R) (p : List R) :
    (homogeneousState u s p).2 = s ^ p.length := by
  induction p with
  | nil => simp
  | cons a p ih =>
    change s * (homogeneousState u s p).2 = s ^ (p.length + 1)
    rw [ih, pow_succ]
    ring

theorem homogeneousHorner_cons {R : Type*} [CommRing R]
    (u s a : R) (p : List R) :
    homogeneousHorner u s (a :: p) =
      a * s ^ p.length + u * homogeneousHorner u s p := by
  change a * (homogeneousState u s p).2 + u * (homogeneousState u s p).1 = _
  rw [homogeneousState_snd]
  rfl

/-- Exact finite-sum semantics, including an empty coefficient vector. -/
theorem homogeneousHorner_ofFn {R : Type*} [CommRing R] (u s : R)
    (N : ℕ) (p : Fin N → R) :
    homogeneousHorner u s (List.ofFn p) =
      ∑ k : Fin N, p k * u ^ k.val * s ^ (N - 1 - k.val) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ, homogeneousHorner_cons, List.length_ofFn, ih,
      Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Nat.add_sub_cancel_right,
      Nat.sub_zero, Fin.val_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hexp : N - (k.val + 1) = N - 1 - k.val := by omega
    rw [hexp, pow_succ]
    ring

theorem homogeneousHorner_ofFn_degree {R : Type*} [CommRing R] (u s : R)
    (n : ℕ) (p : Fin (n + 1) → R) :
    homogeneousHorner u s (List.ofFn p) =
      ∑ k : Fin (n + 1), p k * u ^ k.val * s ^ (n - k.val) := by
  simpa only [Nat.add_sub_cancel_right] using homogeneousHorner_ofFn u s (n + 1) p

end ADMM.UnitCircle.LowerCertificate.IntegerEncoding
