module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs

public section

open scoped ContDiff

universe u uE uF

namespace HasFTaylorSeriesUpTo

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Helper for Infrastructure I.16a (finite-smooth invariant graph): replace only the
top formal Taylor term while retaining a predecessor Taylor series. -/
theorem update_succ_top
    {n : ℕ} {f : E → F}
    {p : E → FormalMultilinearSeries 𝕜 E F}
    (hp : HasFTaylorSeriesUpTo n f p)
    (a : E → (E [×(n + 1)]→L[𝕜] F)) (ha : Continuous a)
    (hderiv : ∀ x, HasFDerivAt (fun y ↦ p y n) ((a x).curryLeft) x) :
    HasFTaylorSeriesUpTo (n + 1) f
      (fun x ↦ Function.update (p x) (n + 1) (a x)) := by
  let q : E → FormalMultilinearSeries 𝕜 E F :=
    fun x ↦ Function.update (p x) (n + 1) (a x)
  have hzero : ∀ x, (q x 0).curry0 = f x := by
    intro x
    dsimp only [q]
    have hzero_ne : (0 : ℕ) ≠ n + 1 := by omega
    rw [Function.update_of_ne hzero_ne]
    exact hp.zero_eq x
  have hderiv_below : ∀ (m : ℕ), m < n + 1 → ∀ x,
      HasFDerivAt (fun y ↦ q y m) (q x m.succ).curryLeft x := by
    intro m hm x
    by_cases htop : m = n
    · subst m
      have hq_prev : (fun y ↦ q y n) = fun y ↦ p y n := by
        funext y
        dsimp only [q]
        have htop_ne : n ≠ n + 1 := by omega
        rw [Function.update_of_ne htop_ne]
      have hq_top : q x n.succ = a x := by
        dsimp only [q]
        rw [Function.update_self]
      rw [hq_prev, hq_top]
      exact hderiv x
    · have hbelow : m < n := by omega
      have hbelow_cast : (m : ℕ∞ω) < n := by exact_mod_cast hbelow
      have hp_deriv := hp.fderiv m hbelow_cast x
      have hq_m : (fun y ↦ q y m) = fun y ↦ p y m := by
        funext y
        dsimp only [q]
        have hindex_ne : m ≠ n + 1 := by omega
        rw [Function.update_of_ne hindex_ne]
      have hq_succ : q x m.succ = p x m.succ := by
        dsimp only [q]
        have hsuccessor_ne : m.succ ≠ n + 1 := by omega
        rw [Function.update_of_ne hsuccessor_ne]
      rw [hq_m, hq_succ]
      exact hp_deriv
  have hcont : ∀ (m : ℕ), m ≤ n + 1 → Continuous (q · m) := by
    intro m hm
    by_cases htop : m = n + 1
    · subst m
      simpa only [q, Function.update_self] using ha
    · have hbelow : m ≤ n := by omega
      have hbelow_cast : (m : ℕ∞ω) ≤ n := by exact_mod_cast hbelow
      have hp_cont := hp.cont m hbelow_cast
      have hq_m : (q · m) = (p · m) := by
        funext y
        dsimp only [q]
        have hindex_ne : m ≠ n + 1 := by omega
        rw [Function.update_of_ne hindex_ne]
      rw [hq_m]
      exact hp_cont
  have hseries : HasFTaylorSeriesUpTo (n + 1) f q := by
    have hcont_cast : ∀ (m : ℕ), (m : ℕ∞ω) ≤ n + 1 → Continuous (q · m) := by
      intro m hm
      have hm_nat : m ≤ n + 1 := by exact_mod_cast hm
      exact hcont m hm_nat
    refine ⟨hzero, ?_, hcont_cast⟩
    intro m hm x
    have hm_nat : m < n + 1 := by exact_mod_cast hm
    exact hderiv_below m hm_nat x
  simpa only [q] using hseries

/-- The updated Taylor witness immediately gives finite smoothness of the updated function. -/
theorem contDiff_update_succ_top
    {n : ℕ} {f : E → F}
    {p : E → FormalMultilinearSeries 𝕜 E F}
    (hp : HasFTaylorSeriesUpTo n f p)
    (a : E → (E [×(n + 1)]→L[𝕜] F)) (ha : Continuous a)
    (hderiv : ∀ x, HasFDerivAt (fun y ↦ p y n) ((a x).curryLeft) x) :
    ContDiff 𝕜 (n + 1) f := by
  exact (update_succ_top hp a ha hderiv).contDiff

end HasFTaylorSeriesUpTo
