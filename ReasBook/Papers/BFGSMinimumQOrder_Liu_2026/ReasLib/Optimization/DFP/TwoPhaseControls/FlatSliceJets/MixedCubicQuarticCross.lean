module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.MixedFlatPath
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.MixedFlatPath

/-!
# The nonzero linear-cubic cross term in a mixed analytic path

This companion refines the zero-cross estimate from `MixedFlatPath` by retaining
the unique order-four Hessian contribution.
-/

public section

open Filter
open Asymptotics
open scoped Matrix Topology BigOperators

universe u v

namespace FiniteTaylorJet

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem diagonal_zero_mixed
    (A : E [×0]→L[ℝ] F) (x y : E) :
    A (fun _ : Fin 0 => x + y) - A (fun _ : Fin 0 => x) -
        A (fun _ : Fin 0 => y) + A (fun _ : Fin 0 => 0) = 0 := by
  have hconst (w : E) : (fun _ : Fin 0 => w) = (fun _ : Fin 0 => 0) :=
    Subsingleton.elim _ _
  rw [hconst (x + y), hconst x, hconst y]
  abel

private theorem diagonal_one_add_sub
    (A : E [×1]→L[ℝ] F) (x y : E) :
    A (fun _ : Fin 1 => x + y) - A (fun _ : Fin 1 => x) -
        A (fun _ : Fin 1 => y) = 0 := by
  let tail : Fin 0 → E := fun i => Fin.elim0 i
  have h := A.cons_add tail x y
  have hxy : Fin.cons (x + y) tail = (fun _ : Fin 1 => x + y) := by
    funext i
    fin_cases i
    rfl
  have hx : Fin.cons x tail = (fun _ : Fin 1 => x) := by
    funext i
    fin_cases i
    rfl
  have hy : Fin.cons y tail = (fun _ : Fin 1 => y) := by
    funext i
    fin_cases i
    rfl
  rw [hxy, hx, hy] at h
  rw [h]
  abel

private theorem diagonal_two_add_sub
    (A : E [×2]→L[ℝ] F) (x y : E) :
    A (fun _ : Fin 2 => x + y) - A (fun _ : Fin 2 => x) -
        A (fun _ : Fin 2 => y) =
      A ![x, y] + A ![y, x] := by
  let X : Fin 2 → E := fun _ => x
  let Y : Fin 2 → E := fun _ => y
  have hsum : (fun _ : Fin 2 => x + y) = X + Y := by rfl
  have h0 : ({0} : Finset (Fin 2)).piecewise X Y = ![x, y] := by
    funext i
    fin_cases i <;> simp [X, Y]
  have h1 : ({1} : Finset (Fin 2)).piecewise X Y = ![y, x] := by
    funext i
    fin_cases i <;> simp [X, Y]
  have hall : ({0, 1} : Finset (Fin 2)).piecewise X Y = X := by
    funext i
    fin_cases i <;> simp [X, Y]
  have hnone : (∅ : Finset (Fin 2)).piecewise X Y = Y := by
    funext i
    simp [X, Y]
  rw [hsum, A.map_add_univ]
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) =
      {∅, {0}, {1}, {0, 1}} := by
    decide
  rw [huniv,
    Finset.sum_insert (by decide : ∅ ∉ ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2)))),
    Finset.sum_insert (by decide : {0} ∉ ({{1}, {0, 1}} : Finset (Finset (Fin 2)))),
    Finset.sum_insert (by decide : {1} ∉ ({{0, 1}} : Finset (Finset (Fin 2)))),
    Finset.sum_singleton, hnone, h0, h1, hall]
  dsimp only [X, Y]
  abel

private theorem bilinear_add_right
    (A : E [×2]→L[ℝ] F) (x y z : E) :
    A ![x, y + z] = A ![x, y] + A ![x, z] := by
  have hupdate (w : E) : Function.update ![x, 0] (1 : Fin 2) w = ![x, w] := by
    funext i
    fin_cases i <;> simp
  have h := A.map_update_add ![x, 0] (1 : Fin 2) y z
  simpa only [hupdate] using h

private theorem bilinear_add_left
    (A : E [×2]→L[ℝ] F) (x y z : E) :
    A ![y + z, x] = A ![y, x] + A ![z, x] := by
  have hupdate (w : E) : Function.update ![0, x] (0 : Fin 2) w = ![w, x] := by
    funext i
    fin_cases i <;> simp
  have h := A.map_update_add ![0, x] (0 : Fin 2) y z
  simpa only [hupdate] using h

private theorem bilinear_smul
    (A : E [×2]→L[ℝ] F) (c d : ℝ) (x y : E) :
    A ![c • x, d • y] = (c * d) • A ![x, y] := by
  have h := A.map_smul_univ ![c, d] ![x, y]
  have hprod : (∏ i : Fin 2, ![c, d] i) = c * d := by
    rw [Fin.prod_univ_two]
    rfl
  rw [hprod] at h
  calc
    A ![c • x, d • y] = A (fun i => ![c, d] i • ![x, y] i) := by
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = (c * d) • A ![x, y] := h

private theorem diagonal_two_scale_cubic_quartic_sub_cross
    (A : E [×2]→L[ℝ] F) (u v₃ v₄ : E) (ε : ℝ) :
    A (fun _ : Fin 2 =>
          ε • u + (ε ^ 3 • v₃ + ε ^ 4 • v₄)) -
        A (fun _ : Fin 2 => ε • u) -
        A (fun _ : Fin 2 => ε ^ 3 • v₃ + ε ^ 4 • v₄) -
        ε ^ 4 • (A ![u, v₃] + A ![v₃, u]) =
      ε ^ 5 • (A ![u, v₄] + A ![v₄, u]) := by
  rw [diagonal_two_add_sub]
  rw [bilinear_add_right, bilinear_add_left]
  rw [bilinear_smul, bilinear_smul, bilinear_smul, bilinear_smul]
  module

/-- After subtracting its degree-two linear-cubic cross coefficient, the mixed part of
the degree-four partial sum along `ε • u + ε³ • v₃ + ε⁴ • v₄` is order five. -/
theorem partialSum_five_mixed_cubic_quartic_sub_cross_isBigO
    (p : FormalMultilinearSeries ℝ E F) (u v₃ v₄ : E) :
    (fun ε : ℝ =>
      let x := ε • u
      let y := ε ^ 3 • v₃ + ε ^ 4 • v₄
      p.partialSum 5 (x + y) - p.partialSum 5 x -
        p.partialSum 5 y + p.partialSum 5 0 -
        ε ^ 4 • (p 2 ![u, v₃] + p 2 ![v₃, u])) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 5) := by
  let x : ℝ → E := fun ε => ε • u
  let y : ℝ → E := fun ε => ε ^ 3 • v₃ + ε ^ 4 • v₄
  have huO : (fun _ : ℝ => u) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto tendsto_const_nhds one_ne_zero
  have hv₃O : (fun _ : ℝ => v₃) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto tendsto_const_nhds one_ne_zero
  have hv₄O : (fun _ : ℝ => v₄) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto tendsto_const_nhds one_ne_zero
  have hxO : x =O[𝓝 0] (fun ε : ℝ => ε) := by
    simpa only [x, Pi.smul_apply, smul_eq_mul, mul_one] using
      (Asymptotics.isBigO_refl (fun ε : ℝ => ε) (𝓝 0)).smul huO
  have hyO₃ : y =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
    let q : ℝ → E := fun ε => v₃ + ε • v₄
    have hq0 : Tendsto q (𝓝 0) (𝓝 v₃) := by
      dsimp only [q]
      have hε : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
      simpa using tendsto_const_nhds.add (hε.smul_const v₄)
    have hqO : q =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
      Asymptotics.isBigO_const_of_tendsto hq0 one_ne_zero
    have hsmul :=
      (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)).smul hqO
    refine hsmul.congr' ?_ ?_
    · filter_upwards
      intro ε
      dsimp only [y, q, Pi.smul_apply]
      rw [smul_add, smul_smul]
      congr 1
    · filter_upwards
      intro ε
      simp
  have hyO₁ : y =O[𝓝 0] (fun ε : ℝ => ε) := by
    exact hyO₃.trans
      (by simpa only [pow_one] using
        (Asymptotics.isLittleO_pow_pow (by norm_num : 1 < 3)).isBigO)
  have hterm₀ :
      (fun ε : ℝ =>
        p 0 (fun _ : Fin 0 => x ε + y ε) - p 0 (fun _ : Fin 0 => x ε) -
          p 0 (fun _ : Fin 0 => y ε) + p 0 (fun _ : Fin 0 => 0)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    refine (Asymptotics.isBigO_zero (fun ε : ℝ => ε ^ 5) (𝓝 0)).congr_left ?_
    intro ε
    exact (diagonal_zero_mixed (p 0) (x ε) (y ε)).symm
  have hterm₁ :
      (fun ε : ℝ =>
        p 1 (fun _ : Fin 1 => x ε + y ε) - p 1 (fun _ : Fin 1 => x ε) -
          p 1 (fun _ : Fin 1 => y ε) + p 1 (fun _ : Fin 1 => 0)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    refine (Asymptotics.isBigO_zero (fun ε : ℝ => ε ^ 5) (𝓝 0)).congr_left ?_
    intro ε
    rw [show p 1 (fun _ : Fin 1 => 0) = 0 by exact (p 1).map_zero]
    simpa only [add_zero] using (diagonal_one_add_sub (p 1) (x ε) (y ε)).symm
  have hterm₂ :
      (fun ε : ℝ =>
        p 2 (fun _ : Fin 2 => x ε + y ε) - p 2 (fun _ : Fin 2 => x ε) -
          p 2 (fun _ : Fin 2 => y ε) + p 2 (fun _ : Fin 2 => 0) -
          ε ^ 4 • (p 2 ![u, v₃] + p 2 ![v₃, u])) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    have hconst : (fun _ : ℝ => p 2 ![u, v₄] + p 2 ![v₄, u]) =O[𝓝 0]
        (fun _ : ℝ => (1 : ℝ)) :=
      Asymptotics.isBigO_const_of_tendsto tendsto_const_nhds one_ne_zero
    have hraw := (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 5) (𝓝 0)).smul hconst
    refine hraw.congr' ?_ ?_
    · filter_upwards
      intro ε
      rw [show p 2 (fun _ : Fin 2 => 0) = 0 by exact (p 2).map_zero, add_zero]
      exact
        (diagonal_two_scale_cubic_quartic_sub_cross (p 2) u v₃ v₄ ε).symm
    · filter_upwards
      intro ε
      simp
  have hdiagY₃ :
      (fun ε : ℝ => p 3 (fun _ : Fin 3 => y ε)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    have hzero : (fun _ : ℝ => (0 : E)) =O[𝓝 0] (fun ε : ℝ => ε ^ 3) :=
      Asymptotics.isBigO_zero _ _
    have hraw := (p 3).diagonal_add_sub_isBigO hzero hyO₃ hyO₃
    have hraw' :
        (fun ε : ℝ => p 3 (fun _ : Fin 3 => y ε)) =O[𝓝 0]
          (fun ε : ℝ => ε ^ 9) := by
      refine hraw.congr' ?_ ?_
      · filter_upwards
        intro ε
        rw [show p 3 (fun _ : Fin 3 => (0 : E)) = 0 by exact (p 3).map_zero]
        simp only [zero_add, sub_zero]
      · filter_upwards
        intro ε
        ring
    exact hraw'.trans
      (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 9)).isBigO
  have hterm₃ :
      (fun ε : ℝ =>
        p 3 (fun _ : Fin 3 => x ε + y ε) - p 3 (fun _ : Fin 3 => x ε) -
          p 3 (fun _ : Fin 3 => y ε) + p 3 (fun _ : Fin 3 => 0)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    have hraw := (p 3).diagonal_add_sub_isBigO hxO hyO₁ hyO₃
    have hfull :
        (fun ε : ℝ =>
          p 3 (fun _ : Fin 3 => x ε + y ε) - p 3 (fun _ : Fin 3 => x ε)) =O[𝓝 0]
          (fun ε : ℝ => ε ^ 5) := by
      refine hraw.congr' Filter.EventuallyEq.rfl ?_
      filter_upwards
      intro ε
      ring
    refine (hfull.sub hdiagY₃).congr_left ?_
    intro ε
    rw [show p 3 (fun _ : Fin 3 => (0 : E)) = 0 by exact (p 3).map_zero]
    simp only [add_zero]
  have hdiagY₄ :
      (fun ε : ℝ => p 4 (fun _ : Fin 4 => y ε)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    have hzero : (fun _ : ℝ => (0 : E)) =O[𝓝 0] (fun ε : ℝ => ε ^ 3) :=
      Asymptotics.isBigO_zero _ _
    have hraw := (p 4).diagonal_add_sub_isBigO hzero hyO₃ hyO₃
    have hraw' :
        (fun ε : ℝ => p 4 (fun _ : Fin 4 => y ε)) =O[𝓝 0]
          (fun ε : ℝ => ε ^ 12) := by
      refine hraw.congr' ?_ ?_
      · filter_upwards
        intro ε
        rw [show p 4 (fun _ : Fin 4 => (0 : E)) = 0 by exact (p 4).map_zero]
        simp only [zero_add, sub_zero]
      · filter_upwards
        intro ε
        ring
    exact hraw'.trans
      (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 12)).isBigO
  have hterm₄ :
      (fun ε : ℝ =>
        p 4 (fun _ : Fin 4 => x ε + y ε) - p 4 (fun _ : Fin 4 => x ε) -
          p 4 (fun _ : Fin 4 => y ε) + p 4 (fun _ : Fin 4 => 0)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    have hraw := (p 4).diagonal_add_sub_isBigO hxO hyO₁ hyO₃
    have hraw₆ :
        (fun ε : ℝ =>
          p 4 (fun _ : Fin 4 => x ε + y ε) - p 4 (fun _ : Fin 4 => x ε)) =O[𝓝 0]
          (fun ε : ℝ => ε ^ 6) :=
      hraw.congr_right (fun ε => by ring)
    have hfull :
        (fun ε : ℝ =>
          p 4 (fun _ : Fin 4 => x ε + y ε) - p 4 (fun _ : Fin 4 => x ε)) =O[𝓝 0]
          (fun ε : ℝ => ε ^ 5) :=
      hraw₆.trans (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 6)).isBigO
    refine (hfull.sub hdiagY₄).congr_left ?_
    intro ε
    rw [show p 4 (fun _ : Fin 4 => (0 : E)) = 0 by exact (p 4).map_zero]
    simp only [add_zero]
  have hall := (((hterm₀.add hterm₁).add hterm₂).add hterm₃).add hterm₄
  refine hall.congr' ?_ ?_
  · filter_upwards
    intro ε
    dsimp only [x, y]
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    abel
  · filter_upwards
    intro ε
    simp

/-- An analytic map along a linear direction and a cubic-quartic perturbation has only
the quadratic linear-cubic cross term below order five. -/
theorem analytic_mixed_cubic_quartic_sub_cross_isBigO [CompleteSpace F]
    (f : E → F) (a u v₃ v₄ : E) (hf : AnalyticAt ℝ f a) :
    (fun ε : ℝ =>
      let x := ε • u
      let y := ε ^ 3 • v₃ + ε ^ 4 • v₄
      f (a + (x + y)) - f (a + x) - f (a + y) + f a -
        ε ^ 4 • iteratedFDeriv ℝ 2 f a ![u, v₃]) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 5) := by
  obtain ⟨p, hpAt⟩ := hf
  obtain ⟨r, hpBall⟩ := hpAt
  have hpAt' : HasFPowerSeriesAt f p a := ⟨r, hpBall⟩
  have hsumPerm (A : E [×2]→L[ℝ] F) (v w : E) :
      (∑ σ : Equiv.Perm (Fin 2), A (fun i => ![v, w] (σ i))) =
        A ![v, w] + A ![w, v] := by
    have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
        {1, Equiv.swap 0 1} := by
      decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
      decide
    have hid : (fun i => ![v, w] ((1 : Equiv.Perm (Fin 2)) i)) = ![v, w] := by
      funext i
      fin_cases i <;> rfl
    have hswap : (fun i => ![v, w] ((Equiv.swap 0 1) i)) = ![w, v] := by
      funext i
      fin_cases i <;> rfl
    rw [huniv, Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne),
      Finset.sum_singleton, hid, hswap]
  have hiter := hpBall.iteratedFDeriv_eq_sum_of_completeSpace ![u, v₃]
  rw [hsumPerm] at hiter
  let x : ℝ → E := fun ε => ε • u
  let y : ℝ → E := fun ε => ε ^ 3 • v₃ + ε ^ 4 • v₄
  let z : ℝ → E := fun ε => x ε + y ε
  let rem : E → F := fun w => f (a + w) - p.partialSum 5 w
  have huO : (fun _ : ℝ => u) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto tendsto_const_nhds one_ne_zero
  have hxO : x =O[𝓝 0] (fun ε : ℝ => ε) := by
    simpa only [x, Pi.smul_apply, smul_eq_mul, mul_one] using
      (Asymptotics.isBigO_refl (fun ε : ℝ => ε) (𝓝 0)).smul huO
  have hyO₃ : y =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
    let q : ℝ → E := fun ε => v₃ + ε • v₄
    have hq0 : Tendsto q (𝓝 0) (𝓝 v₃) := by
      dsimp only [q]
      have hε : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
      simpa using tendsto_const_nhds.add (hε.smul_const v₄)
    have hqO : q =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
      Asymptotics.isBigO_const_of_tendsto hq0 one_ne_zero
    have hsmul :=
      (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)).smul hqO
    refine hsmul.congr' ?_ ?_
    · filter_upwards
      intro ε
      dsimp only [y, q, Pi.smul_apply]
      rw [smul_add, smul_smul]
      congr 1
    · filter_upwards
      intro ε
      simp
  have hyO₁ : y =O[𝓝 0] (fun ε : ℝ => ε) :=
    hyO₃.trans (by simpa only [pow_one] using
      (Asymptotics.isLittleO_pow_pow (by norm_num : 1 < 3)).isBigO)
  have hzO : z =O[𝓝 0] (fun ε : ℝ => ε) := by
    simpa only [z] using hxO.add hyO₁
  have hε0 : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
  have hε30 : Tendsto (fun ε : ℝ => ε ^ 3) (𝓝 0) (𝓝 0) := by
    simpa using hε0.pow 3
  have hx0 : Tendsto x (𝓝 0) (𝓝 0) := hxO.trans_tendsto hε0
  have hy0 : Tendsto y (𝓝 0) (𝓝 0) := hyO₃.trans_tendsto hε30
  have hz0 : Tendsto z (𝓝 0) (𝓝 0) := hzO.trans_tendsto hε0
  have hrem : rem =O[𝓝 0] (fun w : E => ‖w‖ ^ 5) := by
    simpa only [rem] using hpAt'.isBigO_sub_partialSum_pow 5
  have hremXRaw := hrem.comp_tendsto hx0
  have hremX : (fun ε : ℝ => rem (x ε)) =O[𝓝 0] (fun ε : ℝ => ε ^ 5) := by
    have hnorm : (fun ε : ℝ => ‖x ε‖ ^ 5) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
      simpa using hxO.norm_left.pow 5
    have hcomp : (fun ε : ℝ => rem (x ε)) =O[𝓝 0]
        (fun ε : ℝ => ‖x ε‖ ^ 5) := by
      change (fun ε : ℝ => rem (x ε)) =O[𝓝 0] (fun ε : ℝ => ‖x ε‖ ^ 5) at hremXRaw
      exact hremXRaw
    exact hcomp.trans hnorm
  have hremYRaw := hrem.comp_tendsto hy0
  have hremY₁₅ : (fun ε : ℝ => rem (y ε)) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 15) := by
    have hnorm : (fun ε : ℝ => ‖y ε‖ ^ 5) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 15) := by
      simpa only [← pow_mul, Nat.reduceMul] using hyO₃.norm_left.pow 5
    have hcomp : (fun ε : ℝ => rem (y ε)) =O[𝓝 0]
        (fun ε : ℝ => ‖y ε‖ ^ 5) := by
      change (fun ε : ℝ => rem (y ε)) =O[𝓝 0] (fun ε : ℝ => ‖y ε‖ ^ 5) at hremYRaw
      exact hremYRaw
    exact hcomp.trans hnorm
  have hremY : (fun ε : ℝ => rem (y ε)) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 5) :=
    hremY₁₅.trans (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 15)).isBigO
  have hremZRaw := hrem.comp_tendsto hz0
  have hremZ : (fun ε : ℝ => rem (z ε)) =O[𝓝 0] (fun ε : ℝ => ε ^ 5) := by
    have hnorm : (fun ε : ℝ => ‖z ε‖ ^ 5) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
      simpa using hzO.norm_left.pow 5
    have hcomp : (fun ε : ℝ => rem (z ε)) =O[𝓝 0]
        (fun ε : ℝ => ‖z ε‖ ^ 5) := by
      change (fun ε : ℝ => rem (z ε)) =O[𝓝 0] (fun ε : ℝ => ‖z ε‖ ^ 5) at hremZRaw
      exact hremZRaw
    exact hcomp.trans hnorm
  have hpoly :
      (fun ε : ℝ =>
        p.partialSum 5 (x ε + y ε) - p.partialSum 5 (x ε) -
          p.partialSum 5 (y ε) + p.partialSum 5 0 -
          ε ^ 4 • (p 2 ![u, v₃] + p 2 ![v₃, u])) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5) := by
    simpa only [x, y] using
      partialSum_five_mixed_cubic_quartic_sub_cross_isBigO p u v₃ v₄
  have hp0 : p.partialSum 5 0 = f a := by
    have hp1 : p 1 (fun _ : Fin 1 => (0 : E)) = 0 := (p 1).map_zero
    have hp2 : p 2 (fun _ : Fin 2 => (0 : E)) = 0 := (p 2).map_zero
    have hp3 : p 3 (fun _ : Fin 3 => (0 : E)) = 0 := (p 3).map_zero
    have hp4 : p 4 (fun _ : Fin 4 => (0 : E)) = 0 := (p 4).map_zero
    rw [FormalMultilinearSeries.partialSum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hpAt'.coeff_zero]
    rw [hp1, hp2, hp3, hp4]
    simp
  have hall := hpoly.add ((hremZ.sub hremX).sub hremY)
  refine hall.congr_left ?_
  intro ε
  dsimp only [rem, z, x, y]
  rw [hp0, ← hiter]
  abel

end FiniteTaylorJet
