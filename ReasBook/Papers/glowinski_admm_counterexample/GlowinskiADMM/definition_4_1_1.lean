module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle

@[expose] public section

namespace ConsensusADMM

universe u

variable {N : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.1.1 (1): for cyclic indices modulo `N ≥ 2` and `γ > 0`,
the families `ρ`, `ξ`, `a`, and `c` are respectively `residual`, `xVertex`,
`xNormal`, and `yNormal`. -/
#check (CycleConfig.cycleData_spec :
  ∀ (q : CycleConfig N E) (i : Fin N),
    q.residual i = q.gamma⁻¹ • (q.nu i - q.nu (q.previous i)) ∧
      q.xVertex i = q.eta i + q.residual i ∧
        q.xNormal i = q.eta (q.previous i) - q.nu (q.previous i) - q.xVertex i ∧
          q.yNormal i = q.nu (q.previous i) + q.residual i)
#check (CycleConfig :
  (N : ℕ) → (E : Type u) → [AddCommGroup E] → [Module ℝ E] → Type u)
#check (CycleConfig.residual : CycleConfig N E → Fin N → E)
#check (CycleConfig.xVertex : CycleConfig N E → Fin N → E)
#check (CycleConfig.xNormal : CycleConfig N E → Fin N → E)
#check (CycleConfig.yNormal : CycleConfig N E → Fin N → E)

/- Definition 4.1.1 (2): a nonself support compares a phase vertex with
the origin or with a vertex at a distinct phase. -/
#check (ProjectionCycle.mem_nonselfVertices :
  ∀ {v : Fin N → E} {i : Fin N} {z : E},
    z ∈ ProjectionCycle.nonselfVertices v i ↔ z = 0 ∨ ∃ j, j ≠ i ∧ z = v j)
#check (ProjectionCycle.nonselfVertices : (Fin N → E) → Fin N → Set E)

end ConsensusADMM
