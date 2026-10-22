/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_47

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace Net

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]

private theorem mapClusterPt_liminf (ξ : A → EReal) :
    MapClusterPt (Filter.liminf ξ atTop) atTop ξ := sorry

private theorem mapClusterPt_limsup (ξ : A → EReal) :
    MapClusterPt (Filter.limsup ξ atTop) atTop ξ := sorry

/-- Fact 1.15 (1): the net of tail infima of an extended-real-valued net converges to its limit
inferior. -/
-- Proof sketch: use the tail formula for `Net.liminf ξ` as a supremum of the tail infima, note
-- that the tail-infimum net is monotone, and apply the monotone convergence theorem in the order
-- topology on `EReal`.
theorem tendsto_tailInf_liminf (ξ : A → EReal) :
    Tendsto (fun a ↦ sInf (ξ '' Set.Ici a)) atTop (nhds (Filter.liminf ξ atTop)) := sorry

/-- Fact 1.15 (2): the net of tail suprema of an extended-real-valued net converges to its limit
superior. -/
-- Proof sketch: identify `Net.limsup ξ` with the infimum of the tail suprema, observe that the
-- tail-supremum net is monotone in the opposite direction, and conclude by antitone order
-- convergence.
theorem tendsto_tailSup_limsup (ξ : A → EReal) :
    Tendsto (fun a ↦ sSup (ξ '' Set.Ici a)) atTop (nhds (Filter.limsup ξ atTop)) := sorry

/-- Fact 1.15 (3): an extended-real-valued net admits a subnet converging to its limit inferior.
-/
-- Proof sketch: apply the subnet characterization of cluster points to the limit inferior, using
-- the tail-infimum convergence and the order structure of `EReal` to show that `Net.liminf ξ` is a
-- cluster point of `ξ`, then extract a monotone cofinal reindexing map.
theorem exists_subnet_tendsto_liminf (ξ : A → EReal) :
    ∃ (B : Type u) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B) (φ : B → A)
      (_ : Monotone φ) (_ : Tendsto φ atTop atTop),
        Tendsto (ξ ∘ φ) atTop (nhds (Filter.liminf ξ atTop)) := by
  rcases mapClusterPt_atTop_iff_exists_subnet_tendsto.mp (mapClusterPt_liminf ξ) with
    ⟨B, hB, hPreorder, hDirected, φ, hMonotone, hTendsto, hConv⟩
  exact ⟨B, hB, hPreorder, hDirected, φ, hMonotone, hTendsto, hConv⟩

/-- Fact 1.15 (4): an extended-real-valued net admits a subnet converging to its limit superior.
-/
-- Proof sketch: prove that `Net.limsup ξ` is a cluster point of `ξ` by combining the tail-supremum
-- convergence with the order topology on `EReal`, then invoke the cluster-point/subnet criterion
-- and record the monotone cofinal reindexing map.
theorem exists_subnet_tendsto_limsup (ξ : A → EReal) :
    ∃ (B : Type u) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B) (φ : B → A)
      (_ : Monotone φ) (_ : Tendsto φ atTop atTop),
        Tendsto (ξ ∘ φ) atTop (nhds (Filter.limsup ξ atTop)) := by
  rcases mapClusterPt_atTop_iff_exists_subnet_tendsto.mp (mapClusterPt_limsup ξ) with
    ⟨B, hB, hPreorder, hDirected, φ, hMonotone, hTendsto, hConv⟩
  exact ⟨B, hB, hPreorder, hDirected, φ, hMonotone, hTendsto, hConv⟩

/-- Fact 1.15 (5): an extended-real-valued net converges to `x` exactly when its limit inferior and
limit superior both equal `x`. -/
-- Proof sketch: if `ξ` tends to `x`, use `Filter.Tendsto.liminf_eq` and
-- `Filter.Tendsto.limsup_eq`. For the converse, combine the tail-infimum and tail-supremum
-- convergence from (1) and (2) with the squeeze criterion in the order topology.
theorem tendsto_iff_liminf_eq_limsup_eq {x : EReal} (ξ : A → EReal) :
    Tendsto ξ atTop (nhds x) ↔
      Filter.liminf ξ atTop = x ∧ Filter.limsup ξ atTop = x := by
  constructor
  · intro hξ
    exact ⟨hξ.liminf_eq, hξ.limsup_eq⟩
  · rintro ⟨h_liminf, h_limsup⟩
    exact tendsto_of_liminf_eq_limsup h_liminf h_limsup

/-- Fact 1.15 (6): for a sequence, there is a subsequence converging to the limit inferior. -/
-- Proof sketch: specialize the subnet statement to `A = ℕ` and use that subnets of sequences can
-- be represented by strictly monotone maps `ℕ → ℕ`.
theorem exists_subsequence_tendsto_liminf (ξ : ℕ → EReal) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (ξ ∘ φ) atTop (nhds (Filter.liminf ξ atTop)) := by
  simpa using TopologicalSpace.FirstCountableTopology.tendsto_subseq (mapClusterPt_liminf ξ)

/-- Fact 1.15 (7): for a sequence, there is a subsequence converging to the limit superior. -/
-- Proof sketch: specialize the subnet statement to sequences and rewrite the resulting cofinal
-- monotone reindexing as a strictly monotone subsequence of `ℕ`.
theorem exists_subsequence_tendsto_limsup (ξ : ℕ → EReal) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (ξ ∘ φ) atTop (nhds (Filter.limsup ξ atTop)) := by
  simpa using TopologicalSpace.FirstCountableTopology.tendsto_subseq (mapClusterPt_limsup ξ)

end Net
