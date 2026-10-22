/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

noncomputable section

section

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]

/-- Helper for Theorem 6.58: if `f` attains `⊥`, then every Moreau envelope value of `f` is
already `⊥`. -/
lemma moreau_envelope_eq_bot_of_exists_eq_bot
    {F : Type*} [NormedAddCommGroup F] {f : F → EReal}
    (hbot : ∃ u, f u = ⊥) (μ : PosReal) (x : F) :
    M[μ, f] x = ⊥ := by
  rcases hbot with ⟨u, hu⟩
  -- Evaluate the infimum at the point where the objective already equals `⊥`.
  rw [moreau_envelope_apply]
  refine le_antisymm ?_ bot_le
  calc
    (⨅ v : F, f v + ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal)) ≤
        f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
      iInf_le _ u
    _ = ⊥ := by simp [hu]

/-- Helper for Theorem 6.58: the penalized objective for `PiLp.separableSum f` splits into the
sum of the coordinatewise penalized objectives. -/
lemma separable_moreau_objective_eq_sum_coordinate_objectives
    (f : ∀ i, E i → EReal) (μ : PosReal) (x u : PiLp (2 : ENNReal) E) :
    PiLp.separableSum f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) =
      ∑ i, (f i (u i) + ((((1 / (2 * μ) : ℝ) * ‖x i - u i‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
  -- Expand both the separable sum and the `L²` product norm into coordinatewise finite sums.
  rw [PiLp.separableSum_apply, PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.sub_apply]
  have hquad :
      ((((1 / (2 * μ) : ℝ) * ∑ i, ‖x i - u i‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        ∑ i, ((((1 / (2 * μ) : ℝ) * ‖x i - u i‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    rw [Finset.mul_sum]
    simpa using
      (ereal_coe_sum Finset.univ
        (fun i : ι ↦ (1 / (2 * μ) : ℝ) * ‖x i - u i‖ ^ (2 : ℕ)))
  -- After distributing the scalar penalty over the finite sum, each coordinate is independent.
  rw [hquad, ← Finset.sum_add_distrib]

/-- Helper for Theorem 6.58: under the no-`⊥` and finite-value-witness hypotheses, the infimum of
an independent two-block objective separates into the sum of the two coordinate infima. -/
lemma iInf_prod_add_eq_add_iInf_of_ne_bot_of_lt_top_witness
    {α β : Type*} (g : α → EReal) (h : β → EReal)
    (hg_ne_bot : ∀ a, g a ≠ ⊥)
    (hg_dom : ∃ a, g a < ⊤) (hh_dom : ∃ b, h b < ⊤) :
    (⨅ p : α × β, g p.1 + h p.2) = (⨅ a, g a) + ⨅ b, h b := by
  classical
  rcases hg_dom with ⟨a0, ha0_top⟩
  rcases hh_dom with ⟨b0, hb0_top⟩
  let _ : Nonempty α := ⟨a0⟩
  let _ : Nonempty β := ⟨b0⟩
  have hi_g_ne_top : (⨅ a, g a) ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp ((iInf_le g a0).trans_lt ha0_top)
  have hi_h_ne_top : (⨅ b, h b) ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp ((iInf_le h b0).trans_lt hb0_top)
  by_cases hi_h_bot : (⨅ b, h b) = ⊥
  · have hstep : (⨅ b, g a0 + h b) = (⊥ : EReal) := by
      let F : EReal → EReal × EReal := fun z ↦ (g a0, z)
      have hF : ContinuousAt F (⨅ b, h b) := by
        exact continuousAt_const.prodMk continuousAt_id
      have hAdd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (F (⨅ b, h b)) := by
        simpa [F] using
          EReal.continuousAt_add (p := (g a0, ⨅ b, h b))
            (Or.inl (lt_top_iff_ne_top.mp ha0_top))
            (Or.inl (hg_ne_bot a0))
      have hmono : Monotone (fun z : EReal ↦ g a0 + z) := by
        intro y z hyz
        exact add_le_add_right hyz _
      -- First pull the inner infimum through addition by the finite-left witness `g a0`.
      calc
        (⨅ b, g a0 + h b) = g a0 + (⨅ b, h b) := by
          symm
          simpa [F] using Monotone.map_ciInf_of_continuousAt (ContinuousAt.comp hAdd hF) hmono
        _ = ⊥ := by simp [hi_h_bot]
    -- If the right infimum is already `⊥`, then the whole product infimum is also `⊥`.
    apply le_antisymm
    · calc
        (⨅ p : α × β, g p.1 + h p.2) = ⨅ a, ⨅ b, g a + h b := by rw [iInf_prod]
        _ ≤ ⨅ b, g a0 + h b := iInf_le _ a0
        _ = (⊥ : EReal) := hstep
        _ ≤ (⨅ a, g a) + ⨅ b, h b := by simp [hi_h_bot]
    · simp [hi_h_bot]
  · have hmap_h : ∀ a, (⨅ b, g a + h b) = g a + (⨅ b, h b) := by
      intro a
      let F : EReal → EReal × EReal := fun z ↦ (g a, z)
      have hF : ContinuousAt F (⨅ b, h b) := by
        exact continuousAt_const.prodMk continuousAt_id
      have hAdd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (F (⨅ b, h b)) := by
        simpa [F] using
          EReal.continuousAt_add (p := (g a, ⨅ b, h b))
            (Or.inr hi_h_bot)
            (Or.inl (hg_ne_bot a))
      have hmono : Monotone (fun z : EReal ↦ g a + z) := by
        intro y z hyz
        exact add_le_add_right hyz _
      -- In the non-`⊥` branch, addition by `g a` commutes with the inner infimum.
      symm
      simpa [F] using Monotone.map_ciInf_of_continuousAt (ContinuousAt.comp hAdd hF) hmono
    have houter : (⨅ a, g a + (⨅ b, h b)) = (⨅ a, g a) + (⨅ b, h b) := by
      let F : EReal → EReal × EReal := fun z ↦ (z, ⨅ b, h b)
      have hF : ContinuousAt F (⨅ a, g a) := by
        exact continuousAt_id.prodMk continuousAt_const
      have hAdd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (F (⨅ a, g a)) := by
        simpa [F] using
          EReal.continuousAt_add (p := ((⨅ a, g a), (⨅ b, h b)))
            (Or.inl hi_g_ne_top)
            (Or.inr hi_h_ne_top)
      have hmono : Monotone (fun z : EReal ↦ z + (⨅ b, h b)) := by
        intro y z hyz
        exact add_le_add_left hyz _
      -- Then commute the remaining outer infimum with addition by the fixed right infimum.
      symm
      simpa [F] using Monotone.map_ciInf_of_continuousAt (ContinuousAt.comp hAdd hF) hmono
    calc
      (⨅ p : α × β, g p.1 + h p.2) = ⨅ a, ⨅ b, g a + h b := by rw [iInf_prod]
      _ = ⨅ a, (g a + (⨅ b, h b)) := by simp [hmap_h]
      _ = (⨅ a, g a) + (⨅ b, h b) := houter

/-- Helper for Theorem 6.58: on a finite `Fin n` product, the infimum of a sum of independent
coordinate objectives equals the sum of the coordinate infima. -/
lemma iInf_sum_fin_eq_sum_iInf_of_ne_bot_of_lt_top_witness :
    ∀ {n : ℕ} {A : Fin n → Type*} (G : ∀ i, A i → EReal),
      (∀ i a, G i a ≠ ⊥) →
      (∀ i, ∃ a, G i a < ⊤) →
      (⨅ u : (i : Fin n) → A i, ∑ i, G i (u i)) = ∑ i, ⨅ a, G i a
  | 0, A, G, hG_ne_bot, hG_dom => by
      -- The empty product has one point and both sides reduce to the empty sum.
      simp
  | n + 1, A, G, hG_ne_bot, hG_dom => by
      rw [show (⨅ u : (i : Fin (n + 1)) → A i, ∑ i, G i (u i)) =
          (⨅ p : A 0 × ((i : Fin n) → A i.succ), G 0 p.1 + ∑ i, G i.succ (p.2 i)) by
            refine Equiv.iInf_congr (Fin.consEquiv A).symm ?_
            intro u
            simp [Fin.sum_univ_succ, Fin.tail]]
      -- Split the head coordinate from the tail coordinates, then apply the two-block lemma.
      rw [iInf_prod_add_eq_add_iInf_of_ne_bot_of_lt_top_witness
        (g := fun a : A 0 ↦ G 0 a)
        (h := fun v : (i : Fin n) → A i.succ ↦ ∑ i, G i.succ (v i))]
      · have htail :=
          iInf_sum_fin_eq_sum_iInf_of_ne_bot_of_lt_top_witness
            (G := fun i : Fin n ↦ G i.succ)
            (fun i a ↦ hG_ne_bot i.succ a)
            (fun i ↦ hG_dom i.succ)
        simpa [Fin.sum_univ_succ] using
          congrArg (fun t : EReal ↦ (⨅ a, G 0 a) + t) htail
      · intro a
        exact hG_ne_bot 0 a
      · exact hG_dom 0
      · classical
        choose a ha using fun i : Fin n ↦ hG_dom i.succ
        refine ⟨a, ?_⟩
        exact ereal_sum_lt_top Finset.univ (fun i : Fin n ↦ G i.succ (a i))
          (fun i _ ↦ ha i)

/-- Helper for Theorem 6.58: for any finite index type, the infimum of a sum of independent
coordinate objectives equals the sum of the coordinate infima under the standard `EReal`
no-`⊥` and finite-value-witness hypotheses. -/
lemma iInf_sum_pi_eq_sum_iInf_of_ne_bot_of_lt_top_witness
    {κ : Type*} [Fintype κ] {A : κ → Type*} (G : ∀ i, A i → EReal)
    (hG_ne_bot : ∀ i a, G i a ≠ ⊥) (hG_dom : ∀ i, ∃ a, G i a < ⊤) :
    (⨅ u : (i : κ) → A i, ∑ i, G i (u i)) = ∑ i, ⨅ a, G i a := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hleft :
      (⨅ u : ((i : κ) → A i), ∑ i, G i (u i)) =
        (⨅ u : ((j : Fin (Fintype.card κ)) → A (e j)), ∑ j, G (e j) (u j)) := by
    -- Reindex the function space from `κ` to `Fin (card κ)`.
    refine Equiv.iInf_congr (Equiv.piCongrLeft A e).symm ?_
    intro u
    simpa [e] using (Equiv.sum_comp e (fun i : κ ↦ G i (u i)))
  have hright :
      (∑ i, ⨅ a, G i a) = ∑ j, ⨅ a, G (e j) a := by
    -- Reindex the finite sum of coordinate infima by the same equivalence.
    symm
    simpa [e] using (Equiv.sum_comp e (fun i : κ ↦ ⨅ a, G i a))
  rw [hleft, iInf_sum_fin_eq_sum_iInf_of_ne_bot_of_lt_top_witness
    (G := fun j : Fin (Fintype.card κ) ↦ G (e j))]
  · exact hright.symm
  · intro j a
    exact hG_ne_bot (e j) a
  · intro j
    exact hG_dom (e j)

/- Theorem 6.58 is `source-facing`: the source asserts that the Moreau envelope of a separable
sum on a finite product splits coordinatewise. The existing chapter owners already provide the
right abstraction level: `separableSum` from Theorem 6.6 for the finite product model
`PiLp (2 : ENNReal) E`, and `M[μ, f]` from Definition 6.7 for the Moreau envelope. The theorem is
therefore stated for an arbitrary finite index type `ι`, not just `Fin m`. In `EReal`, however,
some properness is essential: without a finite-valued point in each coordinate, one summand can
force the right-hand side to `⊥` through a nonattained coordinatewise infimum while another
summand keeps the left-hand side at `⊤`. The canonical chapter owner for exactly the needed
primitive data is therefore the coordinatewise nonemptiness of `effective_domain`; the textbook
closed/convex assumptions and the no-`⊥` half of properness remain redundant for this separability
identity beyond the positive Moreau parameter already built into the owner. -/

-- Proof sketch: unfold `M[μ, PiLp.separableSum f]` via `moreau_envelope_apply` and
-- `PiLp.separableSum`.
-- Rewrite the `PiLp` quadratic term as the finite sum of the coordinatewise quadratic penalties.
-- The penalized objective becomes a finite sum of independent coordinatewise objectives.
-- Nonemptiness of the effective domain of each summand supplies exactly the finite-valued
-- witnesses needed to prevent the `⊤`/nonattained-`⊥` pathology in `EReal`, so the infimum over
-- the finite product separates into the sum of the coordinatewise infima.
/-- Theorem 6.58: the Moreau envelope of a finite separable sum on `PiLp (2 : ENNReal) E`
is the sum of the coordinatewise Moreau envelopes. This is the product-space rendering of
`M_f^μ (x₁, …, x_m) = ∑ i, M_{f_i}^μ (x_i)`. -/
theorem moreau_envelope_separableSum_eq_sum
    (f : ∀ i, E i → EReal) (hdom : ∀ i, (effective_domain (f i)).Nonempty)
    (μ : PosReal) (x : PiLp (2 : ENNReal) E) :
    M[μ, PiLp.separableSum f] x = ∑ i, M[μ, f i] (x i) := by
  classical
  by_cases hbot : ∃ i u, f i u = ⊥
  · rcases hbot with ⟨i, u, hu⟩
    choose y hy using hdom
    let z : PiLp (2 : ENNReal) E := WithLp.toLp 2 (Function.update y i u)
    have hsep_bot : PiLp.separableSum f z = ⊥ := by
      -- Put the bad coordinate into the product point; one `⊥` summand forces the whole sum to `⊥`.
      rw [PiLp.separableSum_apply]
      simpa [z, hu] using
        (WithBot.sum_eq_bot_iff (s := Finset.univ) (f := fun j ↦ f j (z j))).2
          ⟨i, by simp, by simpa [z] using hu⟩
    have hsep_bot_exists : ∃ z : PiLp (2 : ENNReal) E, PiLp.separableSum f z = ⊥ := ⟨z, hsep_bot⟩
    have hlhs_bot : M[μ, PiLp.separableSum f] x = ⊥ := by
      exact moreau_envelope_eq_bot_of_exists_eq_bot hsep_bot_exists μ x
    have hcoord_bot : M[μ, f i] (x i) = ⊥ := by
      exact moreau_envelope_eq_bot_of_exists_eq_bot ⟨u, hu⟩ μ (x i)
    have hrhs_bot : (∑ j, M[μ, f j] (x j)) = ⊥ := by
      simpa using
        (WithBot.sum_eq_bot_iff (s := Finset.univ) (f := fun j ↦ M[μ, f j] (x j))).2
          ⟨i, by simp, hcoord_bot⟩
    rw [hlhs_bot, hrhs_bot]
  · have hf_ne_bot : ∀ i u, f i u ≠ ⊥ := by
      intro i u hfu
      exact hbot ⟨i, u, hfu⟩
    let G : ∀ i, E i → EReal := fun i u ↦
      f i u + ((((1 / (2 * μ) : ℝ) * ‖x i - u‖ ^ (2 : ℕ)) : ℝ) : EReal)
    have hG_ne_bot : ∀ i u, G i u ≠ ⊥ := by
      intro i u
      simpa [G, EReal.add_ne_bot_iff] using
        (show f i u ≠ ⊥ ∧ ((((1 / (2 * μ) : ℝ) * ‖x i - u‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊥ from
          ⟨hf_ne_bot i u, EReal.coe_ne_bot _⟩)
    have hG_dom : ∀ i, ∃ u, G i u < ⊤ := by
      intro i
      rcases hdom i with ⟨u, hu_dom⟩
      refine ⟨u, ?_⟩
      -- The domain witness gives a finite function value, and the quadratic term is always finite.
      simpa [G] using
        EReal.add_lt_top (lt_top_iff_ne_top.mp hu_dom) (EReal.coe_ne_top _)
    let e : ((i : ι) → E i) ≃ PiLp (2 : ENNReal) E :=
      (WithLp.equiv 2 ((i : ι) → E i)).symm
    -- Route correction: the stable proof works directly at the `iInf` level rather than through
    -- the proximal-set API, because the hypotheses give domain witnesses but not minimizers.
    calc
      M[μ, PiLp.separableSum f] x =
          (⨅ u : PiLp (2 : ENNReal) E, ∑ i, G i (u i)) := by
            rw [moreau_envelope_apply]
            refine iInf_congr fun u ↦ ?_
            simpa [G] using
              separable_moreau_objective_eq_sum_coordinate_objectives f μ x u
      _ = (⨅ v : (i : ι) → E i, ∑ i, G i (v i)) := by
            refine Equiv.iInf_congr e.symm ?_
            intro v
            simp [e]
      _ = ∑ i, ⨅ u, G i u := by
            exact iInf_sum_pi_eq_sum_iInf_of_ne_bot_of_lt_top_witness G hG_ne_bot hG_dom
      _ = ∑ i, M[μ, f i] (x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [G, moreau_envelope_apply]

end
