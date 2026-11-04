/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_theorem_4_16

open scoped BigOperators

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- A residual `s,t`-path is shortest when no other residual `s,t`-path has fewer arcs. -/
def IsShortestResidualSTPath
    (tail head : A → V) (c x : A → ℝ) (s t : V) (P : List (ResidualArc A)) : Prop :=
  IsResidualSTPath tail head c x s t P ∧
    ∀ Q : List (ResidualArc A), IsResidualSTPath tail head c x s t Q → P.length ≤ Q.length

/-- A single shortest-augmenting-path step replaces a feasible flow `x` by the flow obtained by
augmenting it along a shortest residual `s,t`-path by its bottleneck value. -/
def IsShortestAugmentingPathStep
    (tail head : A → V) (s t : V) (c : A → ℝ) (x x' : A → ℝ) : Prop :=
  IsFeasibleSTFlow tail head s t c x ∧
    IsFeasibleSTFlow tail head s t c x' ∧
    ∃ ε : ℝ,
      ∃ P : List (ResidualArc A),
        IsShortestResidualSTPath tail head c x s t P ∧
        (∀ a ∈ P, ε ≤ residual_arc_capacity c x a) ∧
        (∃ a ∈ P, residual_arc_capacity c x a = ε) ∧
        x' = augment_flow x ε P

/-- A terminating shortest-augmenting-path execution starts from the zero flow, each consecutive
pair of flows is related by a shortest-augmenting-path step, and the last flow has no residual
`s,t`-path. -/
def IsTerminatingShortestAugmentingPathExecution
    (tail head : A → V) (s t : V) (c : A → ℝ) (xs : List (A → ℝ)) : Prop :=
  xs.head? = some (fun _ ↦ (0 : ℝ)) ∧
    xs.IsChain (IsShortestAugmentingPathStep tail head s t c) ∧
    ∀ x : A → ℝ,
      xs.getLast? = some x →
        NoResidualSTPath tail head c x s t

omit [Fintype V] [Fintype A] [DecidableEq A] in
/-- Helper for Theorem 4.17: a generalized residual path may be empty exactly in the trivial
case where the endpoints coincide; otherwise it is an ordinary nonempty residual path between
the prescribed endpoints. -/
def IsResidualPathBetween
    (tail head : A → V) (c x : A → ℝ) (u v : V) (P : List (ResidualArc A)) : Prop :=
  (P = [] ∧ u = v) ∨ IsResidualSTPath tail head c x u v P

section

omit [Fintype V] [Fintype A] [DecidableEq A]

/-- Helper for Theorem 4.17: the empty list is the generalized residual path from a vertex to
itself. -/
lemma is_residual_path_between_nil
    (tail head : A → V) (c x : A → ℝ) (u : V) :
    IsResidualPathBetween tail head c x u u [] := by
  -- The generalized predicate was designed so that the zero-length case is explicit.
  exact Or.inl ⟨rfl, rfl⟩

/-- Helper for Theorem 4.17: for distinct endpoints, the generalized residual-path predicate
reduces to the original nonempty `s,t`-path predicate. -/
private lemma is_residual_st_path_iff_residual_path_between
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    (P : List (ResidualArc A)) :
    IsResidualSTPath tail head c x s t P ↔
      IsResidualPathBetween tail head c x s t P := by
  constructor
  · intro hP
    -- Distinct endpoints rule out the empty-path branch, so the old predicate is enough.
    exact Or.inr hP
  · intro hP
    -- The generalized predicate only adds the empty-path case, which is impossible here.
    rcases hP with hnil | hpath
    · rcases hnil with ⟨hPnil, hst_eq⟩
      subst hPnil
      exact False.elim (hst hst_eq)
    · exact hpath

end

/-- Helper for Theorem 4.17: the residual distance is the minimum generalized residual-path
length, with the default value `|V|` when the target is unreachable. -/
private noncomputable def residual_distance
    (tail head : A → V) (c x : A → ℝ) (u v : V) : ℕ :=
  let _ : Decidable (∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x u v P) :=
    Classical.propDecidable _
  if _h : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x u v P then
    sInf
      {n : ℕ |
        ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x u v P ∧ P.length = n}
  else
    Fintype.card V

/-- Helper for Theorem 4.17: the ordered vertex list visited by a realized residual path. -/
private def residual_path_vertices
    (tail head : A → V) : List (ResidualArc A) → List V
  | [] => []
  | a :: P => ResidualArc.tail tail head a :: (a :: P).map (ResidualArc.head tail head)

section

omit [Fintype A] [DecidableEq A]

/-- Helper for Theorem 4.17: when no generalized residual path exists, the residual distance
uses the default terminal value `|V|`. -/
private lemma residual_distance_eq_card_of_no_path
    (tail head : A → V) (c x : A → ℝ) (u v : V)
    (h : ¬ ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x u v P) :
    residual_distance tail head c x u v = Fintype.card V := by
  -- The definition takes the default branch exactly in the unreachable case.
  classical
  simp [residual_distance, h]

/-- Helper for Theorem 4.17: every concrete generalized residual path gives an upper bound on
the residual distance between its endpoints. -/
private lemma residual_distance_le_length_of_path
    (tail head : A → V) (c x : A → ℝ) {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualPathBetween tail head c x u v P) :
    residual_distance tail head c x u v ≤ P.length := by
  -- In the reachable branch, the infimum is below the length of every realized path.
  classical
  let S : Set ℕ := {n : ℕ |
    ∃ Q : List (ResidualArc A), IsResidualPathBetween tail head c x u v Q ∧ Q.length = n}
  have hreachable : ∃ Q : List (ResidualArc A), IsResidualPathBetween tail head c x u v Q :=
    ⟨P, hP⟩
  have hdist : residual_distance tail head c x u v = sInf S := by
    simp [residual_distance, hreachable, S]
  have hsInf_le : sInf S ≤ P.length := by
    exact Nat.sInf_le ⟨P, hP, rfl⟩
  simpa [hdist] using hsInf_le

/-- Helper for Theorem 4.17: when a generalized residual path exists, the residual distance is
realized by one with minimal length. -/
private lemma existsPathBetweenRealizingResidualDistance
    (tail head : A → V) (c x : A → ℝ) {u v : V}
    (hpath : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x u v P) :
    ∃ P : List (ResidualArc A),
      IsResidualPathBetween tail head c x u v P ∧
        P.length = residual_distance tail head c x u v ∧
        ∀ Q : List (ResidualArc A),
          IsResidualPathBetween tail head c x u v Q → P.length ≤ Q.length := by
  -- Extract a witness at the infimum and record that every other realized path lies above it.
  classical
  let S : Set ℕ := {n : ℕ |
    ∃ Q : List (ResidualArc A), IsResidualPathBetween tail head c x u v Q ∧ Q.length = n}
  have hS_nonempty : S.Nonempty := by
    rcases hpath with ⟨P, hP⟩
    exact ⟨P.length, ⟨P, hP, rfl⟩⟩
  have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
  rcases hsInf_mem with ⟨P, hP, hlen⟩
  refine ⟨P, hP, ?_, ?_⟩
  · -- Rewrite the selected infimum witness back into the residual-distance definition.
    have hdist : residual_distance tail head c x u v = sInf S := by
      simp [residual_distance, hpath, S]
    exact hlen.trans hdist.symm
  · intro Q hQ
    -- Every realized path contributes an admissible length above the infimum.
    have hsInf_le : sInf S ≤ Q.length := by
      exact Nat.sInf_le ⟨Q, hQ, rfl⟩
    rwa [← hlen] at hsInf_le

/-- Helper for Theorem 4.17: a nonempty realized residual path contributes exactly one more
vertex than arc. -/
private lemma residual_path_vertices_length_eq_add_one
    (tail head : A → V) {P : List (ResidualArc A)} (hP : P ≠ []) :
    (residual_path_vertices tail head P).length = P.length + 1 := by
  -- Expanding the vertex list on a nonempty path exposes the single initial tail vertex.
  cases P with
  | nil =>
      exact False.elim (hP rfl)
  | cons a P =>
      simp [residual_path_vertices]

/-- Helper for Theorem 4.17: every residual step already comes with a concrete active residual
arc witness whose endpoints realize that step. -/
private lemma exists_residual_arc_of_step
    (tail head : A → V) (c x : A → ℝ) {u v : V}
    (hstep : ResidualStep tail head c x u v) :
    ∃ a : ResidualArc A,
      ResidualArc.tail tail head a = u ∧
        ResidualArc.head tail head a = v ∧
        IsActiveResidualArc c x a := by
  -- Unpack the step witness directly into its oriented-edge realization.
  rcases hstep with ⟨a, ha_active, ha_tail, ha_head⟩
  exact ⟨a, ha_tail, ha_head, ha_active⟩

/-- Helper for Theorem 4.17: prepending one active residual arc to a generalized residual path
with matching endpoint data yields a longer generalized residual path. -/
private lemma residual_path_between_cons
    (tail head : A → V) (c x : A → ℝ) {u v w : V} {a : ResidualArc A}
    (ha_tail : ResidualArc.tail tail head a = u)
    (ha_head : ResidualArc.head tail head a = v)
    (ha_active : IsActiveResidualArc c x a)
    {P : List (ResidualArc A)}
    (hP : IsResidualPathBetween tail head c x v w P) :
    IsResidualPathBetween tail head c x u w (a :: P) := by
  -- Split according to whether the suffix path is empty or already a realized nonempty path.
  rcases hP with hP_nil | hP_path
  · rcases hP_nil with ⟨hP_nil, hvw⟩
    subst hP_nil
    subst hvw
    refine Or.inr ?_
    refine ⟨by simp, ?_, ?_, ?_, List.isChain_singleton _⟩
    · intro b hb
      rcases List.mem_singleton.mp hb with rfl
      exact ha_active
    · simpa [ha_tail]
    · simpa [ha_head]
  · rcases hP_path with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
    cases P with
    | nil =>
        exact False.elim (hP_ne rfl)
    | cons b Q =>
        refine Or.inr ?_
        have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head b := by
          have hb_tail : some (ResidualArc.tail tail head b) = some v := by
            simpa using hP_head
          injection hb_tail with hb_tail_eq
          simpa [ha_head] using hb_tail_eq.symm
        refine ⟨by simp, ?_, ?_, ?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact ha_active
          · exact hP_active z hz'
        · simpa [ha_tail]
        · simpa using hP_last
        · exact hP_chain.cons_cons hlink

/-- Helper for Theorem 4.17: appending one active residual arc to a generalized residual path
with matching endpoint data yields a longer generalized residual path. -/
private lemma residualPathBetweenSnoc
    (tail head : A → V) (c x : A → ℝ) {u v w : V} {a : ResidualArc A}
    (ha_tail : ResidualArc.tail tail head a = v)
    (ha_head : ResidualArc.head tail head a = w)
    (ha_active : IsActiveResidualArc c x a)
    {P : List (ResidualArc A)}
    (hP : IsResidualPathBetween tail head c x u v P) :
    IsResidualPathBetween tail head c x u w (P ++ [a]) := by
  -- Split on the empty-prefix case, then append the final active arc to the realized suffix.
  rcases hP with hP_nil | hP_path
  · rcases hP_nil with ⟨hP_nil, huv⟩
    subst hP_nil
    subst huv
    refine Or.inr ?_
    refine ⟨by simp, ?_, ?_, ?_, List.isChain_singleton _⟩
    · intro b hb
      rcases List.mem_singleton.mp hb with rfl
      exact ha_active
    · simpa [ha_tail]
    · simpa [ha_head]
  · rcases hP_path with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
    refine Or.inr ?_
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hP_active b hb
      · rcases List.mem_singleton.mp hb with rfl
        exact ha_active
    · simpa [List.head?_append_of_ne_nil P hP_ne] using hP_head
    · -- The appended singleton contributes the new terminal head vertex.
      have hlast : (P ++ [a]).getLast? = some a := by
        simpa using List.getLast?_append_cons P a ([] : List (ResidualArc A))
      simpa [hlast, ha_head]
    · -- The chain glues at the old endpoint `v`, which is the tail of the appended arc.
      refine hP_chain.append (List.isChain_singleton _) ?_
      intro b hb_last z hz_head
      have hz_eq : z = a := by
        simpa using hz_head.symm
      subst hz_eq
      rcases List.mem_getLast?_eq_getLast hb_last with ⟨hP_ne', rfl⟩
      have hlast_head :
          ResidualArc.head tail head (P.getLast hP_ne') = v := by
        have :
            some (ResidualArc.head tail head (P.getLast hP_ne')) = some v := by
          simpa [List.getLast?_eq_getLast_of_ne_nil hP_ne'] using hP_last
        exact Option.some.inj this
      simpa [ha_tail] using hlast_head

/-- Helper for Theorem 4.17: concatenating two generalized residual paths with matching middle
vertex yields a generalized residual path between the outer endpoints. -/
private lemma residualPathBetweenAppend
    (tail head : A → V) (c x : A → ℝ) {u v w : V}
    {P Q : List (ResidualArc A)}
    (hP : IsResidualPathBetween tail head c x u v P)
    (hQ : IsResidualPathBetween tail head c x v w Q) :
    IsResidualPathBetween tail head c x u w (P ++ Q) := by
  -- Split on the empty-path branches; otherwise glue the two realized residual paths at `v`.
  rcases hP with hP_nil | hP_path
  · rcases hP_nil with ⟨rfl, rfl⟩
    simpa using hQ
  · rcases hQ with hQ_nil | hQ_path
    · rcases hQ_nil with ⟨rfl, rfl⟩
      simpa [List.append_nil] using
        (Or.inr hP_path : IsResidualPathBetween tail head c x u v P)
    · rcases hP_path with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
      rcases hQ_path with ⟨hQ_ne, hQ_active, hQ_head, hQ_last, hQ_chain⟩
      refine Or.inr ?_
      refine ⟨by
        intro happ
        exact hP_ne ((List.append_eq_nil_iff.mp happ).1), ?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with haP | haQ
        · exact hP_active a haP
        · exact hQ_active a haQ
      · simpa [List.head?_append_of_ne_nil P hP_ne] using hP_head
      · simpa [List.getLast?_append_of_ne_nil P hQ_ne] using hQ_last
      · cases Q with
        | nil =>
            exact False.elim (hQ_ne rfl)
        | cons b Q' =>
            have hhead_b : ResidualArc.tail tail head b = v := by
              have : some (ResidualArc.tail tail head b) = some v := by
                simpa using hQ_head
              exact Option.some.inj this
            refine hP_chain.append hQ_chain ?_
            intro a ha_last z hz_head
            have hz_eq : z = b := by
              simpa [List.head?] using hz_head.symm
            subst hz_eq
            rcases List.mem_getLast?_eq_getLast ha_last with ⟨hP_ne', rfl⟩
            have hlast_v : ResidualArc.head tail head (P.getLast hP_ne') = v := by
              have :
                  some (ResidualArc.head tail head (P.getLast hP_ne')) = some v := by
                simpa [List.getLast?_eq_getLast_of_ne_nil hP_ne'] using hP_last
              exact Option.some.inj this
            simpa [hhead_b] using hlast_v

/-- Helper for Theorem 4.17: splitting a realized residual path at one of its arcs yields
generalized prefix and suffix residual paths at that arc's endpoints. -/
private lemma residualPathBetweenSplitAtMember
    (tail head : A → V) (c x : A → ℝ) {s t : V}
    {P : List (ResidualArc A)} {a : ResidualArc A}
    (hP : IsResidualSTPath tail head c x s t P)
    (ha : a ∈ P) :
    ∃ P₁ P₂,
      P = P₁ ++ a :: P₂ ∧
        IsResidualPathBetween tail head c x s (ResidualArc.tail tail head a) P₁ ∧
        IsResidualPathBetween tail head c x (ResidualArc.head tail head a) t P₂ := by
  -- Induct on the realized path and stop when the chosen arc reaches the head of the list.
  rcases hP with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
  cases P with
  | nil =>
      exact False.elim (hP_ne rfl)
  | cons b P =>
      rcases List.mem_cons.mp ha with rfl | ha_tail
      · refine ⟨[], P, by simp, ?_, ?_⟩
        · have hs : s = ResidualArc.tail tail head a := by
            have : some (ResidualArc.tail tail head a) = some s := by
              simpa using hP_head
            exact (Option.some.inj this).symm
          exact Or.inl ⟨rfl, hs⟩
        · cases P with
          | nil =>
              have ht : ResidualArc.head tail head a = t := by
                have : some (ResidualArc.head tail head a) = some t := by
                  simpa using hP_last
                exact Option.some.inj this
              exact Or.inl ⟨rfl, ht⟩
          | cons d Q =>
              have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head d := by
                exact hP_chain.rel_head
              have htail_active :
                  ∀ z ∈ d :: Q, IsActiveResidualArc c x z := by
                intro z hz
                exact hP_active z (by simp [hz])
              have htail_path :
                  IsResidualSTPath tail head c x (ResidualArc.tail tail head d) t (d :: Q) := by
                refine ⟨by simp, htail_active, by simp, hP_last, hP_chain.tail⟩
              have hsuffix' :
                  IsResidualPathBetween tail head c x
                    (ResidualArc.tail tail head d) t (d :: Q) :=
                Or.inr htail_path
              simpa [hlink] using hsuffix'
      · cases P with
        | nil =>
            cases ha_tail
        | cons d Q =>
            have hs : ResidualArc.tail tail head b = s := by
              have : some (ResidualArc.tail tail head b) = some s := by
                simpa using hP_head
              exact Option.some.inj this
            have hb_active : IsActiveResidualArc c x b := hP_active b (by simp)
            have hlink : ResidualArc.head tail head b = ResidualArc.tail tail head d := by
              exact hP_chain.rel_head
            have htail_active :
                ∀ z ∈ d :: Q, IsActiveResidualArc c x z := by
              intro z hz
              exact hP_active z (by simp [hz])
            have htail_path :
                IsResidualSTPath tail head c x (ResidualArc.tail tail head d) t (d :: Q) := by
              refine ⟨by simp, htail_active, by simp, hP_last, hP_chain.tail⟩
            rcases residualPathBetweenSplitAtMember tail head c x htail_path ha_tail with
              ⟨P₁, P₂, hdecomp, hprefix, hsuffix⟩
            have hprefix' :
                IsResidualPathBetween tail head c x
                  (ResidualArc.head tail head b) (ResidualArc.tail tail head a) P₁ := by
              simpa [hlink] using hprefix
            refine ⟨b :: P₁, P₂, ?_, ?_, hsuffix⟩
            · simpa [hdecomp, List.cons_append]
            · exact residual_path_between_cons tail head c x hs rfl hb_active hprefix'

/-- Helper for Theorem 4.17: any finite chain of residual steps can be realized by a generalized
residual path whose number of arcs is one less than the number of listed vertices. -/
private lemma exists_residual_path_between_of_vertex_chain
    (tail head : A → V) (c x : A → ℝ) :
    ∀ {L : List V} (hL_ne : L ≠ []),
      List.IsChain (ResidualStep tail head c x) L →
        ∃ P : List (ResidualArc A),
          IsResidualPathBetween tail head c x (L.head hL_ne) (L.getLast hL_ne) P ∧
            P.length + 1 = L.length
  | [], hL_ne, _ => False.elim (hL_ne rfl)
  | [u], _, _ =>
      -- A singleton vertex list realizes the empty generalized path at that vertex.
      ⟨[], is_residual_path_between_nil tail head c x u, by simp⟩
  | u :: v :: W, _, hchain => by
      -- Realize the first residual step, then prepend that arc to the recursive tail path.
      have huv : ResidualStep tail head c x u v := by
        exact (List.isChain_cons.mp hchain).1 _ (by simp)
      have htail : List.IsChain (ResidualStep tail head c x) (v :: W) := by
        exact (List.isChain_cons.mp hchain).2
      rcases exists_residual_arc_of_step tail head c x huv with
        ⟨a, ha_tail, ha_head, ha_active⟩
      rcases exists_residual_path_between_of_vertex_chain tail head c x (L := v :: W)
          (by simp) htail with ⟨P, hP, hlen⟩
      refine ⟨a :: P, residual_path_between_cons tail head c x ha_tail ha_head ha_active hP, ?_⟩
      calc
        (a :: P).length + 1 = P.length + 2 := by simp
        _ = (v :: W).length + 1 := by omega
        _ = (u :: v :: W).length := by simp

/-- Helper for Theorem 4.17: the ordered vertex list of a realized residual path forms a chain
of residual steps from the source endpoint to the sink endpoint. -/
private lemma residual_path_vertices_is_step_chain
    (tail head : A → V) (c x : A → ℝ) {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P) :
    List.IsChain (ResidualStep tail head c x) (residual_path_vertices tail head P) := by
  -- Induct on the realized path and turn each active residual arc into the matching step.
  rcases hP with ⟨hP_ne, hP_active, _, hP_last, hP_chain⟩
  cases P with
  | nil =>
      exact False.elim (hP_ne rfl)
  | cons a P =>
      have hstep_a :
          ResidualStep tail head c x
            (ResidualArc.tail tail head a) (ResidualArc.head tail head a) := by
        exact ⟨a, hP_active a (by simp), rfl, rfl⟩
      cases P with
      | nil =>
          simpa [residual_path_vertices] using (List.isChain_pair.2 hstep_a)
      | cons b Q =>
          have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head b := by
            exact hP_chain.rel_head
          have htail_active :
              ∀ z ∈ b :: Q, IsActiveResidualArc c x z := by
            intro z hz
            exact hP_active z (by simp [hz])
          have htail_path :
              IsResidualSTPath tail head c x (ResidualArc.tail tail head b) v (b :: Q) := by
            refine ⟨by simp, htail_active, by simp, hP_last, hP_chain.tail⟩
          have htail_chain :=
            residual_path_vertices_is_step_chain tail head c x htail_path
          have hstep_ab :
              ResidualStep tail head c x
                (ResidualArc.tail tail head a) (ResidualArc.tail tail head b) := by
            simpa [hlink] using hstep_a
          have hcons :
              List.IsChain (ResidualStep tail head c x)
                (ResidualArc.tail tail head a :: residual_path_vertices tail head (b :: Q)) := by
            refine List.IsChain.cons htail_chain ?_
            intro y hy
            have hy' : ResidualArc.tail tail head b = y := by
              simpa [residual_path_vertices] using hy
            simpa [hy'] using hstep_ab
          simpa [residual_path_vertices, hlink] using hcons

/-- Helper for Theorem 4.17: the first vertex on the visited-vertex list of a realized residual
path is its source endpoint. -/
private lemma residual_path_vertices_head
    (tail head : A → V) (c x : A → ℝ) {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P) :
    (residual_path_vertices tail head P).head? = some u := by
  -- The first visited vertex is the residual tail of the first arc.
  rcases hP with ⟨hP_ne, _, hP_head, _, _⟩
  cases P with
  | nil =>
      exact False.elim (hP_ne rfl)
  | cons a P =>
      simpa [residual_path_vertices] using hP_head

/-- Helper for Theorem 4.17: the last vertex on the visited-vertex list of a realized residual
path is its sink endpoint. -/
private lemma residual_path_vertices_getLast
    (tail head : A → V) (c x : A → ℝ) {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P) :
    (residual_path_vertices tail head P).getLast? = some v := by
  -- Drop the initial source vertex; the last visited vertex is still the path endpoint.
  rcases hP with ⟨hP_ne, hP_active, _, hP_last, hP_chain⟩
  cases P with
  | nil =>
      exact False.elim (hP_ne rfl)
  | cons a P =>
      cases P with
      | nil =>
          simpa [residual_path_vertices] using hP_last
      | cons b Q =>
          have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head b := by
            exact hP_chain.rel_head
          have htail_active :
              ∀ z ∈ b :: Q, IsActiveResidualArc c x z := by
            intro z hz
            exact hP_active z (by simp [hz])
          have htail_path :
              IsResidualSTPath tail head c x (ResidualArc.tail tail head b) v (b :: Q) := by
            refine ⟨by simp, htail_active, by simp, hP_last, hP_chain.tail⟩
          have htail_last :=
            residual_path_vertices_getLast tail head c x htail_path
          simpa [residual_path_vertices, hlink] using htail_last

/-- Helper for Theorem 4.17: every duplicate in a list yields a decomposition with two explicit
occurrences of the repeated element. -/
private lemma duplicate_decomposition {α : Type*} {x : α} {L : List α}
    (hdup : List.Duplicate x L) :
    ∃ L₁ L₂ L₃ : List α, L = L₁ ++ x :: L₂ ++ x :: L₃ := by
  -- Induct on the duplicate witness and expose the second copy of `x`.
  induction hdup with
  | @cons_mem l hmem =>
      have hsplit : ∃ L₂ L₃ : List α, l = L₂ ++ x :: L₃ := by
        revert hmem
        induction l with
        | nil =>
            intro hmem
            cases hmem
        | cons y l ih =>
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem_tail
            · exact ⟨[], l, by simp⟩
            · rcases ih hmem_tail with ⟨L₂, L₃, hEq⟩
              exact ⟨y :: L₂, L₃, by simp [hEq, List.cons_append]⟩
      rcases hsplit with ⟨L₂, L₃, hEq⟩
      exact ⟨[], L₂, L₃, by simpa [hEq]⟩
  | @cons_duplicate y l hdup ih =>
      rcases ih with ⟨L₁, L₂, L₃, hEq⟩
      exact ⟨y :: L₁, L₂, L₃, by simp [hEq, List.cons_append]⟩

/-- Helper for Theorem 4.17: removing a closed middle segment between two equal vertices in a
vertex chain preserves the residual-step chain property. -/
private lemma shorten_residual_step_chain
    (tail head : A → V) (c x : A → ℝ)
    {L₁ L₂ L₃ : List V} {w : V}
    (hchain : List.IsChain (ResidualStep tail head c x) (L₁ ++ w :: L₂ ++ w :: L₃)) :
    List.IsChain (ResidualStep tail head c x) (L₁ ++ w :: L₃) := by
  -- Split at the first and second copies of `w`, then discard the closed middle segment.
  have hsplit₁ :
      List.IsChain (ResidualStep tail head c x) (L₁ ++ [w]) ∧
        List.IsChain (ResidualStep tail head c x) (w :: (L₂ ++ w :: L₃)) := by
    have hchain' :
        List.IsChain (ResidualStep tail head c x) (L₁ ++ (w :: (L₂ ++ w :: L₃))) := by
      simpa [List.append_assoc] using hchain
    exact
      (List.isChain_split (R := ResidualStep tail head c x) (c := w)
        (l₁ := L₁) (l₂ := L₂ ++ w :: L₃)).1 hchain'
  have hsplit₂ :
      List.IsChain (ResidualStep tail head c x) (w :: (L₂ ++ [w])) ∧
        List.IsChain (ResidualStep tail head c x) (w :: L₃) := by
    exact
      (List.isChain_cons_split (R := ResidualStep tail head c x) (a := w) (c := w)
        (l₁ := L₂) (l₂ := L₃)).1 hsplit₁.2
  have hfinal :
      List.IsChain (ResidualStep tail head c x) (L₁ ++ (w :: L₃)) := by
    exact
      (List.isChain_split (R := ResidualStep tail head c x) (c := w)
        (l₁ := L₁) (l₂ := L₃)).2 ⟨hsplit₁.1, hsplit₂.2⟩
  simpa [List.append_assoc] using hfinal

end

/-- Helper for Theorem 4.17: a residual arc is relevant when it lies on a shortest residual
`s,t`-route in the source-proof layer decomposition. -/
private noncomputable def IsRelevantResidualArc
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ) (a : ResidualArc A) : Prop :=
  IsActiveResidualArc c x a ∧
    residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
        residual_distance tail head c x (ResidualArc.head tail head a) t =
      residual_distance tail head c x s t

/-- Helper for Theorem 4.17: the relevance count is taken on original arcs, so either residual
orientation of an edge contributes to the same ambient bound `|A|`. -/
private noncomputable def relevant_edge_count
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ) : ℕ :=
  let _ : DecidablePred
      (fun e : A ↦ ∃ o : ResidualArcOrientation,
        IsRelevantResidualArc tail head c s t x ⟨e, o⟩) :=
    Classical.decPred _
  Fintype.card {e : A // ∃ o : ResidualArcOrientation,
    IsRelevantResidualArc tail head c s t x ⟨e, o⟩}

section

omit [DecidableEq A] in
/-- Helper for Theorem 4.17: counting relevant original arcs can never exceed the total number
of original arcs. -/
private lemma relevant_edge_count_le_card_edges
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ) :
    relevant_edge_count tail head c s t x ≤ Fintype.card A := by
  classical
  -- The relevance count is a subtype cardinality inside the finite edge type.
  dsimp [relevant_edge_count]
  simpa using
    (Fintype.card_subtype_le
      (fun e : A ↦ ∃ o : ResidualArcOrientation,
        IsRelevantResidualArc tail head c s t x ⟨e, o⟩))

end

/-- Helper for Theorem 4.17: the source-proof rank uses the residual `s,t`-distance as the
primary coordinate and the complement of the relevant-edge count as the tie-breaker. When there
is no residual `s,t`-path left, the rank takes its terminal value `|V| |A|`. -/
private noncomputable def sap_rank
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ) : ℕ :=
  let _ : Decidable (∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P) :=
    Classical.propDecidable _
  if _h : ∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P then
    residual_distance tail head c x s t * Fintype.card A +
      (Fintype.card A - relevant_edge_count tail head c s t x)
  else
    Fintype.card V * Fintype.card A

section

omit [DecidableEq A] in
/-- Helper for Theorem 4.17: once the residual digraph has no `s,t`-path, the rank is exactly
the terminal value `|V| |A|`. -/
private lemma sap_rank_eq_bound_of_no_residual_path
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ)
    (h : ¬ ∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P) :
    sap_rank tail head c s t x = Fintype.card V * Fintype.card A := by
  -- The terminal branch of the rank definition is immediate from the missing-path hypothesis.
  classical
  simp [sap_rank, h]

end

section

omit [Fintype A] [DecidableEq A]

/-- Helper for Theorem 4.17: a shortest realized residual path cannot revisit a vertex, because
deleting the closed subwalk between two equal visited vertices yields a strictly shorter
generalized residual path with the same endpoints. -/
private lemma shortenResidualPathBetweenOfDuplicateVertex
    (tail head : A → V) (c x : A → ℝ) {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P)
    {w : V} (hdup : List.Duplicate w (residual_path_vertices tail head P)) :
    ∃ Q : List (ResidualArc A),
      IsResidualPathBetween tail head c x u v Q ∧
        Q.length < P.length := by
  -- Remove the closed segment between two equal visited vertices and realize the shorter chain.
  have hP_ne : P ≠ [] := hP.1
  have hverts_len :
      (residual_path_vertices tail head P).length = P.length + 1 :=
    residual_path_vertices_length_eq_add_one tail head hP_ne
  rcases duplicate_decomposition hdup with ⟨L₁, L₂, L₃, hdecomp⟩
  have hshort_chain :
      List.IsChain (ResidualStep tail head c x) (L₁ ++ w :: L₃) := by
    have hchain :=
      residual_path_vertices_is_step_chain tail head c x hP
    have hchain' :
        List.IsChain (ResidualStep tail head c x) (L₁ ++ w :: L₂ ++ w :: L₃) := by
      simpa [hdecomp, List.append_assoc] using hchain
    exact
      shorten_residual_step_chain tail head c x (L₁ := L₁) (L₂ := L₂) (L₃ := L₃)
        (w := w) hchain'
  have hshort_ne : L₁ ++ w :: L₃ ≠ [] := by
    simp
  rcases exists_residual_path_between_of_vertex_chain tail head c x
      (L := L₁ ++ w :: L₃) hshort_ne hshort_chain with
    ⟨Q, hQ_between, hQ_len⟩
  have hhead_opt_long :
      (L₁ ++ w :: L₂ ++ w :: L₃).head? = some u := by
    simpa [hdecomp] using residual_path_vertices_head tail head c x hP
  have hhead_opt_short :
      (L₁ ++ w :: L₃).head? = some u := by
    cases L₁ with
    | nil =>
        simpa using hhead_opt_long
    | cons a L₁ =>
        simpa using hhead_opt_long
  have hlast_opt_long :
      (L₁ ++ w :: L₂ ++ w :: L₃).getLast? = some v := by
    simpa [hdecomp] using residual_path_vertices_getLast tail head c x hP
  have hlast_opt_short :
      (L₁ ++ w :: L₃).getLast? = some v := by
    have hsuffix_ne : (w :: L₃) ≠ [] := by simp
    calc
      (L₁ ++ w :: L₃).getLast? = (w :: L₃).getLast? := by
        simpa using List.getLast?_append_of_ne_nil L₁ hsuffix_ne
      _ = (L₁ ++ w :: L₂ ++ w :: L₃).getLast? := by
        symm
        simpa [List.append_assoc] using
          List.getLast?_append_of_ne_nil (L₁ ++ w :: L₂) hsuffix_ne
      _ = some v := hlast_opt_long
  have hhead_eq : (L₁ ++ w :: L₃).head hshort_ne = u := by
    cases L₁ with
    | nil =>
        have : w = u := by
          have htmp : some w = some u := by simpa using hhead_opt_short
          exact Option.some.inj htmp
        simpa [this]
    | cons a L₁ =>
        have : a = u := by
          have htmp : some a = some u := by simpa using hhead_opt_short
          exact Option.some.inj htmp
        simpa [this]
  have hlast_eq : (L₁ ++ w :: L₃).getLast hshort_ne = v := by
    have : some ((L₁ ++ w :: L₃).getLast hshort_ne) = some v := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hshort_ne] using hlast_opt_short
    exact Option.some.inj this
  have hshorter_vertices :
      (L₁ ++ w :: L₃).length < (L₁ ++ w :: L₂ ++ w :: L₃).length := by
    have hlen :
        (L₁ ++ w :: L₂ ++ w :: L₃).length =
          (L₁ ++ w :: L₃).length + (L₂.length + 1) := by
      simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [hlen]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  have hQ_lt : Q.length < P.length := by
    have hlong_len :
        (L₁ ++ w :: L₂ ++ w :: L₃).length = P.length + 1 := by
      simpa [hdecomp] using hverts_len
    have hQ_lt_succ : Q.length + 1 < P.length + 1 := by
      calc
        Q.length + 1 = (L₁ ++ w :: L₃).length := hQ_len
        _ < (L₁ ++ w :: L₂ ++ w :: L₃).length := hshorter_vertices
        _ = P.length + 1 := hlong_len
    omega
  refine ⟨Q, ?_, hQ_lt⟩
  -- The shortened chain keeps the original source and sink endpoints.
  simpa [hhead_eq, hlast_eq] using hQ_between

/-- Helper for Theorem 4.17: every shortest residual path between distinct endpoints has length
strictly smaller than `|V|`. -/
private lemma shortest_residual_path_length_lt_card_vertices
    (tail head : A → V) (c x : A → ℝ) {u v : V} (huv : u ≠ v)
    {P : List (ResidualArc A)}
    (hP_between : IsResidualPathBetween tail head c x u v P)
    (hP_shortest :
      ∀ Q : List (ResidualArc A),
        IsResidualPathBetween tail head c x u v Q → P.length ≤ Q.length) :
    P.length < Fintype.card V := by
  -- Distinct endpoints force a nonempty realized path, whose visited-vertex list must be nodup.
  have hP : IsResidualSTPath tail head c x u v P :=
    (is_residual_st_path_iff_residual_path_between tail head c x huv P).2 hP_between
  have hP_ne : P ≠ [] := hP.1
  let L := residual_path_vertices tail head P
  have hL_len : L.length = P.length + 1 :=
    residual_path_vertices_length_eq_add_one tail head hP_ne
  have hL_nodup : L.Nodup := by
    by_contra hL_not_nodup
    rcases (List.exists_duplicate_iff_not_nodup).2 hL_not_nodup with ⟨w, hdup⟩
    rcases shortenResidualPathBetweenOfDuplicateVertex tail head c x hP hdup with
      ⟨Q, hQ_between, hQ_lt⟩
    have hmin := hP_shortest Q hQ_between
    exact (Nat.not_lt_of_ge hmin) hQ_lt
  have hL_card : L.length ≤ Fintype.card V := List.Nodup.length_le_card hL_nodup
  omega

/-- Helper for Theorem 4.17: residual distances are always bounded above by the total number of
vertices, with equality only in the unreachable default branch. -/
private lemma residualDistanceLeCardVertices
    (tail head : A → V) (c x : A → ℝ) (u v : V) :
    residual_distance tail head c x u v ≤ Fintype.card V := by
  -- Reachable pairs have a shortest realizing path, and unreachable pairs use the default value.
  by_cases hpath : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x u v P
  · by_cases huv : u = v
    · subst huv
      have hnil : IsResidualPathBetween tail head c x u u [] :=
        is_residual_path_between_nil tail head c x u
      have hzero : residual_distance tail head c x u u = 0 := by
        simpa using residual_distance_le_length_of_path tail head c x hnil
      rw [hzero]
      exact Nat.zero_le _
    · rcases existsPathBetweenRealizingResidualDistance tail head c x hpath with
        ⟨P, hP_between, hP_len, hP_shortest⟩
      have hlt : P.length < Fintype.card V :=
        shortest_residual_path_length_lt_card_vertices
          tail head c x huv hP_between hP_shortest
      rw [← hP_len]
      exact Nat.le_of_lt hlt
  · rw [residual_distance_eq_card_of_no_path tail head c x u v hpath]

/-- Helper for Theorem 4.17: every active residual arc satisfies the basic triangle inequalities
for the source and sink distance labels. -/
private lemma residualDistanceTriangleOfActiveArc
    (tail head : A → V) (c x : A → ℝ) (s t : V) {a : ResidualArc A}
    (ha_active : IsActiveResidualArc c x a) :
    residual_distance tail head c x s (ResidualArc.head tail head a) ≤
        residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 ∧
      residual_distance tail head c x (ResidualArc.tail tail head a) t ≤
        residual_distance tail head c x (ResidualArc.head tail head a) t + 1 := by
  constructor
  · -- Realize a shortest path to the arc tail, then append the active arc.
    by_cases hpath :
        ∃ P : List (ResidualArc A),
          IsResidualPathBetween tail head c x s (ResidualArc.tail tail head a) P
    · rcases existsPathBetweenRealizingResidualDistance tail head c x hpath with
        ⟨P, hP_between, hP_len, hP_shortest⟩
      have hPa :
          IsResidualPathBetween tail head c x s (ResidualArc.head tail head a) (P ++ [a]) :=
        residualPathBetweenSnoc tail head c x rfl rfl ha_active hP_between
      have hbound :
          residual_distance tail head c x s (ResidualArc.head tail head a) ≤ (P ++ [a]).length :=
        residual_distance_le_length_of_path tail head c x hPa
      rw [List.length_append, List.length_singleton, hP_len] at hbound
      simpa [Nat.add_assoc] using hbound
    · calc
        residual_distance tail head c x s (ResidualArc.head tail head a)
            ≤ Fintype.card V :=
          residualDistanceLeCardVertices tail head c x s (ResidualArc.head tail head a)
        _ ≤ Fintype.card V + 1 := Nat.le_succ _
        _ =
            residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 := by
          rw [residual_distance_eq_card_of_no_path tail head c x
            s (ResidualArc.tail tail head a) hpath]
  · -- Realize a shortest path from the arc head to the sink, then prepend the active arc.
    by_cases hpath :
        ∃ P : List (ResidualArc A),
          IsResidualPathBetween tail head c x (ResidualArc.head tail head a) t P
    · rcases existsPathBetweenRealizingResidualDistance tail head c x hpath with
        ⟨P, hP_between, hP_len, hP_shortest⟩
      have haP :
          IsResidualPathBetween tail head c x (ResidualArc.tail tail head a) t (a :: P) :=
        residual_path_between_cons tail head c x rfl rfl ha_active hP_between
      have hbound :
          residual_distance tail head c x (ResidualArc.tail tail head a) t ≤ (a :: P).length :=
        residual_distance_le_length_of_path tail head c x haP
      rw [List.length_cons, hP_len] at hbound
      simpa [Nat.add_assoc] using hbound
    · calc
        residual_distance tail head c x (ResidualArc.tail tail head a) t
            ≤ Fintype.card V :=
          residualDistanceLeCardVertices tail head c x (ResidualArc.tail tail head a) t
        _ ≤ Fintype.card V + 1 := Nat.le_succ _
        _ =
            residual_distance tail head c x (ResidualArc.head tail head a) t + 1 := by
          rw [residual_distance_eq_card_of_no_path tail head c x
            (ResidualArc.head tail head a) t hpath]

/-- Helper for Theorem 4.17: the residual distance from a vertex to itself is zero, realized by
the empty generalized residual path. -/
private lemma residualDistanceSelf
    (tail head : A → V) (c x : A → ℝ) (u : V) :
    residual_distance tail head c x u u = 0 := by
  -- The empty generalized residual path gives a zero upper bound, forcing equality in `ℕ`.
  have hzero :
      residual_distance tail head c x u u ≤ 0 :=
    residual_distance_le_length_of_path tail head c x
      (is_residual_path_between_nil tail head c x u)
  exact Nat.eq_zero_of_le_zero hzero

/-- Helper for Theorem 4.17: routing through an intermediate vertex bounds the total residual
distance by the sum of the source-to-middle and middle-to-sink residual distances. -/
private lemma residualDistanceLeAddOfIntermediate
    (tail head : A → V) (c x : A → ℝ) (s m t : V) :
    residual_distance tail head c x s t ≤
      residual_distance tail head c x s m + residual_distance tail head c x m t := by
  -- Realize shortest generalized paths to and from the middle vertex when they exist, and use
  -- the default `|V|` branch otherwise.
  by_cases hsm : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x s m P
  · by_cases hmt : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x m t P
    · rcases existsPathBetweenRealizingResidualDistance tail head c x hsm with
        ⟨P, hP, hP_len, _⟩
      rcases existsPathBetweenRealizingResidualDistance tail head c x hmt with
        ⟨Q, hQ, hQ_len, _⟩
      have hPQ : IsResidualPathBetween tail head c x s t (P ++ Q) :=
        residualPathBetweenAppend tail head c x hP hQ
      have hbound :
          residual_distance tail head c x s t ≤ (P ++ Q).length :=
        residual_distance_le_length_of_path tail head c x hPQ
      rw [List.length_append, hP_len, hQ_len] at hbound
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound
    · calc
        residual_distance tail head c x s t ≤ Fintype.card V :=
          residualDistanceLeCardVertices tail head c x s t
        _ ≤ residual_distance tail head c x s m + Fintype.card V :=
          Nat.le_add_left _ _
        _ = residual_distance tail head c x s m + residual_distance tail head c x m t := by
          rw [residual_distance_eq_card_of_no_path tail head c x m t hmt]
  · calc
      residual_distance tail head c x s t ≤ Fintype.card V :=
        residualDistanceLeCardVertices tail head c x s t
      _ ≤ Fintype.card V + residual_distance tail head c x m t :=
        Nat.le_add_right _ _
      _ = residual_distance tail head c x s m + residual_distance tail head c x m t := by
        rw [residual_distance_eq_card_of_no_path tail head c x s m hsm]

/-- Helper for Theorem 4.17: a shortest realized residual `s,t`-path has length equal to the
residual distance between its endpoints. -/
private lemma shortestResidualPathLengthEqResidualDistance
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)}
    (hPshort : IsShortestResidualSTPath tail head c x s t P) :
    residual_distance tail head c x s t = P.length := by
  -- Compare the chosen shortest realized path with a realizing witness for the distance infimum.
  have hP_between :
      IsResidualPathBetween tail head c x s t P :=
    (is_residual_st_path_iff_residual_path_between tail head c x hst P).1 hPshort.1
  have hdist_le :
      residual_distance tail head c x s t ≤ P.length :=
    residual_distance_le_length_of_path tail head c x hP_between
  rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨P, hP_between⟩ with
    ⟨Q, hQ_between, hQ_len, hQ_shortest⟩
  have hQ : IsResidualSTPath tail head c x s t Q :=
    (is_residual_st_path_iff_residual_path_between tail head c x hst Q).2 hQ_between
  have hlen_le : P.length ≤ Q.length := hPshort.2 Q hQ
  exact Nat.le_antisymm hdist_le (by simpa [hQ_len] using hlen_le)

/-- Helper for Theorem 4.17: replacing the prefix of a shortest residual path by any other
generalized path to the same split vertex cannot shorten the total path. -/
private lemma shortestResidualPathPrefixReplacementNotShorter
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {a : ResidualArc A} {P₁ P₂ Q : List (ResidualArc A)}
    (hdecomp : P = P₁ ++ a :: P₂)
    (hsuffix : IsResidualPathBetween tail head c x (ResidualArc.head tail head a) t P₂)
    (hQ : IsResidualPathBetween tail head c x s (ResidualArc.tail tail head a) Q) :
    P₁.length ≤ Q.length := by
  -- Turn the replacement `Q ++ (a :: P₂)` into a realized `s,t`-path and invoke shortestness.
  have ha_mem : a ∈ P := by
    rw [hdecomp]
    simp
  have ha_active : IsActiveResidualArc c x a := hPshort.1.2.1 a ha_mem
  have htail :
      IsResidualPathBetween tail head c x (ResidualArc.tail tail head a) t (a :: P₂) :=
    residual_path_between_cons tail head c x rfl rfl ha_active hsuffix
  have hreplace :
      IsResidualPathBetween tail head c x s t (Q ++ (a :: P₂)) :=
    residualPathBetweenAppend tail head c x hQ htail
  have hreplace_st : IsResidualSTPath tail head c x s t (Q ++ (a :: P₂)) :=
    (is_residual_st_path_iff_residual_path_between tail head c x hst _).2 hreplace
  have hlen : P.length ≤ (Q ++ (a :: P₂)).length := hPshort.2 _ hreplace_st
  rw [hdecomp, List.length_append, List.length_cons, List.length_append, List.length_cons] at hlen
  omega

/-- Helper for Theorem 4.17: replacing the suffix of a shortest residual path by any other
generalized path from the split vertex to the sink cannot shorten the total path. -/
private lemma shortestResidualPathSuffixReplacementNotShorter
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {a : ResidualArc A} {P₁ P₂ Q : List (ResidualArc A)}
    (hdecomp : P = P₁ ++ a :: P₂)
    (hprefix : IsResidualPathBetween tail head c x s (ResidualArc.tail tail head a) P₁)
    (hQ : IsResidualPathBetween tail head c x (ResidualArc.head tail head a) t Q) :
    P₂.length ≤ Q.length := by
  -- Turn the replacement `P₁ ++ a :: Q` into a realized `s,t`-path and invoke shortestness.
  have ha_mem : a ∈ P := by
    rw [hdecomp]
    simp
  have ha_active : IsActiveResidualArc c x a := hPshort.1.2.1 a ha_mem
  have htail :
      IsResidualPathBetween tail head c x (ResidualArc.tail tail head a) t (a :: Q) :=
    residual_path_between_cons tail head c x rfl rfl ha_active hQ
  have hreplace :
      IsResidualPathBetween tail head c x s t (P₁ ++ (a :: Q)) :=
    residualPathBetweenAppend tail head c x hprefix htail
  have hreplace_st : IsResidualSTPath tail head c x s t (P₁ ++ (a :: Q)) :=
    (is_residual_st_path_iff_residual_path_between tail head c x hst _).2 hreplace
  have hlen : P.length ≤ (P₁ ++ (a :: Q)).length := hPshort.2 _ hreplace_st
  rw [hdecomp, List.length_append, List.length_cons, List.length_append, List.length_cons] at hlen
  omega

/-- Helper for Theorem 4.17: every arc on a shortest residual `s,t`-path advances the source
distance by one and decreases the sink distance by one. -/
private lemma shortestResidualPathMemberDistanceEqualities
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {a : ResidualArc A} (ha : a ∈ P) :
    residual_distance tail head c x s (ResidualArc.head tail head a) =
        residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 ∧
      residual_distance tail head c x (ResidualArc.tail tail head a) t =
        residual_distance tail head c x (ResidualArc.head tail head a) t + 1 := by
  -- Split the chosen shortest path once, then identify the prefix and suffix lengths with the
  -- corresponding residual distances.
  have ha_active : IsActiveResidualArc c x a := hPshort.1.2.1 a ha
  have htriangle := residualDistanceTriangleOfActiveArc tail head c x s t ha_active
  rcases residualPathBetweenSplitAtMember tail head c x hPshort.1 ha with
    ⟨P₁, P₂, hdecomp, hprefix, hsuffix⟩
  have hprefix_dist_le :
      residual_distance tail head c x s (ResidualArc.tail tail head a) ≤ P₁.length :=
    residual_distance_le_length_of_path tail head c x hprefix
  rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨P₁, hprefix⟩ with
    ⟨Q₁, hQ₁, hQ₁_len, hQ₁_short⟩
  have hprefix_len_le :
      P₁.length ≤ residual_distance tail head c x s (ResidualArc.tail tail head a) := by
    have hbound :
        P₁.length ≤ Q₁.length :=
      shortestResidualPathPrefixReplacementNotShorter tail head c x hst hPshort
        hdecomp hsuffix hQ₁
    simpa [hQ₁_len] using hbound
  have hprefix_len :
      P₁.length = residual_distance tail head c x s (ResidualArc.tail tail head a) :=
    Nat.le_antisymm hprefix_len_le hprefix_dist_le
  have hsuffix_dist_le :
      residual_distance tail head c x (ResidualArc.head tail head a) t ≤ P₂.length :=
    residual_distance_le_length_of_path tail head c x hsuffix
  rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨P₂, hsuffix⟩ with
    ⟨Q₂, hQ₂, hQ₂_len, hQ₂_short⟩
  have hsuffix_len_le :
      P₂.length ≤ residual_distance tail head c x (ResidualArc.head tail head a) t := by
    have hbound :
        P₂.length ≤ Q₂.length :=
      shortestResidualPathSuffixReplacementNotShorter tail head c x hst hPshort
        hdecomp hprefix hQ₂
    simpa [hQ₂_len] using hbound
  have hsuffix_len :
      P₂.length = residual_distance tail head c x (ResidualArc.head tail head a) t :=
    Nat.le_antisymm hsuffix_len_le hsuffix_dist_le
  have hst_len :
      residual_distance tail head c x s t = P.length :=
    shortestResidualPathLengthEqResidualDistance tail head c x hst hPshort
  have htotal :
      residual_distance tail head c x s t =
        residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
          residual_distance tail head c x (ResidualArc.head tail head a) t := by
    calc
      residual_distance tail head c x s t = P.length := hst_len
      _ = (P₁ ++ a :: P₂).length := by rw [hdecomp]
      _ = P₁.length + 1 + P₂.length := by
        simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ =
          residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
            residual_distance tail head c x (ResidualArc.head tail head a) t := by
        rw [hprefix_len, hsuffix_len]
  have hsource_concat :
      residual_distance tail head c x s t ≤
        residual_distance tail head c x s (ResidualArc.head tail head a) +
          residual_distance tail head c x (ResidualArc.head tail head a) t := by
    -- Realize a shortest path from `s` to the arc head and append the fixed suffix.
    have hhead_between :
        IsResidualPathBetween tail head c x s (ResidualArc.head tail head a) (P₁ ++ [a]) :=
      residualPathBetweenSnoc tail head c x rfl rfl ha_active hprefix
    rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨P₁ ++ [a], hhead_between⟩ with
      ⟨Q, hQ, hQ_len, _⟩
    have happend :
        IsResidualPathBetween tail head c x s t (Q ++ P₂) :=
      residualPathBetweenAppend tail head c x hQ hsuffix
    have hbound :
        residual_distance tail head c x s t ≤ (Q ++ P₂).length :=
      residual_distance_le_length_of_path tail head c x happend
    rw [List.length_append, hQ_len, hsuffix_len] at hbound
    exact hbound
  have hsource_total_le :
      residual_distance tail head c x s (ResidualArc.head tail head a) +
          residual_distance tail head c x (ResidualArc.head tail head a) t ≤
        residual_distance tail head c x s t := by
    -- The active-arc triangle inequality gives the reverse bound after adding the sink suffix.
    calc
      residual_distance tail head c x s (ResidualArc.head tail head a) +
          residual_distance tail head c x (ResidualArc.head tail head a) t
          ≤
            (residual_distance tail head c x s (ResidualArc.tail tail head a) + 1) +
              residual_distance tail head c x (ResidualArc.head tail head a) t := by
        exact Nat.add_le_add_right htriangle.1 _
      _ = residual_distance tail head c x s t := by
        simpa [Nat.add_assoc] using htotal.symm
  have hsource_eq_sum :
      residual_distance tail head c x s (ResidualArc.head tail head a) +
          residual_distance tail head c x (ResidualArc.head tail head a) t =
        residual_distance tail head c x s t :=
    Nat.le_antisymm hsource_total_le hsource_concat
  have hsource_eq :
      residual_distance tail head c x s (ResidualArc.head tail head a) =
        residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 := by
    apply Nat.add_right_cancel
    calc
      residual_distance tail head c x s (ResidualArc.head tail head a) +
          residual_distance tail head c x (ResidualArc.head tail head a) t
          = residual_distance tail head c x s t := hsource_eq_sum
      _ =
          residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
            residual_distance tail head c x (ResidualArc.head tail head a) t := htotal
  have hsink_concat :
      residual_distance tail head c x s t ≤
        residual_distance tail head c x s (ResidualArc.tail tail head a) +
          residual_distance tail head c x (ResidualArc.tail tail head a) t := by
    -- Realize a shortest path from the arc tail to `t` and append it to the fixed prefix.
    have htail_between :
        IsResidualPathBetween tail head c x (ResidualArc.tail tail head a) t (a :: P₂) :=
      residual_path_between_cons tail head c x rfl rfl ha_active hsuffix
    rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨a :: P₂, htail_between⟩ with
      ⟨Q, hQ, hQ_len, _⟩
    have happend :
        IsResidualPathBetween tail head c x s t (P₁ ++ Q) :=
      residualPathBetweenAppend tail head c x hprefix hQ
    have hbound :
        residual_distance tail head c x s t ≤ (P₁ ++ Q).length :=
      residual_distance_le_length_of_path tail head c x happend
    rw [List.length_append, hprefix_len, hQ_len] at hbound
    exact hbound
  have hsink_eq :
      residual_distance tail head c x (ResidualArc.tail tail head a) t =
        residual_distance tail head c x (ResidualArc.head tail head a) t + 1 := by
    have hsink_lower :
        residual_distance tail head c x (ResidualArc.head tail head a) t + 1 ≤
          residual_distance tail head c x (ResidualArc.tail tail head a) t := by
      have hcalc :
          residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
              residual_distance tail head c x (ResidualArc.head tail head a) t ≤
            residual_distance tail head c x s (ResidualArc.tail tail head a) +
              residual_distance tail head c x (ResidualArc.tail tail head a) t := by
        calc
          residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
              residual_distance tail head c x (ResidualArc.head tail head a) t
              = residual_distance tail head c x s t := htotal.symm
          _ ≤
              residual_distance tail head c x s (ResidualArc.tail tail head a) +
                residual_distance tail head c x (ResidualArc.tail tail head a) t := hsink_concat
      omega
    exact Nat.le_antisymm htriangle.2 hsink_lower
  exact ⟨hsource_eq, hsink_eq⟩

end

/-- Helper for Theorem 4.17: every arc on a shortest residual `s,t`-path splits the total
residual distance into its source-side prefix length, one traversed arc, and its sink-side
suffix length. -/
private lemma shortestResidualPathMemberTotalEquality
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {a : ResidualArc A} (ha : a ∈ P) :
    residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
        residual_distance tail head c x (ResidualArc.head tail head a) t =
      residual_distance tail head c x s t := by
  -- Split the shortest path at `a`, identify the prefix and suffix lengths with distances, and
  -- then rewrite the total path length through that decomposition.
  rcases residualPathBetweenSplitAtMember tail head c x hPshort.1 ha with
    ⟨P₁, P₂, hdecomp, hprefix, hsuffix⟩
  have hprefix_dist_le :
      residual_distance tail head c x s (ResidualArc.tail tail head a) ≤ P₁.length :=
    residual_distance_le_length_of_path tail head c x hprefix
  rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨P₁, hprefix⟩ with
    ⟨Q₁, hQ₁, hQ₁_len, _⟩
  have hprefix_len_le :
      P₁.length ≤ residual_distance tail head c x s (ResidualArc.tail tail head a) := by
    have hbound :
        P₁.length ≤ Q₁.length :=
      shortestResidualPathPrefixReplacementNotShorter tail head c x hst hPshort
        hdecomp hsuffix hQ₁
    simpa [hQ₁_len] using hbound
  have hprefix_len :
      P₁.length = residual_distance tail head c x s (ResidualArc.tail tail head a) :=
    Nat.le_antisymm hprefix_len_le hprefix_dist_le
  have hsuffix_dist_le :
      residual_distance tail head c x (ResidualArc.head tail head a) t ≤ P₂.length :=
    residual_distance_le_length_of_path tail head c x hsuffix
  rcases existsPathBetweenRealizingResidualDistance tail head c x ⟨P₂, hsuffix⟩ with
    ⟨Q₂, hQ₂, hQ₂_len, _⟩
  have hsuffix_len_le :
      P₂.length ≤ residual_distance tail head c x (ResidualArc.head tail head a) t := by
    have hbound :
        P₂.length ≤ Q₂.length :=
      shortestResidualPathSuffixReplacementNotShorter tail head c x hst hPshort
        hdecomp hprefix hQ₂
    simpa [hQ₂_len] using hbound
  have hsuffix_len :
      P₂.length = residual_distance tail head c x (ResidualArc.head tail head a) t :=
    Nat.le_antisymm hsuffix_len_le hsuffix_dist_le
  have hst_len :
      residual_distance tail head c x s t = P.length :=
    shortestResidualPathLengthEqResidualDistance tail head c x hst hPshort
  calc
    residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
        residual_distance tail head c x (ResidualArc.head tail head a) t
        = P₁.length + 1 + P₂.length := by
      rw [hprefix_len, hsuffix_len]
    _ = (P₁ ++ a :: P₂).length := by
      simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = P.length := by rw [hdecomp]
    _ = residual_distance tail head c x s t := hst_len.symm

/-- Helper for Theorem 4.17: every arc on a shortest residual `s,t`-path is relevant in the
source-proof rank decomposition. -/
private lemma memShortestResidualPathIsRelevant
    (tail head : A → V) (c : A → ℝ) {s t : V} (x : A → ℝ) (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {a : ResidualArc A} (ha : a ∈ P) :
    IsRelevantResidualArc tail head c s t x a := by
  -- The path membership gives activity, and the split-at-member identity gives the relevance
  -- equality used by `relevant_edge_count`.
  refine ⟨hPshort.1.2.1 a ha, ?_⟩
  exact shortestResidualPathMemberTotalEquality tail head c x hst hPshort ha

/-- Helper for Theorem 4.17: a positive forward-use count recovers a concrete forward traversal
of the same original edge on the augmenting path. -/
private lemma existsForwardResidualUseOfCountPos
    {P : List (ResidualArc A)} {e : A}
    (hcount : 0 < residual_forward_use_count P e) :
    ∃ a ∈ P, a.edge = e ∧ a.orientation = .forward := by
  -- Convert the list count to the multiset positivity criterion to recover a path witness.
  have hcount' :
      0 < Multiset.countP (fun a : ResidualArc A ↦ a.edge = e ∧ a.orientation = .forward)
        (P : Multiset (ResidualArc A)) := by
    simpa [residual_forward_use_count] using hcount
  rcases Multiset.countP_pos.mp hcount' with ⟨a, haP, hae, haori⟩
  exact ⟨a, by simpa using haP, hae, haori⟩

/-- Helper for Theorem 4.17: a positive backward-use count recovers a concrete backward traversal
of the same original edge on the augmenting path. -/
private lemma existsBackwardResidualUseOfCountPos
    {P : List (ResidualArc A)} {e : A}
    (hcount : 0 < residual_backward_use_count P e) :
    ∃ a ∈ P, a.edge = e ∧ a.orientation = .backward := by
  -- Convert the list count to the multiset positivity criterion to recover a path witness.
  have hcount' :
      0 < Multiset.countP (fun a : ResidualArc A ↦ a.edge = e ∧ a.orientation = .backward)
        (P : Multiset (ResidualArc A)) := by
    simpa [residual_backward_use_count] using hcount
  rcases Multiset.countP_pos.mp hcount' with ⟨a, haP, hae, haori⟩
  exact ⟨a, by simpa using haP, hae, haori⟩

omit [Fintype V] in
/-- Helper for Theorem 4.17: if a residual arc is active after a shortest augmenting-path step
but was inactive before, then it is the reverse traversal of an original edge used on the chosen
shortest augmenting path. -/
private lemma newActiveResidualArcReversesPathArc
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    {a : ResidualArc A}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (ha' : IsActiveResidualArc c x' a)
    (ha_old : ¬ IsActiveResidualArc c x a) :
    ∃ P : List (ResidualArc A),
      IsShortestResidualSTPath tail head c x s t P ∧
        ∃ b ∈ P,
          b.edge = a.edge ∧
            ResidualArc.tail tail head b = ResidualArc.head tail head a ∧
            ResidualArc.head tail head b = ResidualArc.tail tail head a := by
  -- Route correction: isolate the `augment_flow` arithmetic at the underlying-edge count level,
  -- then recover the reversing path arc from forward/backward count positivity.
  rcases hstep with ⟨hx, hx', ε, P, hPshort, hε_le, hε_hit, rfl⟩
  have hε_pos : 0 < ε := by
    rcases hε_hit with ⟨b, hbP, hbcap⟩
    have hb_active : IsActiveResidualArc c x b := hPshort.1.2.1 b hbP
    rw [IsActiveResidualArc, hbcap] at hb_active
    exact hb_active
  refine ⟨P, hPshort, ?_⟩
  cases hori : a.orientation with
  | forward =>
      -- A newly active forward residual arc forces a net negative use-count gap, hence some
      -- backward traversal of the same original edge on the augmenting path.
      have hold_not : ¬ 0 < c a.edge - x a.edge := by
        simpa [IsActiveResidualArc, residual_arc_capacity, hori] using ha_old
      have hslack_nonneg : 0 ≤ c a.edge - x a.edge := sub_nonneg.mpr (hx.le_capacity a.edge)
      have hslack_zero : c a.edge - x a.edge = 0 := by
        linarith
      have hnew :
          0 <
            c a.edge -
              (x a.edge +
                ε * (((residual_forward_use_count P a.edge : ℕ) : ℝ) -
                  residual_backward_use_count P a.edge)) := by
        simpa [IsActiveResidualArc, residual_arc_capacity, augment_flow, hori] using ha'
      have hmul_neg :
          ε * (((residual_forward_use_count P a.edge : ℕ) : ℝ) -
              residual_backward_use_count P a.edge) < 0 := by
        linarith [hnew, hslack_zero]
      have hcount_gap :
          ((residual_forward_use_count P a.edge : ℕ) : ℝ) <
            residual_backward_use_count P a.edge := by
        have hdiff_neg :
            (((residual_forward_use_count P a.edge : ℕ) : ℝ) -
                residual_backward_use_count P a.edge) < 0 :=
          by nlinarith [hε_pos, hmul_neg]
        linarith
      have hbackward_ne_zero : residual_backward_use_count P a.edge ≠ 0 := by
        intro hzero
        have hzero_real :
            ((residual_backward_use_count P a.edge : ℕ) : ℝ) = 0 := by
          exact_mod_cast hzero
        have hforward_nonneg :
            0 ≤ ((residual_forward_use_count P a.edge : ℕ) : ℝ) := by
          positivity
        linarith
      have hbackward_pos : 0 < residual_backward_use_count P a.edge :=
        Nat.pos_of_ne_zero hbackward_ne_zero
      rcases existsBackwardResidualUseOfCountPos hbackward_pos with ⟨b, hbP, hbe, hbori⟩
      refine ⟨b, hbP, hbe, ?_, ?_⟩
      · simpa [ResidualArc.tail, ResidualArc.head, hori, hbori, hbe]
      · simpa [ResidualArc.tail, ResidualArc.head, hori, hbori, hbe]
  | backward =>
      -- A newly active backward residual arc forces a net positive use-count gap, hence some
      -- forward traversal of the same original edge on the augmenting path.
      have hold_not : ¬ 0 < x a.edge := by
        simpa [IsActiveResidualArc, residual_arc_capacity, hori] using ha_old
      have hflow_nonneg : 0 ≤ x a.edge := hx.nonneg a.edge
      have hflow_zero : x a.edge = 0 := by
        linarith
      have hnew :
          0 <
            x a.edge +
              ε * (((residual_forward_use_count P a.edge : ℕ) : ℝ) -
                residual_backward_use_count P a.edge) := by
        simpa [IsActiveResidualArc, residual_arc_capacity, augment_flow, hori] using ha'
      have hmul_pos :
          0 <
            ε * (((residual_forward_use_count P a.edge : ℕ) : ℝ) -
              residual_backward_use_count P a.edge) := by
        linarith [hnew, hflow_zero]
      have hcount_gap :
          ((residual_backward_use_count P a.edge : ℕ) : ℝ) <
            residual_forward_use_count P a.edge := by
        have hdiff_pos :
            0 <
              (((residual_forward_use_count P a.edge : ℕ) : ℝ) -
                residual_backward_use_count P a.edge) :=
          by nlinarith [hε_pos, hmul_pos]
        linarith
      have hforward_ne_zero : residual_forward_use_count P a.edge ≠ 0 := by
        intro hzero
        have hzero_real :
            ((residual_forward_use_count P a.edge : ℕ) : ℝ) = 0 := by
          exact_mod_cast hzero
        have hbackward_nonneg :
            0 ≤ ((residual_backward_use_count P a.edge : ℕ) : ℝ) := by
          positivity
        linarith
      have hforward_pos : 0 < residual_forward_use_count P a.edge :=
        Nat.pos_of_ne_zero hforward_ne_zero
      rcases existsForwardResidualUseOfCountPos hforward_pos with ⟨b, hbP, hbe, hbori⟩
      refine ⟨b, hbP, hbe, ?_, ?_⟩
      · simpa [ResidualArc.tail, ResidualArc.head, hori, hbori, hbe]
      · simpa [ResidualArc.tail, ResidualArc.head, hori, hbori, hbe]

/-- Helper for Theorem 4.17: every residual arc that is active after a shortest augmenting-path
step still satisfies the old source-distance triangle inequality in the pre-augmentation
residual graph. -/
private lemma oldLabelTriangleOfStepArc
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hst : s ≠ t) {a : ResidualArc A}
    (ha' : IsActiveResidualArc c x' a) :
    residual_distance tail head c x s (ResidualArc.head tail head a) ≤
        residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 := by
  -- Route correction: instead of reopening `augment_flow`, move any genuinely new `x'`-arc
  -- back to the reversed old shortest-path arc and read off the old labels there.
  by_cases ha_old : IsActiveResidualArc c x a
  · exact (residualDistanceTriangleOfActiveArc tail head c x s t ha_old).1
  · rcases newActiveResidualArcReversesPathArc tail head c hstep ha' ha_old with
      ⟨P, hPshort, b, hbP, _, hbtail, hbhead⟩
    have hb_labels :=
      shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort hbP
    have hreverse :
        residual_distance tail head c x s (ResidualArc.tail tail head a) =
          residual_distance tail head c x s (ResidualArc.head tail head a) + 1 := by
      simpa [hbtail, hbhead] using hb_labels.1
    omega

/-- Helper for Theorem 4.17: if the old source-distance to the start of a realized `x'`-path is
bounded by `n`, then the old source-distance to its end is bounded by `n` plus the path length. -/
private lemma oldSourceDistanceLeOfStepPath
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hst : s ≠ t) {u v : V} {n : ℕ} {P : List (ResidualArc A)}
    (hu : residual_distance tail head c x s u ≤ n)
    (hP : IsResidualPathBetween tail head c x' u v P) :
    residual_distance tail head c x s v ≤ n + P.length := by
  -- Induct along the realized `x'`-path while transporting each active arc back to an old
  -- source-label triangle inequality.
  induction P generalizing u n with
  | nil =>
      rcases hP with ⟨hPnil, huv⟩ | hPst
      · simpa [hPnil, huv] using hu
      · exact False.elim (hPst.1 rfl)
  | cons a P ih =>
      rcases hP with hnil | hPst
      · rcases hnil with ⟨hcons, _⟩
        simp at hcons
      · rcases hPst with ⟨_, hP_active, hP_head, hP_last, hP_chain⟩
        have ha_tail : ResidualArc.tail tail head a = u := by
          have htail_some : some (ResidualArc.tail tail head a) = some u := by
            simpa using hP_head
          exact Option.some.inj htail_some
        have ha_bound :
            residual_distance tail head c x s (ResidualArc.head tail head a) ≤ n + 1 := by
          -- Push the current old source-label bound across the first `x'`-active arc.
          calc
            residual_distance tail head c x s (ResidualArc.head tail head a)
                ≤ residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 :=
              oldLabelTriangleOfStepArc tail head c hstep hst (a := a)
                (hP_active a (by simp))
            _ = residual_distance tail head c x s u + 1 := by rw [ha_tail]
            _ ≤ n + 1 := Nat.add_le_add_right hu 1
        cases P with
        | nil =>
            have hv : v = ResidualArc.head tail head a := by
              have hhead_some : some (ResidualArc.head tail head a) = some v := by
                simpa using hP_last
              exact (Option.some.inj hhead_some).symm
            subst hv
            simpa using ha_bound
        | cons b Q =>
            have hchain' := hP_chain
            rw [List.isChain_cons_cons] at hchain'
            have hsuffix :
                IsResidualPathBetween tail head c x' (ResidualArc.head tail head a) v (b :: Q) := by
              refine Or.inr ?_
              refine ⟨by simp, ?_, ?_, ?_, hchain'.2⟩
              · intro z hz
                exact hP_active z (by simp [hz])
              · simpa [hchain'.1]
              · simpa using hP_last
            have hrec :=
              ih (u := ResidualArc.head tail head a) (n := n + 1) ha_bound hsuffix
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec

/-- Helper for Theorem 4.17: a shortest augmenting-path step cannot decrease any residual
distance measured from the fixed source `s`. -/
private lemma residualSourceDistanceMonotoneOfShortestAugmentingStep
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hst : s ≠ t) (v : V) :
    residual_distance tail head c x s v ≤ residual_distance tail head c x' s v := by
  -- Realize a shortest generalized `x'`-path when one exists; otherwise `x'` already takes the
  -- default value `|V|`, which dominates every old residual distance.
  by_cases hpath : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x' s v P
  · rcases existsPathBetweenRealizingResidualDistance tail head c x' hpath with
      ⟨P, hP, hP_len, _⟩
    have hs_self : residual_distance tail head c x s s ≤ 0 := by
      rw [residualDistanceSelf tail head c x s]
    have hbound :=
      oldSourceDistanceLeOfStepPath tail head c hstep hst (u := s) (n := 0) hs_self hP
    simpa [Nat.zero_add, hP_len] using hbound
  · rw [residual_distance_eq_card_of_no_path tail head c x' s v hpath]
    exact residualDistanceLeCardVertices tail head c x s v

/-- Helper for Theorem 4.17: every residual arc that is active after a shortest augmenting-path
step still satisfies the old sink-distance triangle inequality in the pre-augmentation
residual graph. -/
private lemma oldSinkTriangleOfStepArc
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hst : s ≠ t) {a : ResidualArc A}
    (ha' : IsActiveResidualArc c x' a) :
    residual_distance tail head c x (ResidualArc.tail tail head a) t ≤
      residual_distance tail head c x (ResidualArc.head tail head a) t + 1 := by
  -- Route correction: mirror the source-side transport, but now read the reversed shortest-path
  -- member equalities on the old sink labels.
  by_cases ha_old : IsActiveResidualArc c x a
  · exact (residualDistanceTriangleOfActiveArc tail head c x s t ha_old).2
  · rcases newActiveResidualArcReversesPathArc tail head c hstep ha' ha_old with
      ⟨P, hPshort, b, hbP, _, hbtail, hbhead⟩
    have hb_labels :=
      shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort hbP
    have hreverse :
        residual_distance tail head c x (ResidualArc.head tail head a) t =
          residual_distance tail head c x (ResidualArc.tail tail head a) t + 1 := by
      simpa [hbtail, hbhead] using hb_labels.2
    omega

/-- Helper for Theorem 4.17: if the old sink-distance from the end of a realized `x'`-path is
bounded by `n`, then the old sink-distance from its start is bounded by the path length plus `n`.
-/
private lemma oldSinkDistanceLeOfStepPath
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hst : s ≠ t) {u v : V} {n : ℕ} {P : List (ResidualArc A)}
    (hv : residual_distance tail head c x v t ≤ n)
    (hP : IsResidualPathBetween tail head c x' u v P) :
    residual_distance tail head c x u t ≤ P.length + n := by
  -- Induct along the realized `x'`-path while transporting each active arc back to an old
  -- sink-label triangle inequality.
  induction P generalizing u n with
  | nil =>
      rcases hP with ⟨hPnil, huv⟩ | hPst
      · simpa [hPnil, huv] using hv
      · exact False.elim (hPst.1 rfl)
  | cons a P ih =>
      rcases hP with hnil | hPst
      · rcases hnil with ⟨hcons, _⟩
        simp at hcons
      · rcases hPst with ⟨_, hP_active, hP_head, hP_last, hP_chain⟩
        have ha_tail : ResidualArc.tail tail head a = u := by
          have htail_some : some (ResidualArc.tail tail head a) = some u := by
            simpa using hP_head
          exact Option.some.inj htail_some
        cases P with
        | nil =>
            have hv_eq : v = ResidualArc.head tail head a := by
              have hhead_some : some (ResidualArc.head tail head a) = some v := by
                simpa using hP_last
              exact (Option.some.inj hhead_some).symm
            subst hv_eq
            calc
              residual_distance tail head c x u t
                  = residual_distance tail head c x (ResidualArc.tail tail head a) t := by
                    rw [ha_tail]
              _ ≤ residual_distance tail head c x (ResidualArc.head tail head a) t + 1 :=
                oldSinkTriangleOfStepArc tail head c hstep hst
                  (a := a) (hP_active a (by simp))
              _ ≤ n + 1 := Nat.add_le_add_right hv 1
              _ = [a].length + n := by simp [Nat.add_comm]
        | cons b Q =>
            have hchain' := hP_chain
            rw [List.isChain_cons_cons] at hchain'
            have hsuffix :
                IsResidualPathBetween tail head c x' (ResidualArc.head tail head a) v (b :: Q) := by
              refine Or.inr ?_
              refine ⟨by simp, ?_, ?_, ?_, hchain'.2⟩
              · intro z hz
                exact hP_active z (by simp [hz])
              · simpa [hchain'.1]
              · simpa using hP_last
            have hrec :=
              ih (u := ResidualArc.head tail head a) (n := n) hv hsuffix
            calc
              residual_distance tail head c x u t
                  = residual_distance tail head c x (ResidualArc.tail tail head a) t := by
                    rw [ha_tail]
              _ ≤ residual_distance tail head c x (ResidualArc.head tail head a) t + 1 :=
                oldSinkTriangleOfStepArc tail head c hstep hst
                  (a := a) (hP_active a (by simp))
              _ ≤ (b :: Q).length + n + 1 := Nat.add_le_add_right hrec 1
              _ = (a :: b :: Q).length + n := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Theorem 4.17: a shortest augmenting-path step cannot decrease any residual
distance measured to the fixed sink `t`. -/
private lemma residualSinkDistanceMonotoneOfShortestAugmentingStep
    (tail head : A → V) {s t : V} (c : A → ℝ) {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hst : s ≠ t) (v : V) :
    residual_distance tail head c x v t ≤ residual_distance tail head c x' v t := by
  -- Realize a shortest generalized `x'`-path to the sink when one exists; otherwise `x'`
  -- already takes the default value `|V|`, which dominates every old residual distance.
  by_cases hpath : ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x' v t P
  · rcases existsPathBetweenRealizingResidualDistance tail head c x' hpath with
      ⟨P, hP, hP_len, _⟩
    have ht_self : residual_distance tail head c x t t ≤ 0 := by
      rw [residualDistanceSelf tail head c x t]
    have hbound :=
      oldSinkDistanceLeOfStepPath tail head c hstep hst
        (u := v) (v := t) (n := 0) ht_self hP
    simpa [Nat.add_comm, Nat.zero_add, hP_len] using hbound
  · rw [residual_distance_eq_card_of_no_path tail head c x' v t hpath]
    exact residualDistanceLeCardVertices tail head c x v t

/-- Helper for Theorem 4.17: under equal total residual distance, every `x'`-relevant oriented
residual arc is already relevant in the old residual graph with the same orientation. -/
private lemma relevantResidualArcOfEqualDistanceAfterStep
    (tail head : A → V) {s t : V} (c : A → ℝ) (hst : s ≠ t)
    {x x' : A → ℝ} {a : ResidualArc A}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hEq : residual_distance tail head c x' s t = residual_distance tail head c x s t)
    (ha : IsRelevantResidualArc tail head c s t x' a) :
    IsRelevantResidualArc tail head c s t x a := by
  rcases ha with ⟨ha_active, ha_total⟩
  have hsource_mon :
      residual_distance tail head c x s (ResidualArc.tail tail head a) ≤
        residual_distance tail head c x' s (ResidualArc.tail tail head a) :=
    residualSourceDistanceMonotoneOfShortestAugmentingStep tail head c hstep hst
      (ResidualArc.tail tail head a)
  have hsink_mon :
      residual_distance tail head c x (ResidualArc.head tail head a) t ≤
        residual_distance tail head c x' (ResidualArc.head tail head a) t :=
    residualSinkDistanceMonotoneOfShortestAugmentingStep tail head c hstep hst
      (ResidualArc.head tail head a)
  have hold_upper :
      residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
          residual_distance tail head c x (ResidualArc.head tail head a) t ≤
        residual_distance tail head c x s t := by
    -- Compare the old and new labels on the same oriented arc, then rewrite the new total
    -- distance back to the old one through the equal-distance hypothesis.
    calc
      residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
            residual_distance tail head c x (ResidualArc.head tail head a) t
          ≤
            residual_distance tail head c x' s (ResidualArc.tail tail head a) + 1 +
              residual_distance tail head c x (ResidualArc.head tail head a) t := by
        exact Nat.add_le_add_right (Nat.add_le_add_right hsource_mon 1) _
      _ ≤
            residual_distance tail head c x' s (ResidualArc.tail tail head a) + 1 +
              residual_distance tail head c x' (ResidualArc.head tail head a) t := by
        exact Nat.add_le_add_left hsink_mon _
      _ = residual_distance tail head c x' s t := ha_total
      _ = residual_distance tail head c x s t := hEq
  by_cases ha_old : IsActiveResidualArc c x a
  · have htriangle := residualDistanceTriangleOfActiveArc tail head c x s t ha_old
    have hold_lower :
        residual_distance tail head c x s t ≤
          residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
            residual_distance tail head c x (ResidualArc.head tail head a) t := by
      -- Route correction: keep the old-active branch at the old-label level and recover the
      -- required lower bound by routing through the arc tail, then using the sink triangle.
      calc
        residual_distance tail head c x s t
            ≤
              residual_distance tail head c x s (ResidualArc.tail tail head a) +
                residual_distance tail head c x (ResidualArc.tail tail head a) t :=
          residualDistanceLeAddOfIntermediate tail head c x s
            (ResidualArc.tail tail head a) t
        _ ≤
              residual_distance tail head c x s (ResidualArc.tail tail head a) +
                (residual_distance tail head c x (ResidualArc.head tail head a) t + 1) := by
          exact Nat.add_le_add_left htriangle.2 _
        _ = residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 +
              residual_distance tail head c x (ResidualArc.head tail head a) t := by
          omega
    exact ⟨ha_old, Nat.le_antisymm hold_upper hold_lower⟩
  · rcases newActiveResidualArcReversesPathArc tail head c hstep ha_active ha_old with
      ⟨P, hPshort, b, hbP, _, hbtail, hbhead⟩
    have hb_total :=
      shortestResidualPathMemberTotalEquality tail head c x hst hPshort hbP
    have hb_labels :=
      shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort hbP
    have hreverse_source :
        residual_distance tail head c x s (ResidualArc.tail tail head a) =
          residual_distance tail head c x s (ResidualArc.head tail head a) + 1 := by
      simpa [hbtail, hbhead] using hb_labels.1
    have hreverse_sink :
        residual_distance tail head c x (ResidualArc.head tail head a) t =
          residual_distance tail head c x (ResidualArc.tail tail head a) t + 1 := by
      simpa [hbtail, hbhead] using hb_labels.2
    have hreverse_total :
        residual_distance tail head c x s (ResidualArc.head tail head a) + 1 +
            residual_distance tail head c x (ResidualArc.tail tail head a) t =
          residual_distance tail head c x s t := by
      simpa [hbtail, hbhead] using hb_total
    -- A genuinely new `x'`-relevant arc would force an old route of length `d_x(s,t) + 2`,
    -- contradicting the transported upper bound from the equal-distance hypothesis.
    have : False := by
      omega
    exact False.elim this

/-- Helper for Theorem 4.17: a shortest residual path cannot use the opposite residual
orientation of one of its member edges elsewhere on the same path. -/
private lemma oppositeResidualUseCountZeroOfShortestPathMember
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {a : ResidualArc A} (ha : a ∈ P) :
    match a.orientation with
    | .forward => residual_backward_use_count P a.edge = 0
    | .backward => residual_forward_use_count P a.edge = 0 := by
  -- Any opposite traversal of the same underlying edge would force contradictory source-label
  -- increments on the same shortest residual path.
  cases hori : a.orientation with
  | forward =>
      by_contra hcount
      have hcount_pos : 0 < residual_backward_use_count P a.edge := Nat.pos_of_ne_zero hcount
      rcases existsBackwardResidualUseOfCountPos hcount_pos with ⟨b, hbP, hbe, hbori⟩
      have ha_labels :=
        shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort ha
      have hb_labels :=
        shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort hbP
      have hb_reverse :
          residual_distance tail head c x s (ResidualArc.tail tail head a) =
            residual_distance tail head c x s (ResidualArc.head tail head a) + 1 := by
        simpa [ResidualArc.tail, ResidualArc.head, hori, hbe, hbori] using hb_labels.1
      omega
  | backward =>
      by_contra hcount
      have hcount_pos : 0 < residual_forward_use_count P a.edge := Nat.pos_of_ne_zero hcount
      rcases existsForwardResidualUseOfCountPos hcount_pos with ⟨b, hbP, hbe, hbori⟩
      have ha_labels :=
        shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort ha
      have hb_labels :=
        shortestResidualPathMemberDistanceEqualities tail head c x hst hPshort hbP
      have hb_reverse :
          residual_distance tail head c x s (ResidualArc.tail tail head a) =
            residual_distance tail head c x s (ResidualArc.head tail head a) + 1 := by
        simpa [ResidualArc.tail, ResidualArc.head, hori, hbe, hbori] using hb_labels.1
      omega

/-- Helper for Theorem 4.17: after augmenting by the bottleneck value, that bottleneck path arc
is no longer active in its original orientation. -/
private lemma bottleneckPathArcInactiveAfterAugment
    (tail head : A → V) (c x : A → ℝ) {s t : V} (hst : s ≠ t)
    {P : List (ResidualArc A)} (hPshort : IsShortestResidualSTPath tail head c x s t P)
    {ε : ℝ} {b : ResidualArc A}
    (hbP : b ∈ P)
    (hbcap : residual_arc_capacity c x b = ε) :
    ¬ IsActiveResidualArc c (augment_flow x ε P) b := by
  have hb_active : IsActiveResidualArc c x b := hPshort.1.2.1 b hbP
  have hε_pos : 0 < ε := by
    rw [← hbcap]
    exact hb_active
  cases hori : b.orientation with
  | forward =>
      have hbcap' : c b.edge - x b.edge = ε := by
        simpa [residual_arc_capacity, hori] using hbcap
      have hfwd_pos : 0 < residual_forward_use_count P b.edge := by
        have hcount :
            0 <
              Multiset.countP (fun a : ResidualArc A ↦ a.edge = b.edge ∧ a.orientation = .forward)
                (P : Multiset (ResidualArc A)) := by
          exact Multiset.countP_pos.mpr ⟨b, by simpa using hbP, rfl, hori⟩
        simpa [residual_forward_use_count] using hcount
      have hback_zero : residual_backward_use_count P b.edge = 0 := by
        simpa [hori] using
          oppositeResidualUseCountZeroOfShortestPathMember
            tail head c x hst hPshort hbP
      intro hb_new
      have hfwd_one : (1 : ℝ) ≤ ((residual_forward_use_count P b.edge : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hfwd_pos
      have hnew :
          0 < c b.edge - (x b.edge + ε * (((residual_forward_use_count P b.edge : ℕ) : ℝ))) := by
        simpa [IsActiveResidualArc, residual_arc_capacity, augment_flow, hori, hback_zero]
          using hb_new
      have hnonpos :
          c b.edge - (x b.edge + ε * (((residual_forward_use_count P b.edge : ℕ) : ℝ))) ≤ 0 := by
        nlinarith [hbcap', hε_pos, hfwd_one]
      exact (not_lt_of_ge hnonpos) hnew
  | backward =>
      have hbcap' : x b.edge = ε := by
        simpa [residual_arc_capacity, hori] using hbcap
      have hback_pos : 0 < residual_backward_use_count P b.edge := by
        have hcount :
            0 <
              Multiset.countP (fun a : ResidualArc A ↦ a.edge = b.edge ∧ a.orientation = .backward)
                (P : Multiset (ResidualArc A)) := by
          exact Multiset.countP_pos.mpr ⟨b, by simpa using hbP, rfl, hori⟩
        simpa [residual_backward_use_count] using hcount
      have hfwd_zero : residual_forward_use_count P b.edge = 0 := by
        simpa [hori] using
          oppositeResidualUseCountZeroOfShortestPathMember
            tail head c x hst hPshort hbP
      intro hb_new
      have hback_one : (1 : ℝ) ≤ ((residual_backward_use_count P b.edge : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hback_pos
      have hnew :
          0 < x b.edge - ε * (((residual_backward_use_count P b.edge : ℕ) : ℝ)) := by
        simpa [IsActiveResidualArc, residual_arc_capacity, augment_flow, hori, hfwd_zero]
          using hb_new
      have hnonpos :
          x b.edge - ε * (((residual_backward_use_count P b.edge : ℕ) : ℝ)) ≤ 0 := by
        nlinarith [hbcap', hε_pos, hback_one]
      exact (not_lt_of_ge hnonpos) hnew

/-- Helper for Theorem 4.17: a relevant residual arc forces the source label to increase by one
along the arc and the sink label to decrease by one. -/
private lemma relevantResidualArcDistanceEqualities
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ) {a : ResidualArc A}
    (ha : IsRelevantResidualArc tail head c s t x a) :
    residual_distance tail head c x s (ResidualArc.head tail head a) =
        residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 ∧
      residual_distance tail head c x (ResidualArc.tail tail head a) t =
        residual_distance tail head c x (ResidualArc.head tail head a) t + 1 := by
  rcases ha with ⟨ha_active, ha_total⟩
  have htriangle := residualDistanceTriangleOfActiveArc tail head c x s t ha_active
  have hsource_lower :
      residual_distance tail head c x s (ResidualArc.tail tail head a) + 1 ≤
        residual_distance tail head c x s (ResidualArc.head tail head a) := by
    -- Route correction: derive the reverse source inequality from the path concatenation bound
    -- through the arc head, then combine it with the basic active-arc triangle inequality.
    have hmid :
        residual_distance tail head c x s t ≤
          residual_distance tail head c x s (ResidualArc.head tail head a) +
            residual_distance tail head c x (ResidualArc.head tail head a) t :=
      residualDistanceLeAddOfIntermediate tail head c x s
        (ResidualArc.head tail head a) t
    rw [← ha_total] at hmid
    omega
  have hsink_lower :
      residual_distance tail head c x (ResidualArc.head tail head a) t + 1 ≤
        residual_distance tail head c x (ResidualArc.tail tail head a) t := by
    -- The same concatenation argument through the arc tail gives the reverse sink inequality.
    have hmid :
        residual_distance tail head c x s t ≤
          residual_distance tail head c x s (ResidualArc.tail tail head a) +
            residual_distance tail head c x (ResidualArc.tail tail head a) t :=
      residualDistanceLeAddOfIntermediate tail head c x s
        (ResidualArc.tail tail head a) t
    rw [← ha_total] at hmid
    omega
  exact ⟨Nat.le_antisymm htriangle.1 hsource_lower, Nat.le_antisymm htriangle.2 hsink_lower⟩

/-- Helper for Theorem 4.17: one original edge cannot be relevant in both residual orientations
at the same time, because relevance forces contradictory source-label increments. -/
private lemma notBothOrientationsRelevantOnSameEdge
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ) (e : A) :
    ¬ (IsRelevantResidualArc tail head c s t x ⟨e, .forward⟩ ∧
        IsRelevantResidualArc tail head c s t x ⟨e, .backward⟩) := by
  rintro ⟨hforward, hbackward⟩
  have hforward_eq :=
    relevantResidualArcDistanceEqualities tail head c s t x hforward
  have hforward_eq' :
      residual_distance tail head c x s (head e) =
        residual_distance tail head c x s (tail e) + 1 ∧
      residual_distance tail head c x (tail e) t =
        residual_distance tail head c x (head e) t + 1 := by
    simpa [ResidualArc.tail, ResidualArc.head] using hforward_eq
  have hforward_total :
      residual_distance tail head c x s (tail e) + 1 +
          residual_distance tail head c x (head e) t =
        residual_distance tail head c x s t := by
    simpa [ResidualArc.tail, ResidualArc.head] using hforward.2
  have hbackward_total :
      residual_distance tail head c x s (head e) + 1 +
          residual_distance tail head c x (tail e) t =
        residual_distance tail head c x s t := by
    simpa [ResidualArc.tail, ResidualArc.head] using hbackward.2
  -- After simplifying both orientations to the original tail/head maps, the backward relevance
  -- equality exceeds the forward one by two.
  have hforward_source := hforward_eq'.1
  have hforward_sink := hforward_eq'.2
  omega

omit [DecidableEq A] in
/-- Helper for Theorem 4.17: if a residual `s,t`-path exists, then at least one original edge is
relevant for the source-proof rank tie-breaker. -/
private lemma relevantEdgeCountPosOfPath
    (tail head : A → V) (c : A → ℝ) {s t : V} (x : A → ℝ) (hst : s ≠ t)
    (hpath : ∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P) :
    0 < relevant_edge_count tail head c s t x := by
  classical
  -- Choose a shortest realized residual path, take one of its arcs, and count its underlying
  -- original edge in the relevance subtype.
  rcases hpath with ⟨Q, hQ⟩
  have hQ_between :
      ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x s t P := by
    exact ⟨Q, (is_residual_st_path_iff_residual_path_between tail head c x hst Q).1 hQ⟩
  rcases existsPathBetweenRealizingResidualDistance tail head c x hQ_between with
    ⟨P, hP_between, _, hP_short⟩
  have hP : IsResidualSTPath tail head c x s t P :=
    (is_residual_st_path_iff_residual_path_between tail head c x hst P).2 hP_between
  have hPshort : IsShortestResidualSTPath tail head c x s t P := by
    refine ⟨hP, ?_⟩
    intro R hR
    exact hP_short R ((is_residual_st_path_iff_residual_path_between tail head c x hst R).1 hR)
  rcases List.exists_mem_of_ne_nil (l := P) hP.1 with ⟨a, haP⟩
  have ha_rel :
      IsRelevantResidualArc tail head c s t x a :=
    memShortestResidualPathIsRelevant tail head c x hst hPshort haP
  change 0 < Fintype.card {e : A // ∃ o : ResidualArcOrientation,
    IsRelevantResidualArc tail head c s t x ⟨e, o⟩}
  refine Fintype.card_pos_iff.mpr ?_
  refine ⟨⟨a.edge, a.orientation, ?_⟩⟩
  simpa using ha_rel

section

omit [DecidableEq A] in
/-- Helper for Theorem 4.17: the residual `s,t`-distance and relevance count together keep the
rank inside the interval `[0, |V| |A|]`. -/
private lemma sap_rank_le_bound
    (tail head : A → V) (c : A → ℝ) {s t : V} (hst : s ≠ t) (x : A → ℝ) :
    sap_rank tail head c s t x ≤ Fintype.card V * Fintype.card A := by
  -- Split by reachability: the terminal branch is exact, and the reachable branch is bounded by
  -- the shortest-path distance together with the ambient edge-count cap.
  classical
  by_cases hpath : ∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P
  · have hpath_between :
        ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x s t P := by
      rcases hpath with ⟨P, hP⟩
      exact ⟨P, (is_residual_st_path_iff_residual_path_between tail head c x hst P).1 hP⟩
    rcases existsPathBetweenRealizingResidualDistance tail head c x hpath_between with
      ⟨P, hP_between, hP_len, hP_shortest⟩
    have hdist_lt : residual_distance tail head c x s t < Fintype.card V := by
      rw [← hP_len]
      exact shortest_residual_path_length_lt_card_vertices
        tail head c x hst hP_between hP_shortest
    have hcount_le : relevant_edge_count tail head c s t x ≤ Fintype.card A :=
      relevant_edge_count_le_card_edges tail head c s t x
    have hsub_le : Fintype.card A - relevant_edge_count tail head c s t x ≤ Fintype.card A :=
      Nat.sub_le _ _
    have hdist_mul :
        residual_distance tail head c x s t * Fintype.card A + Fintype.card A ≤
          Fintype.card V * Fintype.card A := by
      have hsucc_le : residual_distance tail head c x s t + 1 ≤ Fintype.card V :=
        Nat.succ_le_of_lt hdist_lt
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right (Fintype.card A) hsucc_le
    have hsap :
        sap_rank tail head c s t x =
          residual_distance tail head c x s t * Fintype.card A +
            (Fintype.card A - relevant_edge_count tail head c s t x) := by
      simp [sap_rank, hpath]
    rw [hsap]
    calc
      residual_distance tail head c x s t * Fintype.card A +
            (Fintype.card A - relevant_edge_count tail head c s t x)
          ≤ residual_distance tail head c x s t * Fintype.card A + Fintype.card A := by
        exact Nat.add_le_add_left hsub_le _
      _ ≤ Fintype.card V * Fintype.card A := hdist_mul
  · rw [sap_rank_eq_bound_of_no_residual_path tail head c s t x hpath]

end

/-- Helper for Theorem 4.17: a shortest augmentation never decreases the source-proof rank. If
the residual `s,t`-distance stays fixed, the relevant-edge count strictly drops, so the rank
strictly increases. -/
private lemma sap_rank_lt_bound_of_path
    (tail head : A → V) (c : A → ℝ) {s t : V} (hst : s ≠ t) (x : A → ℝ)
    (hpath : ∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P) :
    sap_rank tail head c s t x < Fintype.card V * Fintype.card A := by
  -- The distance coordinate stays below `|V|`, and when a path exists the relevance tie-breaker
  -- is strictly smaller than `|A|` because at least one original edge is relevant.
  classical
  have hpath_between :
      ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x s t P := by
    rcases hpath with ⟨P, hP⟩
    exact ⟨P, (is_residual_st_path_iff_residual_path_between tail head c x hst P).1 hP⟩
  rcases existsPathBetweenRealizingResidualDistance tail head c x hpath_between with
    ⟨P, hP_between, hP_len, hP_shortest⟩
  have hdist_lt : residual_distance tail head c x s t < Fintype.card V := by
    rw [← hP_len]
    exact shortest_residual_path_length_lt_card_vertices
      tail head c x hst hP_between hP_shortest
  have hcount_pos :
      0 < relevant_edge_count tail head c s t x :=
    relevantEdgeCountPosOfPath tail head c x hst hpath
  have hcount_le :
      relevant_edge_count tail head c s t x ≤ Fintype.card A :=
    relevant_edge_count_le_card_edges tail head c s t x
  have hcardA_pos : 0 < Fintype.card A :=
    lt_of_lt_of_le hcount_pos hcount_le
  have hsub_lt :
      Fintype.card A - relevant_edge_count tail head c s t x < Fintype.card A :=
    Nat.sub_lt hcardA_pos hcount_pos
  have hsap :
      sap_rank tail head c s t x =
        residual_distance tail head c x s t * Fintype.card A +
          (Fintype.card A - relevant_edge_count tail head c s t x) := by
    simp [sap_rank, hpath]
  rw [hsap]
  calc
    residual_distance tail head c x s t * Fintype.card A +
          (Fintype.card A - relevant_edge_count tail head c s t x)
        <
      residual_distance tail head c x s t * Fintype.card A + Fintype.card A := by
      exact Nat.add_lt_add_left hsub_lt _
    _ = (residual_distance tail head c x s t + 1) * Fintype.card A := by
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ ≤ Fintype.card V * Fintype.card A := by
      exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdist_lt)

/-- Helper for Theorem 4.17: when a shortest augmenting-path step leaves the `s,t` residual
distance unchanged, the original-edge relevance count must strictly drop. -/
private lemma relevantEdgeCountLtOfEqualDistanceAfterStep
    (tail head : A → V) {s t : V} (c : A → ℝ) (hst : s ≠ t)
    {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x')
    (hEq : residual_distance tail head c x' s t = residual_distance tail head c x s t) :
    relevant_edge_count tail head c s t x' <
      relevant_edge_count tail head c s t x := by
  classical
  -- Route correction: keep orientation information until the very end. First transport every new
  -- relevant oriented residual arc back to the old graph, then exclude the bottleneck edge.
  rcases hstep with ⟨hx, hx', ε, P, hPshort, hε_le, hε_hit, rfl⟩
  let R : A → Prop := fun e ↦
    ∃ o : ResidualArcOrientation,
      IsRelevantResidualArc tail head c s t x ⟨e, o⟩
  let R' : A → Prop := fun e ↦
    ∃ o : ResidualArcOrientation,
      IsRelevantResidualArc tail head c s t (augment_flow x ε P) ⟨e, o⟩
  have hstep' : IsShortestAugmentingPathStep tail head s t c x (augment_flow x ε P) := by
    exact ⟨hx, hx', ε, P, hPshort, hε_le, hε_hit, rfl⟩
  have hsubset : ∀ e : A, R' e → R e := by
    intro e he
    rcases he with ⟨o, ho⟩
    exact ⟨o, relevantResidualArcOfEqualDistanceAfterStep
      tail head c hst hstep' hEq ho⟩
  rcases hε_hit with ⟨⟨e, bo⟩, hbP, hbcap⟩
  have hb_old_rel :
      IsRelevantResidualArc tail head c s t x ⟨e, bo⟩ :=
    memShortestResidualPathIsRelevant tail head c x hst hPshort hbP
  have hb_in_R : R e := ⟨bo, hb_old_rel⟩
  have hb_same_inactive :
      ¬ IsActiveResidualArc c (augment_flow x ε P) ⟨e, bo⟩ := by
    simpa using
      bottleneckPathArcInactiveAfterAugment
        tail head c x hst hPshort (b := ⟨e, bo⟩) hbP hbcap
  have hb_not_new : ¬ R' e := by
    intro hb_new
    rcases hb_new with ⟨o, ho⟩
    have hold :
        IsRelevantResidualArc tail head c s t x ⟨e, o⟩ :=
      relevantResidualArcOfEqualDistanceAfterStep tail head c hst hstep' hEq ho
    by_cases ho_same : o = bo
    · have hactive_same :
          IsActiveResidualArc c (augment_flow x ε P) ⟨e, bo⟩ := by
        simpa [ho_same] using ho.1
      exact hb_same_inactive hactive_same
    · cases bo with
      | forward =>
          cases o with
          | forward =>
              exact False.elim (ho_same rfl)
          | backward =>
              have hb_forward :
                  IsRelevantResidualArc tail head c s t x ⟨e, .forward⟩ := hb_old_rel
              exact
                (notBothOrientationsRelevantOnSameEdge tail head c s t x e)
                  ⟨hb_forward, hold⟩
      | backward =>
          cases o with
          | forward =>
              have hb_backward :
                  IsRelevantResidualArc tail head c s t x ⟨e, .backward⟩ := hb_old_rel
              exact
                (notBothOrientationsRelevantOnSameEdge tail head c s t x e)
                  ⟨hold, hb_backward⟩
          | backward =>
              exact False.elim (ho_same rfl)
  have hcard_lt :
      Fintype.card {e : A // R' e} < Fintype.card {e : A // R e} := by
    let f : {e : A // R' e} → {e : A // R e} := fun e ↦ ⟨e.1, hsubset e.1 e.2⟩
    have hf_inj : Function.Injective f := by
      intro e₁ e₂ h
      exact Subtype.ext (congrArg (fun z : {e : A // R e} => z.1) h)
    have hf_not_surj : ¬ Function.Surjective f := by
      intro hf_surj
      rcases hf_surj ⟨e, hb_in_R⟩ with ⟨e', heq⟩
      have hval : e'.1 = e := congrArg (fun z : {e : A // R e} => z.1) heq
      exact hb_not_new (hval ▸ e'.2)
    exact Fintype.card_lt_of_injective_not_surjective f hf_inj hf_not_surj
  simpa [relevant_edge_count, R, R'] using hcard_lt

private lemma sap_rank_strict_increase_of_step
    (tail head : A → V) {s t : V} (c : A → ℝ) (hst : s ≠ t)
    {x x' : A → ℝ}
    (hstep : IsShortestAugmentingPathStep tail head s t c x x') :
    sap_rank tail head c s t x < sap_rank tail head c s t x' := by
  -- Route correction: the transport layer is now separated from the rank arithmetic. The only
  -- remaining source-proof blocker is the equal-distance strict drop in `relevant_edge_count`.
  classical
  rcases hstep with ⟨hx, hx', ε, P, hPshort, hε_le, hε_hit, rfl⟩
  have hstep' : IsShortestAugmentingPathStep tail head s t c x (augment_flow x ε P) := by
    exact ⟨hx, hx', ε, P, hPshort, hε_le, hε_hit, rfl⟩
  have hpath : ∃ Q : List (ResidualArc A), IsResidualSTPath tail head c x s t Q := ⟨P, hPshort.1⟩
  by_cases hpath' : ∃ Q : List (ResidualArc A),
      IsResidualSTPath tail head c (augment_flow x ε P) s t Q
  · have hdist_le :
        residual_distance tail head c x s t ≤
          residual_distance tail head c (augment_flow x ε P) s t :=
      residualSourceDistanceMonotoneOfShortestAugmentingStep tail head c hstep' hst t
    have hsap_old :
        sap_rank tail head c s t x =
          residual_distance tail head c x s t * Fintype.card A +
            (Fintype.card A - relevant_edge_count tail head c s t x) := by
      simp [sap_rank, hpath]
    have hsap_new :
        sap_rank tail head c s t (augment_flow x ε P) =
          residual_distance tail head c (augment_flow x ε P) s t * Fintype.card A +
            (Fintype.card A -
              relevant_edge_count tail head c s t (augment_flow x ε P)) := by
      simp [sap_rank, hpath']
    rw [hsap_old, hsap_new]
    by_cases hEq :
        residual_distance tail head c x s t =
          residual_distance tail head c (augment_flow x ε P) s t
    · have hcount_lt :
          relevant_edge_count tail head c s t (augment_flow x ε P) <
            relevant_edge_count tail head c s t x :=
        relevantEdgeCountLtOfEqualDistanceAfterStep tail head c hst hstep' hEq.symm
      have hcount_le_old :
          relevant_edge_count tail head c s t x ≤ Fintype.card A :=
        relevant_edge_count_le_card_edges tail head c s t x
      have hcount_le_new :
          relevant_edge_count tail head c s t (augment_flow x ε P) ≤ Fintype.card A :=
        relevant_edge_count_le_card_edges tail head c s t (augment_flow x ε P)
      have hsub_lt :
          Fintype.card A - relevant_edge_count tail head c s t x <
            Fintype.card A - relevant_edge_count tail head c s t (augment_flow x ε P) := by
        omega
      calc
        residual_distance tail head c x s t * Fintype.card A +
              (Fintype.card A - relevant_edge_count tail head c s t x)
            <
          residual_distance tail head c x s t * Fintype.card A +
            (Fintype.card A - relevant_edge_count tail head c s t (augment_flow x ε P)) := by
          exact Nat.add_lt_add_left hsub_lt _
        _ =
            residual_distance tail head c (augment_flow x ε P) s t * Fintype.card A +
              (Fintype.card A - relevant_edge_count tail head c s t (augment_flow x ε P)) := by
          rw [← hEq]
    · have hdist_lt :
          residual_distance tail head c x s t <
            residual_distance tail head c (augment_flow x ε P) s t := by
        exact lt_of_le_of_ne hdist_le hEq
      have hcount_pos :
          0 < relevant_edge_count tail head c s t x :=
        relevantEdgeCountPosOfPath tail head c x hst hpath
      have hcount_le :
          relevant_edge_count tail head c s t x ≤ Fintype.card A :=
        relevant_edge_count_le_card_edges tail head c s t x
      have hcardA_pos : 0 < Fintype.card A :=
        lt_of_lt_of_le hcount_pos hcount_le
      have hsub_lt :
          Fintype.card A - relevant_edge_count tail head c s t x < Fintype.card A :=
        Nat.sub_lt hcardA_pos hcount_pos
      calc
        residual_distance tail head c x s t * Fintype.card A +
              (Fintype.card A - relevant_edge_count tail head c s t x)
            <
          residual_distance tail head c x s t * Fintype.card A + Fintype.card A := by
          exact Nat.add_lt_add_left hsub_lt _
        _ = (residual_distance tail head c x s t + 1) * Fintype.card A := by
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ ≤ residual_distance tail head c (augment_flow x ε P) s t * Fintype.card A := by
          exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdist_lt)
        _ ≤
            residual_distance tail head c (augment_flow x ε P) s t * Fintype.card A +
              (Fintype.card A -
                relevant_edge_count tail head c s t (augment_flow x ε P)) := by
          exact Nat.le_add_right _ _
  · rw [sap_rank_eq_bound_of_no_residual_path tail head c s t (augment_flow x ε P) hpath']
    exact sap_rank_lt_bound_of_path tail head c hst x hpath

/-- Theorem 4.17. Given a finite digraph `D = (V, A)` encoded by its tail and head maps,
distinct nodes `s,t ∈ V`, and capacities `c_e` on the arcs, every terminating execution of the
shortest augmenting path algorithm uses at most `|V| |A|` augmentations. -/
theorem shortest_augmenting_path_algorithm_iteration_bound
    (tail head : A → V) {s t : V} (hst : s ≠ t) (c : A → ℝ)
    {xs : List (A → ℝ)}
    (hxs : IsTerminatingShortestAugmentingPathExecution tail head s t c xs) :
    xs.length - 1 ≤ Fintype.card V * Fintype.card A := by
  classical
  let bound := Fintype.card V * Fintype.card A
  rcases hxs with ⟨_, hchain, _⟩
  let f : Fin xs.length → Fin (bound + 1) := fun i ↦
    ⟨sap_rank tail head c s t (xs.get i),
      Nat.lt_succ_of_le (sap_rank_le_bound tail head c hst (xs.get i))⟩
  have hRankChain : (xs.map (fun x ↦ sap_rank tail head c s t x)).IsChain (· < ·) := by
    -- Each shortest augmenting step strictly increases the source-proof rank.
    exact List.isChain_map_of_isChain
      (fun x ↦ sap_rank tail head c s t x)
      (fun x y hxy ↦ sap_rank_strict_increase_of_step tail head c hst hxy)
      hchain
  have hRankPairwise : (xs.map (fun x ↦ sap_rank tail head c s t x)).Pairwise (· < ·) := by
    -- A chain of strict inequalities is pairwise because `<` is transitive on `ℕ`.
    simpa using (List.isChain_iff_pairwise.mp hRankChain)
  have hf_injective : Function.Injective f := by
    intro i j hij
    -- Equal bounded ranks force equal stage indices because the ranks are strictly increasing.
    rcases lt_trichotomy i j with hij_lt | rfl | hij_gt
    · exfalso
      let i' : Fin (xs.map (fun x ↦ sap_rank tail head c s t x)).length := ⟨i.1, by simpa⟩
      let j' : Fin (xs.map (fun x ↦ sap_rank tail head c s t x)).length := ⟨j.1, by simpa⟩
      have hij_lt' : i' < j' := hij_lt
      have hltRanks :
          sap_rank tail head c s t (xs.get i) < sap_rank tail head c s t (xs.get j) := by
        simpa [i', j'] using hRankPairwise.rel_get_of_lt hij_lt'
      have hEqRanks :
          sap_rank tail head c s t (xs.get i) = sap_rank tail head c s t (xs.get j) := by
        simpa [f] using congrArg Fin.val hij
      exact (Nat.ne_of_lt hltRanks) hEqRanks
    · rfl
    · exfalso
      let i' : Fin (xs.map (fun x ↦ sap_rank tail head c s t x)).length := ⟨i.1, by simpa⟩
      let j' : Fin (xs.map (fun x ↦ sap_rank tail head c s t x)).length := ⟨j.1, by simpa⟩
      have hij_gt' : j' < i' := hij_gt
      have hltRanks :
          sap_rank tail head c s t (xs.get j) < sap_rank tail head c s t (xs.get i) := by
        simpa [i', j'] using hRankPairwise.rel_get_of_lt hij_gt'
      have hEqRanks :
          sap_rank tail head c s t (xs.get j) = sap_rank tail head c s t (xs.get i) := by
        simpa [f] using congrArg Fin.val hij.symm
      exact (Nat.ne_of_lt hltRanks) hEqRanks
  have hlen : xs.length ≤ bound + 1 := by
    -- The strictly increasing rank embeds all stages into `Fin (bound + 1)`.
    simpa [bound] using (Fintype.card_le_of_injective f hf_injective)
  -- Subtracting the initial zero-flow stage converts the stage bound into the augmentation bound.
  simpa [bound, Nat.pred_eq_sub_one] using Nat.pred_le_pred hlen
