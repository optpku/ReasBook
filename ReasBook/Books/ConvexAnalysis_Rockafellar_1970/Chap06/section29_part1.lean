/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.ordinary_convex_program_core

section Chap06
section Section29

/-- Definition 6.29.1: A bifunction from `ℝ^m` to `ℝ^n` is a map assigning to each
`u ∈ ℝ^m` an extended-real-valued function on `ℝ^n`, represented in Lean as a curried
map `(Fin m → ℝ) → (Fin n → ℝ) → EReal`. -/
abbrev Bifunction (m n : ℕ) := (Fin m → ℝ) → (Fin n → ℝ) → EReal

/-- Definition 6.29.2: The graph function of a bifunction `F` is the uncurried map
on `ℝ^m × ℝ^n` sending `(u, x)` to `(F u) x`, corresponding to the function on
`ℝ^(m+n)` in the text. -/
def graphFunction {m n : ℕ} (F : Bifunction m n) : ((Fin m → ℝ) × (Fin n → ℝ)) → EReal :=
  fun ux => F ux.1 ux.2

/-- Definition 6.29.3: The `(+∞)` indicator bifunction of a set-valued map `S`
sends `x` to `0` when `x ∈ S u` and to `+∞` otherwise. -/
noncomputable def indicatorBifunction {m n : ℕ} (S : (Fin m → ℝ) → Set (Fin n → ℝ)) :
    Bifunction m n :=
  fun u x =>
    letI : Decidable (x ∈ S u) := Classical.decPred (S u) x
    if x ∈ S u then (0 : EReal) else ⊤

/-- Definition 6.29.4: A bifunction `F` from `ℝ^m` to `ℝ^n` is convex when its graph
function is convex on the ambient space `ℝ^(m+n)`, represented here by the product
`(Fin m → ℝ) × (Fin n → ℝ)`. -/
def IsConvexBifunction {m n : ℕ} (F : Bifunction m n) : Prop :=
  ∀ p q : (Fin m → ℝ) × (Fin n → ℝ), ∀ a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
      graphFunction F (a • p + b • q) ≤
        ((a : ℝ) : EReal) * graphFunction F p + ((b : ℝ) : EReal) * graphFunction F q

-- Proof sketch: specialize the convexity inequality for the graph function to the two
-- points `(u, x)` and `(u, y)`, then simplify the first coordinate using
-- `a • u + b • u = (a + b) • u = u` when `a + b = 1`.
/-- Helper for Proposition 6.29.1: convex-combining the same parameter value leaves it
fixed when the coefficients sum to `1`. -/
lemma helperForProposition_6_29_1_sameParameter_convexCombination {m : ℕ}
    (u : Fin m → ℝ) (a b : ℝ) (hab : a + b = 1) :
    a • u + b • u = u := by
  -- Compare coordinates and collapse the scalar coefficients using `a + b = 1`.
  ext i
  calc
    (a • u + b • u) i = a * u i + b * u i := by
      simp
    _ = (a + b) * u i := by
      ring
    _ = u i := by
      simp [hab]

/-- Helper for Proposition 6.29.1: convex-combining two product points with the same
parameter keeps the parameter coordinate fixed and convex-combines only the second
coordinate. -/
lemma helperForProposition_6_29_1_productPair_convexCombination {m n : ℕ}
    (u : Fin m → ℝ) (x y : Fin n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    a • (u, x) + b • (u, y) = (u, a • x + b • y) := by
  -- Rewrite the two coordinates separately; only the parameter coordinate needs work.
  ext <;> simp [helperForProposition_6_29_1_sameParameter_convexCombination, hab]

/-- Proposition 6.29.1: If a bifunction `F` is convex on `ℝ^m × ℝ^n`, then for every
fixed `u ∈ ℝ^m`, the section `x ↦ F u x` is convex on `ℝ^n`. -/
theorem proposition_29_1 {m n : ℕ} {F : Bifunction m n} (hF : IsConvexBifunction F)
    (u : Fin m → ℝ) :
    ∀ x y : Fin n → ℝ, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 →
        F u (a • x + b • y) ≤ ((a : ℝ) : EReal) * F u x + ((b : ℝ) : EReal) * F u y := by
  intro x y a b ha hb hab
  -- Specialize convexity of the graph function to the two points with parameter `u`.
  have hGraph := hF (u, x) (u, y) a b ha hb hab
  -- Rewrite the product-space convex combination into the desired section inequality.
  rw [helperForProposition_6_29_1_productPair_convexCombination u x y a b hab, graphFunction] at hGraph
  -- The right-hand side is already the target convexity bound for the section `F u`.
  simpa [graphFunction] using hGraph

/-- Definition 6.29.5: A bifunction `F` from `ℝ^m` to `ℝ^n` is closed when its graph
function has closed epigraph on the product space `ℝ^m × ℝ^n`. -/
def IsClosedBifunction {m n : ℕ} (F : Bifunction m n) : Prop :=
  IsClosed {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | graphFunction F p.1 ≤ (p.2 : EReal)}

/-- Definition 6.29.6: A bifunction `F` from `ℝ^m` to `ℝ^n` is proper when its graph
function on `ℝ^m × ℝ^n` is a proper extended-real-valued function. -/
def IsProperBifunction {m n : ℕ} (F : Bifunction m n) : Prop :=
  ProperERealFunction (graphFunction F)

/-- Definition 6.29.7: The graph domain of a bifunction `F` is the effective domain of its
graph function, equivalently the set of pairs `(u, x)` such that `F u x < +∞`. -/
def graphDomain {m n : ℕ} (F : Bifunction m n) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  erealDom (graphFunction F)

/-- Definition 6.29.8: The effective domain `dom F` of a bifunction `F` is the set of
all `u ∈ ℝ^m` for which the section `x ↦ F u x` is not identically `+∞`, equivalently,
whose effective domain is nonempty. -/
def bifunctionEffectiveDomain {m n : ℕ} (F : Bifunction m n) : Set (Fin m → ℝ) :=
  {u | Set.Nonempty (erealDom (F u))}

-- Proof sketch: rewrite `bifunctionEffectiveDomain F` using the definition of `erealDom`,
-- identify this set with the first-coordinate projection of `graphDomain F`, and then obtain
-- convexity from the convexity of the graph domain together with preservation of convexity
-- under linear projection.
/-- Helper for Proposition 6.29.2: rewrite membership in the bifunction effective domain as
existence of a finite section value. -/
lemma helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
    {m n : ℕ} {F : Bifunction m n} {u : Fin m → ℝ} :
    u ∈ bifunctionEffectiveDomain F ↔ ∃ x : Fin n → ℝ, F u x < ⊤ := by
  -- Unfold the effective-domain definitions so the witness is exactly the section point `x`.
  simp [bifunctionEffectiveDomain, erealDom, Set.Nonempty]

/-- Helper for Proposition 6.29.2: a nonnegative weighted sum of finite extended-real values is
still finite. -/
lemma helperForProposition_6_29_2_weightedSum_lt_top {a b : ℝ} {r s : EReal}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r < ⊤) (hs : s < ⊤) :
    ((a : EReal) * r + (b : EReal) * s) < ⊤ := by
  -- Replace finiteness by `≠ ⊤`, prove each weighted term is not `⊤`, and then add them.
  have hr_ne_top : r ≠ ⊤ := lt_top_iff_ne_top.mp hr
  have hs_ne_top : s ≠ ⊤ := lt_top_iff_ne_top.mp hs
  have haE : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hbE : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have har_ne_top : (a : EReal) * r ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inl haE, Or.inl (EReal.coe_ne_top _), Or.inr hr_ne_top⟩
  have hbs_ne_top : (b : EReal) * s ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hbE, Or.inl (EReal.coe_ne_top _), Or.inr hs_ne_top⟩
  exact lt_top_iff_ne_top.mpr (EReal.add_ne_top har_ne_top hbs_ne_top)

/-- Helper for Proposition 6.29.2: the graph domain of a convex bifunction is convex. -/
lemma helperForProposition_6_29_2_graphDomain_convex {m n : ℕ} {F : Bifunction m n}
    (hF : IsConvexBifunction F) :
    Convex ℝ (graphDomain F) := by
  -- Start from two graph-domain points and use convexity of the graph function to control
  -- the value at their convex combination.
  intro p hp q hq a b ha hb hab
  have hp' : graphFunction F p < ⊤ := by
    simpa [graphDomain, erealDom] using hp
  have hq' : graphFunction F q < ⊤ := by
    simpa [graphDomain, erealDom] using hq
  have hgraph : graphFunction F (a • p + b • q) ≤
      ((a : ℝ) : EReal) * graphFunction F p + ((b : ℝ) : EReal) * graphFunction F q :=
    hF p q a b ha hb hab
  have hfinite :
      ((a : ℝ) : EReal) * graphFunction F p + ((b : ℝ) : EReal) * graphFunction F q < ⊤ :=
    helperForProposition_6_29_2_weightedSum_lt_top ha hb hp' hq'
  -- The graph-domain condition is exactly finiteness of the graph function.
  show a • p + b • q ∈ graphDomain F
  simpa [graphDomain, erealDom] using lt_of_le_of_lt hgraph hfinite

/-- Proposition 6.29.2: For a convex bifunction `F`, the effective domain is
`{u | ∃ x, F u x < +∞}`, equivalently the first-coordinate projection of `graphDomain F`;
in particular, `dom F` is convex. -/
theorem proposition_29_2 {m n : ℕ} {F : Bifunction m n} (hF : IsConvexBifunction F) :
    bifunctionEffectiveDomain F = {u | ∃ x, F u x < ⊤} ∧
    bifunctionEffectiveDomain F = Prod.fst '' graphDomain F ∧
    Convex ℝ (bifunctionEffectiveDomain F) := by
  have hdom : bifunctionEffectiveDomain F = {u | ∃ x, F u x < ⊤} := by
    -- Rewrite the domain membership predicate into the textbook existential form.
    ext u
    simp [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue]
  have hproj : bifunctionEffectiveDomain F = Prod.fst '' graphDomain F := by
    -- Unpack the image witness in each direction and translate graph-domain membership.
    ext u
    constructor
    · intro hu
      rw [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue] at hu
      rcases hu with ⟨x, hx⟩
      have hux : (u, x) ∈ graphDomain F := by
        simpa [graphDomain, erealDom, graphFunction] using hx
      exact ⟨(u, x), hux, rfl⟩
    · intro hu
      rcases hu with ⟨ux, hux, rfl⟩
      refine ⟨ux.2, ?_⟩
      simpa [graphDomain, erealDom, graphFunction] using hux
  have hGraphConv : Convex ℝ (graphDomain F) :=
    helperForProposition_6_29_2_graphDomain_convex hF
  have hProjConv : Convex ℝ (Prod.fst '' graphDomain F) := by
    -- Project the convex graph domain along the first-coordinate linear map.
    simpa using hGraphConv.linear_image (LinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))
  have hDomConv : Convex ℝ (bifunctionEffectiveDomain F) := by
    -- Replace the projection set by `dom F` using the previously established equality.
    simpa [hproj] using hProjConv
  exact ⟨hdom, hproj, hDomConv⟩

-- Proof sketch: unfold `bifunctionEffectiveDomain F` and `ProperConvexERealFunction`, use
-- properness of the graph function to show that `u ∈ dom F` is equivalent to the section
-- `F u` being proper, and apply Proposition 6.29.1 together with the standing convexity
-- assumption on `F` to obtain convexity of each section.
/-- Helper for Proposition 6.29.3: properness of the graph function rules out `⊥` at every
section value. -/
lemma helperForProposition_6_29_3_section_ne_bot_of_properBifunction
    {m n : ℕ} {F : Bifunction m n} (hFproper : IsProperBifunction F) :
    ∀ u x, F u x ≠ ⊥ := by
  intro u x
  -- Evaluate the global `≠ ⊥` statement of the graph function at the pair `(u, x)`.
  have hgraph_ne_bot : graphFunction F (u, x) ≠ ⊥ := hFproper.1 (u, x)
  -- Simplifying `graphFunction` turns this into the desired sectionwise statement.
  simpa [graphFunction] using hgraph_ne_bot

/-- Helper for Proposition 6.29.3: a parameter in `dom F` has a proper section because some
section value is finite and global properness excludes `⊥`. -/
lemma helperForProposition_6_29_3_section_proper_of_mem_dom
    {m n : ℕ} {F : Bifunction m n} (hFproper : IsProperBifunction F) {u : Fin m → ℝ} :
    u ∈ bifunctionEffectiveDomain F → ProperERealFunction (F u) := by
  intro hu
  -- Rewrite `u ∈ dom F` as existence of a section point where `F u` is finite.
  rcases
      (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
        (F := F) (u := u)).1 hu with
    ⟨x, hx_lt_top⟩
  refine ⟨?_, ?_⟩
  · -- Global properness of the graph function gives `F u y ≠ ⊥` for every section point `y`.
    intro y
    exact helperForProposition_6_29_3_section_ne_bot_of_properBifunction hFproper u y
  · -- The finite witness `x` gives the required section point with value different from `⊤`.
    exact ⟨x, lt_top_iff_ne_top.mp hx_lt_top⟩

/-- Helper for Proposition 6.29.3: a proper section contributes a finite witness, hence its
parameter lies in the bifunction effective domain. -/
lemma helperForProposition_6_29_3_mem_dom_of_section_proper
    {m n : ℕ} {F : Bifunction m n} {u : Fin m → ℝ} :
    ProperERealFunction (F u) → u ∈ bifunctionEffectiveDomain F := by
  intro hu
  -- Extract a point where the section avoids `⊤`.
  rcases hu.2 with ⟨x, hx_ne_top⟩
  -- Translate that witness back into the textbook domain characterization.
  rw [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue]
  exact ⟨x, lt_top_iff_ne_top.mpr hx_ne_top⟩

/-- Proposition 6.29.3: if `F` is proper, then
`dom F = {u ∈ ℝ^m | F u` is a proper convex function on `ℝ^n`}`. In this formalization,
the ambient convexity assumption on `F` is supplied implicitly as a standing hypothesis. -/
theorem proposition_29_3 {m n : ℕ} {F : Bifunction m n} [Fact (IsConvexBifunction F)]
    (hFproper : IsProperBifunction F) :
    bifunctionEffectiveDomain F = {u | ProperConvexERealFunction (F u)} := by
  ext u
  constructor
  · intro hu
    -- Membership in `dom F` gives properness of the section `F u`.
    have hproperSection : ProperERealFunction (F u) :=
      helperForProposition_6_29_3_section_proper_of_mem_dom hFproper hu
    refine ⟨hproperSection, ?_⟩
    -- Convexity of the section is exactly Proposition 6.29.1 for the fixed parameter `u`.
    intro x y a b ha hb hab
    exact proposition_29_1 (F := F) Fact.out u x y a b ha hb hab
  · intro hu
    -- Forget the convexity half; the properness half already characterizes membership in `dom F`.
    exact helperForProposition_6_29_3_mem_dom_of_section_proper hu.1

/-- Definition 6.29.9: The `(+∞)`-indicator bifunction of a linear map `A : ℝ^m → ℝ^n`
sends `u` and `x` to `0` when `x = A u` and to `+∞` otherwise. -/
noncomputable def linearIndicatorBifunction {m n : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    Bifunction m n :=
  fun u x => if x = A u then (0 : EReal) else ⊤

/-- An ordinary convex program on `ℝ^n` with `m` constraint functions, of which the
first `inequalityCount` are treated as inequality constraints and the rest as equality
constraints; the objective and inequality constraints are convex, while the equality
constraints are affine. In keeping with the book's convention, the objective takes
values in `(-∞, +∞]`, so it never attains `⊥`; moreover, the objective has nonempty
effective domain, matching the standing setup used in the text. -/
structure IndexedOrdinaryConvexProgram (m n : ℕ) where
  objective : (Fin n → ℝ) → EReal
  objective_ne_bot : ∀ x, objective x ≠ (⊥ : EReal)
  objective_dom_nonempty : Set.Nonempty (erealDom objective)
  constraint : Fin m → (Fin n → ℝ) → ℝ
  inequalityCount : ℕ
  inequalityCount_le : inequalityCount ≤ m
  objective_convex : ConvexFunction objective
  inequalityConstraint_convex :
    ∀ i : Fin m, (i : ℕ) < inequalityCount →
      ConvexFunction (fun x => (constraint i x : EReal))
  equalityConstraint_affine :
    ∀ i : Fin m, inequalityCount ≤ (i : ℕ) →
      ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x, a x = constraint i x

/-- The inequality-constraint indices extracted from the single indexed family in an
`IndexedOrdinaryConvexProgram`. -/
def IndexedOrdinaryConvexProgram.inequalityIndex {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :=
  {i : Fin m // (i : ℕ) < P.inequalityCount}

/-- The equality-constraint indices extracted from the single indexed family in an
`IndexedOrdinaryConvexProgram`. -/
def IndexedOrdinaryConvexProgram.equalityIndex {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :=
  {i : Fin m // P.inequalityCount ≤ (i : ℕ)}

/-- The ambient set `C = dom f₀` used to convert an indexed encoding into the canonical ordinary
convex-program core. -/
def IndexedOrdinaryConvexProgram.coreConstraintSet {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : Set (Fin n → ℝ) :=
  erealDom P.objective

/-- The real-valued objective on the ambient set `C = dom f₀` for the canonical core object. -/
noncomputable def IndexedOrdinaryConvexProgram.coreObjective {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : (Fin n → ℝ) → ℝ :=
  fun x => (P.objective x).toReal

/-- The canonical ordinary-convex-program core associated with an indexed encoding. This bridge
separates the mathematical object from the single-family implementation used in Section 29. -/
noncomputable def IndexedOrdinaryConvexProgram.toOrdinaryConvexProgram {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    OrdinaryConvexProgram (Fin n → ℝ) P.inequalityIndex P.equalityIndex := by
  classical
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) P.objective := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [ConvexFunction] using P.objective_convex
    · exact
        (nonempty_epigraph_iff_nonempty_effectiveDomain
          (Set.univ : Set (Fin n → ℝ)) P.objective).2 (by
            simpa [erealDom, effectiveDomain_eq] using P.objective_dom_nonempty)
    · intro x hx
      exact P.objective_ne_bot x
  refine
    { C := P.coreConstraintSet
      f0 := P.coreObjective
      g := fun i => P.constraint i.1
      h := fun j => P.constraint j.1
      C_convex := ?_
      f0_convexOn := ?_
      g_convexOn := ?_
      h_affineOn := ?_ }
  · simpa [IndexedOrdinaryConvexProgram.coreConstraintSet, erealDom, effectiveDomain_eq] using
      effectiveDomain_convex
        (S := (Set.univ : Set (Fin n → ℝ))) (f := P.objective) hProper.1
  · simpa [IndexedOrdinaryConvexProgram.coreConstraintSet,
      IndexedOrdinaryConvexProgram.coreObjective, erealDom, effectiveDomain_eq] using
      convexOn_toReal_effectiveDomain hProper
  · intro i
    simpa [IndexedOrdinaryConvexProgram.coreConstraintSet, erealDom,
      effectiveDomain_eq] using
      convexOn_toReal_on_affine_of_finite
        (f := fun x => ((P.constraint i.1 x : ℝ) : EReal))
        (P.inequalityConstraint_convex i.1 i.2)
        (effectiveDomain_convex
          (S := (Set.univ : Set (Fin n → ℝ))) (f := P.objective) hProper.1)
        (by simp)
  · intro j
    rcases P.equalityConstraint_affine j.1 j.2 with ⟨a, ha⟩
    exact ⟨a, by
      intro x hx
      symm
      exact ha x⟩

/-- Definition 6.29.10: For an ordinary convex program `(P)` and `u ∈ ℝ^m`,
`ordinaryConvexProgramConstraintSet P u` is the set of `x ∈ ℝ^n` such that the first
`r` constraint functions satisfy `f_i x ≤ u_i` and the remaining ones satisfy
`f_i x = u_i`, where `r = P.inequalityCount`. -/
def ordinaryConvexProgramConstraintSet {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n)
    (u : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i : Fin m,
    if (i : ℕ) < P.inequalityCount then
      P.constraint i x ≤ u i
    else
      P.constraint i x = u i}

/-- Definition 6.29.11: The bifunction associated with an ordinary convex program `(P)` is
the map `F` defined by `F u = f₀ + δ(· | Sᵤ)`, represented here as the objective function
of `P` plus the indicator bifunction of the constraint sets
`ordinaryConvexProgramConstraintSet P u`. -/
noncomputable def ordinaryConvexProgramAssociatedBifunction {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : Bifunction m n :=
  fun u x => P.objective x + indicatorBifunction (ordinaryConvexProgramConstraintSet P) u x

/-- An extended-real minimization problem on `ℝ^n`, represented by its objective function. -/
structure ExtendedRealMinimizationProblem (n : ℕ) where
  objective : (Fin n → ℝ) → EReal

/-- A family of extended-real minimization problems on `ℝ^n` indexed by perturbation
parameters `u ∈ ℝ^m`. -/
abbrev ParameterizedExtendedRealMinimizationProblem (m n : ℕ) :=
  (Fin m → ℝ) → ExtendedRealMinimizationProblem n

/-- Data consisting of an unperturbed problem `(P)` together with a perturbation
family `(P_u)` of extended-real minimization problems. -/
structure GeneralizedConvexProgramData (m n : ℕ) where
  primal : ExtendedRealMinimizationProblem n
  perturbation : ParameterizedExtendedRealMinimizationProblem m n

/-- Convex bifunctions from `ℝ^m` to `ℝ^n`, bundled with the convexity hypothesis used by
generalized convex programs. This bundled API is kept separate from the Prop-valued
`section30` predicate `ConvexBifunction`. -/
def BundledConvexBifunction (m n : ℕ) := {F : Bifunction m n // IsConvexBifunction F}

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Definition 6.29.12: For a convex bifunction `F`, the generalized convex program
associated with `F` consists of the unperturbed problem `(P)` on `ℝ^n` with objective
function `F₀`, together with the perturbation family `(P_u)` whose `u`-th member has
objective function `F_u`. -/
def generalizedConvexProgram {m n : ℕ} (F : ConvexBifunction m n) :
    GeneralizedConvexProgramData m n :=
  { primal := ⟨F.1 0⟩
    perturbation := fun u => ⟨F.1 u⟩ }

/-- The unperturbed problem `(P)` extracted from Definition 6.29.12. -/
abbrev generalizedConvexProgramPrimal {m n : ℕ} (F : ConvexBifunction m n) :
    ExtendedRealMinimizationProblem n :=
  (generalizedConvexProgram F).primal

/-- The perturbation family `(P_u)` extracted from Definition 6.29.12. -/
def generalizedConvexProgramPerturbation {m n : ℕ} (F : ConvexBifunction m n) :
    ParameterizedExtendedRealMinimizationProblem m n :=
  (generalizedConvexProgram F).perturbation

/-- The `g₀` summand in the decomposition of the graph function associated with an
ordinary convex program. -/
def ordinaryConvexProgramGraphObjectiveSummand {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    ((Fin m → ℝ) × (Fin n → ℝ)) → EReal :=
  fun ux => P.objective ux.2

/-- The set `C = dom f₀` attached to an ordinary convex program, namely the effective
domain of its extended-real-valued objective. -/
def ordinaryConvexProgramObjectiveDomain {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    Set (Fin n → ℝ) :=
  erealDom P.objective

/-- The `gᵢ` summand for the `i`-th constraint in the decomposition of the graph function
associated with an ordinary convex program. -/
noncomputable def ordinaryConvexProgramGraphConstraintSummand {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) (i : Fin m) :
    ((Fin m → ℝ) × (Fin n → ℝ)) → EReal :=
  fun ux =>
    if (i : ℕ) < P.inequalityCount then
      indicatorBifunction (fun u => {x | P.constraint i x ≤ u i}) ux.1 ux.2
    else
      indicatorBifunction (fun u => {x | P.constraint i x = u i}) ux.1 ux.2

/-- Helper for Lemma 6.29.1: the indicator of the full constraint set is the finite sum of the
individual graph-constraint indicators. -/
lemma helperForLemma_6_29_1_constraintIndicator_eq_sum_graphConstraintSummands {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) (ux : (Fin m → ℝ) × (Fin n → ℝ)) :
    indicatorBifunction (ordinaryConvexProgramConstraintSet P) ux.1 ux.2 =
      ∑ i : Fin m, ordinaryConvexProgramGraphConstraintSummand P i ux := by
  classical
  -- Split according to whether the point satisfies every constraint simultaneously.
  by_cases hmem : ux.2 ∈ ordinaryConvexProgramConstraintSet P ux.1
  · have hzero : ∀ i : Fin m, ordinaryConvexProgramGraphConstraintSummand P i ux = 0 := by
      intro i
      -- Each coordinate summand vanishes once the corresponding constraint holds.
      by_cases hi : (i : ℕ) < P.inequalityCount
      · have hi_mem : P.constraint i ux.2 ≤ ux.1 i := by
          simpa [ordinaryConvexProgramConstraintSet, hi] using hmem i
        simp [ordinaryConvexProgramGraphConstraintSummand, hi, indicatorBifunction, hi_mem]
      · have hi_mem : P.constraint i ux.2 = ux.1 i := by
          simpa [ordinaryConvexProgramConstraintSet, hi] using hmem i
        simp [ordinaryConvexProgramGraphConstraintSummand, hi, indicatorBifunction, hi_mem]
    -- In the feasible case both sides reduce to `0`.
    simp [indicatorBifunction, hmem, hzero]
  · rcases not_forall.mp hmem with ⟨i, hi_fail⟩
    have hterm_top : ordinaryConvexProgramGraphConstraintSummand P i ux = ⊤ := by
      -- A violated coordinate contributes the `⊤` summand that forces the whole sum to `⊤`.
      by_cases hi : (i : ℕ) < P.inequalityCount
      · have hi_fail' : ¬ P.constraint i ux.2 ≤ ux.1 i := by
          simpa [ordinaryConvexProgramConstraintSet, hi] using hi_fail
        simp [ordinaryConvexProgramGraphConstraintSummand, hi, indicatorBifunction, hi_fail']
      · have hi_fail' : ¬ P.constraint i ux.2 = ux.1 i := by
          simpa [ordinaryConvexProgramConstraintSet, hi] using hi_fail
        simp [ordinaryConvexProgramGraphConstraintSummand, hi, indicatorBifunction, hi_fail']
    have hterm_not_bot :
        ∀ j : Fin m, ordinaryConvexProgramGraphConstraintSummand P j ux ≠ (⊥ : EReal) := by
      intro j
      by_cases hj : (j : ℕ) < P.inequalityCount
      · by_cases hji : P.constraint j ux.2 ≤ ux.1 j
        · simp [ordinaryConvexProgramGraphConstraintSummand, hj, indicatorBifunction, hji]
        · simp [ordinaryConvexProgramGraphConstraintSummand, hj, indicatorBifunction, hji]
      · by_cases hji : P.constraint j ux.2 = ux.1 j
        · simp [ordinaryConvexProgramGraphConstraintSummand, hj, indicatorBifunction, hji]
        · simp [ordinaryConvexProgramGraphConstraintSummand, hj, indicatorBifunction, hji]
    have hsum_top : (∑ j : Fin m, ordinaryConvexProgramGraphConstraintSummand P j ux) = ⊤ := by
      exact sum_eq_top_of_term_top (s := Finset.univ)
        (f := fun j : Fin m => ordinaryConvexProgramGraphConstraintSummand P j ux)
        (i := i) (by simp) hterm_top (fun j _ => hterm_not_bot j)
    -- The global indicator is also `⊤` at any infeasible point.
    simp [indicatorBifunction, hmem, hsum_top]

/-- Helper for Lemma 6.29.1: feasibility is preserved under convex combinations of feasible graph
points. -/
lemma helperForLemma_6_29_1_mem_constraintSet_of_convexCombo {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n)
    {p q : (Fin m → ℝ) × (Fin n → ℝ)} {a b : ℝ}
    (hp : p.2 ∈ ordinaryConvexProgramConstraintSet P p.1)
    (hq : q.2 ∈ ordinaryConvexProgramConstraintSet P q.1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • p + b • q).2 ∈ ordinaryConvexProgramConstraintSet P ((a • p + b • q).1) := by
  classical
  -- First discharge the endpoint cases where the convex combination is just one endpoint.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    simpa using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    subst hb0
    subst ha1
    simpa using hp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hb_lt_one : b < 1 := by linarith
  have ha_eq : a = 1 - b := by linarith
  intro i
  -- Now check feasibility constraint-by-constraint, splitting inequality versus equality indices.
  by_cases hi : (i : ℕ) < P.inequalityCount
  · have hp_i : P.constraint i p.2 ≤ p.1 i := by
      simpa [ordinaryConvexProgramConstraintSet, hi] using hp i
    have hq_i : P.constraint i q.2 ≤ q.1 i := by
      simpa [ordinaryConvexProgramConstraintSet, hi] using hq i
    have hnotbot :
        ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), (P.constraint i x : EReal) ≠ (⊥ : EReal) := by
      intro x hx
      exact EReal.coe_ne_bot _
    have hconvOn :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => (P.constraint i x : EReal)) := by
      simpa [ConvexFunction] using P.inequalityConstraint_convex i hi
    have hseg :=
      (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin n → ℝ)))
        (f := fun x => (P.constraint i x : EReal))
        (hC := convex_univ) (hnotbot := hnotbot)).1 hconvOn
        p.2 (by simp) q.2 (by simp) b hb_pos hb_lt_one
    have hconstraint :
        (P.constraint i ((a • p + b • q).2) : EReal) ≤
          ((a : ℝ) : EReal) * (P.constraint i p.2 : EReal) +
            ((b : ℝ) : EReal) * (P.constraint i q.2 : EReal) := by
      simpa [ha_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hseg
    have hpw :
        ((a : ℝ) : EReal) * (P.constraint i p.2 : EReal) ≤ ((a : ℝ) : EReal) * (p.1 i : EReal) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hp_i) (by exact_mod_cast ha)
    have hqw :
        ((b : ℝ) : EReal) * (P.constraint i q.2 : EReal) ≤ ((b : ℝ) : EReal) * (q.1 i : EReal) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hq_i) (by exact_mod_cast hb)
    have hfinalE :
        (P.constraint i ((a • p + b • q).2) : EReal) ≤ ((a • p + b • q).1 i : EReal) := by
      calc
        (P.constraint i ((a • p + b • q).2) : EReal)
            ≤ ((a : ℝ) : EReal) * (P.constraint i p.2 : EReal) +
              ((b : ℝ) : EReal) * (P.constraint i q.2 : EReal) := hconstraint
        _ ≤ ((a : ℝ) : EReal) * (p.1 i : EReal) + ((b : ℝ) : EReal) * (q.1 i : EReal) :=
          add_le_add hpw hqw
        _ = ((a • p + b • q).1 i : EReal) := by simp
    have hfinal : P.constraint i ((a • p + b • q).2) ≤ (a • p + b • q).1 i := by
      exact_mod_cast hfinalE
    simpa [ordinaryConvexProgramConstraintSet, hi] using hfinal
  · have hi' : P.inequalityCount ≤ (i : ℕ) := le_of_not_gt hi
    rcases P.equalityConstraint_affine i hi' with ⟨A, hA⟩
    have hp_i : P.constraint i p.2 = p.1 i := by
      simpa [ordinaryConvexProgramConstraintSet, hi] using hp i
    have hq_i : P.constraint i q.2 = q.1 i := by
      simpa [ordinaryConvexProgramConstraintSet, hi] using hq i
    -- Affinity transports the second-coordinate convex combination exactly onto the first one.
    have hfinal :
        P.constraint i ((a • p + b • q).2) = (a • p + b • q).1 i := by
      calc
        P.constraint i ((a • p + b • q).2) = A ((a • p + b • q).2) := by symm; exact hA _
        _ = a * p.1 i + b * q.1 i := by
          calc
            A ((a • p + b • q).2) = A ((1 - b) • p.2 + b • q.2) := by simp [ha_eq]
            _ = A (AffineMap.lineMap p.2 q.2 b) := by simp [AffineMap.lineMap_apply_module]
            _ = AffineMap.lineMap (A p.2) (A q.2) b := by simpa using A.apply_lineMap p.2 q.2 b
            _ = a * p.1 i + b * q.1 i := by
              simp [AffineMap.lineMap_apply_module, hA, hp_i, hq_i, ha_eq]
        _ = (a • p + b • q).1 i := by simp
    simpa [ordinaryConvexProgramConstraintSet, hi] using hfinal

/-- Helper for Lemma 6.29.1: the objective term already satisfies the required convexity
inequality on graph-space points. -/
lemma helperForLemma_6_29_1_objectiveSummand_convexOnGraph {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n)
    (p q : (Fin m → ℝ) × (Fin n → ℝ)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ordinaryConvexProgramGraphObjectiveSummand P (a • p + b • q) ≤
      ((a : ℝ) : EReal) * ordinaryConvexProgramGraphObjectiveSummand P p +
      ((b : ℝ) : EReal) * ordinaryConvexProgramGraphObjectiveSummand P q := by
  -- Handle the endpoint case separately, then use the segment inequality for the interior case.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    simp [ordinaryConvexProgramGraphObjectiveSummand]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    subst hb0
    subst ha1
    simp [ordinaryConvexProgramGraphObjectiveSummand]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hb_lt : b < 1 := by linarith
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), P.objective x ≠ (⊥ : EReal) := by
    intro x hx
    exact P.objective_ne_bot x
  have hconvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) P.objective := by
    simpa [ConvexFunction] using P.objective_convex
  have hseg :=
    (convexFunctionOn_iff_segment_inequality
      (C := (Set.univ : Set (Fin n → ℝ))) (f := P.objective)
      (hC := convex_univ) (hnotbot := hnotbot)).1 hconvOn
      p.2 (by simp) q.2 (by simp) b hb_pos hb_lt
  have ha_eq : a = 1 - b := by linarith
  simpa [ordinaryConvexProgramGraphObjectiveSummand, ha_eq, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hseg

/-- Helper for Lemma 6.29.1: the associated graph function never takes the value `-∞`. -/
lemma helperForLemma_6_29_1_graphValue_ne_bot {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) (ux : (Fin m → ℝ) × (Fin n → ℝ)) :
    graphFunction (ordinaryConvexProgramAssociatedBifunction P) ux ≠ (⊥ : EReal) := by
  classical
  -- The objective never takes `⊥`, and the indicator takes only `0` or `⊤`.
  have hobj : P.objective ux.2 ≠ (⊥ : EReal) := P.objective_ne_bot ux.2
  have hind : indicatorBifunction (ordinaryConvexProgramConstraintSet P) ux.1 ux.2 ≠ (⊥ : EReal) := by
    by_cases hmem : ux.2 ∈ ordinaryConvexProgramConstraintSet P ux.1
    · simp [indicatorBifunction, hmem]
    · simp [indicatorBifunction, hmem]
  simpa [graphFunction, ordinaryConvexProgramAssociatedBifunction] using add_ne_bot_of_notbot hobj hind

/-- Helper for Lemma 6.29.1: infeasible graph points force the associated bifunction value to
`⊤`. -/
lemma helperForLemma_6_29_1_graphValue_eq_top_of_infeasible {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hx : x ∉ ordinaryConvexProgramConstraintSet P u) :
    ordinaryConvexProgramAssociatedBifunction P u x = ⊤ := by
  classical
  -- Once the indicator is `⊤`, adding the objective term still gives `⊤`.
  have hobj : P.objective x ≠ (⊥ : EReal) := P.objective_ne_bot x
  have hind : indicatorBifunction (ordinaryConvexProgramConstraintSet P) u x = ⊤ := by
    simp [indicatorBifunction, hx]
  calc
    ordinaryConvexProgramAssociatedBifunction P u x =
        P.objective x + indicatorBifunction (ordinaryConvexProgramConstraintSet P) u x := by rfl
    _ = ⊤ := by simpa [hind] using EReal.add_top_of_ne_bot hobj

-- Proof sketch: rewrite the associated bifunction as the objective term plus the indicator of
-- the constraint set, then expand that indicator into the sum of the individual graph-constraint
-- indicators. Convexity follows because the objective summand is convex, each inequality
-- indicator is the indicator of a convex epigraph-type set, each equality indicator is the
-- indicator of an affine graph, and finite sums of convex functions are convex.
/-- Lemma 6.29.1: The graph function of the bifunction associated with an ordinary convex
program is convex on `ℝ^m × ℝ^n`; moreover it decomposes as the objective summand plus the
sum of the individual constraint-indicator summands. -/
theorem ordinaryConvexProgramAssociatedBifunction_graphFunction_convex {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    IsConvexBifunction (ordinaryConvexProgramAssociatedBifunction P) ∧
      graphFunction (ordinaryConvexProgramAssociatedBifunction P) =
        fun ux =>
          ordinaryConvexProgramGraphObjectiveSummand P ux +
            ∑ i : Fin m, ordinaryConvexProgramGraphConstraintSummand P i ux := by
  classical
  refine ⟨?_, ?_⟩
  · intro p q a b ha hb hab
    let F := ordinaryConvexProgramAssociatedBifunction P
    let S := ordinaryConvexProgramConstraintSet P
    have hObjective :=
      helperForLemma_6_29_1_objectiveSummand_convexOnGraph P p q a b ha hb hab
    -- Separate the endpoint cases before handling the genuinely two-point convex combination.
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simp [graphFunction, F, ordinaryConvexProgramAssociatedBifunction]
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      subst hb0
      subst ha1
      simp [graphFunction, F, ordinaryConvexProgramAssociatedBifunction]
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    -- The remaining proof splits according to feasibility of the two endpoints.
    by_cases hp : p.2 ∈ S p.1
    · by_cases hq : q.2 ∈ S q.1
      · have hcombo : (a • p + b • q).2 ∈ S ((a • p + b • q).1) :=
          helperForLemma_6_29_1_mem_constraintSet_of_convexCombo P hp hq ha hb hab
        have hcombo' :
            a • p.2 + b • q.2 ∈ ordinaryConvexProgramConstraintSet P (a • p.1 + b • q.1) := by
          simpa [S] using hcombo
        -- When both endpoints are feasible, the indicator terms vanish and only the objective remains.
        calc
          graphFunction F (a • p + b • q) =
              ordinaryConvexProgramGraphObjectiveSummand P (a • p + b • q) := by
                change P.objective (a • p.2 + b • q.2) +
                    (if a • p.2 + b • q.2 ∈ ordinaryConvexProgramConstraintSet P (a • p.1 + b • q.1)
                      then (0 : EReal) else ⊤) = P.objective (a • p.2 + b • q.2)
                rw [if_pos hcombo', add_zero]
          _ ≤ ((a : ℝ) : EReal) * ordinaryConvexProgramGraphObjectiveSummand P p +
                ((b : ℝ) : EReal) * ordinaryConvexProgramGraphObjectiveSummand P q := hObjective
          _ = ((a : ℝ) : EReal) * graphFunction F p + ((b : ℝ) : EReal) * graphFunction F q := by
                simp [graphFunction, F, S, ordinaryConvexProgramAssociatedBifunction,
                  ordinaryConvexProgramGraphObjectiveSummand, indicatorBifunction, hp, hq]
      · have hqTop : ((b : ℝ) : EReal) * graphFunction F q = ⊤ := by
          have hqGraphTop : graphFunction F q = ⊤ := by
            simpa [graphFunction, F] using
              helperForLemma_6_29_1_graphValue_eq_top_of_infeasible P hq
          simpa [hqGraphTop] using EReal.coe_mul_top_of_pos hb_pos
        have hpWeighted_ne_bot : ((a : ℝ) : EReal) * graphFunction F p ≠ (⊥ : EReal) := by
          have haE : (0 : EReal) ≤ (a : EReal) := by exact_mod_cast ha
          rw [EReal.mul_ne_bot]
          exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (helperForLemma_6_29_1_graphValue_ne_bot P p),
            Or.inl (EReal.coe_ne_top _), Or.inl haE⟩
        -- A positively weighted infeasible endpoint makes the right-hand side equal `⊤`.
        calc
          graphFunction F (a • p + b • q) ≤ ⊤ := le_top
          _ = ((a : ℝ) : EReal) * graphFunction F p + ((b : ℝ) : EReal) * graphFunction F q := by
                rw [hqTop]
                symm
                exact EReal.add_top_of_ne_bot hpWeighted_ne_bot
    · have hpTop : ((a : ℝ) : EReal) * graphFunction F p = ⊤ := by
        have hpGraphTop : graphFunction F p = ⊤ := by
          simpa [graphFunction, F] using
            helperForLemma_6_29_1_graphValue_eq_top_of_infeasible P hp
        simpa [hpGraphTop] using EReal.coe_mul_top_of_pos ha_pos
      have hqWeighted_ne_bot : ((b : ℝ) : EReal) * graphFunction F q ≠ (⊥ : EReal) := by
        have hbE : (0 : EReal) ≤ (b : EReal) := by exact_mod_cast hb
        rw [EReal.mul_ne_bot]
        exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (helperForLemma_6_29_1_graphValue_ne_bot P q),
          Or.inl (EReal.coe_ne_top _), Or.inl hbE⟩
      -- If the first endpoint is infeasible with positive weight, the same `⊤` argument applies.
      calc
        graphFunction F (a • p + b • q) ≤ ⊤ := le_top
        _ = ((a : ℝ) : EReal) * graphFunction F p + ((b : ℝ) : EReal) * graphFunction F q := by
              rw [hpTop]
              symm
              exact EReal.top_add_of_ne_bot hqWeighted_ne_bot
  · ext ux
    -- The decomposition is exactly the objective term plus the expanded constraint indicator.
    simp [graphFunction, ordinaryConvexProgramAssociatedBifunction,
      ordinaryConvexProgramGraphObjectiveSummand,
      helperForLemma_6_29_1_constraintIndicator_eq_sum_graphConstraintSummands]

-- Proof sketch: unfold the associated bifunction and `bifunctionEffectiveDomain`. Since an
-- ordinary convex program has objective values in `(-∞, +∞]`, the sum `f₀ + δ(· | Sᵤ)` is finite
-- exactly at those `x ∈ Sᵤ` for which `f₀ x < +∞`, so the effective domain is characterized by
-- nonemptiness of `Sᵤ ∩ C`, where `C = dom f₀`.
/-- Helper for Lemma 6.29.2: on feasible points, the associated bifunction reduces to the
objective because the indicator term vanishes. -/
lemma helperForLemma_6_29_2_associatedValue_eq_objective_of_mem_constraintSet {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {u : Fin m → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ ordinaryConvexProgramConstraintSet P u) :
    ordinaryConvexProgramAssociatedBifunction P u x = P.objective x := by
  classical
  -- Feasibility makes the indicator term equal to `0`.
  simp [ordinaryConvexProgramAssociatedBifunction, indicatorBifunction, hx]

/-- Helper for Lemma 6.29.2: the associated bifunction has a finite value exactly at the
points that are feasible and lie in the objective domain. -/
lemma helperForLemma_6_29_2_associatedValue_lt_top_iff {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {u : Fin m → ℝ} {x : Fin n → ℝ} :
    ordinaryConvexProgramAssociatedBifunction P u x < ⊤ ↔
      x ∈ ordinaryConvexProgramConstraintSet P u ∩ ordinaryConvexProgramObjectiveDomain P := by
  constructor
  · intro hx
    -- First rule out infeasibility: an infeasible point would force the associated value to be `⊤`.
    have hfeasible : x ∈ ordinaryConvexProgramConstraintSet P u := by
      by_contra hnot
      have htop : ordinaryConvexProgramAssociatedBifunction P u x = ⊤ :=
        helperForLemma_6_29_1_graphValue_eq_top_of_infeasible P hnot
      have : ¬ ordinaryConvexProgramAssociatedBifunction P u x < ⊤ := by
        simp [htop]
      exact this hx
    -- Once feasibility is known, finiteness is exactly finiteness of the objective value.
    have hobjective :
        ordinaryConvexProgramAssociatedBifunction P u x = P.objective x :=
      helperForLemma_6_29_2_associatedValue_eq_objective_of_mem_constraintSet P hfeasible
    have hobjective_lt_top : P.objective x < ⊤ := by
      simpa [hobjective] using hx
    exact ⟨hfeasible, by
      simpa [ordinaryConvexProgramObjectiveDomain, erealDom] using hobjective_lt_top⟩
  · rintro ⟨hfeasible, hobjective⟩
    -- On a feasible point, the indicator disappears and only the objective remains.
    have hobjective_lt_top : P.objective x < ⊤ := by
      simpa [ordinaryConvexProgramObjectiveDomain, erealDom] using hobjective
    have hassociated :
        ordinaryConvexProgramAssociatedBifunction P u x = P.objective x :=
      helperForLemma_6_29_2_associatedValue_eq_objective_of_mem_constraintSet P hfeasible
    simpa [hassociated] using hobjective_lt_top

/-- Helper for Lemma 6.29.2: a perturbation lies in the effective domain of the associated
bifunction exactly when the feasible set meets the objective domain. -/
lemma helperForLemma_6_29_2_mem_dom_iff_nonempty_inter {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {u : Fin m → ℝ} :
    u ∈ bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) ↔
      Set.Nonempty
        (ordinaryConvexProgramConstraintSet P u ∩ ordinaryConvexProgramObjectiveDomain P) := by
  -- Rewrite domain membership into existence of a finite section value.
  rw [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue]
  constructor
  · rintro ⟨x, hx⟩
    -- Translate the finite witness into the intersection condition from the statement.
    exact ⟨x, (helperForLemma_6_29_2_associatedValue_lt_top_iff P).1 hx⟩
  · rintro ⟨x, hx⟩
    -- Any point in the intersection provides the required finite section witness.
    exact ⟨x, (helperForLemma_6_29_2_associatedValue_lt_top_iff P).2 hx⟩

/-- Lemma 6.29.2: For the bifunction `F` associated with an ordinary convex program `(P)`,
`dom F` is the set of perturbations `u` such that the constraint set `Sᵤ` meets
`C = dom f₀`. -/
theorem ordinaryConvexProgramAssociatedBifunction_dom_eq_nonempty_inter_dom_objective {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) =
      {u | Set.Nonempty
        (ordinaryConvexProgramConstraintSet P u ∩
          ordinaryConvexProgramObjectiveDomain P)} := by
  -- Extensionalize in the perturbation parameter and apply the domain-membership characterization.
  ext u
  exact helperForLemma_6_29_2_mem_dom_iff_nonempty_inter P

/-- Helper for Lemma 6.29.3: when the perturbation vector records the constraint values at
`x`, the same point `x` satisfies every defining constraint of `Sᵤ` by reflexivity. -/
lemma helperForLemma_6_29_3_constraintVector_mem_constraintSet_self {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {x : Fin n → ℝ} :
    x ∈ ordinaryConvexProgramConstraintSet P (fun i => P.constraint i x) := by
  -- Check each coordinate separately; both branches reduce to a reflexive relation.
  intro i
  by_cases hi : (i : ℕ) < P.inequalityCount
  · -- In the inequality branch, the constraint becomes `fᵢ x ≤ fᵢ x`.
    simp [hi]
  · -- In the equality branch, the constraint becomes `fᵢ x = fᵢ x`.
    simp [hi]

/-- Helper for Lemma 6.29.3: a point in the objective domain also lies in the intersection
`Sᵤ ∩ dom f₀` for the perturbation `uᵢ = fᵢ(x)`. -/
lemma helperForLemma_6_29_3_constraintVector_mem_inter_objectiveDomain {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {x : Fin n → ℝ}
    (hx : x ∈ ordinaryConvexProgramObjectiveDomain P) :
    x ∈ ordinaryConvexProgramConstraintSet P (fun i => P.constraint i x) ∩
      ordinaryConvexProgramObjectiveDomain P := by
  -- Package the feasibility fact together with the given objective-domain hypothesis.
  constructor
  · exact helperForLemma_6_29_3_constraintVector_mem_constraintSet_self P
  · exact hx

/-- Helper for Lemma 6.29.3: every point of `dom f₀` yields a perturbation vector lying in
the effective domain of the associated bifunction. -/
lemma helperForLemma_6_29_3_constraintVector_mem_dom_of_objectiveDomain {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) {x : Fin n → ℝ}
    (hx : x ∈ ordinaryConvexProgramObjectiveDomain P) :
    (fun i => P.constraint i x) ∈
      bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) := by
  -- Use Lemma 6.29.2 to replace domain membership by a nonempty intersection condition.
  rw [helperForLemma_6_29_2_mem_dom_iff_nonempty_inter P]
  -- The witness is the same point `x`, now known to lie in `Sᵤ ∩ dom f₀`.
  exact ⟨x, helperForLemma_6_29_3_constraintVector_mem_inter_objectiveDomain P hx⟩

-- Proof sketch: let `u := (fun i => P.constraint i x)`. Since `x ∈ dom f₀`, it suffices to
-- show `x ∈ Sᵤ`; this holds because each inequality constraint becomes `fᵢ x ≤ fᵢ x` and each
-- equality constraint becomes `fᵢ x = fᵢ x`. This yields the pointwise membership statement.
-- The nonemptiness assertion then follows from the standing assumption in
-- `IndexedOrdinaryConvexProgram` that `C = dom f₀` is nonempty.
/-- Lemma 6.29.3: Let `F` be the bifunction associated with `(P)`, and let
`C = dom f₀`. Then `dom F` is nonempty. In fact, for every `x ∈ C`,
the perturbation vector `(f₁(x), …, f_m(x))` belongs to `dom F`. -/
theorem ordinaryConvexProgram_constraintValues_mem_associatedBifunctionEffectiveDomain
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    Set.Nonempty
        (bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P)) ∧
      ∀ {x : Fin n → ℝ}, x ∈ ordinaryConvexProgramObjectiveDomain P →
        (fun i => P.constraint i x) ∈
          bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) := by
  constructor
  · -- Choose any objective-domain point supplied by the standing nonemptiness hypothesis.
    rcases P.objective_dom_nonempty with ⟨x, hx⟩
    -- Its constraint-value perturbation lies in `dom F` by the pointwise statement.
    exact
      ⟨(fun i => P.constraint i x),
        helperForLemma_6_29_3_constraintVector_mem_dom_of_objectiveDomain P hx⟩
  · intro x hx
    -- Reuse the same witness `x` to certify nonemptiness of the relevant section domain.
    exact helperForLemma_6_29_3_constraintVector_mem_dom_of_objectiveDomain P hx

-- Proof sketch: use Lemma 6.29.3 to obtain a perturbation `u` for which the associated
-- bifunction has a finite value, giving nonemptiness of its effective domain. For the
-- `⊥`-avoidance part of properness, combine the standing hypothesis that `P.objective`
-- never takes the value `⊥` with the fact that the indicator bifunction only takes the
-- values `0` and `⊤`.
/-- Lemma 6.29.4: If `F` is the bifunction associated with an ordinary convex program `(P)`,
then `F` is proper. -/
theorem ordinaryConvexProgramAssociatedBifunction_proper {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    IsProperBifunction (ordinaryConvexProgramAssociatedBifunction P) := by
  refine ⟨?_, ?_⟩
  · -- Properness first requires that the graph function never takes the value `⊥`.
    intro ux
    exact helperForLemma_6_29_1_graphValue_ne_bot P ux
  · -- Next extract a perturbation in the effective domain and convert it to a finite graph point.
    rcases ordinaryConvexProgram_constraintValues_mem_associatedBifunctionEffectiveDomain P with
      ⟨⟨u, hu⟩, _⟩
    rcases
        (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
          (F := ordinaryConvexProgramAssociatedBifunction P) (u := u)).1 hu with
      ⟨x, hx_lt_top⟩
    refine ⟨(u, x), ?_⟩
    -- The finite section value becomes a finite graph value after unfolding `graphFunction`.
    simpa [graphFunction] using lt_top_iff_ne_top.mp hx_lt_top

-- Proof sketch: write the graph function of the associated bifunction as the sum of the
-- objective summand and the individual constraint-indicator summands from Lemma 6.29.1.
-- Closedness of the objective gives a closed epigraph for the first summand, the closed
-- inequality constraints give closed epigraph-type sets for the indicator terms, and the
-- equality constraints are affine by the ordinary convex program hypotheses, so their graph
-- indicator terms are closed as well. Closedness is then preserved under finite sums.
-- Lemma 6.29.5 is proved below by expressing the associated epigraph as the intersection of the
-- objective epigraph with the graph-space feasibility set and showing both pieces are closed.
/-- Helper for Lemma 6.29.5: the objective epigraph condition on the graph-space triple is a
closed set because it is the continuous preimage of the usual epigraph of `f₀`. -/
lemma helperForLemma_6_29_5_objectiveEpigraph_closed {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n)
    (hObjectiveClosed : ClosedConvexFunction P.objective) :
    IsClosed
      {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | P.objective p.1.2 ≤ (p.2 : EReal)} := by
  -- Convert closedness of `f₀` into closedness of its epigraph in the `x`-space.
  have hsublevel : ∀ α : ℝ, IsClosed {x : Fin n → ℝ | P.objective x ≤ (α : EReal)} :=
    ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := P.objective)).1).1
      hObjectiveClosed.2
  have hObjectiveEpigraph :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) P.objective) :=
    ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := P.objective)).2).1
      hsublevel
  have hProjectionX : Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => p.1.2 :=
    continuous_snd.comp continuous_fst
  have hProjectionR : Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => p.2 :=
    continuous_snd
  have hProjection :
      Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => (p.1.2, p.2) :=
    hProjectionX.prodMk hProjectionR
  -- Pull the closed epigraph back along the projection that forgets the parameter coordinate.
  have hPreimage :
      (fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => (p.1.2, p.2)) ⁻¹'
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) P.objective =
        {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | P.objective p.1.2 ≤ (p.2 : EReal)} := by
    ext p
    constructor
    · intro hp
      change (p.1.2, p.2) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) P.objective at hp
      exact (mem_epigraph_univ_iff (f := P.objective)).1 hp
    · intro hp
      change (p.1.2, p.2) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) P.objective
      exact (mem_epigraph_univ_iff (f := P.objective)).2 hp
  rw [← hPreimage]
  exact hObjectiveEpigraph.preimage hProjection

/-- Helper for Lemma 6.29.5: each inequality graph-constraint slice is closed because it is the
continuous preimage of the epigraph of the closed inequality function. -/
lemma helperForLemma_6_29_5_inequalityConstraintSlice_closed {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n)
    (hInequalityClosed :
      ∀ i : Fin m, (i : ℕ) < P.inequalityCount →
        ClosedConvexFunction (fun x => (P.constraint i x : EReal)))
    (i : Fin m) (hi : (i : ℕ) < P.inequalityCount) :
    IsClosed
      {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | P.constraint i p.1.2 ≤ p.1.1 i} := by
  -- Closedness of the inequality function again gives a closed epigraph in the `x`-coordinate.
  have hsublevel :
      ∀ α : ℝ, IsClosed {x : Fin n → ℝ | (P.constraint i x : EReal) ≤ (α : EReal)} :=
    ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph
      (f := fun x => (P.constraint i x : EReal))).1).1 (hInequalityClosed i hi).2
  have hConstraintEpigraph :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (fun x => (P.constraint i x : EReal))) :=
    ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph
      (f := fun x => (P.constraint i x : EReal))).2).1 hsublevel
  have hProjectionX : Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => p.1.2 :=
    continuous_snd.comp continuous_fst
  have hProjectionU :
      Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => p.1.1 i :=
    (continuous_apply i).comp (continuous_fst.comp continuous_fst)
  have hProjection :
      Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => (p.1.2, p.1.1 i) :=
    hProjectionX.prodMk hProjectionU
  -- The constraint slice is exactly the pullback of that epigraph by the `(x, uᵢ)` map.
  have hPreimage :
      (fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => (p.1.2, p.1.1 i)) ⁻¹'
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) (fun x => (P.constraint i x : EReal)) =
        {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | P.constraint i p.1.2 ≤ p.1.1 i} := by
    ext p
    constructor
    · intro hp
      change (p.1.2, p.1.1 i) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (fun x => (P.constraint i x : EReal)) at hp
      exact_mod_cast (mem_epigraph_univ_iff (f := fun x => (P.constraint i x : EReal))).1 hp
    · intro hp
      change (p.1.2, p.1.1 i) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (fun x => (P.constraint i x : EReal))
      exact (mem_epigraph_univ_iff (f := fun x => (P.constraint i x : EReal))).2 (by
        exact_mod_cast hp)
  rw [← hPreimage]
  exact hConstraintEpigraph.preimage hProjection

/-- Helper for Lemma 6.29.5: each equality graph-constraint slice is closed because an affine
constraint is continuous, so its graph against the coordinate projection is closed. -/
lemma helperForLemma_6_29_5_equalityConstraintSlice_closed {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) (i : Fin m)
    (hi : P.inequalityCount ≤ (i : ℕ)) :
    IsClosed
      {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | P.constraint i p.1.2 = p.1.1 i} := by
  rcases P.equalityConstraint_affine i hi with ⟨A, hA⟩
  have hLeftProjection :
      Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => p.1.2 :=
    continuous_snd.comp continuous_fst
  have hLeft :
      Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => A p.1.2 :=
    (AffineMap.continuous_of_finiteDimensional A).comp hLeftProjection
  have hRight :
      Continuous fun p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => p.1.1 i :=
    (continuous_apply i).comp (continuous_fst.comp continuous_fst)
  -- Rewrite the constraint using the affine representative and apply closedness of an equality set.
  convert isClosed_eq hLeft hRight using 1
  ext p
  simp [hA (p.1.2)]

/-- Helper for Lemma 6.29.5: a graph-space point belongs to the epigraph of the associated
bifunction exactly when its objective value is below the height and all graph constraints hold. -/
lemma helperForLemma_6_29_5_mem_associatedEpigraph_iff {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n)
    (p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :
    graphFunction (ordinaryConvexProgramAssociatedBifunction P) p.1 ≤ (p.2 : EReal) ↔
      P.objective p.1.2 ≤ (p.2 : EReal) ∧
        p.1.2 ∈ ordinaryConvexProgramConstraintSet P p.1.1 := by
  classical
  -- Split on feasibility, since the indicator is `0` on feasible points and `⊤` otherwise.
  by_cases hFeasible : p.1.2 ∈ ordinaryConvexProgramConstraintSet P p.1.1
  · -- On the feasible branch, the associated bifunction reduces to the objective.
    simp [graphFunction, ordinaryConvexProgramAssociatedBifunction, indicatorBifunction, hFeasible]
  · have hTop :
        ordinaryConvexProgramAssociatedBifunction P p.1.1 p.1.2 = ⊤ :=
      helperForLemma_6_29_1_graphValue_eq_top_of_infeasible P hFeasible
    -- On the infeasible branch, the associated value is `⊤`, so no real epigraph bound can hold.
    constructor
    · intro hp
      have : ¬ graphFunction (ordinaryConvexProgramAssociatedBifunction P) p.1 ≤ (p.2 : EReal) := by
        simpa [graphFunction, hTop]
      exact False.elim (this hp)
    · rintro ⟨_, hpFeasible⟩
      exact False.elim (hFeasible hpFeasible)

end Section29
end Chap06
