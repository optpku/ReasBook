module

public import glowinski_admm_counterexample.ReasLib.Convex.EReal.FenchelConjugate
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Proximal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Matrix.Basic

@[expose] public section

namespace ADMM.ImageReduction

/-- The extended-real infimum of a function over a matrix fiber. -/
noncomputable def fiberInf {n m : ℕ} (φ : (Fin n → ℝ) → EReal)
    (L : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → ℝ) : EReal :=
  sInf {r | ∃ x, L.mulVec x = q ∧ r = φ x}

/-- Evaluation of a fiber infimum by its defining set of attained values. -/
theorem fiberInf_apply {n m : ℕ} (φ : (Fin n → ℝ) → EReal)
    (L : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → ℝ) :
    fiberInf φ L q = sInf {r | ∃ x, L.mulVec x = q ∧ r = φ x} := by
  -- Unfolding the named fiber infimum exposes exactly the displayed set.
  rfl

/-- A fiber infimum is bounded above by the value at every displayed point of
the fiber. -/
theorem fiberInf_le_of_mulVec_eq {n m : ℕ} (φ : (Fin n → ℝ) → EReal)
    (L : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} {q : Fin m → ℝ}
    (hx : L.mulVec x = q) :
    fiberInf φ L q ≤ φ x := by
  -- The displayed point contributes its objective value to the defining set.
  rw [fiberInf_apply]
  refine sInf_le ?_
  exact ⟨x, hx, rfl⟩

/-- The extended-real infimum of a function over the affine matrix fiber
`L.mulVec x - b = v`. -/
noncomputable def shiftedFiberInf {n m : ℕ} (φ : (Fin n → ℝ) → EReal)
    (L : Matrix (Fin m) (Fin n) ℝ) (b v : Fin m → ℝ) : EReal :=
  sInf {r | ∃ x, L.mulVec x - b = v ∧ r = φ x}

/-- Evaluation of an affine-fiber infimum by its defining set of attained values. -/
theorem shiftedFiberInf_apply {n m : ℕ} (φ : (Fin n → ℝ) → EReal)
    (L : Matrix (Fin m) (Fin n) ℝ) (b v : Fin m → ℝ) :
    shiftedFiberInf φ L b v =
      sInf {r | ∃ x, L.mulVec x - b = v ∧ r = φ x} := by
  -- Unfolding the affine-fiber infimum exposes the same defining set.
  rfl

/-- A supporting plane whose normal factors through a transpose descends to an
affine matrix fiber and touches it at the displayed image point. -/
private lemma shiftedFiberSupportTransfer {n m : ℕ}
    {φ : (Fin n → ℝ) → EReal} {L : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} {p : Fin m → ℝ} {x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt φ (L.transpose.mulVec p) x) :
    shiftedFiberInf φ L b (L.mulVec x - b) = φ x ∧
      ADMM.IsSubgradientAt (shiftedFiberInf φ L b) p (L.mulVec x - b) := by
  obtain ⟨c, hxvalue, hsupport⟩ := (ADMM.isSubgradientAt_iff _ _ _).mp h
  -- On the displayed fiber, the factored supporting plane has zero increment.
  have hfiberLower : φ x ≤ shiftedFiberInf φ L b (L.mulVec x - b) := by
    rw [shiftedFiberInf_apply]
    refine le_sInf ?_
    intro r hr
    obtain ⟨z, hz, rfl⟩ := hr
    have himage : L.mulVec z - L.mulVec x = 0 := by
      ext i
      have hz_i := congrFun hz i
      simp only [Pi.sub_apply, Pi.zero_apply] at hz_i ⊢
      linarith
    have hdot : dotProduct (L.transpose.mulVec p) (z - x) = 0 := by
      calc
        dotProduct (L.transpose.mulVec p) (z - x) =
            dotProduct (z - x) (L.transpose.mulVec p) := dotProduct_comm _ _
        _ = dotProduct p (L.mulVec (z - x)) :=
          Matrix.dotProduct_transpose_mulVec L (z - x) p
        _ = 0 := by rw [Matrix.mulVec_sub, himage, dotProduct_zero]
    simpa only [hdot, EReal.coe_zero, add_zero] using hsupport z
  have hfiberUpper : shiftedFiberInf φ L b (L.mulVec x - b) ≤ φ x := by
    rw [shiftedFiberInf_apply]
    refine sInf_le ?_
    exact ⟨x, rfl, rfl⟩
  have htouch : shiftedFiberInf φ L b (L.mulVec x - b) = φ x :=
    le_antisymm hfiberUpper hfiberLower
  refine ⟨htouch, ?_⟩
  rw [ADMM.isSubgradientAt_iff]
  refine ⟨c, hxvalue ▸ htouch, ?_⟩
  intro v
  -- Every point in a target fiber inherits the original supporting inequality.
  rw [htouch]
  rw [shiftedFiberInf_apply]
  refine le_sInf ?_
  intro r hr
  obtain ⟨z, hz, rfl⟩ := hr
  have himage : L.mulVec z - L.mulVec x = v - (L.mulVec x - b) := by
    ext i
    have hz_i := congrFun hz i
    simp only [Pi.sub_apply] at hz_i ⊢
    linarith
  have hdot : dotProduct (L.transpose.mulVec p) (z - x) =
      dotProduct p (v - (L.mulVec x - b)) := by
    calc
      dotProduct (L.transpose.mulVec p) (z - x) =
          dotProduct (z - x) (L.transpose.mulVec p) := dotProduct_comm _ _
      _ = dotProduct p (L.mulVec (z - x)) :=
        Matrix.dotProduct_transpose_mulVec L (z - x) p
      _ = dotProduct p (v - (L.mulVec x - b)) := by
        rw [Matrix.mulVec_sub, himage]
  rw [← hdot]
  exact hsupport z

/-- A pointwise affine difference is bounded above by the Fenchel conjugate. -/
private lemma affineDifference_le_fenchelConjugate {n : ℕ}
    (φ : (Fin n → ℝ) → EReal) (x p : Fin n → ℝ) :
    ((dotProduct x p : ℝ) : EReal) - φ x ≤
      ERealConvex.fenchelConjugate φ p := by
  -- The chosen point is one of the affine differences in the defining supremum.
  rw [ERealConvex.fenchelConjugate_apply]
  refine le_sSup ?_
  exact ⟨x, rfl⟩

/-- At a finite supporting point, the Fenchel conjugate attains the associated
affine intercept. -/
private lemma fenchelConjugate_eq_of_subgradient {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {p x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt φ p x) :
    ERealConvex.fenchelConjugate φ p =
      ((dotProduct x p : ℝ) : EReal) - φ x := by
  obtain ⟨c, hxvalue, hsupport⟩ := (ADMM.isSubgradientAt_iff _ _ _).mp h
  apply le_antisymm
  · rw [ERealConvex.fenchelConjugate_apply]
    refine sSup_le ?_
    intro r hr
    obtain ⟨z, rfl⟩ := hr
    by_cases hztop : φ z = ⊤
    · simp [hztop]
    · have hzbot : φ z ≠ ⊥ := by
        intro hzbot
        have hzsupport := hsupport z
        rw [hxvalue, hzbot] at hzsupport
        have hfinite : (((c + dotProduct p (z - x) : ℝ) : EReal)) ≤ ⊥ := by
          simpa only [← EReal.coe_add] using hzsupport
        exact EReal.coe_ne_bot _ (le_bot_iff.mp hfinite)
      let d := (φ z).toReal
      have hzvalue : (d : EReal) = φ z := EReal.coe_toReal hztop hzbot
      have hdot : dotProduct p (z - x) = dotProduct z p - dotProduct x p := by
        rw [dotProduct_sub, dotProduct_comm p z, dotProduct_comm p x]
      have hzsupport := hsupport z
      rw [hxvalue, ← hzvalue, hdot, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hzsupport
      rw [← hzvalue, hxvalue, ← EReal.coe_sub, ← EReal.coe_sub,
        EReal.coe_le_coe_iff]
      linarith
  · exact affineDifference_le_fenchelConjugate φ x p

/-- At every finite point, the Fenchel biconjugate is bounded above by the
original function. -/
private lemma fenchelBiconjugate_le_of_finite {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {c : ℝ}
    (hx : φ x = c) :
    ERealConvex.fenchelBiconjugate φ x ≤ φ x := by
  rw [ERealConvex.fenchelBiconjugate_apply,
    ERealConvex.fenchelConjugate_apply]
  refine sSup_le ?_
  intro r hr
  obtain ⟨p, rfl⟩ := hr
  have hlower := affineDifference_le_fenchelConjugate φ x p
  have hxbot : φ x ≠ ⊥ := by
    rw [hx]
    exact EReal.coe_ne_bot c
  have hxtop : φ x ≠ ⊤ := by
    rw [hx]
    exact EReal.coe_ne_top c
  have hsum : ((dotProduct x p : ℝ) : EReal) ≤
      ERealConvex.fenchelConjugate φ p + φ x :=
    (EReal.sub_le_iff_le_add (.inl hxbot) (.inl hxtop)).mp hlower
  rw [dotProduct_comm p x]
  exact EReal.sub_le_of_le_add' hsum

/-- Fenchel biconjugation preserves a finite supporting plane and its touching
value. -/
private lemma fenchelBiconjugateSupport {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {p x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt φ p x) :
    ERealConvex.fenchelBiconjugate φ x = φ x ∧
      ADMM.IsSubgradientAt (ERealConvex.fenchelBiconjugate φ) p x := by
  obtain ⟨c, hxvalue, hsupport⟩ := (ADMM.isSubgradientAt_iff _ _ _).mp h
  have hconjugate := fenchelConjugate_eq_of_subgradient h
  have hlower : φ x ≤ ERealConvex.fenchelBiconjugate φ x := by
    rw [ERealConvex.fenchelBiconjugate_apply,
      ERealConvex.fenchelConjugate_apply]
    refine le_trans ?_ (le_sSup ⟨p, rfl⟩)
    rw [hconjugate, hxvalue, ← EReal.coe_sub, ← EReal.coe_sub,
      EReal.coe_le_coe_iff]
    rw [dotProduct_comm p x]
    ring_nf
    exact le_rfl
  have htouch : ERealConvex.fenchelBiconjugate φ x = φ x :=
    le_antisymm (fenchelBiconjugate_le_of_finite hxvalue) hlower
  refine ⟨htouch, ?_⟩
  rw [ADMM.isSubgradientAt_iff]
  refine ⟨c, htouch.trans hxvalue, ?_⟩
  intro y
  -- The same conjugate term supplies the biconjugate support at every point.
  rw [htouch]
  rw [ERealConvex.fenchelBiconjugate_apply,
    ERealConvex.fenchelConjugate_apply]
  refine le_trans ?_ (le_sSup ⟨p, rfl⟩)
  rw [hconjugate, hxvalue, ← EReal.coe_sub, ← EReal.coe_add,
    ← EReal.coe_sub, EReal.coe_le_coe_iff]
  rw [dotProduct_sub]
  rw [dotProduct_comm x p]
  ring_nf
  exact le_rfl

/-- A real affine epigraph halfspace is convex and closed. -/
private lemma affineEpigraphHalfspace_closedConvex {n : ℕ}
    (p : Fin n → ℝ) (a : ℝ) :
    Convex ℝ {z : (Fin n → ℝ) × ℝ |
        (((dotProduct z.1 p - a : ℝ) : EReal)) ≤ (z.2 : EReal)} ∧
      IsClosed {z : (Fin n → ℝ) × ℝ |
        (((dotProduct z.1 p - a : ℝ) : EReal)) ≤ (z.2 : EReal)} := by
  have hset :
      {z : (Fin n → ℝ) × ℝ |
          (((dotProduct z.1 p - a : ℝ) : EReal)) ≤ (z.2 : EReal)} =
        {z : (Fin n → ℝ) × ℝ | dotProduct z.1 p - a ≤ z.2} := by
    ext z
    exact EReal.coe_le_coe_iff
  rw [hset]
  constructor
  · rw [convex_iff_add_mem]
    intro u hu v hv s t hs ht hst
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      add_dotProduct]
    rw [smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
    have hu' := mul_le_mul_of_nonneg_left hu hs
    have hv' := mul_le_mul_of_nonneg_left hv ht
    calc
      s * dotProduct u.1 p + t * dotProduct v.1 p - a =
          s * dotProduct u.1 p + t * dotProduct v.1 p - (s + t) * a := by
        rw [hst]
        ring
      _ = s * (dotProduct u.1 p - a) + t * (dotProduct v.1 p - a) := by
        ring
      _ ≤ s * u.2 + t * v.2 := add_le_add hu' hv'
  · exact isClosed_le
      ((continuous_fst.dotProduct continuous_const).sub continuous_const)
      continuous_snd

/-- The biconjugate epigraph inequality is the family of all conjugate affine
inequalities. -/
private lemma fenchelBiconjugate_le_coe_iff {n : ℕ}
    (φ : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (t : ℝ) :
    ERealConvex.fenchelBiconjugate φ x ≤ (t : EReal) ↔
      ∀ p, ((dotProduct p x : ℝ) : EReal) -
        ERealConvex.fenchelConjugate φ p ≤ (t : EReal) := by
  rw [ERealConvex.fenchelBiconjugate_apply,
    ERealConvex.fenchelConjugate_apply]
  constructor
  · intro h p
    exact (affineDifference_le_fenchelConjugate
      (ERealConvex.fenchelConjugate φ) p x).trans h
  · intro h
    refine sSup_le ?_
    intro r hr
    obtain ⟨p, rfl⟩ := hr
    exact h p

/-- A Fenchel biconjugate with a finite touching support plane is closed,
proper, and convex. -/
private lemma fenchelBiconjugate_isClosedProperConvex_of_subgradient {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {p x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt φ p x) :
    ADMM.IsClosedProperConvex (ERealConvex.fenchelBiconjugate φ) := by
  obtain ⟨c, hxvalue, hsupport⟩ := (ADMM.isSubgradientAt_iff _ _ _).mp h
  have hconjugate := fenchelConjugate_eq_of_subgradient h
  have hbiconjugate := fenchelBiconjugateSupport h
  have hconjugate_ne_bot (r : Fin n → ℝ) :
      ERealConvex.fenchelConjugate φ r ≠ ⊥ := by
    intro hrbot
    have hlower := affineDifference_le_fenchelConjugate φ x r
    rw [hrbot, hxvalue, ← EReal.coe_sub] at hlower
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hlower)
  have hepi :
      {z : (Fin n → ℝ) × ℝ |
          ERealConvex.fenchelBiconjugate φ z.1 ≤ (z.2 : EReal)} =
        ⋂ r, {z : (Fin n → ℝ) × ℝ |
          ((dotProduct r z.1 : ℝ) : EReal) -
            ERealConvex.fenchelConjugate φ r ≤ (z.2 : EReal)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact fenchelBiconjugate_le_coe_iff φ z.1 z.2
  refine ADMM.IsClosedProperConvex.ofEpigraph ?_ ?_ ?_ ?_
  · rw [hepi]
    refine convex_iInter fun r ↦ ?_
    by_cases hrtop : ERealConvex.fenchelConjugate φ r = ⊤
    · have hset :
          {z : (Fin n → ℝ) × ℝ |
              ((dotProduct r z.1 : ℝ) : EReal) -
                ERealConvex.fenchelConjugate φ r ≤ (z.2 : EReal)} = Set.univ := by
          ext z
          simp [hrtop]
      rw [hset]
      exact convex_univ
    · let a := (ERealConvex.fenchelConjugate φ r).toReal
      have hrvalue : (a : EReal) = ERealConvex.fenchelConjugate φ r :=
        EReal.coe_toReal hrtop (hconjugate_ne_bot r)
      have hset :
          {z : (Fin n → ℝ) × ℝ |
              ((dotProduct r z.1 : ℝ) : EReal) -
                ERealConvex.fenchelConjugate φ r ≤ (z.2 : EReal)} =
            {z : (Fin n → ℝ) × ℝ |
              (((dotProduct z.1 r - a : ℝ) : EReal)) ≤ (z.2 : EReal)} := by
        ext z
        simp only [Set.mem_setOf_eq]
        rw [← hrvalue, ← EReal.coe_sub, dotProduct_comm r z.1]
      rw [hset]
      exact (affineEpigraphHalfspace_closedConvex r a).1
  · rw [hepi]
    refine isClosed_iInter fun r ↦ ?_
    by_cases hrtop : ERealConvex.fenchelConjugate φ r = ⊤
    · have hset :
          {z : (Fin n → ℝ) × ℝ |
              ((dotProduct r z.1 : ℝ) : EReal) -
                ERealConvex.fenchelConjugate φ r ≤ (z.2 : EReal)} = Set.univ := by
          ext z
          simp [hrtop]
      rw [hset]
      exact isClosed_univ
    · let a := (ERealConvex.fenchelConjugate φ r).toReal
      have hrvalue : (a : EReal) = ERealConvex.fenchelConjugate φ r :=
        EReal.coe_toReal hrtop (hconjugate_ne_bot r)
      have hset :
          {z : (Fin n → ℝ) × ℝ |
              ((dotProduct r z.1 : ℝ) : EReal) -
                ERealConvex.fenchelConjugate φ r ≤ (z.2 : EReal)} =
            {z : (Fin n → ℝ) × ℝ |
              (((dotProduct z.1 r - a : ℝ) : EReal)) ≤ (z.2 : EReal)} := by
        ext z
        simp only [Set.mem_setOf_eq]
        rw [← hrvalue, ← EReal.coe_sub, dotProduct_comm r z.1]
      rw [hset]
      exact (affineEpigraphHalfspace_closedConvex r a).2
  · intro y hybot
    have hlower := affineDifference_le_fenchelConjugate
      (ERealConvex.fenchelConjugate φ) p y
    rw [← ERealConvex.fenchelBiconjugate_apply] at hlower
    rw [hybot, hconjugate, hxvalue, ← EReal.coe_sub,
      ← EReal.coe_sub] at hlower
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hlower)
  · have hxtop : ERealConvex.fenchelBiconjugate φ x ≠ ⊤ := by
      rw [hbiconjugate.1, hxvalue]
      exact EReal.coe_ne_top c
    exact ⟨x, hxtop⟩

/-- Division by a positive real scalar preserves closed proper convexity. -/
private lemma divPositive_isClosedProperConvex {n : ℕ}
    {ψ : (Fin n → ℝ) → EReal} (hψ : ADMM.IsClosedProperConvex ψ)
    {β : ℝ} (hβ : 0 < β) :
    ADMM.IsClosedProperConvex (fun q ↦ ψ q / (β : EReal)) := by
  have hβereal : (0 : EReal) < (β : EReal) := EReal.coe_pos.mpr hβ
  have hepi :
      {z : (Fin n → ℝ) × ℝ | ψ z.1 / (β : EReal) ≤ (z.2 : EReal)} =
        (fun z : (Fin n → ℝ) × ℝ ↦ (z.1, β * z.2)) ⁻¹'
          {z : (Fin n → ℝ) × ℝ | ψ z.1 ≤ (z.2 : EReal)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [EReal.div_le_iff_le_mul hβereal (EReal.coe_ne_top β), ← EReal.coe_mul]
  refine ADMM.IsClosedProperConvex.ofEpigraph ?_ ?_ ?_ ?_
  · rw [convex_iff_add_mem]
    intro u hu v hv s t hs ht hst
    have hu' : ψ u.1 ≤ ((β * u.2 : ℝ) : EReal) := by
      exact (EReal.div_le_iff_le_mul hβereal (EReal.coe_ne_top β)).mp hu
    have hv' : ψ v.1 ≤ ((β * v.2 : ℝ) : EReal) := by
      exact (EReal.div_le_iff_le_mul hβereal (EReal.coe_ne_top β)).mp hv
    have huepi : (u.1, β * u.2) ∈
        {z : (Fin n → ℝ) × ℝ | ψ z.1 ≤ (z.2 : EReal)} := hu'
    have hvepi : (v.1, β * v.2) ∈
        {z : (Fin n → ℝ) × ℝ | ψ z.1 ≤ (z.2 : EReal)} := hv'
    have hcombo := hψ.epigraph_convex huepi hvepi hs ht hst
    apply (EReal.div_le_iff_le_mul hβereal (EReal.coe_ne_top β)).mpr
    change ψ (s • u.1 + t • v.1) ≤
      (((s * (β * u.2) + t * (β * v.2) : ℝ)) : EReal) at hcombo
    have hscale : s * (β * u.2) + t * (β * v.2) =
        β * (s * u.2 + t * v.2) := by ring
    rw [hscale] at hcombo
    simpa only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul, ← EReal.coe_mul] using hcombo
  · rw [hepi]
    exact hψ.epigraph_closed.preimage
      (Continuous.prodMk continuous_fst (continuous_const.mul continuous_snd))
  · intro q
    induction hq : ψ q using EReal.rec with
    | bot => exact False.elim (hψ.ne_bot q hq)
    | coe r =>
      rw [← EReal.coe_div]
      exact EReal.coe_ne_bot (r / β)
    | top =>
      rw [EReal.top_div_of_pos_ne_top hβereal (EReal.coe_ne_top β)]
      exact top_ne_bot
  · obtain ⟨q, hqtop⟩ := hψ.exists_ne_top
    have hqbot := hψ.ne_bot q
    let r := (ψ q).toReal
    have hqvalue : (r : EReal) = ψ q := EReal.coe_toReal hqtop hqbot
    have hfinite : ψ q / (β : EReal) ≠ ⊤ := by
      rw [← hqvalue, ← EReal.coe_div]
      exact EReal.coe_ne_top (r / β)
    exact ⟨q, hfinite⟩

/-- Dividing a supported extended-real function by a positive scalar divides
its supporting normal by the same scalar. -/
private lemma isSubgradientAt_divPositive {n : ℕ}
    {ψ : (Fin n → ℝ) → EReal} {p x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt ψ p x) {β : ℝ} (hβ : 0 < β) :
    ADMM.IsSubgradientAt (fun q ↦ ψ q / (β : EReal)) (β⁻¹ • p) x := by
  obtain ⟨c, hxvalue, hsupport⟩ := (ADMM.isSubgradientAt_iff _ _ _).mp h
  rw [ADMM.isSubgradientAt_iff]
  refine ⟨c / β, ?_, ?_⟩
  · rw [hxvalue, ← EReal.coe_div]
  · intro z
    by_cases hztop : ψ z = ⊤
    · rw [hztop, EReal.top_div_of_pos_ne_top
        (EReal.coe_pos.mpr hβ) (EReal.coe_ne_top β)]
      exact le_top
    · have hzbot : ψ z ≠ ⊥ := by
        intro hzbot
        have hzsupport := hsupport z
        rw [hxvalue, hzbot, ← EReal.coe_add] at hzsupport
        exact EReal.coe_ne_bot _ (le_bot_iff.mp hzsupport)
      let d := (ψ z).toReal
      have hzvalue : (d : EReal) = ψ z := EReal.coe_toReal hztop hzbot
      have hzsupport := hsupport z
      rw [hxvalue, ← hzvalue, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hzsupport
      rw [hxvalue, ← hzvalue, ← EReal.coe_div, ← EReal.coe_div,
        ← EReal.coe_add, EReal.coe_le_coe_iff]
      simp only [smul_dotProduct, smul_eq_mul]
      have hβne : β ≠ 0 := hβ.ne'
      calc
        c / β + β⁻¹ * dotProduct p (z - x) =
            (c + dotProduct p (z - x)) / β := by field_simp
        _ ≤ d / β := div_le_div_of_nonneg_right hzsupport hβ.le

/-- A finite support plane supplies the complete positive-scaled biconjugate
interface: closed proper convexity, touching, and the scaled support normal. -/
private lemma scaledFenchelBiconjugateSupport {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {p x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt φ p x) {β : ℝ} (hβ : 0 < β) :
    ADMM.IsClosedProperConvex
        (fun q ↦ ERealConvex.fenchelBiconjugate φ q / (β : EReal)) ∧
      ERealConvex.fenchelBiconjugate φ x = φ x ∧
      ADMM.IsSubgradientAt
        (fun q ↦ ERealConvex.fenchelBiconjugate φ q / (β : EReal))
        (β⁻¹ • p) x := by
  have hsupport := fenchelBiconjugateSupport h
  -- Closed proper convexity and the scaled normal are projections of the two interfaces.
  exact ⟨divPositive_isClosedProperConvex
      (fenchelBiconjugate_isClosedProperConvex_of_subgradient h) hβ,
    hsupport.1, isSubgradientAt_divPositive hsupport.2 hβ⟩

/-- The affine fiber construction with zero shift is the ordinary matrix
fiber construction. -/
private lemma shiftedFiberInf_zero {n m : ℕ} (φ : (Fin n → ℝ) → EReal)
    (L : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → ℝ) :
    shiftedFiberInf φ L 0 q = fiberInf φ L q := by
  rw [shiftedFiberInf_apply, fiberInf_apply]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, sub_zero]

/-- A transpose-factored supporting plane descends to an ordinary matrix
fiber and touches it at the displayed image. -/
private lemma fiberSupportTransfer {n m : ℕ}
    {φ : (Fin n → ℝ) → EReal} {L : Matrix (Fin m) (Fin n) ℝ}
    {p : Fin m → ℝ} {x : Fin n → ℝ}
    (h : ADMM.IsSubgradientAt φ (L.transpose.mulVec p) x) :
    fiberInf φ L (L.mulVec x) = φ x ∧
      ADMM.IsSubgradientAt (fiberInf φ L) p (L.mulVec x) := by
  have hshift := shiftedFiberSupportTransfer (b := (0 : Fin m → ℝ)) h
  have hzero : shiftedFiberInf φ L 0 = fiberInf φ L := by
    funext q
    exact shiftedFiberInf_zero φ L q
  rw [hzero] at hshift
  simpa only [sub_zero] using hshift

/-- The first image objective after Fenchel biconjugation and scaling by `β`. -/
noncomputable def reducedFirst {n m : ℕ} (f : (Fin n → ℝ) → EReal)
    (A : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) : (Fin m → ℝ) → EReal :=
  fun q ↦ ERealConvex.fenchelBiconjugate (fiberInf f A) q / (β : EReal)

/-- Evaluation of the first scaled biconjugated image objective. -/
theorem reducedFirst_apply {n m : ℕ} (f : (Fin n → ℝ) → EReal)
    (A : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) (q : Fin m → ℝ) :
    reducedFirst f A β q =
      ERealConvex.fenchelBiconjugate (fiberInf f A) q / (β : EReal) := by
  -- Function application reduces the first objective to its defining quotient.
  rfl

/-- The second affine-image objective after Fenchel biconjugation and scaling by `β`. -/
noncomputable def reducedSecond {n m : ℕ} (g : (Fin n → ℝ) → EReal)
    (B : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (β : ℝ) :
    (Fin m → ℝ) → EReal :=
  fun v ↦ ERealConvex.fenchelBiconjugate (shiftedFiberInf g B b) v / (β : EReal)

/-- Evaluation of the second scaled biconjugated affine-image objective. -/
theorem reducedSecond_apply {n m : ℕ} (g : (Fin n → ℝ) → EReal)
    (B : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (β : ℝ)
    (v : Fin m → ℝ) :
    reducedSecond g B b β v =
      ERealConvex.fenchelBiconjugate (shiftedFiberInf g B b) v /
        (β : EReal) := by
  -- Function application reduces the second objective to its defining quotient.
  rfl

end ADMM.ImageReduction

namespace ADMM

/-- A finite minimizer of a convex objective plus an affine quadratic has the
expected first-order supporting normal for the convex term. -/
lemma isSubgradientAtOfAugmentedMinimizer {n m : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    (L : Matrix (Fin m) (Fin n) ℝ) (d multiplier : Fin m → ℝ)
    {β : ℝ} (hβ : 0 < β) (x : Fin n → ℝ)
    (hmin : IsFiniteMinimizer
      (fun z ↦ φ z + dotProduct multiplier (L.mulVec z + d) +
        (((β / 2) * dotProduct (L.mulVec z + d) (L.mulVec z + d) : ℝ) : EReal)) x) :
    IsSubgradientAt φ
      (-L.transpose.mulVec (multiplier + β • (L.mulVec x + d))) x := by
  obtain ⟨cJ, hxJ, hminimum⟩ := (isFiniteMinimizer_iff _ _).mp hmin
  let rx := L.mulVec x + d
  let smoothX := dotProduct multiplier rx + (β / 2) * dotProduct rx rx
  have hxJ' : φ x + (smoothX : EReal) = (cJ : EReal) := by
    dsimp only [smoothX, rx]
    rw [EReal.coe_add, ← add_assoc]
    exact hxJ
  let cx := cJ - smoothX
  have hxvalue : φ x = (cx : EReal) := by
    have hcancel := congrArg (fun a : EReal ↦ a - (smoothX : EReal)) hxJ'
    simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub, cx] using hcancel
  rw [isSubgradientAt_iff]
  refine ⟨cx, hxvalue, ?_⟩
  intro z
  by_cases hztop : φ z = ⊤
  · rw [hztop]
    exact le_top
  · have hzbot : φ z ≠ ⊥ := hφ.ne_bot z
    let cz := (φ z).toReal
    have hzvalue : (cz : EReal) = φ z := EReal.coe_toReal hztop hzbot
    let rz := L.mulVec z + d
    let delta := rz - rx
    let Q := dotProduct delta delta
    let A := cz - cx + dotProduct (multiplier + β • rx) delta
    have hQ : 0 ≤ Q := by
      dsimp only [Q]
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (delta i)
    have hdirection (t : ℝ) (htpos : 0 < t) (htlt : t < 1) :
        0 ≤ A + (β / 2) * t * Q := by
      let w := (1 - t) • x + t • z
      have hxepi : (x, cx) ∈
          {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
        change φ x ≤ (cx : EReal)
        rw [hxvalue]
      have hzepi : (z, cz) ∈
          {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
        change φ z ≤ (cz : EReal)
        rw [hzvalue]
      have hcoeffsum : (1 - t) + t = 1 := by ring
      have hconvex := hφ.epigraph_convex hxepi hzepi
        (sub_nonneg.mpr htlt.le) htpos.le hcoeffsum
      have hφw : φ w ≤ (((1 - t) * cx + t * cz : ℝ) : EReal) := by
        simpa only [w, Set.mem_setOf_eq, Prod.smul_mk, Prod.fst_add,
          Prod.snd_add, Prod.fst, Prod.snd, smul_eq_mul] using hconvex
      have hresidual : L.mulVec w + d = rx + t • delta := by
        ext i
        simp only [w, rx, rz, delta, Matrix.mulVec_add, Matrix.mulVec_smul,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hsmooth :
          dotProduct multiplier (L.mulVec w + d) +
              (β / 2) * dotProduct (L.mulVec w + d) (L.mulVec w + d) =
            smoothX + t * dotProduct (multiplier + β • rx) delta +
              (β / 2) * t ^ 2 * Q := by
        rw [hresidual]
        simp only [smoothX, Q, add_dotProduct, dotProduct_add, smul_dotProduct,
          dotProduct_smul, smul_eq_mul]
        rw [dotProduct_comm rx delta]
        ring
      have hupper :
          φ w + dotProduct multiplier (L.mulVec w + d) +
              (((β / 2) * dotProduct (L.mulVec w + d) (L.mulVec w + d) : ℝ) : EReal) ≤
            (((1 - t) * cx + t * cz +
              (dotProduct multiplier (L.mulVec w + d) +
                (β / 2) * dotProduct (L.mulVec w + d) (L.mulVec w + d)) : ℝ) : EReal) := by
        let smoothW := dotProduct multiplier (L.mulVec w + d) +
          (β / 2) * dotProduct (L.mulVec w + d) (L.mulVec w + d)
        calc
          φ w + ((dotProduct multiplier (L.mulVec w + d) : ℝ) : EReal) +
              (((β / 2) * dotProduct (L.mulVec w + d) (L.mulVec w + d) : ℝ) : EReal) =
              φ w + (smoothW : EReal) := by
            dsimp only [smoothW]
            rw [EReal.coe_add, add_assoc]
          _ ≤ (((1 - t) * cx + t * cz : ℝ) : EReal) + (smoothW : EReal) :=
            (EReal.addLECancellable_coe smoothW).add_le_add_iff_right.mpr hφw
          _ = (((1 - t) * cx + t * cz + smoothW : ℝ) : EReal) := by
            exact (EReal.coe_add _ _).symm
      have hbound := (hminimum w).trans hupper
      rw [hxJ] at hbound
      rw [EReal.coe_le_coe_iff] at hbound
      dsimp only [A]
      rw [hsmooth] at hbound
      dsimp only [cx] at hbound
      nlinarith
    have hA : 0 ≤ A := by
      by_contra hAnot
      have hAneg : A < 0 := lt_of_not_ge hAnot
      have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
      have hhalflt : (1 / 2 : ℝ) < 1 := by norm_num
      by_cases hQzero : Q = 0
      · have hhalf := hdirection (1 / 2) hhalfpos hhalflt
        rw [hQzero] at hhalf
        norm_num at hhalf
        exact hAnot hhalf
      · have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hQzero)
        let t := min (1 / 2 : ℝ) (-A / (β * Q))
        have hdenom : 0 < β * Q := mul_pos hβ hQpos
        have htpos : 0 < t := by
          exact lt_min hhalfpos (div_pos (neg_pos.mpr hAneg) hdenom)
        have htlt : t < 1 := lt_of_le_of_lt (min_le_left _ _) hhalflt
        have htupper : t ≤ -A / (β * Q) := min_le_right _ _
        have hsmall := hdirection t htpos htlt
        have hmul := mul_le_mul_of_nonneg_right htupper (le_of_lt hdenom)
        dsimp only [t] at hsmall hmul
        rw [neg_div] at hsmall
        field_simp at hmul
        have hquad :
            β / 2 * min (1 / 2 : ℝ) (-(A / (β * Q))) * Q ≤ -A / 2 := by
          have htwo : (0 : ℝ) ≤ 2 := by norm_num
          calc
            β / 2 * min (1 / 2 : ℝ) (-(A / (β * Q))) * Q =
                (β * Q * min (1 / 2 : ℝ) (-(A / (β * Q)))) / 2 := by ring
            _ ≤ -A / 2 := div_le_div_of_nonneg_right hmul htwo
        nlinarith [hsmall, hquad]
    -- The directional inequality is exactly the desired supporting-plane inequality.
    rw [hxvalue, ← hzvalue, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hdelta : L.mulVec (z - x) = delta := by
      rw [Matrix.mulVec_sub]
      ext i
      simp only [delta, rz, rx, Pi.sub_apply, Pi.add_apply]
      ring
    have hnormal :
        dotProduct (-L.transpose.mulVec (multiplier + β • rx)) (z - x) =
          -dotProduct (multiplier + β • rx) delta := by
      calc
        dotProduct (-L.transpose.mulVec (multiplier + β • rx)) (z - x) =
            -dotProduct (L.transpose.mulVec (multiplier + β • rx)) (z - x) := by
          rw [neg_dotProduct]
        _ = -dotProduct (z - x) (L.transpose.mulVec (multiplier + β • rx)) := by
          rw [dotProduct_comm]
        _ = -dotProduct (multiplier + β • rx) (L.mulVec (z - x)) := by
          rw [Matrix.dotProduct_transpose_mulVec]
        _ = -dotProduct (multiplier + β • rx) delta := by rw [hdelta]
    rw [hnormal]
    dsimp only [A] at hA
    linarith

namespace Problem

/-- The image-reduced problem has the scaled biconjugated image objectives,
identity constraint matrices, and zero right-hand side. -/
noncomputable def reduced {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ) :
    Problem m m m :=
  ofData (ImageReduction.reducedFirst P.f P.A β)
    (ImageReduction.reducedSecond P.g P.B P.b β) 1 1 0

/-- The first objective of the reduced problem is the scaled first image
objective. -/
theorem reduced_f {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ) :
    (P.reduced β).f = ImageReduction.reducedFirst P.f P.A β := by
  rfl

/-- The second objective of the reduced problem is the scaled affine-image
objective. -/
theorem reduced_g {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ) :
    (P.reduced β).g = ImageReduction.reducedSecond P.g P.B P.b β := by
  rfl

/-- The first constraint matrix of the reduced problem is the identity. -/
theorem reduced_A {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ) :
    (P.reduced β).A = 1 := by
  rfl

/-- The second constraint matrix of the reduced problem is the identity. -/
theorem reduced_B {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ) :
    (P.reduced β).B = 1 := by
  rfl

/-- The right-hand side of the reduced problem is zero. -/
theorem reduced_b {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ) :
    (P.reduced β).b = 0 := by
  rfl

end Problem

namespace Problem.IsKKT

/-- Every KKT primal pair attains the infimum defining the problem's optimal
value. -/
lemma optimalValue_eq_objective {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m}
    {x : Fin n₁ → ℝ} {y : Fin n₂ → ℝ} {multiplier : Fin m → ℝ}
    (h : P.IsKKT x y multiplier) :
    P.optimalValue = P.objective x y := by
  apply le_antisymm (P.optimalValue_le x y h.feasible)
  rw [Problem.optimalValue]
  refine le_sInf ?_
  intro r hr
  obtain ⟨x', y', hfeasible', rfl⟩ := hr
  obtain ⟨cx, hxvalue, hxlower⟩ := (isSubgradientAt_iff _ _ _).mp h.firstStationary
  obtain ⟨cy, hyvalue, hylower⟩ := (isSubgradientAt_iff _ _ _).mp h.secondStationary
  have hfirst := hxlower x'
  have hsecond := hylower y'
  have hresidual : P.A.mulVec (x' - x) + P.B.mulVec (y' - y) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    ext i
    have hfeasible_i := congrFun h.feasible i
    have hfeasible_i' := congrFun hfeasible' i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hfeasible_i hfeasible_i' ⊢
    linarith
  have hdot :
      dotProduct (-P.A.transpose.mulVec multiplier) (x' - x) +
          dotProduct (-P.B.transpose.mulVec multiplier) (y' - y) = 0 := by
    calc
      dotProduct (-P.A.transpose.mulVec multiplier) (x' - x) +
          dotProduct (-P.B.transpose.mulVec multiplier) (y' - y) =
          dotProduct (-multiplier) (P.A.mulVec (x' - x)) +
            dotProduct (-multiplier) (P.B.mulVec (y' - y)) := by
        congr 1
        · calc
            dotProduct (-P.A.transpose.mulVec multiplier) (x' - x) =
                dotProduct (x' - x) (-P.A.transpose.mulVec multiplier) :=
              dotProduct_comm _ _
            _ = dotProduct (x' - x) (P.A.transpose.mulVec (-multiplier)) := by
              rw [Matrix.mulVec_neg]
            _ = dotProduct (-multiplier) (P.A.mulVec (x' - x)) :=
              Matrix.dotProduct_transpose_mulVec P.A (x' - x) (-multiplier)
        · calc
            dotProduct (-P.B.transpose.mulVec multiplier) (y' - y) =
                dotProduct (y' - y) (-P.B.transpose.mulVec multiplier) :=
              dotProduct_comm _ _
            _ = dotProduct (y' - y) (P.B.transpose.mulVec (-multiplier)) := by
              rw [Matrix.mulVec_neg]
            _ = dotProduct (-multiplier) (P.B.mulVec (y' - y)) :=
              Matrix.dotProduct_transpose_mulVec P.B (y' - y) (-multiplier)
      _ = dotProduct (-multiplier)
          (P.A.mulVec (x' - x) + P.B.mulVec (y' - y)) := by
        rw [dotProduct_add]
      _ = 0 := by rw [hresidual, dotProduct_zero]
  have hx'bot : P.f x' ≠ ⊥ := by
    intro hx'bot
    rw [hxvalue, hx'bot, ← EReal.coe_add] at hfirst
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hfirst)
  have hy'bot : P.g y' ≠ ⊥ := by
    intro hy'bot
    rw [hyvalue, hy'bot, ← EReal.coe_add] at hsecond
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hsecond)
  by_cases hx'top : P.f x' = ⊤
  · rw [Problem.objective_apply P x' y', hx'top]
    simp [hy'bot]
  · by_cases hy'top : P.g y' = ⊤
    · rw [Problem.objective_apply P x' y', hy'top]
      simp [hx'bot]
    · let dx := (P.f x').toReal
      let dy := (P.g y').toReal
      have hx'value : (dx : EReal) = P.f x' := EReal.coe_toReal hx'top hx'bot
      have hy'value : (dy : EReal) = P.g y' := EReal.coe_toReal hy'top hy'bot
      rw [hxvalue, ← hx'value, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hfirst
      rw [hyvalue, ← hy'value, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hsecond
      rw [Problem.objective_apply, Problem.objective_apply, hxvalue, hyvalue,
        ← hx'value, ← hy'value, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_le_coe_iff]
      linarith

/-- An original KKT triple supplies the reduced KKT triple, both reduced
regularity facts, the touching values, and the scaled optimal value. -/
lemma reducedBundle {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m}
    {x : Fin n₁ → ℝ} {y : Fin n₂ → ℝ} {multiplier : Fin m → ℝ}
    (h : P.IsKKT x y multiplier) {β : ℝ} (hβ : 0 < β) :
    (P.reduced β).IsKKT (P.A.mulVec x) (P.B.mulVec y - P.b)
        (β⁻¹ • multiplier) ∧
      ADMM.IsClosedProperConvex (P.reduced β).f ∧
      ADMM.IsClosedProperConvex (P.reduced β).g ∧
      (P.reduced β).f (P.A.mulVec x) = P.f x / (β : EReal) ∧
      (P.reduced β).g (P.B.mulVec y - P.b) = P.g y / (β : EReal) ∧
      (P.reduced β).optimalValue = P.optimalValue / (β : EReal) := by
  have hfirstStationary :
      IsSubgradientAt P.f (P.A.transpose.mulVec (-multiplier)) x := by
    simpa only [Matrix.mulVec_neg] using h.firstStationary
  have hsecondStationary :
      IsSubgradientAt P.g (P.B.transpose.mulVec (-multiplier)) y := by
    simpa only [Matrix.mulVec_neg] using h.secondStationary
  have hfirstFiber := ImageReduction.fiberSupportTransfer hfirstStationary
  have hsecondFiber := ImageReduction.shiftedFiberSupportTransfer
    (b := P.b) hsecondStationary
  have hfirstScaled := ImageReduction.scaledFenchelBiconjugateSupport
    hfirstFiber.2 hβ
  have hsecondScaled := ImageReduction.scaledFenchelBiconjugateSupport
    hsecondFiber.2 hβ
  have hfirstDef : ImageReduction.reducedFirst P.f P.A β =
      (fun q ↦ ERealConvex.fenchelBiconjugate
        (ImageReduction.fiberInf P.f P.A) q / (β : EReal)) := by
    funext q
    exact ImageReduction.reducedFirst_apply P.f P.A β q
  have hsecondDef : ImageReduction.reducedSecond P.g P.B P.b β =
      (fun q ↦ ERealConvex.fenchelBiconjugate
        (ImageReduction.shiftedFiberInf P.g P.B P.b) q / (β : EReal)) := by
    funext q
    exact ImageReduction.reducedSecond_apply P.g P.B P.b β q
  rw [← hfirstDef] at hfirstScaled
  rw [← hsecondDef] at hsecondScaled
  have hfeasible : P.A.mulVec x + (P.B.mulVec y - P.b) = 0 := by
    ext i
    have hfeasible_i := congrFun h.feasible i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hfeasible_i ⊢
    linarith
  have hred :
      (P.reduced β).IsKKT (P.A.mulVec x) (P.B.mulVec y - P.b)
        (β⁻¹ • multiplier) := by
    refine Problem.IsKKT.ofConditions ?_ ?_ ?_
    · simpa [Problem.reduced_f, Problem.reduced_A, Matrix.one_mulVec] using
          hfirstScaled.2.2
    · simpa [Problem.reduced_g, Problem.reduced_B, Matrix.one_mulVec] using
          hsecondScaled.2.2
    · simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b,
        Matrix.one_mulVec] using hfeasible
  have hfirstClosed : ADMM.IsClosedProperConvex (P.reduced β).f := by
    simpa only [Problem.reduced_f] using
      hfirstScaled.1
  have hsecondClosed : ADMM.IsClosedProperConvex (P.reduced β).g := by
    simpa only [Problem.reduced_g] using
      hsecondScaled.1
  have hfirstValue :
      (P.reduced β).f (P.A.mulVec x) = P.f x / (β : EReal) := by
    rw [Problem.reduced_f, ImageReduction.reducedFirst_apply,
      hfirstScaled.2.1, hfirstFiber.1]
  have hsecondValue :
      (P.reduced β).g (P.B.mulVec y - P.b) = P.g y / (β : EReal) := by
    rw [Problem.reduced_g, ImageReduction.reducedSecond_apply,
      hsecondScaled.2.1, hsecondFiber.1]
  have horiginalOptimal := optimalValue_eq_objective h
  have hreducedOptimal := optimalValue_eq_objective hred
  obtain ⟨cx, hxvalue, hxlower⟩ := (isSubgradientAt_iff _ _ _).mp h.firstStationary
  obtain ⟨cy, hyvalue, hylower⟩ := (isSubgradientAt_iff _ _ _).mp h.secondStationary
  have hoptimal :
      (P.reduced β).optimalValue = P.optimalValue / (β : EReal) := by
    rw [hreducedOptimal, horiginalOptimal, Problem.objective_apply,
      Problem.objective_apply, hfirstValue, hsecondValue, hxvalue, hyvalue,
      ← EReal.coe_div, ← EReal.coe_div, ← EReal.coe_add,
      ← EReal.coe_add, ← EReal.coe_div]
    congr 1
    field_simp
  -- The bundle exposes only stable projections to the public reduced-problem API.
  exact ⟨hred, hfirstClosed, hsecondClosed, hfirstValue, hsecondValue, hoptimal⟩

/-- An original KKT triple induces the scaled image-coordinate KKT triple of
the reduced problem. -/
theorem reduced {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m}
    {x : Fin n₁ → ℝ} {y : Fin n₂ → ℝ} {multiplier : Fin m → ℝ}
    (h : P.IsKKT x y multiplier) {β : ℝ} (hβ : 0 < β) :
    (P.reduced β).IsKKT (P.A.mulVec x) (P.B.mulVec y - P.b)
      (β⁻¹ • multiplier) := by
  -- Project the reduced KKT witness from the support-plane bundle.
  exact (reducedBundle h hβ).1

end Problem.IsKKT

namespace Problem

/-- For an exact positive-parameter trajectory of a closed proper convex
problem with a KKT point, the reduced first objective is closed proper convex. -/
theorem reducedFirst_isClosedProperConvex {n₁ n₂ m : ℕ}
    (P : Problem n₁ n₂ m) (hf : ADMM.IsClosedProperConvex P.f)
    (hg : ADMM.IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    ADMM.IsClosedProperConvex (P.reduced β).f := by
  obtain ⟨x, y, multiplier, h⟩ := hKKT
  -- One original KKT support plane proves regularity of the first reduced objective.
  exact (Problem.IsKKT.reducedBundle h hβ).2.1

/-- For an exact positive-parameter trajectory of a closed proper convex
problem with a KKT point, the reduced second objective is closed proper convex. -/
theorem reducedSecond_isClosedProperConvex {n₁ n₂ m : ℕ}
    (P : Problem n₁ n₂ m) (hf : ADMM.IsClosedProperConvex P.f)
    (hg : ADMM.IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    ADMM.IsClosedProperConvex (P.reduced β).g := by
  obtain ⟨x, y, multiplier, h⟩ := hKKT
  -- The affine-image support plane gives the second regularity projection.
  exact (Problem.IsKKT.reducedBundle h hβ).2.2.1

/-- A closed proper convex problem with an original KKT point induces a KKT
point for its image reduction along every exact positive-parameter trajectory. -/
theorem reduced_exists_kkt {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : ADMM.IsClosedProperConvex P.f) (hg : ADMM.IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    ∃ q v u, (P.reduced β).IsKKT q v u := by
  obtain ⟨x, y, multiplier, h⟩ := hKKT
  -- Use the image coordinates and scaled multiplier from the reduced bundle.
  exact ⟨P.A.mulVec x, P.B.mulVec y - P.b, β⁻¹ • multiplier,
    (Problem.IsKKT.reducedBundle h hβ).1⟩

/-- The image-reduced optimal value is the original optimal value divided by
the positive penalty parameter. -/
theorem reduced_optimalValue {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : ADMM.IsClosedProperConvex P.f) (hg : ADMM.IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ) :
    (P.reduced β).optimalValue = P.optimalValue / (β : EReal) := by
  obtain ⟨x, y, multiplier, h⟩ := hKKT
  -- Both KKT pairs attain their defining infima, leaving only positive scaling.
  exact (Problem.IsKKT.reducedBundle h hβ).2.2.2.2.2

end Problem

namespace Trajectory

/-- A first-block update carries the touching fiber values and the reduced
supporting normal in proximal center-minus-point form. -/
private lemma firstImageSupport {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) {β γ : ℝ} (hβ : 0 < β)
    (z : Trajectory P β γ) (k : ℕ) :
    ImageReduction.fiberInf P.f P.A (P.A.mulVec (z.x (k + 1))) =
        ERealConvex.fenchelBiconjugate (ImageReduction.fiberInf P.f P.A)
          (P.A.mulVec (z.x (k + 1))) ∧
      ERealConvex.fenchelBiconjugate (ImageReduction.fiberInf P.f P.A)
          (P.A.mulVec (z.x (k + 1))) = P.f (z.x (k + 1)) ∧
      IsSubgradientAt (P.reduced β).f
        ((-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k) -
          P.A.mulVec (z.x (k + 1)))
        (P.A.mulVec (z.x (k + 1))) := by
  have hminimum : IsFiniteMinimizer
      (fun w ↦ P.f w +
        dotProduct (z.multiplier k) (P.A.mulVec w + (P.B.mulVec (z.y k) - P.b)) +
        (((β / 2) * dotProduct
          (P.A.mulVec w + (P.B.mulVec (z.y k) - P.b))
          (P.A.mulVec w + (P.B.mulVec (z.y k) - P.b)) : ℝ) : EReal))
      (z.x (k + 1)) := by
    have hobjective : P.firstBlockObjective β (z.multiplier k) (z.y k) =
        (fun w ↦ P.f w +
          dotProduct (z.multiplier k) (P.A.mulVec w + (P.B.mulVec (z.y k) - P.b)) +
          (((β / 2) * dotProduct
            (P.A.mulVec w + (P.B.mulVec (z.y k) - P.b))
            (P.A.mulVec w + (P.B.mulVec (z.y k) - P.b)) : ℝ) : EReal)) := by
      funext w
      rw [Problem.firstBlockObjective_apply, add_sub_assoc]
    rw [← hobjective]
    exact z.firstMinimizes k
  have horiginal := isSubgradientAtOfAugmentedMinimizer hf P.A
    (P.B.mulVec (z.y k) - P.b) (z.multiplier k) hβ (z.x (k + 1)) hminimum
  have horiginal' : IsSubgradientAt P.f
      (P.A.transpose.mulVec
        (-(z.multiplier k + β •
          (P.A.mulVec (z.x (k + 1)) + (P.B.mulVec (z.y k) - P.b)))))
      (z.x (k + 1)) := by
    simpa only [Matrix.mulVec_neg] using horiginal
  have hfiber := ImageReduction.fiberSupportTransfer horiginal'
  have hscaled := ImageReduction.scaledFenchelBiconjugateSupport hfiber.2 hβ
  have hdef : ImageReduction.reducedFirst P.f P.A β =
      (fun q ↦ ERealConvex.fenchelBiconjugate
        (ImageReduction.fiberInf P.f P.A) q / (β : EReal)) := by
    funext q
    exact ImageReduction.reducedFirst_apply P.f P.A β q
  rw [← hdef] at hscaled
  have hnormal :
      β⁻¹ •
          (-(z.multiplier k + β •
            (P.A.mulVec (z.x (k + 1)) + (P.B.mulVec (z.y k) - P.b)))) =
        (-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k) -
          P.A.mulVec (z.x (k + 1)) := by
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hβ.ne']
    ring
  have hsubgradient : IsSubgradientAt (P.reduced β).f
      ((-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k) -
        P.A.mulVec (z.x (k + 1)))
      (P.A.mulVec (z.x (k + 1))) := by
    rw [Problem.reduced_f]
    rw [hnormal] at hscaled
    exact hscaled.2.2
  -- Touching of the fiber and biconjugate gives the two value identities.
  exact ⟨hscaled.2.1.symm, hscaled.2.1.trans hfiber.1, hsubgradient⟩

/-- A second-block update carries the touching affine-fiber values and the
reduced supporting normal in proximal center-minus-point form. -/
private lemma secondImageSupport {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hg : IsClosedProperConvex P.g) {β γ : ℝ} (hβ : 0 < β)
    (z : Trajectory P β γ) (k : ℕ) :
    ImageReduction.shiftedFiberInf P.g P.B P.b
        (P.B.mulVec (z.y (k + 1)) - P.b) =
      ERealConvex.fenchelBiconjugate
        (ImageReduction.shiftedFiberInf P.g P.B P.b)
        (P.B.mulVec (z.y (k + 1)) - P.b) ∧
      ERealConvex.fenchelBiconjugate
          (ImageReduction.shiftedFiberInf P.g P.B P.b)
          (P.B.mulVec (z.y (k + 1)) - P.b) = P.g (z.y (k + 1)) ∧
      IsSubgradientAt (P.reduced β).g
        ((-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k) -
          (P.B.mulVec (z.y (k + 1)) - P.b))
        (P.B.mulVec (z.y (k + 1)) - P.b) := by
  have hminimum : IsFiniteMinimizer
      (fun w ↦ P.g w +
        dotProduct (z.multiplier k) (P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b)) +
        (((β / 2) * dotProduct
          (P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b))
          (P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b)) : ℝ) : EReal))
      (z.y (k + 1)) := by
    have hresidual (w : Fin n₂ → ℝ) :
        P.A.mulVec (z.x (k + 1)) + P.B.mulVec w - P.b =
          P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b) := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have hobjective : P.secondBlockObjective β (z.multiplier k) (z.x (k + 1)) =
        (fun w ↦ P.g w +
          dotProduct (z.multiplier k) (P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b)) +
          (((β / 2) * dotProduct
            (P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b))
            (P.B.mulVec w + (P.A.mulVec (z.x (k + 1)) - P.b)) : ℝ) : EReal)) := by
      funext w
      rw [Problem.secondBlockObjective_apply, hresidual]
    rw [← hobjective]
    exact z.secondMinimizes k
  have horiginal := isSubgradientAtOfAugmentedMinimizer hg P.B
    (P.A.mulVec (z.x (k + 1)) - P.b) (z.multiplier k) hβ (z.y (k + 1)) hminimum
  have horiginal' : IsSubgradientAt P.g
      (P.B.transpose.mulVec
        (-(z.multiplier k + β •
          (P.B.mulVec (z.y (k + 1)) + (P.A.mulVec (z.x (k + 1)) - P.b)))))
      (z.y (k + 1)) := by
    simpa only [Matrix.mulVec_neg] using horiginal
  have hfiber := ImageReduction.shiftedFiberSupportTransfer
    (b := P.b) horiginal'
  have hscaled := ImageReduction.scaledFenchelBiconjugateSupport hfiber.2 hβ
  have hdef : ImageReduction.reducedSecond P.g P.B P.b β =
      (fun q ↦ ERealConvex.fenchelBiconjugate
        (ImageReduction.shiftedFiberInf P.g P.B P.b) q / (β : EReal)) := by
    funext q
    exact ImageReduction.reducedSecond_apply P.g P.B P.b β q
  rw [← hdef] at hscaled
  have hnormal :
      β⁻¹ •
          (-(z.multiplier k + β •
            (P.B.mulVec (z.y (k + 1)) + (P.A.mulVec (z.x (k + 1)) - P.b)))) =
        (-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k) -
          (P.B.mulVec (z.y (k + 1)) - P.b) := by
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    field_simp [hβ.ne']
    ring
  have hsubgradient : IsSubgradientAt (P.reduced β).g
      ((-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k) -
        (P.B.mulVec (z.y (k + 1)) - P.b))
      (P.B.mulVec (z.y (k + 1)) - P.b) := by
    rw [Problem.reduced_g]
    rw [hnormal] at hscaled
    exact hscaled.2.2
  -- The affine-fiber touching equations provide the second value identities.
  exact ⟨hscaled.2.1.symm, hscaled.2.1.trans hfiber.1, hsubgradient⟩

/-- A support normal equal to center minus point certifies proximal
minimality at that center. -/
private lemma isProxPoint_of_subgradient_center_sub {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} {center x : Fin n → ℝ}
    (h : IsSubgradientAt φ (center - x) x) :
    IsProxPoint φ center x := by
  obtain ⟨c, hxvalue, hsupport⟩ := (isSubgradientAt_iff _ _ _).mp h
  rw [isProxPoint_iff]
  refine ⟨c + dotProduct (x - center) (x - center) / 2, ?_, ?_⟩
  · rw [hxvalue, ← EReal.coe_add]
  · intro y
    let qx := dotProduct (x - center) (x - center) / 2
    let qy := dotProduct (y - center) (y - center) / 2
    let linear := dotProduct (center - x) (y - x)
    have hself : 0 ≤ dotProduct (y - x) (y - x) := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg ((y - x) i)
    have hcenter : center - x = -(x - center) := by
      ext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    have hycenter : y - center = (y - x) + (x - center) := by
      ext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    have hquad : qx ≤ linear + qy := by
      dsimp only [qx, qy, linear]
      rw [hcenter, hycenter]
      simp only [neg_dotProduct, add_dotProduct, dotProduct_add]
      rw [dotProduct_comm (y - x) (x - center)]
      nlinarith
    have hsupported := hsupport y
    have hsupported' :=
      (EReal.addLECancellable_coe qy).add_le_add_iff_right.mpr hsupported
    calc
      φ x + (qx : EReal) ≤ φ x + ((linear + qy : ℝ) : EReal) := by
        rw [hxvalue, ← EReal.coe_add, ← EReal.coe_add,
          EReal.coe_le_coe_iff]
        exact add_le_add_right hquad c
      _ = (φ x + (linear : EReal)) + (qy : EReal) := by
        rw [EReal.coe_add, add_assoc]
      _ ≤ φ y + (qy : EReal) := hsupported'

/-- Every attained first-block trajectory update has the same value under the
fiber objective, its Fenchel biconjugate, and the original objective. -/
theorem firstImage_values {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (z : Trajectory P β γ) (k : ℕ) :
    ImageReduction.fiberInf P.f P.A (P.A.mulVec (z.x (k + 1))) =
        ERealConvex.fenchelBiconjugate (ImageReduction.fiberInf P.f P.A)
          (P.A.mulVec (z.x (k + 1))) ∧
      ERealConvex.fenchelBiconjugate (ImageReduction.fiberInf P.f P.A)
          (P.A.mulVec (z.x (k + 1))) = P.f (z.x (k + 1)) := by
  have hsupport := firstImageSupport P hf hβ z k
  -- Discard the cached reduced subgradient and retain the two touching values.
  exact ⟨hsupport.1, hsupport.2.1⟩

/-- Every attained second-block trajectory update has the same value under the
affine-fiber objective, its Fenchel biconjugate, and the original objective. -/
theorem secondImage_values {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (z : Trajectory P β γ) (k : ℕ) :
    ImageReduction.shiftedFiberInf P.g P.B P.b
        (P.B.mulVec (z.y (k + 1)) - P.b) =
      ERealConvex.fenchelBiconjugate
        (ImageReduction.shiftedFiberInf P.g P.B P.b)
        (P.B.mulVec (z.y (k + 1)) - P.b) ∧
      ERealConvex.fenchelBiconjugate
          (ImageReduction.shiftedFiberInf P.g P.B P.b)
          (P.B.mulVec (z.y (k + 1)) - P.b) = P.g (z.y (k + 1)) := by
  have hsupport := secondImageSupport P hg hβ z k
  -- Discard the cached reduced subgradient and retain the affine-fiber values.
  exact ⟨hsupport.1, hsupport.2.1⟩

/-- Every attained first-block trajectory update is the first relational
proximal image update. -/
theorem firstImage_isProxPoint {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (z : Trajectory P β γ) (k : ℕ) :
    IsProxPoint (P.reduced β).f
      (-(P.B.mulVec (z.y k) - P.b) - β⁻¹ • z.multiplier k)
      (P.A.mulVec (z.x (k + 1))) := by
  have hsupport := firstImageSupport P hf hβ z k
  -- The cached normal is exactly proximal center minus the first image point.
  exact isProxPoint_of_subgradient_center_sub hsupport.2.2

/-- Every attained second-block trajectory update is the second relational
proximal image update. -/
theorem secondImage_isProxPoint {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (z : Trajectory P β γ) (k : ℕ) :
    IsProxPoint (P.reduced β).g
      (-P.A.mulVec (z.x (k + 1)) - β⁻¹ • z.multiplier k)
      (P.B.mulVec (z.y (k + 1)) - P.b) := by
  have hsupport := secondImageSupport P hg hβ z k
  -- The cached normal is exactly proximal center minus the second image point.
  exact isProxPoint_of_subgradient_center_sub hsupport.2.2

/-- The scaled multiplier of an exact trajectory obeys the reduced image
iteration recurrence. -/
theorem scaledMultiplier_imageUpdate {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (z : Trajectory P β γ) (k : ℕ) :
    β⁻¹ • z.multiplier (k + 1) = β⁻¹ • z.multiplier k +
      γ • (P.A.mulVec (z.x (k + 1)) +
        (P.B.mulVec (z.y (k + 1)) - P.b)) := by
  -- Scale the trajectory recurrence and cancel the positive penalty parameter.
  rw [z.multiplierStep k]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hβ.ne']
  ring

end Trajectory

end ADMM
