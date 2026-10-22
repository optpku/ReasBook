/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part3

section Chap08
section Section38

/-- The weak topology on the algebraic dual induced by evaluation, used to talk about
lower semicontinuity (and hence "closedness") of functions on dual spaces. -/
noncomputable local instance instTopologicalSpace_moduleDual_weak_part4
    {E : Type*} [AddCommGroup E] [Module ℝ E] :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- The book's `F_*^*` object in §38. In packed coordinates it is the joint Fenchel conjugate
of `F` at `(x*, -u*)`, hence uses the supremal adjoint convention for the concave inverse. -/
noncomputable def bifunctionInverseBookAdjoint {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun uStar xStar =>
    fenchelConjugate (m + n) (bifunctionGraphFunction F)
      (adjointGraphDualVector uStar xStar)

/-- Helper for Theorem 38.4: precomposing an `EReal`-convex function with a linear map preserves
`EReal`-convexity. -/
lemma helperForTheorem_38_4_isERealConvex_precomp_linearMap
    {X Y : Type*} [AddCommMonoid X] [Module ℝ X] [AddCommMonoid Y] [Module ℝ Y]
    (A : X →ₗ[ℝ] Y) {g : Y → EReal} (hg : IsERealConvex g) :
    IsERealConvex (fun x => g (A x)) := by
  let Aprod : X × ℝ →ₗ[ℝ] Y × ℝ :=
    LinearMap.prodMap A (LinearMap.id)
  have hpre :
      ERealEpigraph (fun x => g (A x)) = Aprod ⁻¹' ERealEpigraph g := by
    -- The epigraph of the precomposed function is exactly the linear preimage of the old epigraph.
    ext p
    rfl
  -- Apply convexity of epigraphs through the linear map on graph coordinates.
  rw [IsERealConvex, hpre]
  simpa [Aprod] using (Convex.linear_preimage (hs := hg) Aprod)

/-- Helper for Theorem 38.4: on `Set.univ`, a proper `EReal`-convex function is a Chapter 1
`ProperConvexFunctionOn`. -/
lemma helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
    {n : Nat} (h : (Fin n → ℝ) → EReal)
    (hproper : IsProperEReal h) (hconv : IsERealConvex h) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
  have hconvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    -- Translate the local `IsERealConvex` epigraph predicate into the Chapter 1 `ConvexFunctionOn`
    -- predicate on `Set.univ`.
    simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ] using hconv
  rcases hproper.2 with ⟨x0, hx0⟩
  have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → ℝ)) h) := by
    -- A finite value furnishes an explicit epigraph point.
    refine ⟨(x0, (h x0).toReal), ?_⟩
    constructor
    · exact Set.mem_univ x0
    · simpa using (EReal.le_coe_toReal (x := h x0) hx0)
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), h x ≠ (⊥ : EReal) := by
    -- Properness already excludes the value `⊥` everywhere.
    intro x _
    exact hproper.1 x
  exact ⟨hconvOn, hne, hnotbot⟩

/-- Helper for Theorem 38.4: the image `Ff` is convex because it is the fiber infimum of the
convex function `(x, u) ↦ f u + F u x` on the product space, so Theorem 5.7 applies. -/
lemma helperForTheorem_38_4_imageConvex
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f) :
    IsERealConvex (bifunctionImageRaw F f) := by
  let liftedf : (Fin (n + m) → ℝ) → EReal :=
    fun z => f (projLamLinearMap (n := n) (m := m) z)
  let liftedF : (Fin (n + m) → ℝ) → EReal :=
    fun z =>
      F (projLamLinearMap (n := n) (m := m) z) (projXLinearMap (n := n) (m := m) z)
  have hliftedf_proper : IsProperEReal liftedf := by
    constructor
    · -- The lifted first summand inherits the exclusion of `⊥` from `f`.
      intro z
      simpa [liftedf] using hf_proper.1 (projLamLinearMap (n := n) (m := m) z)
    · -- Any finite point of `f` extends to a finite point of the lifted function.
      rcases hf_proper.2 with ⟨u0, hu0⟩
      refine ⟨Fin.append (0 : Fin n → ℝ) u0, ?_⟩
      simpa [liftedf, projLamLinearMap]
  have hliftedF_proper : IsProperEReal liftedF := by
    constructor
    · -- The lifted bifunction summand inherits the exclusion of `⊥` from the joint properness of
      -- `(u, x) ↦ F u x`.
      intro z
      simpa [liftedF] using
        hF_proper.1
          (projLamLinearMap (n := n) (m := m) z, projXLinearMap (n := n) (m := m) z)
    · -- A finite point of the product function becomes a finite point of the lifted function by
      -- packing `(x, u)` into the combined coordinates.
      rcases hF_proper.2 with ⟨p0, hp0⟩
      refine ⟨Fin.append p0.2 p0.1, ?_⟩
      simpa [liftedF, projLamLinearMap, projXLinearMap] using hp0
  have hliftedf_convex : IsERealConvex liftedf := by
    -- Convexity of `f` survives the projection that forgets the `x`-coordinates.
    simpa [liftedf] using
      helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := projLamLinearMap (n := n) (m := m)) (hg := hf_convex)
  have hliftedF_convex : IsERealConvex liftedF := by
    let pairMap : (Fin (n + m) → ℝ) →ₗ[ℝ] (Fin m → ℝ) × (Fin n → ℝ) :=
      (projLamLinearMap (n := n) (m := m)).prod (projXLinearMap (n := n) (m := m))
    -- Joint convexity of `F` survives the linear reparameterization from combined coordinates to
    -- the pair `(u, x)`.
    simpa [liftedF, pairMap] using
      helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap) (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2)
        (hg := hF_convex)
  have hsumConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ)) (fun z => liftedf z + liftedF z) := by
    -- The combined objective is the sum of two proper convex functions on the product space.
    exact convexFunctionOn_add_of_proper
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        liftedf hliftedf_proper hliftedf_convex)
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        liftedF hliftedF_proper hliftedF_convex)
  have himageConv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => sInf { z : EReal |
          ∃ y : Fin (n + m) → ℝ,
            projXLinearMap (n := n) (m := m) y = x ∧ z = liftedf y + liftedF y }) := by
    -- Theorem 5.7: fiber infima under a linear map preserve convexity.
    simpa using
      (convexFunctionOn_inf_fiber_linearMap (A := projXLinearMap (n := n) (m := m))
        (h := fun z => liftedf z + liftedF z) hsumConv)
  have hEq :
      (fun x => sInf { z : EReal |
          ∃ y : Fin (n + m) → ℝ,
            projXLinearMap (n := n) (m := m) y = x ∧ z = liftedf y + liftedF y }) =
        bifunctionImageRaw F f := by
    funext x
    have hset :
        { z : EReal |
            ∃ y : Fin (n + m) → ℝ,
              projXLinearMap (n := n) (m := m) y = x ∧ z = liftedf y + liftedF y } =
          Set.range (fun u : Fin m → ℝ => f u + F u x) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        -- Any point in the fiber is determined by its `u`-coordinates once the `x`-coordinates are
        -- fixed.
        refine ⟨projLamLinearMap (n := n) (m := m) y, ?_⟩
        simp [liftedf, liftedF, hy]
      · rintro ⟨u, rfl⟩
        -- Conversely, any `u` can be packed with the fixed `x` into a point of the projection
        -- fiber.
        refine ⟨Fin.append x u, ?_, ?_⟩
        · ext i
          simp [projXLinearMap]
        · simp [liftedf, liftedF, projLamLinearMap, projXLinearMap]
    -- The Chapter 1 fiber-infimum formula is exactly the `iInf` defining `bifunctionImageRaw`.
    rw [hset, sInf_range, bifunctionImageRaw]
  have himageConv' : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (bifunctionImageRaw F f) := by
    simpa [hEq] using himageConv
  -- Translate the Chapter 1 `ConvexFunctionOn` conclusion back to the local epigraph predicate.
  simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ] using himageConv'


/-- The qualification point lifts to a common relative-interior point of the two packed
summands used in the Fenchel conjugate-of-a-sum argument. -/
lemma helperForTheorem_38_4_packedSummands_hri
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_convex : IsERealConvex f)
    (hri :
      (intrinsicInterior ℝ (erealDom f) ∩
          intrinsicInterior ℝ (bifunctionDom F)).Nonempty) :
    (intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
            (fun z => f (fun i => z (Fin.castAdd n i)))) ∩
        intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
            (bifunctionGraphFunction F))).Nonempty := by
  rcases hri with ⟨u, hu_f, hu_F⟩
  let pairMap : (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun z =>
        (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
      map_add' := by
        intro z w
        ext i <;> simp
      map_smul' := by
        intro a z
        ext i <;> simp }
  have hPackedEReal : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [pairMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) hF_convex)
  have hF30 : ConvexBifunction F := by
    simpa [ConvexBifunction, ConvexFunction, IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using hPackedEReal
  have hF29 : IsConvexBifunction F :=
    helperForTheorem_6_30_17_isConvexBifunction_of_convexBifunction hF30
      (by
        intro u' x'
        exact hF_proper.1 (u', x'))
  let FB : BundledConvexBifunction m n := ⟨F, hF29⟩
  have hu_F_fin :
      u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain FB.1) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    have hDom : bifunctionEffectiveDomain FB.1 = bifunctionDom F := by
      ext v
      simp only [FB, bifunctionEffectiveDomain, bifunctionDom, Set.mem_setOf_eq,
        Set.nonempty_def, erealDom]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, ne_of_lt hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (lt_top_iff_ne_top).2 hx⟩
    rw [hDom]
    exact hu_F
  rcases helperForTheorem_6_29_4_coordinateGraph_riLift_of_mem_riProjection
      FB hu_F_fin with ⟨x0, hxF⟩
  have hxF' :
      Fin.append u x0 ∈ intrinsicInterior ℝ
        (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
          (bifunctionGraphFunction F)) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] at hxF
    change Fin.append u x0 ∈ intrinsicInterior ℝ
      (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction F)) at hxF
    exact hxF
  have hu_f_dom : u ∈ erealDom f := intrinsicInterior_subset hu_f
  let liftedf : (Fin (m + n) → ℝ) → EReal :=
    fun z => f (fun i => z (Fin.castAdd n i))
  let projU : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun z i => z (Fin.castAdd n i)
      map_add' := by intro z w; ext i; simp
      map_smul' := by intro a z; ext i; simp }
  have hlifted_conv : IsERealConvex liftedf := by
    simpa [liftedf, projU] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := projU) (g := f) hf_convex)
  have hdom_conv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf) :=
    effectiveDomain_convex
      (S := (Set.univ : Set (Fin (m + n) → ℝ)))
      (f := liftedf)
      (by
        simpa [ConvexFunction, IsERealConvex, ConvexFunctionOn,
          helperForTheorem_38_1_epigraph_eq_univ] using hlifted_conv)
  let eMN := EuclideanSpace.equiv (ι := Fin (m + n)) (𝕜 := ℝ)
  let eM := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let eN := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let C : Set (EuclideanSpace ℝ (Fin (m + n))) :=
    eMN.symm '' effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf
  have hC : Convex ℝ C := by
    simpa [C] using hdom_conv.linear_image eMN.symm.toLinearMap
  let append :
      EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (m + n)) :=
    fun y z => eMN.symm (Fin.append (eM y) (eN z))
  let Cy : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun y => {z | append y z ∈ C}
  let D : Set (EuclideanSpace ℝ (Fin m)) := {y | (Cy y).Nonempty}
  have hD : D = eM.symm '' erealDom f := by
    ext y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨eM y, ?_, by simp [eM]⟩
      have hz' :
          Fin.append (eM y) (eN z) ∈
            effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf := by
        simpa [D, Cy, append, C] using hz
      rw [effectiveDomain_eq] at hz'
      simpa [liftedf, erealDom] using hz'.2
    · rintro ⟨u', hu', rfl⟩
      refine ⟨eN.symm 0, ?_⟩
      have hp :
          Fin.append u' (0 : Fin n → ℝ) ∈
            effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf := by
        rw [effectiveDomain_eq]
        refine ⟨Set.mem_univ _, ?_⟩
        simpa [liftedf, erealDom] using hu'
      simpa [D, Cy, append, C, eM, eN, eMN] using hp
  have huD : eM.symm u ∈ euclideanRelativeInterior m D := by
    have huFin : u ∈ euclideanRelativeInterior_fin m (erealDom f) := by
      rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
      exact hu_f
    have huImage :=
      (mem_euclideanRelativeInterior_fin_iff (n := m) (C := erealDom f) (x := u)).1 huFin
    simpa [hD, eM] using huImage
  have hxCy : eN.symm x0 ∈ euclideanRelativeInterior n (Cy (eM.symm u)) := by
    have hCy : Cy (eM.symm u) = Set.univ := by
      ext z
      have hp :
          Fin.append u (eN z) ∈
            effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf := by
        rw [effectiveDomain_eq]
        refine ⟨Set.mem_univ _, ?_⟩
        simpa [liftedf, erealDom] using hu_f_dom
      simpa [Cy, append, C, eM, eN, eMN] using hp
    rw [hCy]
    rw [show euclideanRelativeInterior n
        (Set.univ : Set (EuclideanSpace ℝ (Fin n))) = Set.univ by
      simpa using
        (euclideanRelativeInterior_affineSubspace_eq n
          (⊤ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))))]
    simp
  have hxC :
      append (eM.symm u) (eN.symm x0) ∈ euclideanRelativeInterior (m + n) C := by
    exact
      (euclideanRelativeInterior_mem_iff_relativeInterior_section m n C hC
        (eM.symm u) (eN.symm x0)).2 ⟨huD, hxCy⟩
  have hxLiftedFin :
      Fin.append u x0 ∈ euclideanRelativeInterior_fin (m + n)
        (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf) := by
    apply (mem_euclideanRelativeInterior_fin_iff
      (n := m + n)
      (C := effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf)
      (x := Fin.append u x0)).2
    simpa [C, append, eMN, eM, eN] using hxC
  have hxLifted :
      Fin.append u x0 ∈ intrinsicInterior ℝ
        (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf) := by
    rw [← helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hxLiftedFin
  change Fin.append u x0 ∈ intrinsicInterior ℝ
    (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
      (fun z => f (fun i => z (Fin.castAdd n i)))) at hxLifted
  exact ⟨Fin.append u x0, hxLifted, hxF'⟩

/-- The Euclidean pairing splits over concatenated coordinate blocks. -/
lemma helperForTheorem_38_4_dotProduct_append {m n : Nat}
    (u uStar : Fin m → ℝ) (x xStar : Fin n → ℝ) :
    dotProduct (Fin.append u x) (Fin.append uStar xStar) =
      dotProduct u uStar + dotProduct x xStar := by
  simp [dotProduct, Fin.sum_univ_add]

/-- Swapping the packed `(x,u)` coordinates turns the conjugate of the lifted graph function
into the corrected joint Fenchel realization of `F_*^*`. -/
lemma helperForTheorem_38_4_liftedGraph_conjugate_at_signedPair
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) :
    fenchelConjugate (n + m)
        (fun z : Fin (n + m) → ℝ =>
          F (fun i => z (Fin.natAdd n i)) (fun j => z (Fin.castAdd m j)))
        (Fin.append xStar (-uStar)) =
      bifunctionInverseBookAdjoint F uStar xStar := by
  rw [bifunctionInverseBookAdjoint, fenchelConjugate_eq_iSup,
    fenchelConjugate_eq_iSup]
  apply le_antisymm
  · refine iSup_le ?_
    intro z
    let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
    let u : Fin m → ℝ := fun i => z (Fin.natAdd n i)
    have hz : z = Fin.append x u := by
      ext i
      cases i using Fin.addCases <;> simp [x, u]
    calc
      (((dotProduct z (Fin.append xStar (-uStar)) : ℝ) : EReal) - F u x) =
          (((dotProduct (Fin.append u x) (adjointGraphDualVector uStar xStar) : ℝ) :
              EReal) - bifunctionGraphFunction F (Fin.append u x)) := by
            rw [hz]
            simp [helperForTheorem_38_4_dotProduct_append, adjointGraphDualVector,
              bifunctionGraphFunction, x, u, dotProduct_neg, add_comm]
      _ ≤ ⨆ w : Fin (m + n) → ℝ,
          (((dotProduct w (adjointGraphDualVector uStar xStar) : ℝ) : EReal) -
            bifunctionGraphFunction F w) :=
        le_iSup (fun w : Fin (m + n) → ℝ =>
          (((dotProduct w (adjointGraphDualVector uStar xStar) : ℝ) : EReal) -
            bifunctionGraphFunction F w)) (Fin.append u x)
  · refine iSup_le ?_
    intro w
    let u : Fin m → ℝ := fun i => w (Fin.castAdd n i)
    let x : Fin n → ℝ := fun j => w (Fin.natAdd m j)
    have hw : w = Fin.append u x := by
      ext i
      cases i using Fin.addCases <;> simp [u, x]
    calc
      (((dotProduct w (adjointGraphDualVector uStar xStar) : ℝ) : EReal) -
          bifunctionGraphFunction F w) =
          (((dotProduct (Fin.append x u) (Fin.append xStar (-uStar)) : ℝ) : EReal) -
            F u x) := by
              rw [hw]
              simp [helperForTheorem_38_4_dotProduct_append, adjointGraphDualVector,
                bifunctionGraphFunction, u, x, dotProduct_neg, add_comm]
      _ ≤ ⨆ z : Fin (n + m) → ℝ,
          (((dotProduct z (Fin.append xStar (-uStar)) : ℝ) : EReal) -
            F (fun i => z (Fin.natAdd n i)) (fun j => z (Fin.castAdd m j))) :=
        by
          simpa using
            (le_iSup (fun z : Fin (n + m) → ℝ =>
              (((dotProduct z (Fin.append xStar (-uStar)) : ℝ) : EReal) -
                F (fun i => z (Fin.natAdd n i)) (fun j => z (Fin.castAdd m j))))
              (Fin.append x u))

/-- The conjugate of the cylindrical lift `(x,u) ↦ f u` is finite only when the first
dual block is zero; on that block it is exactly `f⋆`. -/
lemma helperForTheorem_38_4_liftedParameter_conjugate
    {m n : Nat} (f : (Fin m → ℝ) → EReal) (hf_proper : IsProperEReal f)
    (a : Fin n → ℝ) (b : Fin m → ℝ) :
    fenchelConjugate (n + m)
        (fun z : Fin (n + m) → ℝ => f (fun i => z (Fin.natAdd n i)))
        (Fin.append a b) =
      if a = 0 then fenchelConjugate m f b else ⊤ := by
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl, fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup]
    apply le_antisymm
    · refine iSup_le ?_
      intro z
      let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
      let u : Fin m → ℝ := fun i => z (Fin.natAdd n i)
      have hz : z = Fin.append x u := by
        ext i
        cases i using Fin.addCases <;> simp [x, u]
      calc
        (((dotProduct z (Fin.append (0 : Fin n → ℝ) b) : ℝ) : EReal) - f u) =
            (((dotProduct u b : ℝ) : EReal) - f u) := by
              rw [hz, helperForTheorem_38_4_dotProduct_append]
              simp
        _ ≤ ⨆ v : Fin m → ℝ, (((dotProduct v b : ℝ) : EReal) - f v) :=
          le_iSup (fun v : Fin m → ℝ => (((dotProduct v b : ℝ) : EReal) - f v)) u
    · refine iSup_le ?_
      intro u
      have hle := le_iSup
        (fun z : Fin (n + m) → ℝ =>
          (((dotProduct z (Fin.append (0 : Fin n → ℝ) b) : ℝ) : EReal) -
            f (fun i => z (Fin.natAdd n i))))
        (Fin.append (0 : Fin n → ℝ) u)
      simpa [helperForTheorem_38_4_dotProduct_append] using hle
  · rw [if_neg ha, fenchelConjugate_eq_iSup, EReal.eq_top_iff_forall_lt]
    rcases hf_proper.2 with ⟨u0, hu0_top⟩
    have hu0_bot : f u0 ≠ (⊥ : EReal) := hf_proper.1 u0
    cases hfu : f u0 with
    | bot => exact (hu0_bot hfu).elim
    | top => exact (hu0_top hfu).elim
    | coe r =>
      intro y
      have hq : 0 < dotProduct a a := dotProduct_self_pos_of_ne_zero ha
      let q : ℝ := dotProduct a a
      let t : ℝ := (y + r - dotProduct u0 b + 1) / q
      let z : Fin (n + m) → ℝ := Fin.append (t • a) u0
      have hscale : dotProduct (t • a) a = t * q := by
        simpa [q, smul_eq_mul] using (smul_dotProduct t a a)
      have hdot : dotProduct z (Fin.append a b) = y + r + 1 := by
        rw [show z = Fin.append (t • a) u0 by rfl,
          helperForTheorem_38_4_dotProduct_append, hscale]
        dsimp [t, q]
        field_simp [ne_of_gt hq]
        ring
      have hterm :
          ((((y + 1 : ℝ) : EReal))) =
            (((dotProduct z (Fin.append a b) : ℝ) : EReal) -
              f (fun i => z (Fin.natAdd n i))) := by
        symm
        calc
          (((dotProduct z (Fin.append a b) : ℝ) : EReal) -
              f (fun i => z (Fin.natAdd n i))) =
              (((y + r + 1 : ℝ) : EReal) - (r : EReal)) := by
                simp [z, hfu, hdot]
          _ = ((((y + r + 1) - r : ℝ) : EReal)) := by
            rw [EReal.coe_sub]
          _ = (((y + 1 : ℝ) : EReal)) := by
            congr 1
            ring
      have hlt : ((y : ℝ) : EReal) < (((y + 1 : ℝ) : EReal)) := by
        exact_mod_cast (show y < y + 1 by linarith)
      exact lt_of_lt_of_le hlt (by
        rw [hterm]
        exact le_iSup
          (fun z : Fin (n + m) → ℝ =>
            (((dotProduct z (Fin.append a b) : ℝ) : EReal) -
              f (fun i => z (Fin.natAdd n i)))) z)

/-- Parameter-first version of the cylindrical conjugate formula, matching the natural
`(u,x)` packing used by the Chapter 29 relative-interior lift. -/
lemma helperForTheorem_38_4_liftedParameterFirst_conjugate
    {m n : Nat} (f : (Fin m → ℝ) → EReal) (hf_proper : IsProperEReal f)
    (b : Fin m → ℝ) (a : Fin n → ℝ) :
    fenchelConjugate (m + n)
        (fun z : Fin (m + n) → ℝ => f (fun i => z (Fin.castAdd n i)))
        (Fin.append b a) =
      if a = 0 then fenchelConjugate m f b else ⊤ := by
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl, fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup]
    apply le_antisymm
    · refine iSup_le ?_
      intro z
      let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
      let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
      have hz : z = Fin.append u x := by
        ext i
        cases i using Fin.addCases <;> simp [u, x]
      calc
        (((dotProduct z (Fin.append b (0 : Fin n → ℝ)) : ℝ) : EReal) - f u) =
            (((dotProduct u b : ℝ) : EReal) - f u) := by
              rw [hz, helperForTheorem_38_4_dotProduct_append]
              simp
        _ ≤ ⨆ v : Fin m → ℝ, (((dotProduct v b : ℝ) : EReal) - f v) :=
          le_iSup (fun v : Fin m → ℝ => (((dotProduct v b : ℝ) : EReal) - f v)) u
    · refine iSup_le ?_
      intro u
      have hle := le_iSup
        (fun z : Fin (m + n) → ℝ =>
          (((dotProduct z (Fin.append b (0 : Fin n → ℝ)) : ℝ) : EReal) -
            f (fun i => z (Fin.castAdd n i))))
        (Fin.append u (0 : Fin n → ℝ))
      simpa [helperForTheorem_38_4_dotProduct_append] using hle
  · rw [if_neg ha, fenchelConjugate_eq_iSup, EReal.eq_top_iff_forall_lt]
    rcases hf_proper.2 with ⟨u0, hu0_top⟩
    have hu0_bot : f u0 ≠ (⊥ : EReal) := hf_proper.1 u0
    cases hfu : f u0 with
    | bot => exact (hu0_bot hfu).elim
    | top => exact (hu0_top hfu).elim
    | coe r =>
      intro y
      have hq : 0 < dotProduct a a := dotProduct_self_pos_of_ne_zero ha
      let q : ℝ := dotProduct a a
      let t : ℝ := (y + r - dotProduct u0 b + 1) / q
      let z : Fin (m + n) → ℝ := Fin.append u0 (t • a)
      have hscale : dotProduct (t • a) a = t * q := by
        simpa [q, smul_eq_mul] using (smul_dotProduct t a a)
      have hdot : dotProduct z (Fin.append b a) = y + r + 1 := by
        rw [show z = Fin.append u0 (t • a) by rfl,
          helperForTheorem_38_4_dotProduct_append, hscale]
        dsimp [t, q]
        field_simp [ne_of_gt hq]
        ring
      have hterm :
          ((((y + 1 : ℝ) : EReal))) =
            (((dotProduct z (Fin.append b a) : ℝ) : EReal) -
              f (fun i => z (Fin.castAdd n i))) := by
        symm
        calc
          (((dotProduct z (Fin.append b a) : ℝ) : EReal) -
              f (fun i => z (Fin.castAdd n i))) =
              (((y + r + 1 : ℝ) : EReal) - (r : EReal)) := by
                simp [z, hfu, hdot]
          _ = ((((y + r + 1) - r : ℝ) : EReal)) := by rw [EReal.coe_sub]
          _ = (((y + 1 : ℝ) : EReal)) := by congr 1 <;> ring
      have hlt : ((y : ℝ) : EReal) < (((y + 1 : ℝ) : EReal)) := by
        exact_mod_cast (show y < y + 1 by linarith)
      exact lt_of_lt_of_le hlt (by
        rw [hterm]
        exact le_iSup
          (fun z : Fin (m + n) → ℝ =>
            (((dotProduct z (Fin.append b a) : ℝ) : EReal) -
              f (fun i => z (Fin.castAdd n i)))) z)

/-- Conjugating the partial infimum is the same as conjugating the packed joint objective at
the dual vector whose parameter block is zero. -/
lemma helperForTheorem_38_4_imageConjugate_eq_packedSumConjugate
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (xStar : Fin n → ℝ) :
    fenchelConjugate n (bifunctionImageRaw F f) xStar =
      fenchelConjugate (m + n)
        (fun z : Fin (m + n) → ℝ =>
          f (fun i => z (Fin.castAdd n i)) +
            bifunctionGraphFunction F z)
        (Fin.append (0 : Fin m → ℝ) xStar) := by
  have hsub (x : Fin n → ℝ) :
      (((dotProduct x xStar : ℝ) : EReal) - bifunctionImageRaw F f x) =
        ⨆ u : Fin m → ℝ,
          (((dotProduct x xStar : ℝ) : EReal) - (f u + F u x)) := by
    rw [bifunctionImageRaw]
    have h := section16_coeReal_sub_sInf_image_eq_sSup_image
      (S := (Set.univ : Set (Fin m → ℝ)))
      (φ := fun u : Fin m → ℝ => f u + F u x)
      (a := dotProduct x xStar)
    simpa [Set.image_univ, sInf_range, sSup_range] using h
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    rw [hsub]
    refine iSup_le ?_
    intro u
    have hle := le_iSup
      (fun z : Fin (m + n) → ℝ =>
        (((dotProduct z (Fin.append (0 : Fin m → ℝ) xStar) : ℝ) : EReal) -
          (f (fun i => z (Fin.castAdd n i)) + bifunctionGraphFunction F z)))
      (Fin.append u x)
    simpa [helperForTheorem_38_4_dotProduct_append, bifunctionGraphFunction] using hle
  · refine iSup_le ?_
    intro z
    let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    have hz : z = Fin.append u x := by
      ext i
      cases i using Fin.addCases <;> simp [u, x]
    calc
      (((dotProduct z (Fin.append (0 : Fin m → ℝ) xStar) : ℝ) : EReal) -
          (f u + bifunctionGraphFunction F z)) =
          (((dotProduct x xStar : ℝ) : EReal) - (f u + F u x)) := by
            rw [hz, helperForTheorem_38_4_dotProduct_append]
            simp [bifunctionGraphFunction, u, x]
      _ ≤ ⨆ v : Fin m → ℝ,
          (((dotProduct x xStar : ℝ) : EReal) - (f v + F v x)) :=
        le_iSup (fun v : Fin m → ℝ =>
          (((dotProduct x xStar : ℝ) : EReal) - (f v + F v x))) u
      _ = (((dotProduct x xStar : ℝ) : EReal) - bifunctionImageRaw F f x) := hsub x |>.symm
      _ ≤ ⨆ y : Fin n → ℝ,
          (((dotProduct y xStar : ℝ) : EReal) - bifunctionImageRaw F f y) :=
        le_iSup (fun y : Fin n → ℝ =>
          (((dotProduct y xStar : ℝ) : EReal) - bifunctionImageRaw F f y)) x

/-- Helper for Theorem 38.4: the constant-zero bifunction and the constant-zero function still
produce the constant-zero image. -/
lemma helperForTheorem_38_4_zeroBifunction_image_constZero_eq_constZero :
    bifunctionImageRaw
        (fun _ _ : Fin 1 → ℝ => (0 : EReal))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) =
      fun _ : Fin 1 → ℝ => (0 : EReal) := by
  funext x
  apply le_antisymm
  · -- The zero primal point realizes the value `0` in the defining infimum.
    refine le_trans (iInf_le _ (0 : Fin 1 → ℝ)) ?_
    simp
  · -- Every summand equals `0`, so the infimum cannot drop below `0`.
    rw [bifunctionImageRaw]
    refine le_iInf ?_
    intro u
    simp

/-- Helper for Theorem 38.4: the relative-interior qualification hypothesis is satisfied by the
dimension-one constant-zero specialization. -/
lemma helperForTheorem_38_4_zeroSpecialization_qualification :
    (intrinsicInterior ℝ
          (erealDom (fun _ : Fin 1 → ℝ => (0 : EReal))) ∩
        intrinsicInterior ℝ
          (bifunctionDom (fun _ _ : Fin 1 → ℝ => (0 : EReal)))).Nonempty := by
  have hDomf :
      erealDom (fun _ : Fin 1 → ℝ => (0 : EReal)) = (Set.univ : Set (Fin 1 → ℝ)) := by
    ext u
    simp [erealDom]
  have hDomF :
      bifunctionDom (fun _ _ : Fin 1 → ℝ => (0 : EReal)) = (Set.univ : Set (Fin 1 → ℝ)) := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      refine ⟨0, ?_⟩
      simp
  refine ⟨0, ?_⟩
  constructor
  · -- The constant-zero primal function is finite everywhere, so its domain has full intrinsic
    -- interior.
    rw [hDomf]
    exact
      interior_subset_intrinsicInterior
        (by simp : (0 : Fin 1 → ℝ) ∈ interior (Set.univ : Set (Fin 1 → ℝ)))
  · -- The constant-zero bifunction also has full `u`-domain, so the same point qualifies on the
    -- bifunction side.
    rw [hDomF]
    exact
      interior_subset_intrinsicInterior
        (by simp : (0 : Fin 1 → ℝ) ∈ interior (Set.univ : Set (Fin 1 → ℝ)))

/-- Helper for Theorem 38.4: on the constant-zero specialization, the left-hand side conjugate
takes the value `⊤` at the dual point `1`. -/
lemma helperForTheorem_38_4_zeroSpecialization_leftAtOne_eq_top :
    fenchelConjugate 1
        (bifunctionImageRaw
          (fun _ _ : Fin 1 → ℝ => (0 : EReal))
          (fun _ : Fin 1 → ℝ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector = (⊤ : EReal) := by
  rw [helperForTheorem_38_4_zeroBifunction_image_constZero_eq_constZero, fenchelConjugate,
    EReal.eq_top_iff_forall_lt]
  intro y
  let x : Fin 1 → ℝ := fun _ => y + 1
  have hmem :
      (((y + 1 : ℝ) : EReal)) ∈
        Set.range
          (fun x : Fin 1 → ℝ =>
            ((x ⬝ᵥ helperForProposition_36_4_3_oneVector : ℝ) : EReal) - (0 : EReal)) := by
    refine ⟨x, ?_⟩
    simp [x, helperForProposition_36_4_3_oneVector, dotProduct]
  have hlt : ((y : ℝ) : EReal) < (((y + 1 : ℝ) : EReal)) := by
    exact_mod_cast (show y < y + 1 by linarith)
  -- Sending the primal witness `x = y + 1` through the supremum makes the conjugate exceed every
  -- real number, hence forces the value `⊤`.
  exact lt_of_lt_of_le hlt (le_sSup hmem)

/-- Helper for Theorem 38.4: on the constant-zero specialization, the textbook right-hand side
already equals `⊥` at the dual point `1`. -/
lemma helperForTheorem_38_4_zeroSpecialization_rightAtOne_eq_bot :
    bifunctionImageRaw
        (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
          (fun _ _ : Fin 1 → ℝ => (0 : EReal)))
        (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector = (⊥ : EReal) := by
  have hConjAtZero :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))
        helperForProposition_36_4_3_zeroVector = (0 : EReal) := by
    -- At the origin the constant-zero function contributes only the zero pairing term.
    simp [fenchelConjugate, helperForProposition_36_4_3_zeroVector, dotProduct]
  have hAdjointAtZeroOne :
      bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
          (fun _ _ : Fin 1 → ℝ => (0 : EReal))
          helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector =
        (⊥ : EReal) := by
    rw [EReal.eq_bot_iff_forall_lt]
    intro y
    have hUpper :
        bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
            (fun _ _ : Fin 1 → ℝ => (0 : EReal))
            helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector ≤
          ((y - 1 : ℝ) : EReal) := by
      -- Choosing `u = 1 - y` in the outer infimum pushes the textbook `F_*^*` value below any
      -- prescribed real bound.
      refine iInf_le_of_le (fun _ => (1 - y : ℝ)) ?_
      refine iInf_le_of_le (fun _ => (0 : ℝ)) ?_
      simp [bifunctionInverse, helperForProposition_36_4_3_zeroVector,
        helperForProposition_36_4_3_oneVector, finDot, dotProduct]
    have hStrict : (((y - 1 : ℝ) : EReal)) < (y : EReal) := by
      exact_mod_cast (show y - 1 < y by linarith)
    exact lt_of_le_of_lt hUpper hStrict
  rw [bifunctionImageRaw]
  apply le_antisymm
  · -- The dual witness `uStar = 0` already contributes `⊥`, so the infimum is forced to `⊥`.
    refine le_trans (iInf_le _ helperForProposition_36_4_3_zeroVector) ?_
    rw [hConjAtZero, hAdjointAtZeroOne]
    simp
  · -- `⊥` is always a lower bound.
    exact bot_le

/-- Helper for Theorem 38.4: the current statement is false on the dimension-one constant-zero
specialization `F = 0`, `f = 0`. -/
lemma helperForTheorem_38_4_zeroSpecialization_targetFalse :
    ¬ (IsERealConvex
          (bifunctionImageRaw
            (fun _ _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
        ((intrinsicInterior ℝ
              (erealDom (fun _ : Fin 1 → ℝ => (0 : EReal))) ∩
            intrinsicInterior ℝ
              (bifunctionDom (fun _ _ : Fin 1 → ℝ => (0 : EReal)))).Nonempty →
          fenchelConjugate 1
              (bifunctionImageRaw
                (fun _ _ : Fin 1 → ℝ => (0 : EReal))
                (fun _ : Fin 1 → ℝ => (0 : EReal))) =
            bifunctionImageRaw
              (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
                (fun _ _ : Fin 1 → ℝ => (0 : EReal)))
              (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
          (∀ xStar : Fin 1 → ℝ,
            ∃ uStar : Fin 1 → ℝ,
              bifunctionImageRaw
                  (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
                    (fun _ _ : Fin 1 → ℝ => (0 : EReal)))
                  (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)))
                  xStar =
                fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) uStar +
                  bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
                    (fun _ _ : Fin 1 → ℝ => (0 : EReal)) uStar xStar))) := by
  intro hSpecialized
  have hAtOne :=
    congrFun
      ((hSpecialized.2 helperForTheorem_38_4_zeroSpecialization_qualification).1)
      helperForProposition_36_4_3_oneVector
  -- Evaluating the claimed equality at `x* = 1` exposes the contradiction `⊤ = ⊥`.
  rw [helperForTheorem_38_4_zeroSpecialization_leftAtOne_eq_top,
    helperForTheorem_38_4_zeroSpecialization_rightAtOne_eq_bot] at hAtOne
  simp at hAtOne

/-- Helper for Theorem 38.4: the dimension-one constant-zero specialization satisfies all
properness and convexity hypotheses that appear in the theorem statement. -/
lemma helperForTheorem_38_4_zeroSpecialization_hypotheses :
    IsProperEReal (fun _ : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)) ∧
      IsERealConvex (fun _ : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)) ∧
      IsProperEReal (fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      IsERealConvex (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The product-side zero bifunction never hits `⊥`, and the origin is a finite witness.
    constructor
    · intro p
      simp
    · refine ⟨(0, 0), ?_⟩
      simp
  · -- The product-side epigraph is the half-space `{(p, r) | 0 ≤ r}`, which is convex.
    rw [IsERealConvex, ERealEpigraph]
    intro p hp q hq a b ha hb hab
    change (0 : EReal) ≤ (((a • p + b • q).2 : ℝ) : EReal)
    have hp' : 0 ≤ p.2 := by
      exact_mod_cast hp
    have hq' : 0 ≤ q.2 := by
      exact_mod_cast hq
    exact_mod_cast add_nonneg (mul_nonneg ha hp') (mul_nonneg hb hq')
  · -- The primal zero function is proper for the same reason.
    constructor
    · intro u
      simp
    · refine ⟨0, ?_⟩
      simp
  · -- Its epigraph is again the half-space `{(u, r) | 0 ≤ r}`.
    rw [IsERealConvex, ERealEpigraph]
    intro p hp q hq a b ha hb hab
    change (0 : EReal) ≤ (((a • p + b • q).2 : ℝ) : EReal)
    have hp' : 0 ≤ p.2 := by
      exact_mod_cast hp
    have hq' : 0 ≤ q.2 := by
      exact_mod_cast hq
    exact_mod_cast add_nonneg (mul_nonneg ha hp') (mul_nonneg hb hq')

/-- Helper for Theorem 38.4: any universal proof of the current theorem shape would contradict
the dimension-one constant-zero specialization. -/
lemma helperForTheorem_38_4_universalClaimFalse
    (hGeneral :
      ∀ {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
        (_ : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
        (_ : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
        (_ : IsProperEReal f) (_ : IsERealConvex f),
        IsERealConvex (bifunctionImageRaw F f) ∧
          ((intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F)).Nonempty →
            fenchelConjugate n (bifunctionImageRaw F f) =
              bifunctionImageRaw (bifunctionInverseEuclideanAdjointTextbook F)
                (fenchelConjugate m f) ∧
            (∀ xStar : Fin n → ℝ,
              ∃ uStar : Fin m → ℝ,
                bifunctionImageRaw (bifunctionInverseEuclideanAdjointTextbook F)
                    (fenchelConjugate m f) xStar =
                  fenchelConjugate m f uStar +
                    (bifunctionInverseEuclideanAdjointTextbook F) uStar xStar))) :
    False := by
  rcases helperForTheorem_38_4_zeroSpecialization_hypotheses with
    ⟨hF_proper, hF_convex, hf_proper, hf_convex⟩
  -- Feed the zero specialization through the purported universal theorem statement.
  have hSpecialized :=
    hGeneral (m := 1) (n := 1)
      (fun _ _ : Fin 1 → ℝ => (0 : EReal))
      (fun _ : Fin 1 → ℝ => (0 : EReal))
      hF_proper hF_convex hf_proper hf_convex
  -- The previously proved specialization contradiction closes the argument.
  exact helperForTheorem_38_4_zeroSpecialization_targetFalse hSpecialized

-- Proof sketch: View `g(u, x) = f(u) + F(u, x)` as a proper convex function on the product
-- `ℝ^m × ℝ^n`. Partial minimization in `u` preserves convexity in `x`, giving convexity of `Ff`.
-- Under the relative-interior qualification condition `ri (dom f) ∩ ri (dom F) ≠ ∅`, apply the
-- Fenchel duality theorem (Theorems 5.7 and 31.1 in the text) to identify the conjugate of the
-- partial infimum with the dual infimum, and use the same qualification to get attainment.
/-- Theorem 38.4: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n`, and let `f` be a
proper convex function on `ℝ^m`. Then the image `Ff` is a convex function on `ℝ^n`.

If `ri (dom f)` and `ri (dom F)` have a point in common, then one has the conjugacy formula
`(Ff)^* = F_*^* f^*`, and the infimum in the definition of `(F_*^* f^*)(x^*)` is attained for each
`x^*`.

In Lean:
- `Ff` is `bifunctionImageRaw F f`;
- the domain `dom f` is `erealDom f`, and `dom F` is `bifunctionDom F`;
- `f^*` is `fenchelConjugate m f`;
- `F_*` is `bifunctionInverse F`, and `F_*^*` is `bifunctionInverseBookAdjoint F`;
- `F_*^* f^*` is `bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f)`. -/
theorem theorem38_4_image_convex_and_conjugate
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f) :
    IsERealConvex (bifunctionImageRaw F f) ∧
      ( (intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F)).Nonempty →
        fenchelConjugate n (bifunctionImageRaw F f) =
          bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f) ∧
        (∀ xStar : Fin n → ℝ,
          ∃ uStar : Fin m → ℝ,
            bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f)
                xStar =
              fenchelConjugate m f uStar +
                (bifunctionInverseBookAdjoint F) uStar xStar) ) :=
  by
    refine ⟨?_, ?_⟩
    · -- First discharge the convexity half by rewriting `Ff` as a fiber infimum of a convex
      -- function on the product space and applying Theorem 5.7.
      exact helperForTheorem_38_4_imageConvex F f hF_proper hF_convex hf_proper hf_convex
    · intro hri
      let liftedf : (Fin (m + n) → ℝ) → EReal :=
        fun z => f (fun i => z (Fin.castAdd n i))
      let liftedF : (Fin (m + n) → ℝ) → EReal := bifunctionGraphFunction F
      let projU : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
        { toFun := fun z i => z (Fin.castAdd n i)
          map_add' := by intro z w; ext i; simp
          map_smul' := by intro a z; ext i; simp }
      have hliftedf_proper : IsProperEReal liftedf := by
        constructor
        · intro z
          exact hf_proper.1 (fun i => z (Fin.castAdd n i))
        · rcases hf_proper.2 with ⟨u0, hu0⟩
          exact ⟨Fin.append u0 (0 : Fin n → ℝ), by simpa [liftedf]⟩
      have hliftedF_proper : IsProperEReal liftedF := by
        constructor
        · intro z
          exact hF_proper.1
            (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
        · rcases hF_proper.2 with ⟨p0, hp0⟩
          exact ⟨Fin.append p0.1 p0.2, by simpa [liftedF, bifunctionGraphFunction]⟩
      have hliftedf_convex : IsERealConvex liftedf := by
        simpa [liftedf, projU] using
          (helperForTheorem_38_4_isERealConvex_precomp_linearMap
            (A := projU) (g := f) hf_convex)
      let pairMap :
          (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
        { toFun := fun z =>
            (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
          map_add' := by intro z w; ext i <;> simp
          map_smul' := by intro a z; ext i <;> simp }
      have hliftedF_convex : IsERealConvex liftedF := by
        simpa [liftedF, pairMap, bifunctionGraphFunction] using
          (helperForTheorem_38_4_isERealConvex_precomp_linearMap
            (A := pairMap)
            (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) hF_convex)
      have hliftedf_pc :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) liftedf :=
        helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
          liftedf hliftedf_proper hliftedf_convex
      have hliftedF_pc :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) liftedF :=
        helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
          liftedF hliftedF_proper hliftedF_convex
      have hriPacked :
          (intrinsicInterior ℝ
                (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedf) ∩
              intrinsicInterior ℝ
                (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) liftedF)).Nonempty := by
        simpa [liftedf, liftedF] using
          helperForTheorem_38_4_packedSummands_hri
            F f hF_proper hF_convex hf_convex hri
      let fTwo : Fin 2 → (Fin (m + n) → ℝ) → EReal :=
        fun i => if i = 0 then liftedf else liftedF
      have hfTwo :
          ∀ i : Fin 2,
            ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (fTwo i) := by
        intro i
        fin_cases i
        · simpa [fTwo] using hliftedf_pc
        · simpa [fTwo] using hliftedF_pc
      have hriTwo := section16_hri_two_of_intrinsic liftedf liftedF hriPacked
      have hSec :=
        section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
          fTwo hfTwo hriTwo
      have hSecEq :
          fenchelConjugate (m + n) (fun z => liftedf z + liftedF z) =
            infimalConvolution (fenchelConjugate (m + n) liftedf)
              (fenchelConjugate (m + n) liftedF) := by
        simpa [fTwo, Fin.sum_univ_two,
          infimalConvolution_eq_infimalConvolutionFamily_two] using hSec.1
      have hliftedF_conj_ne_bot :
          ∀ zStar : Fin (m + n) → ℝ,
            fenchelConjugate (m + n) liftedF zStar ≠ (⊥ : EReal) := by
        intro zStar
        apply fenchelConjugate_ne_bot_of_exists_ne_top (m + n) liftedF
        rcases hF_proper.2 with ⟨p0, hp0⟩
        exact ⟨Fin.append p0.1 p0.2, by simpa [liftedF, bifunctionGraphFunction]⟩
      have hInfEq (xStar : Fin n → ℝ) :
          infimalConvolution (fenchelConjugate (m + n) liftedf)
              (fenchelConjugate (m + n) liftedF)
              (Fin.append (0 : Fin m → ℝ) xStar) =
            bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f) xStar := by
        rw [infimalConvolution_eq_iInf_second, bifunctionImageRaw]
        apply le_antisymm
        · refine le_iInf ?_
          intro uStar
          have hle := iInf_le
            (fun z : Fin (m + n) → ℝ =>
              fenchelConjugate (m + n) liftedF z +
                fenchelConjugate (m + n) liftedf
                  (Fin.append (0 : Fin m → ℝ) xStar - z))
            (Fin.append (-uStar) xStar)
          have hdiff0 :
              Fin.append (0 : Fin m → ℝ) xStar - Fin.append (-uStar) xStar =
                Fin.append uStar (0 : Fin n → ℝ) := by
            ext i
            cases i using Fin.addCases <;> simp
          calc
            _ ≤ fenchelConjugate (m + n) liftedF (Fin.append (-uStar) xStar) +
                fenchelConjugate (m + n) liftedf
                  (Fin.append (0 : Fin m → ℝ) xStar - Fin.append (-uStar) xStar) := hle
            _ = fenchelConjugate m f uStar +
                bifunctionInverseBookAdjoint F uStar xStar := by
              rw [hdiff0,
                helperForTheorem_38_4_liftedParameterFirst_conjugate f hf_proper,
                if_pos rfl]
              simp [liftedF, bifunctionInverseBookAdjoint,
                adjointGraphDualVector, add_comm]
        · refine le_iInf ?_
          intro z
          let c : Fin m → ℝ := fun i => z (Fin.castAdd n i)
          let d : Fin n → ℝ := fun j => z (Fin.natAdd m j)
          have hz : z = Fin.append c d := by
            ext i
            cases i using Fin.addCases <;> simp [c, d]
          have hdiff :
              Fin.append (0 : Fin m → ℝ) xStar - z =
                Fin.append (-c) (xStar - d) := by
            rw [hz]
            ext i
            cases i using Fin.addCases <;> simp
          have hdiff' :
              Fin.append (0 : Fin m → ℝ) xStar - Fin.append c d =
                Fin.append (-c) (xStar - d) := by
            simpa [hz] using hdiff
          by_cases hd : xStar - d = 0
          · have hd' : d = xStar := by
              exact sub_eq_zero.mp hd |>.symm
            have hle := iInf_le
              (fun uStar : Fin m → ℝ =>
                fenchelConjugate m f uStar + bifunctionInverseBookAdjoint F uStar xStar) (-c)
            calc
              _ ≤ fenchelConjugate m f (-c) +
                  bifunctionInverseBookAdjoint F (-c) xStar := hle
              _ = fenchelConjugate (m + n) liftedF z +
                  fenchelConjugate (m + n) liftedf
                    (Fin.append (0 : Fin m → ℝ) xStar - z) := by
                rw [hz, hdiff', hd,
                  helperForTheorem_38_4_liftedParameterFirst_conjugate f hf_proper,
                  if_pos rfl]
                simp [liftedF, bifunctionInverseBookAdjoint, adjointGraphDualVector,
                  hd', add_comm]
          · rw [hdiff, helperForTheorem_38_4_liftedParameterFirst_conjugate f hf_proper,
              if_neg hd]
            simp [hliftedF_conj_ne_bot z]
      have hConjEq :
          fenchelConjugate n (bifunctionImageRaw F f) =
            bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f) := by
        funext xStar
        calc
          fenchelConjugate n (bifunctionImageRaw F f) xStar =
              fenchelConjugate (m + n) (fun z => liftedf z + liftedF z)
                (Fin.append (0 : Fin m → ℝ) xStar) := by
            simpa [liftedf, liftedF] using
              helperForTheorem_38_4_imageConjugate_eq_packedSumConjugate F f xStar
          _ = infimalConvolution (fenchelConjugate (m + n) liftedf)
                (fenchelConjugate (m + n) liftedF)
                (Fin.append (0 : Fin m → ℝ) xStar) :=
            congrFun hSecEq (Fin.append (0 : Fin m → ℝ) xStar)
          _ = bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f)
                xStar := hInfEq xStar
      refine ⟨hConjEq, ?_⟩
      intro xStar
      let target : Fin (m + n) → ℝ := Fin.append (0 : Fin m → ℝ) xStar
      let D : EReal :=
        infimalConvolutionFamily (fun i => fenchelConjugate (m + n) (fTwo i)) target
      have hDdual :
          D = bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f) xStar := by
        calc
          D =
              fenchelConjugate (m + n) (fun z => ∑ i, fTwo i z) target :=
            congrFun hSec.1.symm target
          _ = fenchelConjugate (m + n) (fun z => liftedf z + liftedF z) target := by
            congr 1
            funext z
            simp [fTwo, Fin.sum_univ_two]
          _ = infimalConvolution (fenchelConjugate (m + n) liftedf)
                (fenchelConjugate (m + n) liftedF) target :=
            congrFun hSecEq target
          _ = bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f)
                xStar := by simpa [target] using hInfEq xStar
      by_cases hDtop : D = ⊤
      · refine ⟨0, ?_⟩
        have hle := iInf_le
          (fun uStar : Fin m → ℝ =>
            fenchelConjugate m f uStar + bifunctionInverseBookAdjoint F uStar xStar) 0
        have htermTop :
            fenchelConjugate m f 0 + bifunctionInverseBookAdjoint F 0 xStar = ⊤ := by
          have htopLe :
              (⊤ : EReal) ≤
                fenchelConjugate m f 0 + bifunctionInverseBookAdjoint F 0 xStar := by
            calc
              (⊤ : EReal) = D := hDtop.symm
              _ = bifunctionImageRaw (bifunctionInverseBookAdjoint F)
                    (fenchelConjugate m f) xStar := hDdual
              _ ≤ fenchelConjugate m f 0 +
                    bifunctionInverseBookAdjoint F 0 xStar := hle
          exact top_unique htopLe
        rw [← hDdual, hDtop, htermTop]
      · have hAtt := hSec.2 target
        rcases hAtt with htop | hAtt
        · exact (hDtop htop).elim
        · rcases hAtt with ⟨w, hwSum, hwVal⟩
          let z0 := w 0
          let z1 := w 1
          let b0 : Fin m → ℝ := fun i => z0 (Fin.castAdd n i)
          let a0 : Fin n → ℝ := fun j => z0 (Fin.natAdd m j)
          have hz0 : z0 = Fin.append b0 a0 := by
            ext i
            cases i using Fin.addCases <;> simp [b0, a0]
          have hwSum' : z0 + z1 = target := by
            simpa [z0, z1, Fin.sum_univ_two] using hwSum
          have hGraphNeBot : fenchelConjugate (m + n) liftedF z1 ≠ (⊥ : EReal) :=
            hliftedF_conj_ne_bot z1
          have ha0 : a0 = 0 := by
            by_contra ha0
            have hCylTop : fenchelConjugate (m + n) liftedf z0 = ⊤ := by
              rw [hz0,
                helperForTheorem_38_4_liftedParameterFirst_conjugate f hf_proper,
                if_neg ha0]
            have hSumTop :
                fenchelConjugate (m + n) liftedf z0 +
                    fenchelConjugate (m + n) liftedF z1 = ⊤ := by
              rw [hCylTop]
              simp [hGraphNeBot]
            change
              ∑ i, fenchelConjugate (m + n) (fTwo i) (w i) = D at hwVal
            have : D = ⊤ := by
              rw [← hwVal]
              simpa [fTwo, z0, z1, Fin.sum_univ_two, add_comm] using hSumTop
            exact hDtop this
          have hz1 : z1 = Fin.append (-b0) xStar := by
            rw [hz0, ha0] at hwSum'
            ext i
            cases i using Fin.addCases with
            | left i =>
                have h := congrFun hwSum' (Fin.castAdd n i)
                simp [target] at h ⊢
                linarith
            | right j =>
                have h := congrFun hwSum' (Fin.natAdd m j)
                simpa [target] using h
          refine ⟨b0, ?_⟩
          calc
            bifunctionImageRaw (bifunctionInverseBookAdjoint F)
                (fenchelConjugate m f) xStar = D := hDdual.symm
            _ = ∑ i, fenchelConjugate (m + n) (fTwo i) (w i) := hwVal.symm
            _ = fenchelConjugate m f b0 +
                bifunctionInverseBookAdjoint F b0 xStar := by
              simp [fTwo, z0, z1, Fin.sum_univ_two, hz0, ha0, hz1,
                liftedf, liftedF,
                helperForTheorem_38_4_liftedParameterFirst_conjugate,
                hf_proper, bifunctionInverseBookAdjoint, adjointGraphDualVector]

/-
Historical note: the helper lemmas in this block record why the earlier local model
`bifunctionInverseEuclideanAdjointTextbook` could not serve as the book's `F_*^*` in
Corollary 38.4.1. The actual theorem statement below now uses the Chapter 34 object
`bifunctionInverseBookAdjoint` instead.
-/
/-- Helper for Corollary 38.4.1: the dimension-one constant-zero specialization satisfies all
closedness, properness, and convexity hypotheses appearing in the corollary statement. -/
lemma helperForCorollary_38_4_1_zeroSpecialization_hypotheses :
    IsProductLowerSemicontinuousBifunction (fun _ _ : Fin 1 → ℝ => (0 : EReal)) ∧
      IsProperEReal (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)) ∧
      IsERealConvex (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)) ∧
      LowerSemicontinuous (fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      IsProperEReal (fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      IsERealConvex (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
  rcases helperForTheorem_38_4_zeroSpecialization_hypotheses with
    ⟨hF_proper, hF_convex, hf_proper, hf_convex⟩
  refine ⟨?_, hF_proper, hF_convex, ?_, hf_proper, hf_convex⟩
  · -- The zero bifunction is constant on the product, so product lower semicontinuity is immediate.
    simpa [IsProductLowerSemicontinuousBifunction] using
      (lowerSemicontinuous_const :
        LowerSemicontinuous (fun _ : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)))
  · -- The zero primal function is likewise lower semicontinuous.
    simpa using
      (lowerSemicontinuous_const :
        LowerSemicontinuous (fun _ : Fin 1 → ℝ => (0 : EReal)))

/-- Helper for Corollary 38.4.1: the conjugate of the dimension-one constant-zero function is
finite exactly at the dual origin. -/
lemma helperForCorollary_38_4_1_constZero_conjugateDom :
    erealDom (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) =
      ({helperForProposition_36_4_3_zeroVector} : Set (Fin 1 → ℝ)) := by
  ext xStar
  constructor
  · intro hxDom
    by_contra hxNe
    have hcoord : xStar 0 ≠ 0 := by
      intro hzero
      apply hxNe
      ext i
      fin_cases i
      simp [helperForProposition_36_4_3_zeroVector, hzero]
    have hTop :
        fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) xStar = (⊤ : EReal) := by
      rw [fenchelConjugate, EReal.eq_top_iff_forall_lt]
      intro y
      let x : Fin 1 → ℝ := fun _ => (y + 1) / (xStar 0)
      have hmem :
          (((y + 1 : ℝ) : EReal)) ∈
            Set.range
              (fun x : Fin 1 → ℝ =>
                ((x ⬝ᵥ xStar : ℝ) : EReal) - (0 : EReal)) := by
        refine ⟨x, ?_⟩
        have hdot : x ⬝ᵥ xStar = y + 1 := by
          simp [x, dotProduct, hcoord]
        simp [hdot]
      have hlt : ((y : ℝ) : EReal) < (((y + 1 : ℝ) : EReal)) := by
        exact_mod_cast (show y < y + 1 by linarith)
      exact lt_of_lt_of_le hlt (le_sSup hmem)
    have hxNotTop : fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) xStar < (⊤ : EReal) := by
      simpa [erealDom] using hxDom
    simpa [hTop] using hxNotTop
  · intro hxEq
    subst hxEq
    -- At the dual origin the defining supremum contains only the value `0`.
    simp [erealDom, fenchelConjugate, helperForProposition_36_4_3_zeroVector, dotProduct]

/-- Helper for Corollary 38.4.1: the strengthened relative-interior qualification still holds for
the dimension-one constant-zero specialization. -/
lemma helperForCorollary_38_4_1_zeroSpecialization_qualification :
    (intrinsicInterior ℝ
          (erealDom (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)))) ∩
        intrinsicInterior ℝ
          (bifunctionDom
            (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (fun _ _ : Fin 1 → ℝ => (0 : EReal))))).Nonempty := by
  have hDomConj :
      erealDom (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) =
        ({helperForProposition_36_4_3_zeroVector} : Set (Fin 1 → ℝ)) :=
    helperForCorollary_38_4_1_constZero_conjugateDom
  have hDomAdjoint :
      bifunctionDom
          (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
            (fun _ _ : Fin 1 → ℝ => (0 : EReal))) =
        (Set.univ : Set (Fin 1 → ℝ)) := by
    ext uStar
    constructor
    · intro _
      simp
    · intro _
      refine ⟨helperForProposition_36_4_3_zeroVector, ?_⟩
      -- Choosing the origin in both infima bounds the textbook iterate above by `0`.
      intro htop
      have hUpper :
          bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (fun _ _ : Fin 1 → ℝ => (0 : EReal))
              uStar helperForProposition_36_4_3_zeroVector ≤
            (0 : EReal) := by
        refine iInf_le_of_le helperForProposition_36_4_3_zeroVector ?_
        refine iInf_le_of_le helperForProposition_36_4_3_zeroVector ?_
        simp [bifunctionInverseEuclideanAdjointTextbook, bifunctionEuclideanAdjointTextbook,
          bifunctionInverse, finDot, dotProduct, helperForProposition_36_4_3_zeroVector]
      have : ¬ ((⊤ : EReal) ≤ (0 : EReal)) := by simp
      exact this (by simpa [htop] using hUpper)
  refine ⟨helperForProposition_36_4_3_zeroVector, ?_⟩
  constructor
  · -- The conjugate domain is the singleton `{0}`, whose intrinsic interior is itself.
    rw [hDomConj]
    simpa [intrinsicInterior_singleton]
  · -- The textbook iterate has full domain in the first variable for this specialization.
    rw [hDomAdjoint]
    exact
      interior_subset_intrinsicInterior
        (by simp :
          helperForProposition_36_4_3_zeroVector ∈ interior (Set.univ : Set (Fin 1 → ℝ)))

/-- Helper for Corollary 38.4.1: once the dual image already attains `⊥`, the current closure
operator collapses it to the constant `⊥` function. -/
lemma helperForCorollary_38_4_1_zeroSpecialization_rhsClosure_eq_const_bot :
    erealFunctionClosure
        (bifunctionImageRaw
          (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
            (fun _ _ : Fin 1 → ℝ => (0 : EReal)))
          (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)))) =
      fun _ : Fin 1 → ℝ => (⊥ : EReal) := by
  let raw :
      (Fin 1 → ℝ) → EReal :=
    bifunctionImageRaw
      (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
        (fun _ _ : Fin 1 → ℝ => (0 : EReal)))
      (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)))
  have hnot : ¬ ∀ x : Fin 1 → ℝ, raw x ≠ (⊥ : EReal) := by
    intro hall
    exact
      (hall helperForProposition_36_4_3_oneVector)
        helperForTheorem_38_4_zeroSpecialization_rightAtOne_eq_bot
  -- Once the raw dual image hits `⊥`, the closure definition takes its constant `⊥` branch.
  funext x
  unfold erealFunctionClosure
  rw [if_neg hnot]

/-- Helper for Corollary 38.4.1: the corollary conclusion is false on the dimension-one
constant-zero specialization. -/
lemma helperForCorollary_38_4_1_zeroSpecialization_targetFalse
    (hClosed :
      LowerSemicontinuous
        (bifunctionImageRaw
          (fun _ _ : Fin 1 → ℝ => (0 : EReal))
          (fun _ : Fin 1 → ℝ => (0 : EReal))))
    (hAttained :
      ∀ x : Fin 1 → ℝ,
        ∃ u : Fin 1 → ℝ,
          bifunctionImageRaw
              (fun _ _ : Fin 1 → ℝ => (0 : EReal))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              x =
            (fun _ : Fin 1 → ℝ => (0 : EReal)) u +
              (fun _ _ : Fin 1 → ℝ => (0 : EReal)) u x)
    (hEq :
      (fenchelConjugate 1
          (bifunctionImageRaw
            (fun _ _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 → ℝ => (0 : EReal))) =
        erealFunctionClosure
          (bifunctionImageRaw
            (bifunctionInverseEuclideanAdjointTextbook (m := 1) (n := 1)
              (fun _ _ : Fin 1 → ℝ => (0 : EReal)))
            (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)))))) :
    False := by
  let _ := hClosed
  let _ := hAttained
  have hAtOne := congrFun hEq helperForProposition_36_4_3_oneVector
  -- Evaluating the claimed equality at `x* = 1` produces the contradiction `⊤ = ⊥`.
  rw [helperForTheorem_38_4_zeroSpecialization_leftAtOne_eq_top,
    helperForCorollary_38_4_1_zeroSpecialization_rhsClosure_eq_const_bot] at hAtOne
  simp at hAtOne

/-- Helper for Corollary 38.4.1: any proof of the current universal corollary schema would already
contradict the dimension-one constant-zero specialization. -/
lemma helperForCorollary_38_4_1_universalClaimFalse
    (hGeneral :
      ∀ {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
        (_ : IsProductLowerSemicontinuousBifunction F)
        (_ : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
        (_ : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
        (_ : LowerSemicontinuous f) (_ : IsProperEReal f) (_ : IsERealConvex f)
        (_ :
          (intrinsicInterior ℝ (erealDom (fenchelConjugate m f)) ∩
              intrinsicInterior ℝ
                (bifunctionDom (bifunctionInverseEuclideanAdjointTextbook F))).Nonempty),
        LowerSemicontinuous (bifunctionImageRaw F f) ∧
          (∀ x : Fin n → ℝ, ∃ u : Fin m → ℝ, bifunctionImageRaw F f x = f u + F u x) ∧
          fenchelConjugate n (bifunctionImageRaw F f) =
            erealFunctionClosure
              (bifunctionImageRaw (bifunctionInverseEuclideanAdjointTextbook F)
                (fenchelConjugate m f))) :
    False := by
  rcases helperForCorollary_38_4_1_zeroSpecialization_hypotheses with
    ⟨hF_closed, hF_proper, hF_convex, hf_closed, hf_proper, hf_convex⟩
  have hSpecialized :=
    hGeneral (m := 1) (n := 1)
      (fun _ _ : Fin 1 → ℝ => (0 : EReal))
      (fun _ : Fin 1 → ℝ => (0 : EReal))
      hF_closed hF_proper hF_convex hf_closed hf_proper hf_convex
      helperForCorollary_38_4_1_zeroSpecialization_qualification
  -- The specialized conclusion contradicts the explicit `x* = 1` computation proved above.
  exact
    helperForCorollary_38_4_1_zeroSpecialization_targetFalse
      hSpecialized.1 hSpecialized.2.1 hSpecialized.2.2

/-- Negate the first block of a packed `(u,x)` vector. -/
noncomputable def signFirstBlock {m n : Nat} (z : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  Fin.append (fun i => -z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

lemma signFirstBlock_involutive {m n : Nat} (z : Fin (m + n) → ℝ) :
    signFirstBlock (signFirstBlock z) = z := by
  ext i
  cases i using Fin.addCases <;> simp [signFirstBlock]

lemma dotProduct_signFirstBlock {m n : Nat} (z w : Fin (m + n) → ℝ) :
    dotProduct (signFirstBlock z) (signFirstBlock w) = dotProduct z w := by
  simp [dotProduct, Fin.sum_univ_add, signFirstBlock]

lemma fenchelConjugate_precomp_signFirstBlock {m n : Nat}
    (g : (Fin (m + n) → ℝ) → EReal) (y : Fin (m + n) → ℝ) :
    fenchelConjugate (m + n) (fun z => g (signFirstBlock z)) (signFirstBlock y) =
      fenchelConjugate (m + n) g y := by
  rw [fenchelConjugate_eq_iSup, fenchelConjugate_eq_iSup]
  apply le_antisymm
  · refine iSup_le ?_
    intro z
    calc
      (((dotProduct z (signFirstBlock y) : ℝ) : EReal) - g (signFirstBlock z)) =
          (((dotProduct (signFirstBlock z) y : ℝ) : EReal) - g (signFirstBlock z)) := by
            rw [← dotProduct_signFirstBlock z (signFirstBlock y),
              signFirstBlock_involutive]
      _ ≤ ⨆ w : Fin (m + n) → ℝ,
          (((dotProduct w y : ℝ) : EReal) - g w) :=
        le_iSup (fun w : Fin (m + n) → ℝ =>
          (((dotProduct w y : ℝ) : EReal) - g w)) (signFirstBlock z)
  · refine iSup_le ?_
    intro z
    have hle := le_iSup
      (fun w : Fin (m + n) → ℝ =>
        (((dotProduct w (signFirstBlock y) : ℝ) : EReal) - g (signFirstBlock w)))
      (signFirstBlock z)
    simpa [signFirstBlock_involutive, dotProduct_signFirstBlock] using hle

lemma packedGraph_biconjugate_eq {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_closed : IsProductLowerSemicontinuousBifunction F)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2)) :
    fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F)) =
      bifunctionGraphFunction F := by
  let split : (Fin (m + n) → ℝ) → (Fin m → ℝ) × (Fin n → ℝ) :=
    fun z => ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
  have hsplit : Continuous split := by fun_prop
  have hclosed : LowerSemicontinuous (bifunctionGraphFunction F) := by
    simpa [IsProductLowerSemicontinuousBifunction, bifunctionGraphFunction, split] using
      hF_closed.comp_continuous hsplit
  let pairMap :
      (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := split
      map_add' := by intro z w; ext i <;> simp [split]
      map_smul' := by intro a z; ext i <;> simp [split] }
  have hconvE : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [bifunctionGraphFunction, split, pairMap] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) hF_convex)
  have hconv : ConvexFunction (bifunctionGraphFunction F) := by
    simpa [IsERealConvex, ConvexFunction,
      helperForTheorem_38_1_epigraph_eq_univ] using hconvE
  have hnobot : ∀ z, bifunctionGraphFunction F z ≠ (⊥ : EReal) := by
    intro z
    exact hF_proper.1 (split z)
  exact fenchelConjugate_biconjugate_eq_of_closedConvex (m + n)
    (bifunctionGraphFunction F) hclosed hconv hnobot

lemma bifunctionInverseBookAdjoint_biadjoint_eq {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_closed : IsProductLowerSemicontinuousBifunction F)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2)) :
    bifunctionInverseBookAdjoint (bifunctionInverseBookAdjoint F) = F := by
  funext u x
  rw [bifunctionInverseBookAdjoint]
  have hgraph :
      bifunctionGraphFunction (bifunctionInverseBookAdjoint F) =
        fun z => fenchelConjugate (m + n) (bifunctionGraphFunction F) (signFirstBlock z) := by
    funext z
    unfold bifunctionGraphFunction bifunctionInverseBookAdjoint
    congr 1
  rw [hgraph]
  have hdual : adjointGraphDualVector u x = signFirstBlock (Fin.append u x) := by
    ext i
    cases i using Fin.addCases <;>
      simp [adjointGraphDualVector, signFirstBlock]
  rw [hdual, fenchelConjugate_precomp_signFirstBlock,
    packedGraph_biconjugate_eq F hF_closed hF_proper hF_convex]
  simp [bifunctionGraphFunction]

lemma isProperEReal_of_properConvexFunctionOn_univ {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsProperEReal f := by
  refine ⟨?_, ?_⟩
  · intro x
    exact hf.2.2 x (by simp)
  · rcases (nonempty_epigraph_iff_nonempty_effectiveDomain
      (Set.univ : Set (Fin n → ℝ)) f).1 hf.2.1 with ⟨x, hx⟩
    exact ⟨x, mem_effectiveDomain_imp_ne_top hx⟩

lemma convexFunctionClosure_eq_erealFunctionClosure_of_convex {n : Nat}
    {g : (Fin n → ℝ) → EReal} (hg : ConvexFunction g) :
    convexFunctionClosure g = erealFunctionClosure g := by
  classical
  by_cases hNoBot : ∀ x, g x ≠ (⊥ : EReal)
  · have hspec := Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) g)
    have hGenericLsc : LowerSemicontinuous (erealLowerSemicontinuousHull g) := by
      unfold erealLowerSemicontinuousHull
      exact lowerSemicontinuous_iSup (fun h => h.2.1)
    have hGenericLe : erealLowerSemicontinuousHull g ≤ g := by
      intro x
      rw [erealLowerSemicontinuousHull]
      exact iSup_le (fun h => h.2.2 x)
    have hChosenLeGeneric : lowerSemicontinuousHull g ≤ erealLowerSemicontinuousHull g := by
      intro x
      rw [erealLowerSemicontinuousHull]
      exact le_iSup_of_le ⟨lowerSemicontinuousHull g, hspec.1, hspec.2.1⟩ le_rfl
    have hGenericLeChosen : erealLowerSemicontinuousHull g ≤ lowerSemicontinuousHull g :=
      hspec.2.2 _ hGenericLsc hGenericLe
    unfold convexFunctionClosure erealFunctionClosure
    simp [hNoBot, le_antisymm hChosenLeGeneric hGenericLeChosen]
  · push_neg at hNoBot
    rcases hNoBot with ⟨x, hx⟩
    have hConvBot : convexFunctionClosure g = fun _ => (⊥ : EReal) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := g) ⟨x, hx⟩
    rw [hConvBot]
    unfold erealFunctionClosure
    rw [if_neg]
    push_neg
    exact ⟨x, hx⟩

/-- Corollary 38.4.1: Let `F` be a closed proper convex bifunction from `ℝ^m` to `ℝ^n`, and let
`f` be a closed proper convex function on `ℝ^m`. If `ri (dom f^*)` meets `ri (dom F_*^*)`, then
`Ff` is closed, and the infimum in the definition of `(Ff)(x)` is attained for each `x`.
Moreover, then `(Ff)^* = cl (F_*^* f^*)`.

In Lean:
- closedness of `F` is `IsProductLowerSemicontinuousBifunction F` and of `f`/`Ff` is `LowerSemicontinuous`;
- `Ff` is `bifunctionImageRaw F f`;
- `f^*` is `fenchelConjugate m f`;
- `F_*^*` is `bifunctionInverseBookAdjoint F`;
- `cl` on functions is modeled by `erealFunctionClosure`;
- `ri` is modeled by `intrinsicInterior`, applied to `erealDom (fenchelConjugate m f)` and
  `bifunctionDom (bifunctionInverseBookAdjoint F)`. -/
theorem corollary38_4_1_image_closed_and_infimum_attained_and_conjugate_eq_closure
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
    (hF_closed : IsProductLowerSemicontinuousBifunction F)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_closed : LowerSemicontinuous f) (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hri :
      (intrinsicInterior ℝ (erealDom (fenchelConjugate m f)) ∩
          intrinsicInterior ℝ (bifunctionDom (bifunctionInverseBookAdjoint F))).Nonempty) :
    LowerSemicontinuous (bifunctionImageRaw F f) ∧
      (∀ x : (Fin n → ℝ), ∃ u : (Fin m → ℝ), bifunctionImageRaw F f x = f u + F u x) ∧
      fenchelConjugate n (bifunctionImageRaw F f) =
        erealFunctionClosure
          (bifunctionImageRaw (bifunctionInverseBookAdjoint F) (fenchelConjugate m f)) := by
  let G := bifunctionInverseBookAdjoint F
  let fStar := fenchelConjugate m f
  let graphF := bifunctionGraphFunction F
  have hgraphFProper : IsProperEReal graphF := by
    refine ⟨?_, ?_⟩
    · intro z
      exact hF_proper.1
        ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
    · rcases hF_proper.2 with ⟨p, hp⟩
      exact ⟨Fin.append p.1 p.2, by simpa [graphF, bifunctionGraphFunction]⟩
  let pairMap :
      (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun z =>
        ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
      map_add' := by intro z w; ext i <;> simp
      map_smul' := by intro a z; ext i <;> simp }
  have hgraphFConvex : IsERealConvex graphF := by
    simpa [graphF, pairMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) hF_convex)
  have hgraphFPC : ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) graphF :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      graphF hgraphFProper hgraphFConvex
  have hconjPC :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (fenchelConjugate (m + n) graphF) :=
    proper_fenchelConjugate_of_proper (m + n) hgraphFPC
  have hconjProper : IsProperEReal (fenchelConjugate (m + n) graphF) :=
    isProperEReal_of_properConvexFunctionOn_univ hconjPC
  have hconjConvex : IsERealConvex (fenchelConjugate (m + n) graphF) := by
    have hc := (fenchelConjugate_closedConvex (m + n) graphF).2
    simpa [IsERealConvex, ConvexFunction,
      helperForTheorem_38_1_epigraph_eq_univ] using hc
  let signedPairMap :
      ((Fin m → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun p => Fin.append (-p.1) p.2
      map_add' := by intro p q; ext i; cases i using Fin.addCases <;> simp [add_comm]
      map_smul' := by intro a p; ext i; cases i using Fin.addCases <;> simp }
  have hGConvex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => G p.1 p.2) := by
    simpa [G, graphF, signedPairMap, bifunctionInverseBookAdjoint,
      adjointGraphDualVector] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := signedPairMap) hconjConvex)
  have hGProper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => G p.1 p.2) := by
    constructor
    · intro p
      exact hconjProper.1 (signedPairMap p)
    · rcases hconjProper.2 with ⟨z, hz⟩
      let u : Fin m → ℝ := fun i => -z (Fin.castAdd n i)
      let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
      refine ⟨(u, x), ?_⟩
      have hpack : signedPairMap (u, x) = z := by
        ext i
        cases i using Fin.addCases <;> simp [signedPairMap, u, x]
      change fenchelConjugate (m + n) graphF (signedPairMap (u, x)) ≠ ⊤
      rw [hpack]
      exact hz
  have hfPC : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  have hfStarPC : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) fStar := by
    simpa [fStar] using proper_fenchelConjugate_of_proper m hfPC
  have hfStarProper : IsProperEReal fStar :=
    isProperEReal_of_properConvexFunctionOn_univ hfStarPC
  have hfStarConvex : IsERealConvex fStar := by
    have hc := (fenchelConjugate_closedConvex m f).2
    simpa [fStar, IsERealConvex, ConvexFunction,
      helperForTheorem_38_1_epigraph_eq_univ] using hc
  have hDual := theorem38_4_image_convex_and_conjugate G fStar
    hGProper hGConvex hfStarProper hfStarConvex
  have hDualQualified := hDual.2 (by simpa [G, fStar] using hri)
  have hfBiconj : fenchelConjugate m fStar = f := by
    simpa [fStar] using
      fenchelConjugate_biconjugate_eq_of_closedConvex m f hf_closed
        (by simpa [IsERealConvex, ConvexFunction,
          helperForTheorem_38_1_epigraph_eq_univ] using hf_convex) hf_proper.1
  have hGBiadj : bifunctionInverseBookAdjoint G = F := by
    simpa [G] using
      bifunctionInverseBookAdjoint_biadjoint_eq F hF_closed hF_proper hF_convex
  let dualImage := bifunctionImageRaw G fStar
  have hPrimalEq : fenchelConjugate n dualImage = bifunctionImageRaw F f := by
    calc
      fenchelConjugate n dualImage =
          bifunctionImageRaw (bifunctionInverseBookAdjoint G)
            (fenchelConjugate m fStar) := by
              simpa [dualImage] using hDualQualified.1
      _ = bifunctionImageRaw F f := by rw [hGBiadj, hfBiconj]
  have hDualConvex : ConvexFunction dualImage := by
    simpa [dualImage, IsERealConvex, ConvexFunction,
      helperForTheorem_38_1_epigraph_eq_univ] using hDual.1
  refine ⟨?_, ?_, ?_⟩
  · rw [← hPrimalEq]
    exact (fenchelConjugate_closedConvex n dualImage).1
  · intro x
    rcases hDualQualified.2 x with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simpa [hGBiadj, hfBiconj] using hu
  · rw [← hPrimalEq]
    calc
      fenchelConjugate n (fenchelConjugate n dualImage) =
          convexFunctionClosure dualImage :=
        section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure hDualConvex
      _ = erealFunctionClosure dualImage :=
        convexFunctionClosure_eq_erealFunctionClosure_of_convex hDualConvex
      _ = erealFunctionClosure
          (bifunctionImageRaw (bifunctionInverseBookAdjoint F)
            (fenchelConjugate m f)) := by rfl

/-- Definition 38.4.1: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n`, and let `G` be a
proper convex bifunction from `ℝ^n` to `ℝ^p`. The composed bifunction `G ⊙ F` from `ℝ^m` to `ℝ^p`
is defined by

`((G ⊙ F) u) y = inf_{x : ℝ^n} ((F u) x + (G x) y)`.

When `F` and `G` are concave instead of convex, the text takes `sup` in place of `inf`. -/
noncomputable def bifunctionCompose {m n p : Nat}
    (G : FiberwiseProperConvexBifunction n p) (F : FiberwiseProperConvexBifunction m n) :
    (Fin m → ℝ) → (Fin p → ℝ) → EReal :=
  fun u y => ⨅ x : (Fin n → ℝ), F.toFun u x + G.toFun x y

/-- Supremum-based composition of raw bifunctions (the concave analogue of `bifunctionCompose`):
`(G ⊙ₛ F) u y = sup_x (F u x + G x y)`. -/
noncomputable def bifunctionComposeSup {m n p : Nat}
    (G : (Fin n → ℝ) → (Fin p → ℝ) → EReal) (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin p → ℝ) → EReal :=
  fun u y => ⨆ x : (Fin n → ℝ), F u x + G x y

/-- Helper for Proposition 38.4.2: negation sends an `iInf` in `EReal` to the corresponding
`iSup`. -/
lemma helperForProposition_38_4_2_neg_iInf {ι : Sort*} (h : ι → EReal) :
    -(⨅ i, h i) = ⨆ i, -h i := by
  -- Transport the infimum through the order isomorphism `x ↦ -x`.
  have hmap :
      OrderDual.ofDual (EReal.negOrderIso (iInf fun i => h i)) =
        OrderDual.ofDual (iInf fun i => EReal.negOrderIso (h i)) :=
    congrArg (fun z => OrderDual.ofDual z) (EReal.negOrderIso.map_iInf h)
  -- Reinterpret the transported infimum back as the desired supremum.
  calc
    -(⨅ i, h i) = OrderDual.ofDual (EReal.negOrderIso (iInf fun i => h i)) := by
      dsimp [EReal.negOrderIso]
    _ = OrderDual.ofDual (iInf fun i => EReal.negOrderIso (h i)) := by
      exact hmap
    _ = ⨆ i, OrderDual.ofDual (EReal.negOrderIso (h i)) := by
      exact ofDual_iInf (f := fun i => EReal.negOrderIso (h i))
    _ = ⨆ i, -h i := by
      simp [EReal.negOrderIso]

/-- Helper for Proposition 38.4.2: if neither summand is `⊥`, negating the sum reverses the
order of the two negated summands. -/
lemma helperForProposition_38_4_2_neg_add_of_neBot {a b : EReal}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    -(a + b) = (-b) + (-a) := by
  -- Properness excludes the forbidden `⊥` cases, so `EReal.neg_add` applies.
  simpa [sub_eq_add_neg, add_comm] using
    (EReal.neg_add (x := a) (y := b) (h1 := Or.inl ha) (h2 := Or.inr hb))

/-- Helper for Proposition 38.4.2: evaluating the supremum composition of the inverse
bifunctions gives the expected pointwise supremum formula. -/
lemma helperForProposition_38_4_2_composeSup_inverse_apply {m n p : Nat}
    (F : FiberwiseProperConvexBifunction m n) (G : FiberwiseProperConvexBifunction n p)
    (y : Fin p → ℝ) (u : Fin m → ℝ) :
    bifunctionComposeSup (bifunctionInverse F.toFun) (bifunctionInverse G.toFun) y u =
      ⨆ x : (Fin n → ℝ), (-G.toFun x y) + (-F.toFun u x) := by
  -- Unfold the reversed-order supremum composition and the inverse pointwise.
  simp [bifunctionComposeSup, bifunctionInverse]

-- Proof sketch: Unfold `bifunctionInverse` and `bifunctionCompose` to see that the left-hand side is
-- `-(inf_x (F u x + G x y))` with arguments swapped. Use that negation on `EReal` is order-reversing,
-- hence sends infima to suprema, to rewrite this as `sup_x (-G x y + -F u x)` and then recognize the
-- right-hand side as `bifunctionComposeSup (bifunctionInverse F) (bifunctionInverse G)` (with the
-- appropriate argument order).
/-- Proposition 38.4.2: For proper convex bifunctions `F` and `G`, the inverse of their composition
`GF` equals the composition of inverses in reversed order:

`(G ⊙ F)_* = F_* G_*`.

In Lean, `G ⊙ F` is `bifunctionCompose G F`, `F_*` is `bifunctionInverse F.toFun`, and the concave
composition on the right-hand side is `bifunctionComposeSup`. -/
theorem bifunctionInverse_compose_eq_composeSup_inverse {m n p : Nat}
    (F : FiberwiseProperConvexBifunction m n) (G : FiberwiseProperConvexBifunction n p) :
    bifunctionInverse (bifunctionCompose G F) =
      bifunctionComposeSup (bifunctionInverse F.toFun) (bifunctionInverse G.toFun) :=
  by
    funext y
    funext u
    -- First turn the negated infimum on the left into a supremum of negated summands.
    calc
      bifunctionInverse (bifunctionCompose G F) y u
          = -(⨅ x : (Fin n → ℝ), F.toFun u x + G.toFun x y) := by
            rfl
      _ = ⨆ x : (Fin n → ℝ), -(F.toFun u x + G.toFun x y) := by
            simpa using
              (helperForProposition_38_4_2_neg_iInf
                (h := fun x : (Fin n → ℝ) => F.toFun u x + G.toFun x y))
      _ = ⨆ x : (Fin n → ℝ), (-G.toFun x y) + (-F.toFun u x) := by
            -- Rewrite each summand using `EReal.neg_add`; properness rules out `⊥`.
            have hterm :
                (fun x : Fin n → ℝ => -(F.toFun u x + G.toFun x y)) =
                  (fun x : Fin n → ℝ => (-G.toFun x y) + (-F.toFun u x)) := by
              funext x
              exact helperForProposition_38_4_2_neg_add_of_neBot
                (ha := F.proper.1 u x) (hb := G.proper.1 x y)
            simp [hterm]
      _ = bifunctionComposeSup (bifunctionInverse F.toFun) (bifunctionInverse G.toFun) y u := by
            -- The remaining expression is exactly the reversed-order supremum composition.
            simpa using
              (helperForProposition_38_4_2_composeSup_inverse_apply
                (F := F) (G := G) (y := y) (u := u)).symm

end Section38
end Chap08
