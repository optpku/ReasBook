module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import stacks_project.Chap07.Example_7_6_5
public import stacks_project.Chap07.Proposition_7_33_3

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

namespace CategoryTheory

noncomputable section

variable (G : Type u) [Group G]

/-- Helper for GSetForgetfulPoint: the orbit map from the left regular `G`-set through a point
commutes with the `G`-actions. -/
theorem leftRegularOrbit_comm {X : Action (Type u) G} (x : X.V) :
    ∀ h : G,
      (Action.leftRegular G).ρ h ≫ (fun g : G ↦ X.ρ g x) =
        (fun g : G ↦ X.ρ g x) ≫ X.ρ h := by
  -- Pointwise, equivariance is exactly multiplicativity of the action homomorphism.
  intro h
  ext g
  exact congrFun (MonoidHom.map_mul X.ρ h g) x

/-- Helper for GSetForgetfulPoint: the orbit map from the left regular `G`-set through a chosen
point of a `G`-set. -/
def leftRegularOrbitHom {X : Action (Type u) G} (x : X.V) :
    Action.leftRegular G ⟶ X where
  hom := fun g ↦ X.ρ g x
  comm := leftRegularOrbit_comm G x

/-- Helper for GSetForgetfulPoint: a morphism out of the left regular `G`-set is determined by
its value at the identity. -/
theorem leftRegularOrbitHom_eq_of_apply_one
    {X : Action (Type u) G} (f : Action.leftRegular G ⟶ X) (x : X.V)
    (hf : f.hom (1 : G) = x) :
    f = leftRegularOrbitHom G x := by
  -- Evaluate equivariance at `1` to recover every value of `f` from the chosen point.
  apply Action.hom_ext
  ext g
  have hcomm := congrFun (f.comm g) (1 : G)
  simpa [types_comp_apply, hf, leftRegularOrbitHom] using hcomm

/-- Helper for GSetForgetfulPoint: the object `(G, 1)` is initial in the category of elements of
the forgetful functor on `G`-sets. -/
theorem gSetForgetful_elements_hasInitial :
    Limits.HasInitial (Functor.Elements (Action.forget (Type u) G)) := by
  -- The left regular action with basepoint `1` corepresents pointed elements of a `G`-set.
  let b : Functor.Elements (Action.forget (Type u) G) :=
    (Action.forget (Type u) G).elementsMk (Action.leftRegular G) (1 : G)
  refine (Limits.IsInitial.ofUniqueHom (X := b) ?hom ?uniq).hasInitial
  · -- Send the base point to the target element by the orbit map.
    intro Y
    refine CategoryOfElements.homMk b Y (leftRegularOrbitHom G Y.2) ?_
    simp [b, leftRegularOrbitHom, Action.forget_map]
  · -- Any other morphism has the same value at `1`, hence is the same orbit map.
    intro Y m
    apply CategoryOfElements.ext (Action.forget (Type u) G)
    apply leftRegularOrbitHom_eq_of_apply_one
    simpa [b, Action.forget_map] using m.property

-- Proof sketch: the category of elements has the explicit initial object `(G, 1)`, and a category
-- with an initial object is initially small.
instance gSetForgetful_elements_initiallySmall :
    InitiallySmall.{u} (Functor.Elements (Action.forget (Type u) G)) := by
  -- Feed the explicit initial object to the standard `HasInitial → InitiallySmall` instance.
  haveI : Limits.HasInitial (Functor.Elements (Action.forget (Type u) G)) :=
    gSetForgetful_elements_hasInitial G
  infer_instance

-- Proof sketch: apply `Action.mem_jointlySurjectiveTopology_iff`; by covering-surjectivity, the chosen point
-- `x : X.V` lies in the image of some arrow belonging to the covering sieve.
/-- Covering sieves in `\mathcal T_G` act jointly surjectively on the forgetful fiber functor. -/
theorem gSetForgetful_jointly_surjective
    {X : Action (Type u) G} (R : Sieve X)
    (hR : R ∈ Action.jointlySurjectiveTopology G X) (x : X.V) :
    ∃ (Y : Action (Type u) G) (f : Y ⟶ X), R f ∧
      ∃ y : Y.V, (Action.forget (Type u) G).map f y = x := by
  -- Rewrite covering membership into the pointwise range condition and unpack the preimage.
  rw [Action.mem_jointlySurjectiveTopology_iff] at hR
  rcases hR x with ⟨Y, f, hf, y, hy⟩
  exact ⟨Y, f, hf, y, by simpa [Action.forget_map] using hy⟩

/-- Helper for GSetForgetfulPoint: the covering-lift condition in the constructor shape required
for a point of the jointly surjective topology. -/
theorem gSetForgetfulPointJointlySurjective :
    ∀ {X : Action (Type u) G}, ∀ R ∈ Action.jointlySurjectiveTopology G X,
      ∀ x : (Action.forget (Type u) G).obj X,
        ∃ (Y : Action (Type u) G) (f : Y ⟶ X), ∃ (_ : R.arrows f),
          ∃ y : (Action.forget (Type u) G).obj Y,
            (Action.forget (Type u) G).map f y = x := by
  -- The public surjectivity lemma has the same content, with the first two witnesses paired.
  intro X R hR x
  rcases gSetForgetful_jointly_surjective G R hR x with ⟨Y, f, hf, y, hy⟩
  exact ⟨Y, f, hf, y, hy⟩

/-- GSetForgetfulPoint: Example 7.33.7: the forgetful functor from the surjective site of
`G`-sets to sets defines a canonical point of the site `\mathcal T_G`. -/
def gSetForgetfulPoint : (Action.jointlySurjectiveTopology G).Point where
  fiber := Action.forget (Type u) G
  isCofiltered := Functor.isCofiltered_elements (Action.forget (Type u) G)
  initiallySmall := gSetForgetful_elements_initiallySmall G
  jointly_surjective := gSetForgetfulPointJointlySurjective G

-- Proof sketch: right multiplication commutes with the left regular action by associativity in
-- the group `G`.
theorem gSetForgetfulPointLeftRegularRightMul_comm (g : G) :
    ∀ h : G,
      (Action.leftRegular G).ρ h ≫ (fun x : G ↦ x * g) =
        (fun x : G ↦ x * g) ≫ (Action.leftRegular G).ρ h := by
  -- Both composites send `x` to `(h * x) * g = h * (x * g)`.
  intro h
  ext x
  simp [mul_assoc]

/-- The endomorphism of the left regular `G`-set given by right multiplication by `g`. -/
def gSetForgetfulPointLeftRegularRightMul (g : G) : Action.leftRegular G ⟶ Action.leftRegular G
    where
  hom := fun x : G ↦ x * g
  comm := gSetForgetfulPointLeftRegularRightMul_comm G g

@[simp] theorem gSetForgetfulPointLeftRegularRightMul_one :
    gSetForgetfulPointLeftRegularRightMul G 1 = 𝟙 (Action.leftRegular G) := by
  apply Action.hom_ext
  ext x
  simp [gSetForgetfulPointLeftRegularRightMul]

@[simp] theorem gSetForgetfulPointLeftRegularRightMul_mul (g h : G) :
    gSetForgetfulPointLeftRegularRightMul G (g * h) =
      gSetForgetfulPointLeftRegularRightMul G g ≫ gSetForgetfulPointLeftRegularRightMul G h := by
  apply Action.hom_ext
  ext x
  simp [gSetForgetfulPointLeftRegularRightMul, mul_assoc]

/-- The right-translation action of `G` on `Map(G, S)` from Example 7.33.7. -/
instance gSetForgetfulPointMapMulAction (S : Type v) : MulAction G (G → S) where
  smul g ψ := fun x ↦ ψ (x * g)
  one_smul ψ := by
    ext x
    change ψ (x * (1 : G)) = ψ x
    simp
  mul_smul g h ψ := by
    ext x
    change ψ (x * (g * h)) = ψ ((x * g) * h)
    simp [mul_assoc]

/-- In the right-translation action on `Map(G, S)`, the element `g` acts by precomposition with
right multiplication by `g`. -/
@[simp] theorem gSetForgetfulPointMapMulAction_smul_apply
    (S : Type v) (g x : G) (ψ : G → S) :
    (g • ψ) x = ψ (x * g) :=
  rfl

end

end CategoryTheory
