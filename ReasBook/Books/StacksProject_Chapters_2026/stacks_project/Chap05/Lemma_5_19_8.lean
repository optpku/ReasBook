module

/-
Lean proof for Stacks Project, Lemma 5.19.8.
-/
public import Mathlib.Topology.Sober

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {U : Type v} {X : Type w}
variable [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X]
variable [T0Space U] [QuasiSober U]
variable (s t : R → U) (π : U → X)

omit [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X] [T0Space U] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: the `π`-fiber over `π u` is exactly the image of the `s`-fiber over
`u` under `t`. -/
lemma pi_fiber_eq_image_preimage
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v)
    (u : U) :
    π ⁻¹' ({π u} : Set X) = t '' (s ⁻¹' ({u} : Set U)) := by
  -- Rewrite the quotient relation into the source relation coming from `s` and `t`.
  ext v
  constructor
  · intro hv
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
    obtain ⟨r, htr, hsr⟩ := (hπ_quot v u).mp hv
    refine ⟨r, ?_, htr⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact hsr
  · rintro ⟨r, hr, htr⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hr ⊢
    simpa [htr] using (hπ_quot (t r) u).mpr ⟨r, rfl, hr⟩

omit [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X] [T0Space U] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: every `π`-fiber is finite because it is the image of a finite
`s`-fiber. -/
lemma finite_pi_fiber
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v)
    (u : U) :
    Set.Finite (π ⁻¹' ({π u} : Set X)) := by
  -- Replace the `π`-fiber by an explicit image of the finite source fiber.
  rw [pi_fiber_eq_image_preimage (s := s) (t := t) (π := π) hπ_quot u]
  exact (hs_finite u).image t

omit [T0Space U] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: over an open quotient map, specialization in the quotient lifts to a
specialization between chosen representatives once the source fiber is finite. -/
lemma exists_specializing_lift_in_fiber_of_open_quotient
    (hπ_openQuot : IsOpenQuotientMap π)
    {u v v' : U} (hx : π u ⤳ π v) (hv' : π v' = π v)
    (hfinite : Set.Finite (π ⁻¹' ({π u} : Set X))) :
    ∃ u' : U, π u' = π u ∧ u' ⤳ v' := by
  classical
  -- Route correction: the lift comes from openness of `π`, not from transporting
  -- specialization through `s` and `t`.
  let F : Set U := π ⁻¹' ({π u} : Set X)
  by_contra hno
  have hno' : ∀ u' : F, ¬ ((u' : U) ⤳ v') := by
    intro u' hu'spec
    apply hno
    refine ⟨u', ?_, hu'spec⟩
    change π u' = π u
    exact u'.2
  -- Choose, for each point in the finite fiber, an open neighborhood of `v'` avoiding it.
  choose W hWopen hv'W hu'W using
    fun u' : F => (not_specializes_iff_exists_open).mp (hno' u')
  letI : Fintype F := hfinite.fintype
  let V : Set U := ⋂ u' : F, W u'
  have hVopen : IsOpen V := by
    -- Intersect finitely many separating neighborhoods.
    simpa [V] using isOpen_iInter_of_finite (fun u' : F => hWopen u')
  have hv'V : v' ∈ V := by
    -- The chosen target lift lies in every neighborhood of the finite family.
    simpa [V] using fun u' : F => hv'W u'
  have hπspec : π u ⤳ π v' := by
    simpa [hv'] using hx
  have hπuV : π u ∈ π '' V := by
    -- Any open neighborhood of `π v'` must contain `π u`.
    apply hπspec.mem_open (hπ_openQuot.isOpenMap _ hVopen)
    exact ⟨v', hv'V, rfl⟩
  obtain ⟨u', hu'V, hu'π⟩ := hπuV
  have hu'F : u' ∈ F := by
    simpa [F, Set.mem_preimage, Set.mem_singleton_iff] using hu'π
  have hu'VW : ∀ a : F, u' ∈ W a := by
    simpa [V] using hu'V
  exact hu'W ⟨u', hu'F⟩ (hu'VW ⟨u', hu'F⟩)

omit [TopologicalSpace R] [QuasiSober U] in
/-- Helper for Lemma 5.19.8: mutual specialization in the quotient forces equality once the fibers
are finite and the quotient map is open. -/
lemma eq_of_mutual_specialization_of_open_quotient_finite_fibers
    (hπ_openQuot : IsOpenQuotientMap π)
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v)
    {x y : X} (hxy : x ⤳ y) (hyx : y ⤳ x) :
    x = y := by
  obtain ⟨u₀, rfl⟩ := hπ_openQuot.surjective x
  obtain ⟨v₀, rfl⟩ := hπ_openQuot.surjective y
  let Fx : Set U := π ⁻¹' ({π u₀} : Set X)
  let Fy : Set U := π ⁻¹' ({π v₀} : Set X)
  have hFx_fin : Set.Finite Fx := by
    simpa [Fx] using finite_pi_fiber (s := s) (t := t) (π := π) hs_finite hπ_quot u₀
  have hFy_fin : Set.Finite Fy := by
    simpa [Fy] using finite_pi_fiber (s := s) (t := t) (π := π) hs_finite hπ_quot v₀
  letI : PartialOrder U := specializationOrder U
  obtain ⟨u, huFx, huMax⟩ := hFx_fin.exists_maximal ⟨u₀, by simp [Fx]⟩
  have huπ : π u = π u₀ := by
    simpa [Fx, Set.mem_preimage, Set.mem_singleton_iff] using huFx
  -- Lift `π v₀ ⤳ π u₀` to a representative of the `π v₀`-fiber specializing to `u`.
  obtain ⟨v, hvπ, hvu⟩ :=
    exists_specializing_lift_in_fiber_of_open_quotient
      (π := π) hπ_openQuot hyx huπ hFy_fin
  -- Lift `π u₀ ⤳ π v₀` back to the `π u₀`-fiber and compare with maximality of `u`.
  obtain ⟨u', hu'π, hu'v⟩ :=
    exists_specializing_lift_in_fiber_of_open_quotient
      (π := π) hπ_openQuot hxy hvπ hFx_fin
  have hu'Fx : u' ∈ Fx := by
    simpa [Fx, Set.mem_preimage, Set.mem_singleton_iff] using hu'π
  have huu' : u ≤ u' := by
    exact hu'v.trans hvu
  have hu'leu : u' ≤ u := huMax hu'Fx huu'
  have huu'_eq : u = u' := le_antisymm huu' hu'leu
  have huv : u ⤳ v := by
    simpa [huu'_eq] using hu'v
  have huv_eq : u = v := by
    apply le_antisymm
    · exact hvu
    · exact huv
  -- Once the two chosen lifts coincide, their quotient points coincide as well.
  calc
    π u₀ = π u := huπ.symm
    _ = π v := by rw [huv_eq]
    _ = π v₀ := hvπ

/-- Lemma 5.19.8, source-facing bridge: let `π : U → X` be an open quotient map with `U`
quasi-sober and `T₀`. Assume the source-facing relation `(u, v) ↦ ∃ r, t r = u ∧ s r = v`
agrees with `Setoid.ker π`, the fibres of `s` are finite, and generalizations lift along both
`s` and `t`. Then `X` is Kolmogorov. -/
theorem t0Space_of_open_quotient_of_quasiSober_of_finiteFibers
    (hπ_openQuot : IsOpenQuotientMap π)
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hs_gen : GeneralizingMap s) (ht_gen : GeneralizingMap t)
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v) :
    T0Space X := by
  -- The quotient is `T₀` once mutual specialization of quotient points collapses.
  refine (t0Space_iff_inseparable X).2 ?_
  intro x y hxy
  let _ := (inferInstance : QuasiSober U)
  let _ := hs_gen
  let _ := ht_gen
  exact eq_of_mutual_specialization_of_open_quotient_finite_fibers
    (s := s) (t := t) (π := π) hπ_openQuot hs_finite hπ_quot
    hxy.specializes hxy.specializes'

end
