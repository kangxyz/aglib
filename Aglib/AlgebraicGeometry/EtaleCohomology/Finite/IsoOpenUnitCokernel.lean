/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.SurjectiveUnit

/-! # The actual finite-unit cokernel is supported outside an isomorphism open

An isomorphism of the literal pullback over the supplied open gives a unique
actual geometric lift. The published finite evaluation then annihilates the
original unit's cokernel stalk. No support or unit-isomorphism premise is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

attribute [local instance] hasSheafifyLarge

/-- The original isomorphic base change produces the unique lift of every
scheme-valued point factoring through the specified base-change map. -/
@[instance_reducible]
def uniqueLiftsOfIsIsoPullback
    {Y U X W : Scheme.{u}} (f : Y ⟶ X) (j : U ⟶ X)
    [IsIso (pullback.snd f j)] (u : W ⟶ U) (s : W ⟶ X) (hs : u ≫ j = s) :
    Unique {y : W ⟶ Y // y ≫ f = s} := by
  let y := (u ≫ inv (pullback.snd f j)) ≫ pullback.fst f j
  have hy : y ≫ f = s := by
    simp only [y, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
    exact hs
  refine ⟨⟨⟨y, hy⟩⟩, ?_⟩
  intro z
  apply Subtype.ext
  have h : pullback.lift z.val u (z.property.trans hs.symm) =
      u ≫ inv (pullback.snd f j) := by
    apply (cancel_mono (pullback.snd f j)).mp
    simp only [pullback.lift_snd, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (pullback.lift_fst z.val u (z.property.trans hs.symm)).symm.trans
    (congrArg (fun a => a ≫ pullback.fst f j) h)

/-- The original finite-unit cokernel has zero stalk throughout an open
where the literal base change is an isomorphism. -/
theorem unit_cokernel_stalk_isZero_of_isIso_open
    {Y U X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd f j)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (default : Spec (.of Ω)) ∈ Set.range j)
    (F : AbelianSheaf.{u, u + 1} X) :
    IsZero (coefficientFiber s (cokernel ((inverseImageAdjunction f).unit.app F))) := by
  have hrange : Set.range s ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x = (default : Spec (.of Ω)) := Subsingleton.elim _ _
    simpa only [hx] using hs
  let t := IsOpenImmersion.lift j s hrange
  let := uniqueLiftsOfIsIsoPullback f j t s (IsOpenImmersion.lift_fac j s hrange)
  exact unit_cokernel_stalk_isZero_of_unique f s F

/-- The literal cokernel of the original finite unit is supported on the
actual closed complement of an open where the original map is an isomorphism.
This is the geometric-stalk support predicate consumed by closed support. -/
theorem unit_cokernel_closedSupport
    {Y U Z X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (j : U ⟶ X) [IsOpenImmersion j] [IsIso (pullback.snd f j)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (F : AbelianSheaf.{u, u + 1} X)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : ∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) :
    IsZero (coefficientFiber s (cokernel ((inverseImageAdjunction f).unit.app F))) := by
  apply unit_cokernel_stalk_isZero_of_isIso_open f j s ?_ F
  rw [hcomp]
  intro h
  obtain ⟨z, hz⟩ := exists_closedImmersion_pointLift i s h
  exact hs z hz

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
