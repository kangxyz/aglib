/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Field-valued points on the closed part of a localization pair

A field-valued point whose image lies in a closed immersion has a unique
actual factorization through that immersion. Its pullback is a surjective
closed immersion onto a reduced field spectrum and is therefore an isomorphism.
This retains the actual point equation needed by the finite direct-image
stalk coordinates; membership of the underlying point alone is not used as
a substitute for a scheme morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  {Ω : Type u} [Field Ω] (η : Spec (.of Ω) ⟶ X)

/-- A field-valued point in a closed immersion's image has an actual lift. -/
theorem exists_closedImmersion_pointLift
    (hη : η (default : Spec (.of Ω)) ∈ Set.range i) :
    ∃ ζ : Spec (.of Ω) ⟶ Z, ζ ≫ i = η := by
  have hs : Function.Surjective (pullback.snd i η) := by
    intro x
    have hx : x ∈ η ⁻¹' Set.range i := by
      have hx : x = (default : Spec (.of Ω)) := Subsingleton.elim _ _
      simpa only [hx, Set.mem_preimage] using hη
    rw [← Scheme.Pullback.range_snd] at hx
    exact hx
  let : Surjective (pullback.snd i η) := ⟨hs⟩
  let : IsIso (pullback.snd i η) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.snd i η)
  refine ⟨inv (pullback.snd i η) ≫ pullback.fst i η, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

/-- Membership in the closed image is equivalent to an actual field-valued factorization. -/
theorem closedImmersion_pointLift_iff :
    (∃ ζ : Spec (.of Ω) ⟶ Z, ζ ≫ i = η) ↔
      η (default : Spec (.of Ω)) ∈ Set.range i := by
  constructor
  · rintro ⟨ζ, hζ⟩
    refine ⟨ζ (default : Spec (.of Ω)), ?_⟩
    exact congrArg (fun f : Spec (.of Ω) ⟶ X => f (default : Spec (.of Ω))) hζ
  · exact exists_closedImmersion_pointLift i η

/-- The actual field-valued fibre of a closed immersion has at most one element. -/
instance closedImmersion_pointLift_subsingleton :
    Subsingleton {ζ : Spec (.of Ω) ⟶ Z // ζ ≫ i = η} where
  allEq a b := by
    apply Subtype.ext
    exact (cancel_mono i).mp (a.property.trans b.property.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
