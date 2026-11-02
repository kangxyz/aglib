/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Regular

/-!
# Universal modification vanishing under the original ring equivalence

Compose the given model with the actual contravariant Spec map. The scheme,
its structure module and its original H1 group are unchanged. No local,
Noetherian, Nagata, completeness or dimension hypothesis is required.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

private theorem normalModificationH1Vanishing_of_ringEquiv
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (e : A ≃+* B) (hA : NormalModificationH1Vanishing A) :
    NormalModificationH1Vanishing B := by
  intro Z hZ f hf hdom hN hff
  let : IsIntegral Z := hZ
  let : IsProper f := hf
  let : IsDominant f := hdom
  let s := Spec.map (CommRingCat.ofHom e.toRingHom)
  let : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  let : IsIso s := by dsimp only [s]; infer_instance
  let : IsIso (CommRingCat.ofHom (functionFieldMap s)) := FunctionField.fieldMap_isIso s
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (f ≫ s))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  exact hA Z (f ≫ s) hN hcomp

/-- Universal H1 vanishing is preserved by the original ring equivalence:
only the base map changes, not the supplied model or its cohomology. -/
theorem normalModificationH1Vanishing_iff_of_ringEquiv
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (e : A ≃+* B) :
    NormalModificationH1Vanishing A ↔ NormalModificationH1Vanishing B :=
  ⟨normalModificationH1Vanishing_of_ringEquiv e,
    normalModificationH1Vanishing_of_ringEquiv e.symm⟩

end AlgebraicGeometry.Scheme.RationalSingularities
