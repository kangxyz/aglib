/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentQuasiProjective

/-!
# Consumer checks for arbitrary-field Picard identity-component quasi-projectivity

The supplied representative remains selected. No algebraic closedness, curve condition,
rational point, explicit Euler polynomial or separatedness premise occurs in the supplier.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard

namespace AglibTest.PicardIdentityComponentQuasiProjective

example {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion i] [Flat (i ≫ toSpec k ι)]
    [GeometricallyIntegral (i ≫ toSpec k ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    IsHQuasiProjective (picardIdentityComponent (i ≫ toSpec k ι) P R).hom :=
  isHQuasiProjective_picardIdentityComponent_hom i e P R

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_range_identityComponent_subset_opens_eulerCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.exists_range_identityComponent_subset_opens_eulerCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_picardIdentityComponent_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_picardIdentityComponent_hom

end AglibTest.PicardIdentityComponentQuasiProjective
