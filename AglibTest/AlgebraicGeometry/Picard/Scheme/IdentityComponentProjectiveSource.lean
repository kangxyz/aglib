/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentProjectiveSource

/-! # Pic0 quasi-projectivity for the original H-projective source and representative -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard

universe u

example {k : Type u} [Field k] (X : FScheme k)
    [IsHProjective X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    IsHQuasiProjective (picardIdentityComponent X.hom P R).hom :=
  isHQuasiProjective_picardIdentityComponent_of_isHProjective X P R

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_picardIdentityComponent_of_isHProjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_picardIdentityComponent_of_isHProjective
