/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Morphism

/-! # Original selected representations, arbitrary value universe and all-test section laws -/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Scheme Scheme.LocallyNoetherianOver

universe w u

variable {S : Scheme.{u}} (F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{w})
  (P Q : LocallyNoetherianOver S)
  (eP : ((locallyNoetherianOverInclusion S).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy P)
  (eQ : ((locallyNoetherianOverInclusion S).op ⋙ G ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy Q)

example (a : F ⟶ G) {T : Over S} (t : T ⟶ P.obj) :
    (G.map (t ≫ (representedMap F G P Q eP eQ a).hom).op).hom (eQ.homEquiv (𝟙 Q)) =
      (a.app (op T)).hom ((F.map t.op).hom (eP.homEquiv (𝟙 P))) :=
  universalClass_comp_representedMap F G P Q eP eQ a t

example [IsLocallyNoetherian S] [LocallyOfFiniteType P.obj.hom]
    [LocallyOfFiniteType Q.obj.hom] (a : F ⟶ G) :
    letI := commGrpObjOfRepresentableBy F P eP
    letI := commGrpObjOfRepresentableBy G Q eQ
    IsMonHom (representedMap F G P Q eP eQ a).hom :=
  isMonHom_representedMap F G P Q eP eQ a

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.isMonHom_representedMap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.isMonHom_representedMap
