/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw

/-! Focused consumer of the comparison of the group law of the base change of a scheme
representing the fppf Picard sheaf with the base change of its group law, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry Scheme.RelativePicard
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

variable {S S' X : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (p : X ⟶ S)
  (g : S' ⟶ S) (P : Scheme.LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The group law of `P ×_S S'` representing `Pic_{X'/S',(fppf)}` is the group law of the base
change `(Over.pullback g).mapGrp` of the group object `P`. -/
example :
    letI := picardCommGrpObj p P e
    (picardCommGrpObj (pullback.snd p g) (Scheme.LocallyNoetherianOver.baseChange g P)
        (baseChangeRepresentableBy p g P e)).toGrpObj =
      ((Over.pullback g).mapGrp.obj (Grp.mk P.obj)).grp :=
  picardCommGrpObj_baseChange_toGrpObj p g P e

/-- The base-changed group law makes the base-changed representation additive. -/
example {T : Scheme.LocallyNoetherianOver S'} (f₁ f₂ : T.obj ⟶ (Over.pullback g).obj P.obj) :
    letI := picardCommGrpObj p P e
    (baseChangeRepresentableBy p g P e).homEquiv (ObjectProperty.homMk (f₁ * f₂)) =
      (baseChangeRepresentableBy p g P e).homEquiv'
          (F := (Scheme.locallyNoetherianOverInclusion S').op ⋙
            (fppfPicardSheaf (pullback.snd p g)).obj)
          (ObjectProperty.homMk f₁) +
        (baseChangeRepresentableBy p g P e).homEquiv'
          (F := (Scheme.locallyNoetherianOverInclusion S').op ⋙
            (fppfPicardSheaf (pullback.snd p g)).obj)
          (ObjectProperty.homMk f₂) :=
  baseChangeRepresentableBy_homEquiv_mul p g P e f₁ f₂

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardCommGrpObj_baseChange_toGrpObj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardCommGrpObj_baseChange_toGrpObj

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.baseChangeRepresentableBy_homEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms baseChangeRepresentableBy_homEquiv_mul
