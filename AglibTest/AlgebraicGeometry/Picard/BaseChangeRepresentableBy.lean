/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy

/-! Focused consumer of the base change of a scheme representing the fppf Picard sheaf on locally
Noetherian test schemes (Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry Scheme.RelativePicard

universe u

variable {S S' X : Scheme.{u}} [IsLocallyNoetherian S'] (p : X ⟶ S) (g : S' ⟶ S)
  (P : Scheme.LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- `Pic_{X'/S',(fppf)}` on locally Noetherian `S'`-schemes is representable, by `P ×_S S'`. -/
example :
    ((Scheme.locallyNoetherianOverInclusion S').op ⋙ (fppfPicardSheaf (pullback.snd p g)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).IsRepresentable :=
  (baseChangeRepresentableBy p g P e).isRepresentable

/-- The bijection: the adjunction `Over.map g ⊣ Over.pullback g`, then `e`, then the inverse base
change of the fppf Picard sheaf. -/
example {T : Scheme.LocallyNoetherianOver S'}
    (f : T ⟶ Scheme.LocallyNoetherianOver.baseChange g P) :
    (baseChangeRepresentableBy p g P e).homEquiv f =
      ((fppfPicardSheafBaseChangeIso p g).inv.app (op T.obj)).hom
        (e.homEquiv
          (ObjectProperty.homMk (((Over.mapPullbackAdj g).homEquiv T.obj P.obj).symm f.hom) :
            (Scheme.LocallyNoetherianOver.map g).obj T ⟶ P)) :=
  baseChangeRepresentableBy_homEquiv p g P e f

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.baseChangeRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms baseChangeRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.baseChangeRepresentableBy_homEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms baseChangeRepresentableBy_homEquiv
