/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.UniversalRigidified

/-! One universal pair, arbitrary-test pullbacks, and classification only on
the test category actually represented by the supplied equivalence. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  {P : Scheme.LocallyNoetherianOver S}
  (Rr : ((Scheme.locallyNoetherianOverInclusion S).op ⋙
    rigidifiedPicardFunctor p o ho).RepresentableBy P)

example {T : Over S} (f : T ⟶ P.obj) : RigidifiedPair p o ho T :=
  universalRigidifiedPullback p o ho Rr f

example {T : Scheme.LocallyNoetherianOver S} (Q : RigidifiedPair p o ho T.obj) :
    ∃! f : T ⟶ P,
      Nonempty (RigidifiedPair.Iso (universalRigidifiedPullback p o ho Rr f.hom) Q) :=
  existsUnique_rigidifiedPairClassifyingMap p o ho Rr Q

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    {T : Scheme.LocallyNoetherianOver S} (Q : RigidifiedPair p o ho T.obj)
    (e : RigidifiedPair.Iso
      (universalRigidifiedPullback p o ho Rr (rigidifiedPairClassifyingMap p o ho Rr Q).hom) Q) :
    e = rigidifiedPairClassifyingIso p o ho Rr Q := by
  have := isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral
    p T.obj.hom
  exact rigidifiedPairClassifyingIso_unique p o ho Rr Q e

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    [LocallyOfFiniteType P.obj.hom]
    (R : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (T : Over S) :
    letI := picardCommGrpObj p P R
    (Scheme.Modules.pullback (originSection p o ho T)).map
        (fppfUniversalRigidifiedUnitIso p o ho R T).iso.hom ≫
      (trivialRigidifiedPair p o ho T).rigidification.hom =
        (RigidifiedPair.map (1 : T ⟶ P.obj)
          (fppfUniversalRigidifiedPair p o ho R)).rigidification.hom := by
  let := picardCommGrpObj p P R
  exact (fppfUniversalRigidifiedUnitIso p o ho R T).comm

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.existsUnique_rigidifiedPairClassifyingMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms existsUnique_rigidifiedPairClassifyingMap

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.universalRigidifiedCompIso_assoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms universalRigidifiedCompIso_assoc

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedPairClassifyingIso_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedPairClassifyingIso_naturality

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfUniversalRigidifiedUnitIso_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fppfUniversalRigidifiedUnitIso_naturality
