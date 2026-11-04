/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf.Pullback
public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy

/-! Transport of the original Picard representation along a source isomorphism. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S : Scheme.{u}}

/-- An isomorphism of the given sources induces an isomorphism of the
original fppf Picard sheaves. -/
def picardSourceSheafIso {A B : Over S} (e : A ≅ B) :
    fppfPicardSheaf A.hom ≅ fppfPicardSheaf B.hom where
  hom := fppfPicardPullback e.inv
  inv := fppfPicardPullback e.hom
  hom_inv_id := by
    rw [← fppfPicardPullback_comp, Iso.hom_inv_id, fppfPicardPullback_id]
  inv_hom_id := by
    rw [← fppfPicardPullback_comp, Iso.inv_hom_id, fppfPicardPullback_id]

/-- Source transport of the original representation on the SAME parameter
object. No representing scheme is selected or replaced. -/
def picardSourceRepresentableBy {A B : Over S} (e : A ≅ B)
    (Q : LocallyNoetherianOver S)
    (RQ : ((locallyNoetherianOverInclusion S).op ⋙
      (fppfPicardSheaf A.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q) :
    ((locallyNoetherianOverInclusion S).op ⋙
      (fppfPicardSheaf B.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q :=
  RQ.ofIso (Functor.isoWhiskerLeft (locallyNoetherianOverInclusion S).op
    (Functor.isoWhiskerRight
      ((sheafToPresheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).mapIso
        (picardSourceSheafIso e)) (CategoryTheory.forget AddCommGrpCat.{u + 1})))

end AlgebraicGeometry.Scheme.RelativePicard
