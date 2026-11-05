/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ChartOrdinaryExchange
public import Aglib.CategoryTheory.Preadditive.Annihilator
public import Aglib.CategoryTheory.Adjunction.Mates.Chart

/-! # Original ordinary comparisons for source chart images

The comparison uses the original composite-chart exchange, the original chart
restriction comparison and the actual inverse-image square. It keeps the
original coefficient and source chart. Invertibility is isolated in
`OrdinaryFaceIsomorphism`; no higher
open-direct-image acyclicity enters.
The original face naturality remains a separate construction in progress.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- The original contravariant face map on source-chart image functors. -/
abbrev sourceEtaleImageMap {U V : X.Etale} (a : U ⟶ V) :
    sourceEtaleImage f V ⟶ sourceEtaleImage f U :=
  Functor.whiskerRight (etaleProductSheafMap a) (directImage f)

include H in
/-- The original chart pullback square, vertically pasted with the given square. -/
theorem sourceEtaleCompositeSquare (U : X.Etale) :
    IsPullback (pullback.fst U.hom g') (pullback.snd U.hom g' ≫ f')
      (U.hom ≫ f) g :=
  (IsPullback.of_hasPullback U.hom g').paste_vert H

/-- Source normalization through the original chart restriction. -/
def sourceEtaleOrdinarySourceIso (U : X.Etale) :
    sourceEtaleImage f U ⋙ inverseImage g ≅
      inverseImage U.hom ⋙ (directImage (U.hom ≫ f) ⋙ inverseImage g) :=
  SourceChartMates.sourceIso (sourceEtaleImageInverseIso f U) (inverseImage g)

/-- Target normalization through the original inverse-image square. -/
def sourceEtaleOrdinaryTargetIso (U : X.Etale) :
    inverseImage U.hom ⋙ (inverseImage (pullback.fst U.hom g') ⋙
      directImage (((siteBaseChange g').obj U).hom ≫ f')) ≅
        inverseImage g' ⋙ sourceEtaleImage f' ((siteBaseChange g').obj U) :=
  let U' := (siteBaseChange g').obj U
  let v := pullback.fst U.hom g'
  SourceChartMates.targetIso
    (inverseImageSquareIso U.hom U'.hom g' v pullback.condition.symm).symm
    (sourceEtaleImageInverseIso f' U')

/-- The canonical ordinary comparison on the original chart image. -/
def sourceEtaleOrdinaryComparison (U : X.Etale) :
    sourceEtaleImage f U ⋙ inverseImage g ⟶
      inverseImage g' ⋙ sourceEtaleImage f' ((siteBaseChange g').obj U) :=
  let U' := (siteBaseChange g').obj U
  SourceChartMates.comparison
    (inverseImageSquareIso U.hom U'.hom g' (pullback.fst U.hom g')
      pullback.condition.symm).symm
    (baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleImageInverseIso f U) (sourceEtaleImageInverseIso f' U')

end AlgebraicGeometry.Scheme.EtaleCohomology
