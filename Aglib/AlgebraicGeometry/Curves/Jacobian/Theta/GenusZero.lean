/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Dimension
public import Aglib.AlgebraicGeometry.Morphisms.Etale.ConnectedSection

/-!
# The original Jacobian of a genus-zero curve is trivial

Over any field, the same Picard representative's identity component is smooth
of relative dimension zero, connected, and has its native identity section.
Its original structure morphism is an isomorphism, with that identity section
as inverse. No rational point on the curve or theta locus in negative degree
is used.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

include hX

/-- The genus-zero Jacobian is the original field spectrum. Its hom is the
original structure morphism and its inverse is the native group identity. -/
def identityComponentIsoSpecOfGenusZero (hg : coherentGenus k X = 0) :
    letI := picardCommGrpObj X.hom P R
    (identityComponentOver P.obj).left ≅ Spec (.of k) := by
  let := picardCommGrpObj X.hom P R
  have hd : SmoothOfRelativeDimension 0 (identityComponentOver P.obj).hom := by
    simpa only [hg] using smoothOfRelativeDimension_identityComponentOver hX P R
  have : Etale (identityComponentOver P.obj).hom :=
    (Etale.iff_smoothOfRelativeDimension_zero _).mpr hd
  exact isoSpecOfEtaleOfPreconnected (identityComponentOver P.obj).hom
    η[identityComponentOver P.obj].left (Over.w η[identityComponentOver P.obj])

/-- Genus-zero triviality is an isomorphism of the actual structural map. -/
theorem isIso_identityComponentOver_hom_of_genus_zero (hg : coherentGenus k X = 0) :
    letI := picardCommGrpObj X.hom P R
    IsIso (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  exact (identityComponentIsoSpecOfGenusZero hX P R hg).isIso_hom

/-- The actual identity section is also a right inverse to the original
genus-zero Jacobian structure morphism. -/
theorem identityComponentOver_hom_comp_one_of_genus_zero (hg : coherentGenus k X = 0) :
    letI := picardCommGrpObj X.hom P R
    (identityComponentOver P.obj).hom ≫ η[identityComponentOver P.obj].left = 𝟙 _ :=
  (identityComponentIsoSpecOfGenusZero hX P R hg).hom_inv_id

end AlgebraicGeometry.Scheme.OverField.Curve
