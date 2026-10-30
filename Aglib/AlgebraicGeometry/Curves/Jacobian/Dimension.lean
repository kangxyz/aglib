/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Genus
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Smooth
public import Aglib.AlgebraicGeometry.Picard.Tangent.IdentityComponent

/-!
# Dimension of the original Jacobian

For a smooth proper geometrically connected curve over an arbitrary field,
every supplied locally Noetherian representative of the fppf Picard sheaf is
smooth. Its actual identity component is smooth of relative dimension equal
to the coherent genus, and has that topological Krull dimension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

variable [LocallyOfFiniteType P.obj.hom]

include hX in
/-- The identity cotangent dimension of the original Jacobian is the coherent
genus of the original curve. -/
theorem finrank_identityComponentCotangent_eq_coherentGenus :
    letI := picardCommGrpObj X.hom P R
    Module.finrank k (Cotangent.Space η[identityComponentOver P.obj]) =
      coherentGenus k X := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  exact finrank_identityComponentCotangent_eq_structureH1 X P R

include hX in
/-- The original Jacobian is smooth of relative dimension equal to the genus,
with no algebraic-closedness or rational-point hypothesis on the field. -/
theorem smoothOfRelativeDimension_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    SmoothOfRelativeDimension (coherentGenus k X) (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  let := smooth_identityComponentOver hX P R
  rw [← finrank_identityComponentCotangent_eq_coherentGenus hX P R]
  exact Group.smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected
    (identityComponentOver P.obj)

include hX in
/-- The topological Krull dimension of the same Jacobian is the coherent
genus of the original curve. -/
theorem topologicalKrullDim_identityComponentOver_eq_coherentGenus :
    letI := picardCommGrpObj X.hom P R
    topologicalKrullDim (identityComponentOver P.obj).left = coherentGenus k X := by
  let := picardCommGrpObj X.hom P R
  exact smoothFieldDimension k (identityComponentOver P.obj).left
    (identityComponentOver P.obj).hom (coherentGenus k X)
    (smoothOfRelativeDimension_identityComponentOver hX P R) inferInstance

end AlgebraicGeometry.Scheme.OverField.Curve
