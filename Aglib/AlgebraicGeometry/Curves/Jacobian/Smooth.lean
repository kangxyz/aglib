/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme
public import Aglib.AlgebraicGeometry.Geometrically.Reduced.Smooth
public import Aglib.AlgebraicGeometry.Group.Dimension
public import Aglib.AlgebraicGeometry.Picard.Smooth.Representative

/-!
# Smoothness and geometric integrality of the original Jacobian

Smoothness transfers from the curve Picard construction to the supplied
representative on locally Noetherian tests. Its same open identity component
is smooth and geometrically integral over the original arbitrary field.
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

include hX R in
/-- The original representative of the curve Picard sheaf is smooth. -/
theorem smooth_picardRepresentative : Smooth P.obj.hom := by
  obtain ⟨N, i, hi, hp⟩ := hX.exists_closedImmersion_projectiveSpace
  have := hX.flat
  have := hX.isGeometricallyIntegral
  have := hX.isIntegral
  have hd := hX.topologicalKrullDim_eq_one
  obtain ⟨Xl, ⟨⟨⟩⟩, p⟩ := X
  change Xl ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1))) at i
  change i ≫ toSpec k (ULift.{u} (Fin (N + 1))) = p at hp
  subst hp
  exact smooth_representative_of_curve i Equiv.ulift hd P R

variable [LocallyOfFiniteType P.obj.hom]

include hX in
/-- The same Picard representative's actual identity component is smooth. -/
theorem smooth_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    Smooth (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  let := smooth_picardRepresentative hX P R
  exact Group.smooth_identityComponentOver P.obj

include hX in
/-- The same smooth identity component is geometrically integral over the
original field, by its existing geometric irreducibility and smoothness. -/
theorem geometricallyIntegral_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    GeometricallyIntegral (identityComponentOver P.obj).hom := by
  let := picardCommGrpObj X.hom P R
  let := smooth_identityComponentOver hX P R
  let := Scheme.geometricallyReduced_of_smooth (identityComponentOver P.obj).hom
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end AlgebraicGeometry.Scheme.OverField.Curve
