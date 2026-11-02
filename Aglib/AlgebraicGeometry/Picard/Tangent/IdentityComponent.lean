/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension
public import Aglib.AlgebraicGeometry.Picard.Scheme.FieldProperties

/-!
# The original Picard identity-component cotangent space

The group identity is the point representing the zero Picard class. Structural
constants agree with those used by the existing cohomology comparison, and
the open subgroup inclusion induces a cotangent equivalence. All comparisons
concern the supplied representative on locally Noetherian tests.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X : FScheme k)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The native group identity cotangent space uses exactly the stalk and
structural scalars of the existing Picard tangent comparison. -/
def cotangentEquivUnitStalk :
    letI := picardCommGrpObj X.hom P R
    Cotangent.Space η[P.obj] ≃ₗ[k] IsLocalRing.CotangentSpace (unitStalk R) := by
  let := picardCommGrpObj X.hom P R
  let q := Cotangent.pointData η[P.obj]
  have hp : unitPoint R = q.point :=
    unitPoint_eq_unitPoint_picardCommGrpObj X.hom P R
  have hc : q.constants = P.obj.hom.stalkScalar q.point :=
    q.constantsAt_eq_stalkScalar q.point
  -- Change the entire typed comparison, including its native additive and scalar structures.
  change (letI := q.constants.toAlgebra
    IsLocalRing.CotangentSpace q.localRing ≃ₗ[k]
      IsLocalRing.CotangentSpace (unitStalk R))
  rw [hc]
  change (letI := (P.obj.hom.stalkScalar q.point).toAlgebra
    IsLocalRing.CotangentSpace (P.obj.left.presheaf.stalk q.point) ≃ₗ[k]
      IsLocalRing.CotangentSpace (unitStalk R))
  rw [← hp]

/-- The identity cotangent dimension of the same Picard identity component
is the coherent first cohomology dimension. -/
theorem finrank_identityComponentCotangent_eq_structureH1
    [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    letI := picardCommGrpObj X.hom P R
    Module.finrank k (Cotangent.Space η[identityComponentOver P.obj]) =
      Module.finrank k (structureCohomology k X 1) := by
  let := picardCommGrpObj X.hom P R
  rw [← (identityComponentCotangentEquiv P.obj).finrank_eq,
    (cotangentEquivUnitStalk X P R).finrank_eq]
  exact
    (finrank_structureH1_eq_finrank_cotangentSpace_of_isProper_of_flat_of_geometricallyIntegral
      X R).symm

end AlgebraicGeometry.Scheme.RelativePicard
