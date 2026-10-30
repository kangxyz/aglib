/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension.QuasiFinite
public import Aglib.AlgebraicGeometry.Picard.Tangent.IdentityComponent

/-!
# Unit dimension and regularity criteria for the same dual Picard component

The supplied representative `P,R` identifies the actual identity cotangent rank of Pic0 with
coherent H1 of the original proper, flat, geometrically integral source. An explicit bound on
that H1 dimension therefore supplies the cotangent inequality in the general group criterion.
An actual locally quasi-finite group morphism from the connected smooth source then forces
equality of unit-stalk dimensions and regularity of the original target unit stalk.

The actual map and original-H1 inequality remain explicit inputs. This file does not assume
target properness, target smoothness, autoduality or a prior dimension formula for Pic0, and it
does not count the pending native H1 bound as a discharged supplier.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original coherent-H1 bound gives the identity cotangent bound on the same chosen
Picard component, through the existing whole tangent comparison. -/
theorem identityComponentCotangent_le_of_structureH1_le
    [IsProper A.hom] [Flat A.hom] [GeometricallyIntegral A.hom]
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    Module.finrank k (Cotangent.Space η[picardIdentityComponent A.hom P R]) ≤
      Module.finrank k (Cotangent.Space η[A]) := by
  let := picardCommGrpObj A.hom P R
  exact (finrank_identityComponentCotangent_eq_structureH1 A P R).le.trans hH1

/-- The original H1 bound and an actual locally quasi-finite group morphism force the unit
dimension and cotangent equalities and regularity of this same Picard component's unit stalk. -/
theorem unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    (f : A ⟶ picardIdentityComponent A.hom P R) [IsMonHom f] [LocallyQuasiFinite f.left]
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    ringKrullDim ((picardIdentityComponent A.hom P R).left.presheaf.stalk
        (Group.unitPoint (picardIdentityComponent A.hom P R))) =
        Module.finrank k (Cotangent.Space η[A]) ∧
      Module.finrank k (Cotangent.Space η[picardIdentityComponent A.hom P R]) =
        Module.finrank k (Cotangent.Space η[A]) ∧
      IsRegularLocalRing ((picardIdentityComponent A.hom P R).left.presheaf.stalk
        (Group.unitPoint (picardIdentityComponent A.hom P R))) := by
  let := picardCommGrpObj A.hom P R
  let J := picardIdentityComponent A.hom P R
  have : Flat A.hom := inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : PreconnectedSpace A.left := inferInstance
  have : LocallyOfFiniteType J.hom := by
    change LocallyOfFiniteType ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  exact unit_dimension_cotangent_and_regular_of_locallyQuasiFinite A J f
    (identityComponentCotangent_le_of_structureH1_le A P R hH1)

end AlgebraicGeometry.Scheme.RelativePicard
