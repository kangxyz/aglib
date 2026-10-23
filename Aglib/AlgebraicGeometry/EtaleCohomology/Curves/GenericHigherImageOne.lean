/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.HigherImageAffineCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceMultiplicative

/-! # Original first higher image of the generic multiplicative sheaf

The actual generic Artin map retains nilpotents. Its affine etale base changes
are Artinian, so the native Picard theorem kills their original multiplicative
cohomology in degree one. Actual represented-cohomology sheafification then
kills the first higher image, without field, dimension or Tsen hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The original first higher image of the actual generic multiplicative sheaf is zero. -/
theorem genericHigherImage_one_isZero
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (genericArtinLocus X))] :
    IsZero ((higherDirectImage (genericArtinMap X) 1).obj (gm (genericArtinLocus X))) := by
  apply higherDirectImage_isZero_of_affine (genericArtinMap X) (gm (genericArtinLocus X)) 1
  intro U hU
  let : IsAffine U.left := hU
  let : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
  let : IsNoetherian U.left := { }
  let : QuasiCompact U.hom :=
    quasiCompact_of_noetherianSpace_source (X := U.left) (Y := X) U.hom
  let T := (siteBaseChange (genericArtinMap X)).obj U
  let : IsArtinianScheme T.left :=
    genericArtinBaseChange_isArtinian (X := X) (U := U.left) U.hom
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} T.left) := HasExt.standard _
  let : HasExt.{u + 2} (Sheaf ((genericArtinLocus X).smallEtaleTopology.over T)
      AddCommGrpCat.{u + 1}) := HasExt.standard _
  exact (Kummer.gmRepresentedCohomologyEquiv.{u, w, u + 2, u + 2} T 1).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
