/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.HigherTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.InverseImage

/-! # Internal torsion in the original direct image and unit cokernel

The original degree-zero derived comparison transports the proved qcqs
higher-image torsion theorem to the actual direct-image coefficient. Its
literal adjunction-unit cokernel is then a quotient of a torsion sheaf.
No common annihilator, finite morphism or surjectivity is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Actual direct image along a qcqs morphism preserves internal torsion. -/
theorem IsTorsion.directImage {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    {F : AbelianSheaf.{u, u + 1} Y} (hF : IsTorsion Y F) :
    IsTorsion X ((directImage f).obj F) :=
  (higherDirectImage_isTorsion f 0 F hF).of_epi
    (((EtaleCohomology.directImage f).rightDerivedZeroIsoSelf.app F).hom)

/-- The literal cokernel of the original qcqs inverse-image adjunction unit
is internally torsion whenever the original coefficient is internally torsion. -/
theorem unit_cokernel_isTorsion {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) :
    IsTorsion X (cokernel ((inverseImageAdjunction f).unit.app F)) :=
  ((hF.inverseImage f).directImage f).of_epi
    (cokernel.π ((inverseImageAdjunction f).unit.app F))

end AlgebraicGeometry.Scheme.EtaleCohomology
