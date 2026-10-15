/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact affine quasicoherent inclusion

The tilde equivalence identifies the actual inclusion with an exact module
functor, over every commutative ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable (R : CommRingCat.{u})

/-- The comparison identifies the composite tilde after global sections with
 the actual inclusion of quasicoherent sheaves. -/
def affineQuasicoherentToSheavesIso :
    (tildeEquiv (R := R)).inverse ⋙ tilde.functor R ≅
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι :=
  (Functor.associator (tildeEquiv (R := R)).inverse (tildeEquiv (R := R)).functor
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι).symm ≪≫
    Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso _ ≪≫ Functor.leftUnitor _

instance affineQuasicoherentToSheaves_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι := by
  have : PreservesFiniteLimits ((tildeEquiv (R := R)).inverse ⋙ tilde.functor R) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (affineQuasicoherentToSheavesIso R)

instance affineQuasicoherentToSheaves_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι := by
  have : PreservesFiniteColimits ((tildeEquiv (R := R)).inverse ⋙ tilde.functor R) :=
    comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (affineQuasicoherentToSheavesIso R)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
