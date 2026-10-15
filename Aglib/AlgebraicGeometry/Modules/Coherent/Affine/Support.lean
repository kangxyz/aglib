/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeSupport
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact

/-!
# Noetherian supported affine coherent categories
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]
  {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The support property is a genuine Serre property in coherent sheaves. -/
instance affineSupportedAway_isSerreClass : (affineSupportedAway R j).IsSerreClass := by
  change ((Scheme.Modules.supportedAway j).inverseImage
    (affineFiniteTypeToModules R)).IsSerreClass
  infer_instance

instance instAbelianSupportedAffineCoherent : Abelian (SupportedAffineFiniteType R j) :=
  inferInstance

instance supportedAffineCoherent_essentiallySmall :
    EssentiallySmall.{u} (SupportedAffineFiniteType R j) :=
  essentiallySmall_of_fully_faithful (affineSupportedAway R j).ι

/-- Its standard abelian exact structure. -/
def supportedAffineCoherentExactStructure : ExactStructure (SupportedAffineFiniteType R j) :=
  abelianExactStructure _

end AlgebraicGeometry.Scheme.Modules.Coherent
