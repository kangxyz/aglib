/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory

/-!
# Noetherian affine finite-type categories

The same quasicoherent finite-type objects form an abelian category under
Noetherianity, with the standard short-exact-sequence exact structure.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.ExactCategory
open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- On a noetherian affine scheme, coherent sheaves form a Serre class inside
quasicoherent sheaves. -/
instance affineFiniteType_isSerreClass : (affineFiniteType R).IsSerreClass := by
  change ((finiteModule R).inverseImage (tildeEquiv (R := R)).inverse).IsSerreClass
  infer_instance

/-- The category of coherent sheaves on a noetherian affine scheme is abelian. -/
instance instAbelianAffineCoherent : Abelian (AffineFiniteType R) := inferInstance

/-- The genuine abelian exact structure on affine coherent sheaves. -/
def affineCoherentExactStructure : ExactStructure (AffineFiniteType R) :=
  abelianExactStructure _

end AlgebraicGeometry.Scheme.Modules.Coherent
