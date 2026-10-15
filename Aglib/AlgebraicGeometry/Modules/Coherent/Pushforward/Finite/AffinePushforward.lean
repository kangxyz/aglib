/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
/-!
# Finite affine direct-image preservation

The unchanged sheaf direct image along a finite affine map preserves
finite-type quasicoherent sheaves. On noetherian rings it is exact, and
actual global sections identify it with finite restriction of scalars.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
open ModuleCat
open ModuleCat.FiniteRestrictionScalars
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

include hφ in
/-- The actual finite affine direct image preserves the finite-type quasicoherent predicate. -/
theorem affineLocallyFiniteType_pushforward {M : (Spec S).Modules} (hM : affineLocallyFiniteType
  (Spec S) M) :
    affineLocallyFiniteType (Spec R) ((Scheme.Modules.pushforward (Spec.map φ)).obj M) :=
  QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward_spec φ hφ hM

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
