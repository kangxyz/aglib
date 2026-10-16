/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support
/-!
# Actual supported coherent sheaves on a noetherian affine scheme

The support category is the kernel of actual open restriction, applied to
actual coherent sheaves. Its Serre property is proved from exactness of the
inclusion and restriction functors. Its objects have ordinary closed stalk
support, and vanishing on the open is equivalent to support in its complement.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent
variable (R : CommRingCat.{u})

/-- The ordinary stalk support of an affine finite-type quasicoherent sheaf is closed. -/
theorem isClosed_support (M : AffineFiniteType R) :
    IsClosed (Scheme.Modules.support ((affineFiniteTypeToModules R).obj M)) :=
  Scheme.Modules.isClosed_support_of_finite_globalSections _

variable {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Finite-type quasicoherent sheaves supported outside the actual open immersion. -/
def affineSupportedAway : ObjectProperty (AffineFiniteType R) :=
  (Scheme.Modules.supportedAway j).inverseImage (affineFiniteTypeToModules R)

@[simp]
theorem affineSupportedAway_iff (M : AffineFiniteType R) :
    affineSupportedAway R j M ↔
      IsZero ((Scheme.Modules.restrictFunctor j).obj ((affineFiniteTypeToModules R).obj M)) :=
  Iff.rfl

/-- Vanishing on the open is equivalent to disjointness of stalk support and
its image. -/
theorem affineSupportedAway_iff_support_disjoint (M : AffineFiniteType R) :
    affineSupportedAway R j M ↔
      Disjoint (Scheme.Modules.support ((affineFiniteTypeToModules R).obj M)) (Set.range j) :=
  Scheme.Modules.supportedAway_iff_support_disjoint j _

/-- Equivalently, ordinary stalk support is contained in the open complement. -/
theorem affineSupportedAway_iff_support_subset (M : AffineFiniteType R) :
    affineSupportedAway R j M ↔
      Scheme.Modules.support ((affineFiniteTypeToModules R).obj M) ⊆ (Set.range j)ᶜ := by
  rw [affineSupportedAway_iff_support_disjoint]
  exact Set.disjoint_left

/-- The full subcategory of affine finite-type quasicoherent sheaves
supported outside the selected open. -/
abbrev SupportedAffineFiniteType := (affineSupportedAway R j).FullSubcategory

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
