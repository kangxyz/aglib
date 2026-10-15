/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Affine-locally finite-type quasicoherent module sheaves

The actual chart predicate and full category are defined for every scheme.
All affine charts are tested. No Noetherianity or general coherence claim is
part of this definition.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- A sheaf is affine-locally quasicoherent of finite type. The condition is
tested on every affine open chart, without any hypothesis on its ring. -/
def affineLocallyFiniteType (X : Scheme.{u}) : ObjectProperty X.Modules := fun M =>
  ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
    affineFiniteSheaf R ((Scheme.Modules.restrictFunctor j).obj M)

instance affineLocallyFiniteType_isoClosed (X : Scheme.{u}) : (affineLocallyFiniteType
  X).IsClosedUnderIsomorphisms where
  of_iso e h R j _ :=
    (affineFiniteSheaf R).prop_of_iso ((Scheme.Modules.restrictFunctor j).mapIso e) (h R j)

/-- Sheaves whose restriction to every affine open chart is quasicoherent of
finite type, with their actual sheaf morphisms. The category is defined over
every scheme; the abelian and exact structures below assume local noetherianity. -/
abbrev FiniteTypeSheaves (X : Scheme.{u}) := (affineLocallyFiniteType X).FullSubcategory

variable (X : Scheme.{u})

/-- The initial size bound uses the genuine sheaf-object universe. -/
instance finiteTypeSheaves_essentiallySmall : EssentiallySmall.{u+1} (FiniteTypeSheaves X) :=
  inferInstance

/-- Inclusion of affine-locally finite-type sheaves into module sheaves. -/
abbrev finiteTypeSheavesToModules : FiniteTypeSheaves X ⥤ X.Modules := (affineLocallyFiniteType X).ι

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
