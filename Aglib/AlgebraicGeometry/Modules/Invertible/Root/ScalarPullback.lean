/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.Scalars

/-! # Original scalar isomorphisms and reduction of unit coordinates -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

/-- The original scalar isomorphism at one is the original identity. -/
theorem scalarIso_one (X : Scheme.{u}) (M : X.Modules) :
    ScalarAutomorphisms.scalarIso X M 1 = CategoryTheory.Iso.refl M := by
  apply CategoryTheory.Iso.ext
  exact ScalarAutomorphisms.scalarMap_one X M

/-- Composition of original scalar isomorphisms is multiplication of their units. -/
theorem scalarIso_trans (X : Scheme.{u}) (M : X.Modules) (a b : Γ(X, ⊤)ˣ) :
    ScalarAutomorphisms.scalarIso X M a ≪≫ ScalarAutomorphisms.scalarIso X M b =
      ScalarAutomorphisms.scalarIso X M (a * b) := by
  apply CategoryTheory.Iso.ext
  exact ScalarAutomorphisms.scalarMap_mul X M a b

/-- Original scheme pullback of a scalar isomorphism uses the original section map. -/
theorem pullback_scalarIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (a : Γ(Y, ⊤)ˣ) :
    (Scheme.Modules.pullback f).mapIso (ScalarAutomorphisms.scalarIso Y M a) =
      ScalarAutomorphisms.scalarIso X ((Scheme.Modules.pullback f).obj M)
        (Units.map f.appTop.hom.toMonoidHom a) := by
  apply CategoryTheory.Iso.ext
  exact pullback_scalarMap f M (a : Γ(Y, ⊤))

/-- If the original pulled-back automorphism is identity, its actual unit
coordinate maps to one under the original global section map. -/
theorem map_autUnit_eq_one_of_pullback_eq_refl
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) (e : L.val ≅ L.val)
    (he : (Scheme.Modules.pullback f).mapIso e = CategoryTheory.Iso.refl _) :
    Units.map f.appTop.hom.toMonoidHom (autUnit Y L e) = 1 := by
  apply (autUnitEquiv X (pullbackLineBundle f L)).symm.injective
  change ScalarAutomorphisms.scalarIso X ((Scheme.Modules.pullback f).obj L.val)
      (Units.map f.appTop.hom.toMonoidHom (autUnit Y L e)) =
    ScalarAutomorphisms.scalarIso X ((Scheme.Modules.pullback f).obj L.val) 1
  rw [← pullback_scalarIso, ← aut_eq_scalar Y L e, he, scalarIso_one]

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
