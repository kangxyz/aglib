/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.EtaleDescent
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Regularity descent along actual etale maps

The algebra structure is induced by the literal scheme stalk map. The ring
theorem proves the essentially etale case and needs no unproved general
flat-local regularity-descent family.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.RegularityDescent.Etale

universe u

/-- Regularity at the source of an essentially etale stalk map implies regularity
at its image. The algebra structure is induced by that same actual stalk map. -/
theorem regular_at_image_of_flat_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] [FormallyUnramified f] (x : X)
    [IsNoetherianRing (Y.presheaf.stalk (f x))]
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) := by
  let := hx
  let := (f.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  let : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  let : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    FormallyUnramified.stalkMap f x
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  exact Algebra.FormallyUnramified.isRegularLocalRing_base_of_flat
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- Regularity descends at the image of an actual etale map. -/
theorem regular_at_image {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Etale f]
    (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))]
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) :=
  regular_at_image_of_flat_formallyUnramified f x hx

/-- A jointly surjective family of etale maps with regular source stalks has
a target with regular stalks. -/
theorem regular_of_etale_cover {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type*} (C : ι → Scheme.{u}) (f : ∀ i, C i ⟶ X)
    [∀ i, AlgebraicGeometry.Etale (f i)]
    (covers : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (regular : ∀ i, Scheme.RegularStalks (C i)) :
    Scheme.RegularStalks X := by
  intro x
  obtain ⟨i, z, rfl⟩ := covers x
  exact regular_at_image (f i) z (regular i z)

end AlgebraicGeometry.Scheme.RegularityDescent.Etale
