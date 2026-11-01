/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionSquare

/-! # Shared original module data of tensor restriction

This record shares the original objects, maps and comparison isomorphisms.
Its square uses the existing complete constructor, not another scalar-extension
or cohomology model.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u w

namespace ModuleCat

/-- All original module objects and maps, with their unit-tensor laws. -/
structure TensorRestrictionData {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S) where
  A : ModuleCat.{max u w} R
  A' : ModuleCat.{max u w} R
  B : ModuleCat.{max u w} S
  B' : ModuleCat.{max u w} S
  D : ModuleCat.{max u w} S
  q : (extendScalars σ).obj A ⟶ B
  δ : (extendScalars σ).obj A' ⟶ D
  eX : A ≅ A'
  eY : B ≅ B'
  eε : B' ≅ D
  g : A → B
  r : A' → D
  hq : ∀ x, q ((1 : S) ⊗ₜ[R,σ] x) = g x
  hδ : ∀ x, δ ((1 : S) ⊗ₜ[R,σ] x) = r x

/-- Assemble the same square from the original shared data and geometric law. -/
def TensorRestrictionData.square {R S : Type u} [CommRing R] [CommRing S]
    {σ : R →+* S} (d : TensorRestrictionData.{u, w} σ)
    (hgeo : ∀ x, d.eε.hom (d.eY.hom (d.g x)) = d.r (d.eX.hom x)) :
    Square (ModuleCat.{max u w} S) :=
  tensorRestrictionSquare.{u, w} σ d.A d.A' d.B d.B' d.D
    d.q d.δ d.eX d.eY d.eε d.g d.r d.hq d.hδ hgeo

end ModuleCat
