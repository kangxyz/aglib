/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionUnit

/-! A separately configured client of the foundation and its actual coefficient-map API. -/

@[expose] public section

noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u
variable {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]

example (a : R →+* A) (φ : A →+* S) (M : ModuleCat.{u} A)
    (x : (ModuleCat.restrictScalars a).obj M) :
    ModuleCat.restrictedExtensionUnit a φ (φ.comp a) rfl M x =
      (1 : S) ⊗ₜ[A,φ] (x : M) :=
  ModuleCat.restrictedExtensionUnit_apply a φ (φ.comp a) rfl M x

example (M : ModuleCat.{u} A) (x : M) :
    ModuleCat.restrictedExtensionUnit (RingHom.id A) (RingHom.id A)
      ((RingHom.id A).comp (RingHom.id A)) rfl M x =
      (1 : A) ⊗ₜ[A,RingHom.id A] (x : M) :=
  ModuleCat.restrictedExtensionUnit_apply _ _ _ rfl M x
