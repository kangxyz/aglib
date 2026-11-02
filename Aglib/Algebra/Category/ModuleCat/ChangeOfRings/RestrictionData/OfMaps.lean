/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionData

/-! # Complete assembly of original tensor-restriction data

Assemble all five original module objects and their maps and laws together
before native cohomology specialization. The result is the existing shared
data, with no second tensor construction.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u w

namespace ModuleCat.TensorRestrictionData

/-- Assemble the entire original comparison over variable module objects. -/
def ofMaps {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (A A' : ModuleCat.{max u w} R) (B B' D : ModuleCat.{max u w} S)
    (q : (extendScalars σ).obj A ⟶ B) (δ : (extendScalars σ).obj A' ⟶ D)
    (eX : A ≅ A') (eY : B ≅ B') (eε : B' ≅ D)
    (g : A → B) (r : A' → D)
    (hq : ∀ x, q ((1 : S) ⊗ₜ[R,σ] x) = g x)
    (hδ : ∀ x, δ ((1 : S) ⊗ₜ[R,σ] x) = r x) :
    TensorRestrictionData.{u, w} σ where
  A := A
  A' := A'
  B := B
  B' := B'
  D := D
  q := q
  δ := δ
  eX := eX
  eY := eY
  eε := eε
  g := g
  r := r
  hq := hq
  hδ := hδ

end ModuleCat.TensorRestrictionData
