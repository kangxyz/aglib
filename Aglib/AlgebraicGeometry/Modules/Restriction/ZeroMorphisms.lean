/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Detecting zero morphisms by open restriction

Restriction detects a zero morphism when its target belongs to the essential image of the actual
direct-image functor along the open immersion.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/GluingSubobjects.lean`.
SHA-256: `d6329afc8058687c07b626f0cf1a82a708d6ed99bcdda9d8fc260402bd0c28a9`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to an open detects zero morphisms whose target comes by
direct image from that open. -/
lemma eq_zero_of_restrict_map_eq_zero
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    (hN : ∃ P : U.Modules, Nonempty (N ≅ (pushforward j).obj P))
    (hf : (restrictFunctor j).map f = 0) : f = 0 := by
  obtain ⟨P, ⟨e⟩⟩ := hN
  have := (restrictAdjunction j).isIso_unit_app_of_iso e
  apply (cancel_mono ((restrictAdjunction j).unit.app N)).mp
  rw [HasZeroMorphisms.zero_comp]
  simpa [hf] using (restrictAdjunction j).unit.naturality f

end AlgebraicGeometry.Scheme.Modules
