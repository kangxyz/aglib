/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Socle
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Detecting freeness by tensoring with a nonzero Artinian module

The residue field embeds into a nonzero Artinian module. Flatness of a source
module therefore transports tensor injectivity to the residue field. For a
finite presentation with free middle term, the native residue-field criterion
then gives freeness. No minimal presentation or choice of a matrix is needed.
-/

@[expose] public section

namespace IsArtinian

variable {R : Type*} {M : Type*} {N : Type*} {P : Type*} {C : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup C] [Module R C]
    [IsArtinian R C] [Nontrivial C]

/-- Tensor injectivity against a nonzero Artinian module detects tensor
injectivity against the residue field when the source is flat. -/
theorem injective_lTensor_residueField_of_injective [Module.Flat R M]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor C)) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) := by
  obtain ⟨e, he⟩ := exists_injective_residueField R C
  have hi : Function.Injective (e.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap e he
  intro a b hab
  apply hi
  apply hf
  change ((f.lTensor C).comp (e.rTensor M)) a =
    ((f.lTensor C).comp (e.rTensor M)) b
  rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  exact congrArg (e.rTensor N) hab

/-- A finite presentation with flat finite source and finite free middle term
has free cokernel if tensoring its first map with a nonzero Artinian module
remains injective. -/
theorem free_of_lTensor_injective [Module.Flat R M] [Module.Finite R M]
    [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hf : Function.Injective (f.lTensor C)) : Module.Free R P :=
  Module.free_of_lTensor_residueField_injective f g hg hex
    (injective_lTensor_residueField_of_injective f hf)

end IsArtinian
