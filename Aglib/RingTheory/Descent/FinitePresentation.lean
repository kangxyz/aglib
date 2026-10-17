/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Finite presentation of modules descends along faithfully flat ring maps

If `B` is a faithfully flat `A`-algebra and `B ⊗[A] M` is a finitely presented `B`-module, then
`M` is a finitely presented `A`-module (Stacks Project, Tag 03C4 (2), Lemma 10.83.2; the
source states it for `M ⊗_R S`, here written `B ⊗[A] M`, an isomorphic `B`-module). Mathlib
supplies the
corresponding descent of finite generation
(`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`) and of flatness
(`Module.Flat.of_flat_tensorProduct`).
-/

@[expose] public section

open TensorProduct

namespace Module.FinitePresentation

/-- Finite presentation descends along a faithfully flat ring map: a presentation kernel of `M`
becomes, after the flat base change to `B`, the kernel of a presentation of the finitely
presented `B ⊗[A] M`, hence finite; finiteness then descends. -/
theorem of_finitePresentation_tensorProduct_of_faithfullyFlat (A B : Type*) [CommRing A]
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (M : Type*) [AddCommGroup M]
    [Module A M] [Module.FinitePresentation B (B ⊗[A] M)] : Module.FinitePresentation A M := by
  have : Module.Finite A M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  have hπB : Function.Surjective (AlgebraTensorModule.lTensor B B π) :=
    LinearMap.lTensor_surjective B hπ
  have hKB : (LinearMap.ker (AlgebraTensorModule.lTensor B B π)).FG :=
    Module.FinitePresentation.fg_ker _ hπB
  have hrange := Module.Flat.ker_lTensor_eq (R := A) (S := B) B π
  have hinj : Function.Injective (AlgebraTensorModule.lTensor B B (LinearMap.ker π).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have : Module.Finite B (LinearMap.ker (AlgebraTensorModule.lTensor B B π)) :=
    Module.Finite.iff_fg.mpr hKB
  have : Module.Finite B (B ⊗[A] LinearMap.ker π) :=
    Module.Finite.equiv ((LinearEquiv.ofInjective _ hinj).trans
      (LinearEquiv.ofEq _ _ hrange.symm)).symm
  have : Module.Finite A (LinearMap.ker π) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  exact Module.finitePresentation_of_surjective π hπ (Module.Finite.iff_fg.mp this)

end Module.FinitePresentation
