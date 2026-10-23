/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Localization
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Descent of finite integral closure along a finite algebra

The actual lower integral closure embeds into the actual upper integral closure
through the supplied field map. Finiteness of the upper closure is
an explicit premise. Finite restriction of scalars and Noetherian submodule
finiteness then give finiteness of the original lower closure.
-/

@[expose] public noncomputable section

universe u

namespace integralClosure

/-- For a finite algebra over a Noetherian ring, finiteness of the upper
integral closure in a field implies finiteness of the lower integral closure
in a compatible subfield. The original coefficient maps are retained. -/
theorem finite_of_finite_extension
    (R S K L : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field K] [Algebra R K]
    [Field L] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]
    [Module.Finite S (integralClosure S L)] :
    Module.Finite R (integralClosure R K) := by
  let : Module.Finite R (integralClosure S L) :=
    Module.Finite.trans S (integralClosure S L)
  let f : K →ₐ[R] L := IsScalarTower.toAlgHom R K L
  let g : integralClosure R K →ₐ[R] integralClosure S L :=
    (scalarExtensionHom R S L).comp f.mapIntegralClosure
  apply Module.Finite.of_injective g.toLinearMap
  intro x y h
  apply Subtype.ext
  apply f.injective
  exact congrArg Subtype.val h

end integralClosure
