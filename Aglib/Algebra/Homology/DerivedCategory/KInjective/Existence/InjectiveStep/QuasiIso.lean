/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InjectiveStep.Naturality
public import Aglib.Algebra.Homology.MappingCocone.ShortExact

/-!
# The actual monomorphic quasi-isomorphism for the injective successor step

The original unit into the quotient cocone is a quasi-isomorphism by the native
short exact sequence. Its componentwise injective factorization was proved
using the same augmentation in `Quotient`. This constructs the injective-factor
operation of Stacks 079N, not a K-injective replacement of every complex.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

instance injectiveStepCoconeι_quasiIso (K : CochainComplex C ℤ) :
    QuasiIso (injectiveStepCoconeι K) :=
  mappingCocone.quasiIso_liftShortComplex (injectiveStepShortComplex K)
    (injectiveStepShortComplex_shortExact K)

instance injectiveStepUnit_quasiIso (K : CochainComplex C ℤ) :
    QuasiIso ((injectiveStepUnit (C := C)).app K) :=
  inferInstanceAs (QuasiIso (injectiveStepCoconeι K))

/-- The original natural unit factors termwise through an actual injective subobject. -/
lemma injectiveStepUnit_injectiveFactor (K : CochainComplex C ℤ) (n : ℤ) :
    ∃ (I : C) (_ : Injective I) (a : K.X n ⟶ I)
      (b : I ⟶ ((injectiveStepFunctor C).obj K).X n), Mono b ∧
        ((injectiveStepUnit (C := C)).app K).f n = a ≫ b :=
  injectiveStepCoconeι_injectiveFactor K n

end CochainComplex
