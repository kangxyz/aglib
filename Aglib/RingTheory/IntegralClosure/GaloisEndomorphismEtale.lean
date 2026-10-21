/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismTrace
public import Aglib.RingTheory.Etale.FiniteFlatPurity

/-!
# The Galois endomorphism map for an etale normalization

For a finite free etale normalization in a finite Galois extension, the original
coefficient map is an equivalence. The proof uses the perfect trace pairing,
not division by the order of the Galois group. Etaleness is a hypothesis here;
this file does not prove that a Galois closure is etale or assert branch purity.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [IsNoetherianRing A]
  [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  [Module.Free A B] [Module.Finite A B] [Algebra.Etale A B]

/-- For a finite free etale normalization, every endomorphism has unique integral
Galois coefficients. -/
theorem galoisEndomorphism_bijective_of_etale :
    Function.Bijective (galoisEndomorphism A K L B) :=
  ⟨galoisEndomorphism_injective A K L B,
    galoisEndomorphism_surjective_of_traceForm_surjective A K L B
      Algebra.traceForm_surjective_of_etale⟩

/-- The equivalence induced by the original Galois coefficient map. -/
def galoisEndomorphismEquivOfEtale :
    ((L ≃ₐ[K] L) → B) ≃ₗ[B] Module.End A B :=
  LinearEquiv.ofBijective (galoisEndomorphism A K L B)
    (galoisEndomorphism_bijective_of_etale A K L B)

/-- The equivalence retains the canonical multiplication-followed-by-action formula. -/
theorem galoisEndomorphismEquivOfEtale_apply (c : (L ≃ₐ[K] L) → B) (x : B) :
    galoisEndomorphismEquivOfEtale A K L B c x =
      ∑ g, c g * galRestrict A K L B g x :=
  galoisEndomorphism_apply A K L B c x

end IsIntegralClosure
