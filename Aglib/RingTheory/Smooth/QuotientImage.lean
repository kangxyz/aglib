/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.LocalEquivalence
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smoothness of the actual kernel quotient of an embedded algebra image

A surjective generator evaluation followed by an injective actual point
identifies its literal kernel quotient with the generated source algebra.
The native quotient equivalence respects the given point, so smoothness at
the inverse image of a target prime transports to the actual kernel quotient.
-/

@[expose] public noncomputable section

namespace Algebra

universe u v w z

variable {R : Type u} {A : Type v} {B : Type w} {C : Type z}
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- The literal kernel quotient of a surjective evaluation followed by an
injective point is smooth at the corresponding target prime whenever the
actual source image is smooth there. -/
theorem IsSmoothAt.of_quotientKer_of_surjective
    (E : A →ₐ[R] B) (hE : Function.Surjective E)
    (f : B →ₐ[R] C) (hf : Function.Injective f)
    (χ : A →+* C) (hχ : ∀ a, χ a = f (E a))
    (qC : Ideal C) [qC.IsPrime]
    (hsmooth : IsSmoothAt R (qC.comap f.toRingHom)) :
    IsSmoothAt R (qC.comap χ.kerLift) := by
  have hker : RingHom.ker χ = RingHom.ker E.toRingHom := by
    ext a
    change χ a = 0 ↔ E a = 0
    rw [hχ]
    exact map_eq_zero_iff f hf
  let e : (A ⧸ RingHom.ker χ) ≃ₐ[R] B :=
    (Ideal.quotientEquivAlgOfEq R hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective hE)
  have hepoint : f.toRingHom.comp e.toRingHom = χ.kerLift := by
    apply RingHom.ext
    intro a
    refine Quotient.inductionOn' a ?_
    intro a
    change f (E a) = χ a
    exact (hχ a).symm
  have hecentre : qC.comap χ.kerLift =
      (qC.comap f.toRingHom).comap e.toRingEquiv := by
    change qC.comap χ.kerLift = (qC.comap f.toRingHom).comap e.toRingHom
    rw [Ideal.comap_comap, hepoint]
  have hlocal := IsSmoothAt.of_algEquiv e (qC.comap f.toRingHom) hsmooth
  simpa only [← hecentre] using hlocal

end Algebra
