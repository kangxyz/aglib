/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Equality over an isomorphic open restriction

Maps into a scheme that lie over the same map to a protected open are equal
when the structure morphism is an isomorphism over that open.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Maps above the same protected-open map agree when the structure morphism
is an isomorphism on that open. -/
theorem ext_of_isIso_restriction {A B T : Scheme.{u}}
    (f : A ⟶ B) (U : B.Opens) [IsIso (f ∣_ U)] (r : T ⟶ U.toScheme)
    (a b : T ⟶ A) (ha : a ≫ f = r ≫ U.ι) (hb : b ≫ f = r ≫ U.ι) : a = b := by
  let K := isPullback_morphismRestrict f U
  let a' := K.lift r a ha.symm
  let b' := K.lift r b hb.symm
  have he : a' = b' := (cancel_mono (f ∣_ U)).mp
    ((K.lift_fst r a ha.symm).trans (K.lift_fst r b hb.symm).symm)
  calc
    a = a' ≫ (f ⁻¹ᵁ U).ι := (K.lift_snd r a ha.symm).symm
    _ = b' ≫ (f ⁻¹ᵁ U).ι := congrArg (fun k ↦ k ≫ (f ⁻¹ᵁ U).ι) he
    _ = b := K.lift_snd r b hb.symm

end AlgebraicGeometry.Scheme.Hom
