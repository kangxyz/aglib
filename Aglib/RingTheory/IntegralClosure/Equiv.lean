/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Integral closure under compatible ring equivalences -/

@[expose] public section

/-- Compatible base and ambient equivalences preserve the literal integral closure. -/
def RingEquiv.mapIntegralClosure
    {R A R' A' : Type*} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R' A'] (eR : R ≃+* R') (eA : A ≃+* A')
    (h : (algebraMap R' A').comp eR.toRingHom = eA.toRingHom.comp (algebraMap R A)) :
    integralClosure R A ≃+* integralClosure R' A' where
  toFun x := ⟨eA x, x.property.map_of_comp_eq eR.toRingHom eA.toRingHom h⟩
  invFun x := ⟨eA.symm x, x.property.map_of_comp_eq eR.symm.toRingHom
    eA.symm.toRingHom (by
      ext r
      apply eA.injective
      simpa using (congrArg (fun f : R →+* A' => f (eR.symm r)) h).symm)⟩
  left_inv x := Subtype.ext (eA.symm_apply_apply x)
  right_inv x := Subtype.ext (eA.apply_symm_apply x)
  map_mul' x y := Subtype.ext (eA.map_mul x y)
  map_add' x y := Subtype.ext (eA.map_add x y)

