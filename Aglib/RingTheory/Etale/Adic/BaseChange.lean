/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.Adic.LocalCriterion
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Local base change of the all-order etale criterion

The reductions of an algebra remain etale after an arbitrary scalar
extension. Applying the local criterion at a Noetherian local target gives
etaleness of the actual tensor algebra whenever the extended ideal is proper.
The comparisons are the native tensor cancellation maps, which send nested
unit tensors to the original unit tensor. No localization choice or
noncanonical module equivalence occurs.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace Algebra

/-- An etale quotient algebra stays etale over any algebra annihilated by the
quotient ideal. The comparison uses the canonical quotient lift and native
algebra tensor cancellation. -/
theorem etale_baseChange_of_etale_quotient {A B T : Type*}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]
    (I : Ideal A) (hI : I ≤ RingHom.ker (algebraMap A T))
    (h : Etale (A ⧸ I) ((A ⧸ I) ⊗[A] B)) :
    Etale T (T ⊗[A] B) := by
  let : Algebra (A ⧸ I) T :=
    (Ideal.Quotient.liftₐ I (Algebra.ofId A T) hI).toRingHom.toAlgebra
  have : IsScalarTower A (A ⧸ I) T := .of_algebraMap_eq' rfl
  let := h
  have : Etale T (T ⊗[A ⧸ I] ((A ⧸ I) ⊗[A] B)) := inferInstance
  exact Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange A (A ⧸ I) T T B)

/-- The literal reduction of a scalar-extended algebra is etale if the
corresponding original reduction is etale. Both comparison maps are native
cancellations of base change and preserve the original `includeRight` maps. -/
theorem etale_quotient_map_pow_baseChange {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]
    (J : Ideal A) (n : ℕ)
    (h : Etale (A ⧸ J ^ n) ((A ⧸ J ^ n) ⊗[A] B)) :
    Etale (R ⧸ (J.map (algebraMap A R)) ^ n)
      ((R ⧸ (J.map (algebraMap A R)) ^ n) ⊗[R] (R ⊗[A] B)) := by
  let T := R ⧸ (J.map (algebraMap A R)) ^ n
  have hkill : J ^ n ≤ RingHom.ker (algebraMap A T) := by
    intro a ha
    change Ideal.Quotient.mk ((J.map (algebraMap A R)) ^ n) (algebraMap A R a) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have : Etale T (T ⊗[A] B) := etale_baseChange_of_etale_quotient (J ^ n) hkill h
  exact Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange A R T T B).symm

/-- All positive etale reductions imply etaleness after scalar extension to
a Noetherian local ring in which the extended ideal is proper. In particular,
this applies to localization at any point containing the ideal. -/
theorem etale_baseChange_of_etale_quotient_pow {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite A B]
    (J : Ideal A) (hJ : J.map (algebraMap A R) ≠ ⊤)
    (h : ∀ n : ℕ, 0 < n → Etale (A ⧸ J ^ n) ((A ⧸ J ^ n) ⊗[A] B)) :
    Etale R (R ⊗[A] B) := by
  apply etale_of_etale_quotient_pow (J.map (algebraMap A R)) hJ
  intro n hn
  exact etale_quotient_map_pow_baseChange J n (h n hn)

end Algebra
