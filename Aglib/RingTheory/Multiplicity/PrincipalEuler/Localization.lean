/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.LengthSurjective
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.ScalarHomology.BaseChange
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization

/-!
# Transport of actual scalar homology under localization

For a surjective scalar-ring map, the two localizations at corresponding primes
give the same kernel and cokernel lengths. This compares the actual scalar
homology, including the kernel of a possibly nonregular scalar action.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEulerScalarTransport` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`f3aef136d6013533d3a6e295159d993b7c0b3f74e1079bb8a7635f13a88e5fd4`.
This module retains the general surjective-localization Euler identity. The kernel and
cokernel transport maps live in `ScalarHomology.BaseChange`; the lower length input is
`Localization.LengthSurjective`. Application interfaces remain outside this extraction.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module
open _root_.TensorProduct
universe u v w
variable {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]
variable (M : Type w) [AddCommGroup M] [Module A M]
variable [Module D M] [IsScalarTower A D M]

/-- Euler expressions agree over source and quotient local rings. The comparison
retains both actual homology modules and does not require scalar regularity. -/
theorem principalEuler_localization_of_surjective (t : A)
    (h : Function.Surjective (algebraMap A D)) (q : Ideal D) [q.IsPrime] :
    principalEuler (N := Localization.AtPrime (q.under A) ⊗[A] M)
      (algebraMap A (Localization.AtPrime (q.under A)) t) =
    principalEuler (N := Localization.AtPrime q ⊗[D] M)
      (algebraMap D (Localization.AtPrime q) (algebraMap A D t)) := by
  let B := Localization.AtPrime (q.under A)
  let E := Localization.AtPrime q
  have hk : Module.length B
      (ScalarKernel (B ⊗[A] M) (algebraMap A B t)) =
      Module.length E
        (ScalarKernel (E ⊗[D] M) (algebraMap D E (algebraMap A D t))) := by
    calc
      _ = Module.length B (B ⊗[A] ScalarKernel M t) :=
        (scalarKernelBaseChangeEquiv M B t).length_eq.symm
      _ = Module.length B (B ⊗[A] ScalarKernel M (algebraMap A D t)) :=
        ((scalarKernelRestrictionEquiv (D := D) M t).baseChange A B _ _).length_eq
      _ = Module.length E (E ⊗[D] ScalarKernel M (algebraMap A D t)) :=
        Module.length_localization_of_surjective _ h q
      _ = _ := (scalarKernelBaseChangeEquiv M E (algebraMap A D t)).length_eq
  have hc : Module.length B
      (ScalarCokernel (B ⊗[A] M) (algebraMap A B t)) =
      Module.length E
        (ScalarCokernel (E ⊗[D] M) (algebraMap D E (algebraMap A D t))) := by
    calc
      _ = Module.length B (B ⊗[A] ScalarCokernel M t) :=
        (principalCokernelBaseChangeEquiv M B t).length_eq.symm
      _ = Module.length B (B ⊗[A] ScalarCokernel M (algebraMap A D t)) :=
        ((scalarCokernelRestrictionEquiv (D := D) M t).baseChange A B _ _).length_eq
      _ = Module.length E (E ⊗[D] ScalarCokernel M (algebraMap A D t)) :=
        Module.length_localization_of_surjective _ h q
      _ = _ := (principalCokernelBaseChangeEquiv M E (algebraMap A D t)).length_eq
  unfold principalEuler
  rw [hc, hk]

end Module
