/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Flat.Localization

/-!
The flat-local length formula at a literal contracted prime.

This is a reusable foundation for the field-pullback slice supporting
K2-018#prop:k2018-arithmetic-characters, mathematical source revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982. The encoded result is only the
flat-local module-length formula; it does not encode the arithmetic character
comparison. Its independent input is the pinned Mathlib theorem
IsLocalRing.length_baseChange on the actual localized rings.
The canonical local map and ordinary flatness hypothesis yield the actual
residue-fibre multiplier, including extended-natural infinite lengths.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.FlatBaseChange` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`1eb05acffb8c68c527a71b87bf9c9944f2ab7ca44c9de1944fd6e6449f7a7b16`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped _root_.TensorProduct
open _root_.TensorProduct
namespace Module

universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type w) [AddCommGroup M] [Module A M]

/-- Local flat scalar extension multiplies the original local module length
by the length of the actual residue fibre. -/
theorem localized_length_flat_baseChange [Module.Flat A B]
    (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    Module.length (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] M) =
      Module.length (Localization.AtPrime (q.under A))
        (Localization.AtPrime (q.under A) ⊗[A] M) *
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸
          (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under A))).map
            (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  let e := AlgebraTensorModule.cancelBaseChange A
    (Localization.AtPrime (q.under A)) (Localization.AtPrime q)
    (Localization.AtPrime q) M
  exact e.length_eq.symm.trans (IsLocalRing.length_baseChange
    (Localization.AtPrime (q.under A)) (Localization.AtPrime q)
    (Localization.AtPrime (q.under A) ⊗[A] M))

end Module
