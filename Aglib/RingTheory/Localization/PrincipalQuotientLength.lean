/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.ScalarHomology.SurjectiveSpecialization
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.PrimeFiltration.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Aglib.RingTheory.Localization.IteratedModuleLength
public import Aglib.RingTheory.Support.Localization
public import Aglib.RingTheory.Localization.LengthSurjective

/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/PrincipalFactorLengths.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`69390222e181ec80c15729a6cf53210bf99acac5350ceba5ddee5c6df9a63bb4`.
-/

@[expose] public section

open _root_.Module (ScalarCokernel length_localization_of_surjective scalarCokernelEquiv)

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
namespace Module
open _root_.Module
universe u

/-- The local principal cokernel of a literal source prime quotient has the
actual target quotient-fibre length. This compares the actual module factors
before any cycle formula is asserted. -/
theorem localized_principalPrimeCokernel_length
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D]
    (P : Ideal A) (t : A) (h : Function.Surjective (algebraMap A D))
    (ht : RingHom.ker (algebraMap A D) = Ideal.span ({t} : Set A))
    (q : Ideal D) [q.IsPrime] :
    Module.length (Localization.AtPrime (q.under A))
      (ScalarCokernel (Localization.AtPrime (q.under A) ⧸
        P.map (algebraMap A (Localization.AtPrime (q.under A))))
        (algebraMap A (Localization.AtPrime (q.under A)) t)) =
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[D] (D ⧸ P.map (algebraMap A D))) := by
  let B := Localization.AtPrime (q.under A)
  let C := D ⧸ P.map (algebraMap A D)
  let e₁ : (B ⧸ P.map (algebraMap A B)) ≃ₗ[B] B ⊗[A] (A ⧸ P) :=
    Ideal.qoutMapEquivTensorQout B
  let e₂ := scalarCokernelEquiv e₁ (algebraMap A B t)
  let e₃ := principalCokernelBaseChangeEquiv (A ⧸ P) B t
  let e₄ : ScalarCokernel (A ⧸ P) t ≃ₗ[A] C :=
    (tensorSpecializationCokernelEquiv (A ⧸ P) t h ht).trans
      ((Ideal.qoutMapEquivTensorQout (I := P) D).symm.restrictScalars A)
  let e₅ := e₄.baseChange A B _ _
  let e := e₂.trans (e₃.symm.trans e₅)
  exact e.length_eq.trans (length_localization_of_surjective C h q)

end Module
