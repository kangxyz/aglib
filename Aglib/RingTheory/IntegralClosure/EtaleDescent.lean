/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GenericTensor
public import Aglib.FieldTheory.Separable.TensorProductSplitting
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descending etaleness from a splitting normalization

An etale normalization `C` in a splitting field makes the base change of the
original normalization a finite product of copies of `C`. Faithfully-flat
etale descent then proves etaleness of the original normalization. No flatness
of that original normalization is assumed, and no averaging is used.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace integralClosure

variable (A K L E : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra.IsIntegral K L]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Algebra.Etale A (integralClosure A L)]

/-- Smooth normalization base change and the actual field splitting identify
the original base-changed normalization with a finite product of the upper one. -/
def splitTensorIntegralClosureEquiv
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    integralClosure A L ⊗[A] integralClosure A E ≃ₐ[integralClosure A L]
      ((E →ₐ[K] L) → integralClosure A L) := by
  let C := integralClosure A L
  let : IsIntegrallyClosedIn C L :=
    IsIntegrallyClosedIn.of_isIntegralClosure (R := A)
  let eC : integralClosure C L ≃ₐ[C] C := IsIntegralClosure.equiv C (integralClosure C L) L C
  let : Module.Finite C (integralClosure C L) :=
    Module.Finite.of_surjective eC.symm.toLinearMap eC.symm.surjective
  let e : C ⊗[A] E ≃ₐ[C] ((E →ₐ[K] L) → L) :=
    (genericTensorEquiv A K L E).trans
      ((Algebra.IsSeparable.tensorProductEquivPi K E L hsplit).restrictScalars C)
  exact (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure A C E)
    TensorProduct.toIntegralClosure_bijective_of_smooth).trans
      ((integralClosure.equivPi C (C ⊗[A] E) (fun _ : E →ₐ[K] L => L) e).trans
        (AlgEquiv.piCongrRight fun _ => eC))

/-- Etaleness of a faithfully-flat splitting normalization descends to the
literal original normalization. Its own flatness is a conclusion, not an input. -/
theorem etale_of_faithfullyFlat_splitting_normalization
    [Module.FaithfullyFlat A (integralClosure A L)]
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    Algebra.Etale A (integralClosure A E) := by
  let e := splitTensorIntegralClosureEquiv A K L E hsplit
  let : Algebra.Etale (integralClosure A L)
      (integralClosure A L ⊗[A] integralClosure A E) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (integralClosure A L)

/-- Etaleness of the upper splitting normalization suffices globally. Its
faithful flatness follows from integrality, injectivity and flatness, not from
global freeness or an extra assumption on the lower normalization. -/
theorem etale_of_splitting_normalization
    (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits) :
    Algebra.Etale A (integralClosure A E) := by
  let : FaithfulSMul A (integralClosure A L) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A L)).mpr (by
      intro x y h
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      have hh := congrArg (algebraMap (integralClosure A L) L) h
      simpa only [← IsScalarTower.algebraMap_apply] using hh)
  let : Module.FaithfullyFlat A (integralClosure A L) := inferInstance
  exact etale_of_faithfullyFlat_splitting_normalization A K L E hsplit

end integralClosure
