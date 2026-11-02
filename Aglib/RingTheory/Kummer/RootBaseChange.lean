/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Original root maps under localization and faithful flat base change

The existing literal-root tensor equivalence determines the original root map.
Its right-oriented version keeps the original root algebra as scalar ring.
Localization and faithful flatness then transfer along that same comparison.
When the localized root algebra is local, its maximal-ideal contraction names
the exact prime localization, not an unrelated selected local model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

universe u v

variable {R : Type u} [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  (N : ℕ) (f : R)

/-- The original root map induced by change of coefficient ring. -/
def rootBaseChangeHom : RootAlgebra N f →ₐ[R] RootAlgebra N (algebraMap R B f) :=
  ((genericRootEquiv (K := B) N f).restrictScalars R).toAlgHom.comp
    Algebra.TensorProduct.includeRight

/-- The target's original-root-algebra action is induced by that actual map. -/
@[instance_reducible] def rootBaseChangeAlgebra :
    Algebra (RootAlgebra N f) (RootAlgebra N (algebraMap R B f)) :=
  (rootBaseChangeHom B N f).toRingHom.toAlgebra

attribute [local instance] rootBaseChangeAlgebra

@[simp] theorem rootBaseChangeHom_root :
    rootBaseChangeHom B N f (AdjoinRoot.root (rootPolynomial N f)) =
      AdjoinRoot.root (rootPolynomial N (algebraMap R B f)) :=
  genericRootEquiv_root N f

theorem rootBaseChangeHom_algebraMap (r : R) :
    rootBaseChangeHom B N f (algebraMap R (RootAlgebra N f) r) =
      algebraMap R (RootAlgebra N (algebraMap R B f)) r :=
  (rootBaseChangeHom B N f).commutes r

/-- The original root tensor comparison, linear over the original root algebra. -/
def rootBaseChangeRightEquiv :
    RootAlgebra N f ⊗[R] B ≃ₐ[RootAlgebra N f] RootAlgebra N (algebraMap R B f) :=
  { ((Algebra.TensorProduct.comm R (RootAlgebra N f) B).trans
      ((genericRootEquiv (K := B) N f).restrictScalars R)).toRingEquiv with
    commutes' _ := rfl }

/-- Pure tensors keep both original coefficient maps. -/
theorem rootBaseChangeRightEquiv_tmul (t : RootAlgebra N f) (b : B) :
    rootBaseChangeRightEquiv B N f (t ⊗ₜ[R] b) =
      algebraMap B (RootAlgebra N (algebraMap R B f)) b * rootBaseChangeHom B N f t := by
  change genericRootEquiv (K := B) N f (b ⊗ₜ[R] t) = _
  have he : b ⊗ₜ[R] t =
      algebraMap B (B ⊗[R] RootAlgebra N f) b * (1 ⊗ₜ[R] t) := by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [he, map_mul, AlgEquiv.commutes]
  rfl

/-- Localizing the coefficient ring localizes the same root algebra at the
image of the original denominator submonoid. -/
theorem rootBaseChange_isLocalization (S : Submonoid R) [IsLocalization S B] :
    IsLocalization (Algebra.algebraMapSubmonoid (RootAlgebra N f) S)
      (RootAlgebra N (algebraMap R B f)) :=
  IsLocalization.isLocalization_of_algEquiv _ (rootBaseChangeRightEquiv B N f)

/-- Faithful flatness transfers to the actual root map, not just an isomorphic
replacement algebra. -/
theorem rootBaseChange_faithfullyFlat [Module.FaithfullyFlat R B] :
    Module.FaithfullyFlat (RootAlgebra N f) (RootAlgebra N (algebraMap R B f)) :=
  Module.FaithfullyFlat.of_linearEquiv _ _ (rootBaseChangeRightEquiv B N f).symm.toLinearEquiv

section Local

variable [IsLocalRing (RootAlgebra N (algebraMap R B f))]
  (S : Submonoid R) [IsLocalization S B]

include S in
/-- A local localized root algebra is precisely the localization at the
contraction of its actual maximal ideal. -/
theorem rootBaseChange_isLocalizationAtPrime :
    IsLocalization.AtPrime (RootAlgebra N (algebraMap R B f))
      ((IsLocalRing.maximalIdeal (RootAlgebra N (algebraMap R B f))).under
        (RootAlgebra N f)) := by
  let := rootBaseChange_isLocalization B N f S
  apply IsLocalization.of_le (Algebra.algebraMapSubmonoid (RootAlgebra N f) S)
  · intro s hs
    change algebraMap (RootAlgebra N f) (RootAlgebra N (algebraMap R B f)) s ∉
      IsLocalRing.maximalIdeal (RootAlgebra N (algebraMap R B f))
    exact fun h => h (IsLocalization.map_units (RootAlgebra N (algebraMap R B f)) ⟨s, hs⟩)
  · intro s hs
    change ¬ ¬ IsUnit (algebraMap (RootAlgebra N f)
      (RootAlgebra N (algebraMap R B f)) s) at hs
    exact not_not.mp hs

/-- The original prime localization and coefficient-localized literal root
algebra agree over the original root algebra. -/
def rootBaseChangeAtPrimeEquiv :
    Localization.AtPrime
        ((IsLocalRing.maximalIdeal (RootAlgebra N (algebraMap R B f))).under
          (RootAlgebra N f)) ≃ₐ[RootAlgebra N f] RootAlgebra N (algebraMap R B f) := by
  let := rootBaseChange_isLocalizationAtPrime B N f S
  exact IsLocalization.algEquiv
    ((IsLocalRing.maximalIdeal (RootAlgebra N (algebraMap R B f))).under
      (RootAlgebra N f)).primeCompl _ _

end Local

end Algebra.Kummer
