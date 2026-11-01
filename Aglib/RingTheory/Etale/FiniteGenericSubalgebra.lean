/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FiniteReducedFactorization
public import Aglib.RingTheory.Localization.SubalgebraPreimage
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-! # The canonical finite subalgebra with separable generic fibre

The intermediate algebra is the inverse image of the actual separable subalgebra
in the given localization. In particular its map into the original algebra is
an inclusion, not a map chosen by abstract finite-presentation descent.
-/

@[expose] public noncomputable section

namespace Algebra.FiniteGenericSubalgebra

variable (R K A A' : Type*) [CommRing R] [Field K] [CommRing A] [CommRing A']
  [Algebra R K] [Algebra R A] [Algebra R A'] [Algebra A A'] [Algebra K A']
  [IsScalarTower R A A'] [IsScalarTower R K A']
  [Module.Finite K A'] [IsReduced A']

/-- The separable part as an actual subalgebra of the given generic algebra. -/
def genericPart : Subalgebra K A' :=
  (FiniteReducedFactorization.inclusion K A').range

/-- The product of separable fields identified with its actual image. -/
def genericPartEquiv : FiniteReducedFactorization.SeparablePart K A' ≃ₐ[K]
    genericPart K A' :=
  AlgEquiv.ofInjective (FiniteReducedFactorization.inclusion K A')
    (FiniteReducedFactorization.inclusion_injective K A')

instance genericPart_finite : Module.Finite K (genericPart K A') :=
  Module.Finite.equiv (genericPartEquiv K A').toLinearEquiv

instance genericPart_etale : Algebra.Etale K (genericPart K A') :=
  Algebra.Etale.of_equiv (genericPartEquiv K A')

/-- The original finite intermediate subalgebra, obtained by inverse image. -/
def model : Subalgebra R A :=
  IsLocalization.SubalgebraPreimage.preimage R K A A' (genericPart K A')

/-- The canonical map from the original intermediate algebra to its generic fibre. -/
def genericMap : model R K A A' →ₐ[R] genericPart K A' :=
  IsLocalization.SubalgebraPreimage.map R K A A' (genericPart K A')

instance modelGenericAlgebra : Algebra (model R K A A') (genericPart K A') :=
  (genericMap R K A A').toRingHom.toAlgebra

instance modelGenericBaseTower : IsScalarTower R (model R K A A') (genericPart K A') :=
  IsScalarTower.of_algebraMap_eq' (genericMap R K A A').comp_algebraMap.symm

instance modelGenericAmbientTower :
    IsScalarTower (model R K A A') (genericPart K A') A' :=
  IsScalarTower.of_algebraMap_eq' rfl

@[simp]
theorem genericMap_coe (b : model R K A A') :
    (genericMap R K A A' b : A') = algebraMap A A' b.val := rfl

instance model_finite [IsNoetherianRing R] [Module.Finite R A] :
    Module.Finite R (model R K A A') :=
  Module.Finite.of_injective (model R K A A').val.toLinearMap Subtype.val_injective

/-- The original algebra remains finite over the actual intermediate subalgebra. -/
instance finite_over_model [Module.Finite R A] :
    Module.Finite (model R K A A') A :=
  Module.Finite.of_restrictScalars_finite R (model R K A A') A

/-- The generic comparison is the original localization map, with its actual
scalar algebra structure, rather than merely an abstract algebra isomorphism. -/
theorem genericMap_isLocalization (M : Submonoid R) [IsLocalization M K]
    [IsLocalization (M.map (algebraMap R A)) A'] :
    letI : Algebra (model R K A A') (genericPart K A') :=
      (genericMap R K A A').toRingHom.toAlgebra
    IsLocalization (M.map (algebraMap R (model R K A A'))) (genericPart K A') :=
  IsLocalization.SubalgebraPreimage.isLocalization R K A A' M (genericPart K A')

/-- The generic comparison square is the actual algebra pushout. -/
theorem genericMap_isPushout (M : Submonoid R) [IsLocalization M K]
    [IsLocalization (M.map (algebraMap R A)) A'] :
    Algebra.IsPushout R (model R K A A') K (genericPart K A') := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (model R K A A') M)
      (genericPart K A') :=
    genericMap_isLocalization R K A A' M
  exact Algebra.isPushout_of_isLocalization M K (model R K A A') (genericPart K A')

/-- The generic inclusion is radicial, expressed on maps to arbitrary fields. -/
theorem genericPart_restriction_injective (L : Type*) [Field L] :
    Function.Injective (fun f : A' →+* L => f.comp (genericPart K A').val.toRingHom) := by
  intro f g h
  apply FiniteReducedFactorization.injective_comp_inclusion K A' L
  ext a
  exact DFunLike.congr_fun h
    ⟨FiniteReducedFactorization.inclusion K A' a, ⟨a, rfl⟩⟩

end Algebra.FiniteGenericSubalgebra
