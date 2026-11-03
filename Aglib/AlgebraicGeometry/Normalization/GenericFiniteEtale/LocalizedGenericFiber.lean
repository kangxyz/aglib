/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # The original fraction field and the localized generic fibre

Localization does not replace the specified fraction field. Its canonical
local algebra action identifies the native scheme function field with that
same field, and the original pullback isomorphisms retain both projections.
No normality, Noetherianity, cover existence, or cohomological zero is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] (q : PrimeSpectrum A)

local notation "L" => Localization.AtPrime q.asIdeal
local notation "γ" =>
  Scheme.fromSpecStalk (Spec (CommRingCat.of L)) (genericPoint (Spec (CommRingCat.of L)))

/-- The original fraction field carries the canonical local algebra action. -/
@[instance_reducible] def localizedFractionAlgebra : Algebra L F :=
  (Localization.mapToFractionRing F q.asIdeal.primeCompl L
    q.asIdeal.primeCompl_le_nonZeroDivisors).toRingHom.toAlgebra

local instance : Algebra L F := localizedFractionAlgebra A F q

local instance : IsScalarTower A L F :=
  IsScalarTower.of_algebraMap_eq'
    (Localization.mapToFractionRing F q.asIdeal.primeCompl L
      q.asIdeal.primeCompl_le_nonZeroDivisors).comp_algebraMap.symm

local instance : IsFractionRing L F :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    q.asIdeal.primeCompl L F

local instance : Algebra L (Spec (CommRingCat.of L)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of L)

local instance : IsFractionRing L (Spec (CommRingCat.of L)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of L)

/-- The native function field of the local spectrum is the original field. -/
def localizedFunctionFieldEquiv : (Spec (CommRingCat.of L)).functionField ≃ₐ[L] F :=
  IsLocalization.algEquiv (nonZeroDivisors L) _ F

/-- The actual spectrum isomorphism, with contravariant orientation. -/
def localizedGenericSpectrumIso : Spec (CommRingCat.of F) ≅
    Spec (Spec (CommRingCat.of L)).functionField :=
  Scheme.Spec.mapIso (localizedFunctionFieldEquiv A F q).toRingEquiv.toCommRingCatIso.op

/-- The canonical field identification respects the original local generic map. -/
@[reassoc] theorem localizedGenericSpectrumIso_hom_generic :
    (localizedGenericSpectrumIso A F q).hom ≫ γ = Spec.algebraMap L F := by
  rw [Spec.fromSpecStalk_eq']
  change Spec.map (CommRingCat.ofHom (localizedFunctionFieldEquiv A F q).toRingHom) ≫
    Spec.algebraMap L (Spec (CommRingCat.of L)).functionField = _
  exact Spec.map_algHom_algebraMap (localizedFunctionFieldEquiv A F q).toAlgHom

/-- The same original ambient fraction-field map factors through the local base. -/
@[reassoc] theorem localizedFraction_base_triangle :
    Spec.algebraMap L F ≫ Spec.algebraMap A L = Spec.algebraMap A F :=
  Spec.map_algHom_algebraMap (Localization.mapToFractionRing F q.asIdeal.primeCompl L
    q.asIdeal.primeCompl_le_nonZeroDivisors)

variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))

local notation "l" => Spec.algebraMap A L
local notation "pq" => pullback.snd p l

/-- The original generic fibre is the native generic fibre after localization,
using only canonical pullback composition and the original field isomorphism. -/
def localizedGenericFiberIso : pullback p (Spec.algebraMap A F) ≅ pullback pq γ :=
  pullback.congrHom rfl (localizedFraction_base_triangle A F q).symm ≪≫
    (pullbackLeftPullbackSndIso p l (Spec.algebraMap L F)).symm ≪≫
    asIso (pullback.map pq (Spec.algebraMap L F) pq γ
      (𝟙 _) (localizedGenericSpectrumIso A F q).hom (𝟙 _)
      (by simp) (by simpa using (localizedGenericSpectrumIso_hom_generic A F q).symm))

/-- The original scheme projection is unchanged. -/
@[reassoc] theorem localizedGenericFiberIso_hom_fst :
    (localizedGenericFiberIso A F q p).hom ≫ pullback.fst pq γ ≫ pullback.fst p l =
      pullback.fst p (Spec.algebraMap A F) := by
  simp only [localizedGenericFiberIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, pullback.congrHom_hom, pullback.map, Category.comp_id]
  erw [pullback.lift_fst_assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.lift_fst]

/-- The coefficient projection uses exactly the canonical original field map. -/
@[reassoc] theorem localizedGenericFiberIso_hom_snd :
    (localizedGenericFiberIso A F q p).hom ≫ pullback.snd pq γ =
      pullback.snd p (Spec.algebraMap A F) ≫ (localizedGenericSpectrumIso A F q).hom := by
  simp only [localizedGenericFiberIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, pullback.congrHom_hom, pullback.map, Category.comp_id]
  erw [pullback.lift_snd, pullbackLeftPullbackSndIso_inv_snd_snd_assoc,
    pullback.lift_snd_assoc]

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
