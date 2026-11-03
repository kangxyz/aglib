/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.CompleteIntermediateField
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover.Nagata
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AdaptedCharts
public import Aglib.AlgebraicGeometry.FunctionField.AffineCompatibility
public import Aglib.AlgebraicGeometry.Normalization.Relative
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The actual normalized cover of an intermediate-field model

The intermediate ring is the literal integral closure, and its map to the
original upper ring is the native integral-closure lift. A supplied birational
model of that intermediate ring is used through the existing normalized Cover.
The original generic maps identify its actual degree and its normalization of
the original generic component in the literal pullback.

Complete-local surface hypotheses prove Nagata on actual model charts and hence
finiteness of the same normalization. No resolution of the original upper ring,
completed-domain conclusion, smaller-degree premise or normalized point chain
is supplied or asserted here. Regularity of the supplied intermediate model is
needed by the later completed-branch consumer, not by this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.IntermediateFieldModel

universe u

/-- The canonical coefficient algebra on the function field of the original affine spectrum. -/
local instance originalSpecFieldAlgebra (C : Type u) [CommRing C] [IsDomain C] :
    Algebra C (Spec (.of C)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of C)

local instance originalSpecFractionRing (C : Type u) [CommRing C] [IsDomain C] :
    IsFractionRing C (Spec (.of C)).functionField :=
  functionField_isFractionRing_of_affine (.of C)

/-- The native fraction identification of the original upper affine scheme. -/
def originalFieldEquiv (A : Type u) [CommRing A] [IsDomain A] :
    (Spec (.of A)).functionField ≃ₐ[A] FractionRing A :=
  (FractionRing.algEquiv A (Spec (.of A)).functionField).symm

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]

attribute [local instance] FractionRing.liftAlgebra

variable (L : IntermediateField (FractionRing R) (FractionRing A))

local notation "B" => integralClosure R L

/-- The native fraction identification uses the actual intermediate field. -/
def intermediateFieldEquiv : (Spec (.of B)).functionField ≃ₐ[B] L := by
  let : IsFractionRing B L := integralClosure.completeIntermediate_fractionRing R A L
  exact IsLocalization.algEquiv (nonZeroDivisors B) _ _

variable [IsIntegrallyClosed A]

/-- The original affine base map is induced by the actual intermediate lift. -/
def baseMap : Spec (.of A) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (integralClosure.intermediateToOriginal R A L).toRingHom)

instance baseMap_isDominant : IsDominant (baseMap R A L) :=
  specMap_isDominant_of_injective _ (integralClosure.intermediateToOriginal_injective R A L)

instance baseMap_isFinite : IsFinite (baseMap R A L) := by
  apply specMap_isFinite
  exact integralClosure.intermediateToOriginal_finite R A L

/-- The original generic-stalk map agrees with the literal intermediate field
inclusion, through the native fraction identifications of the same rings. -/
theorem baseMap_field_square :
    (algebraMap L (FractionRing A)).comp (intermediateFieldEquiv R A L).toRingHom =
      (originalFieldEquiv A).toRingHom.comp (functionFieldMap (baseMap R A L)) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors B)
  apply RingHom.ext
  intro b
  change algebraMap L (FractionRing A)
      (intermediateFieldEquiv R A L (algebraMap B (Spec (.of B)).functionField b)) =
    originalFieldEquiv A
      (functionFieldMap (baseMap R A L) (algebraMap B (Spec (.of B)).functionField b))
  rw [(intermediateFieldEquiv R A L).commutes]
  let : IsDominant
      (Spec.map (CommRingCat.ofHom (integralClosure.intermediateToOriginal R A L).toRingHom)) :=
    baseMap_isDominant R A L
  have hs := RingHom.congr_fun
    (FunctionField.AffineCompatibility.fieldMap_spec_constants (.of A) (.of B)
      (CommRingCat.ofHom (integralClosure.intermediateToOriginal R A L).toRingHom)) b
  change functionFieldMap (baseMap R A L) (algebraMap B (Spec (.of B)).functionField b) =
    algebraMap A (Spec (.of A)).functionField
      (integralClosure.intermediateToOriginal R A L b) at hs
  rw [hs, (originalFieldEquiv A).commutes]
  exact (integralClosure.intermediateToOriginal_fraction R A L b).symm

/-- Finiteness is for the original affine generic-stalk map, not a chosen
function-field embedding supplied as an additional hypothesis. -/
theorem baseMap_field_finite : (functionFieldMap (baseMap R A L)).Finite := by
  let := functionFieldMapAlgebra (baseMap R A L)
  let : FiniteDimensional (FractionRing R) (FractionRing A) :=
    integralClosure.completeIntermediate_fieldFinite R A
  let : FiniteDimensional L (FractionRing A) := IntermediateField.finiteDimensional_right L
  let eB := intermediateFieldEquiv R A L
  let eA := originalFieldEquiv A
  apply Module.Finite.of_equiv_equiv eB.symm.toRingEquiv eA.symm.toRingEquiv
  apply RingHom.ext
  intro l
  apply eA.injective
  change eA (functionFieldMap (baseMap R A L) (eB.symm l)) =
    eA (eA.symm (algebraMap L (FractionRing A) l))
  rw [AlgEquiv.apply_symm_apply]
  have h := RingHom.congr_fun (baseMap_field_square R A L) (eB.symm l)
  change algebraMap L (FractionRing A) (eB (eB.symm l)) =
    eA (functionFieldMap (baseMap R A L) (eB.symm l)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The degree of the original affine generic map is exactly the actual
intermediate extension degree. -/
theorem baseMap_field_finrank :
    letI := functionFieldMapAlgebra (baseMap R A L)
    Module.finrank (Spec (.of B)).functionField (Spec (.of A)).functionField =
      Module.finrank L (FractionRing A) := by
  let := functionFieldMapAlgebra (baseMap R A L)
  exact Algebra.finrank_eq_of_equiv_equiv
    (intermediateFieldEquiv R A L).toRingEquiv (originalFieldEquiv A).toRingEquiv
    (baseMap_field_square R A L)

variable {Y : Scheme.{u}} [IsIntegral Y]
  (a : Y ⟶ Spec (.of (integralClosure R L))) [IsDominant a]
  (ha : IsIso (CommRingCat.ofHom (functionFieldMap a)))

/-- Normality concerns the same existing Cover, with no separability input. -/
theorem normalization_normalStalks :
    NormalStalks (Cover.normalization a ha (baseMap R A L)) :=
  Cover.Nagata.normalization_normalStalks a ha (baseMap R A L) (baseMap_field_finite R A L)

/-- The actual finite-cover degree is exactly the original intermediate degree.
Both vertical identifications are the original birational function-field maps. -/
theorem pi_field_finrank :
    letI := functionFieldMapAlgebra (Cover.pi a ha (baseMap R A L))
    Module.finrank Y.functionField (Cover.normalization a ha (baseMap R A L)).functionField =
      Module.finrank L (FractionRing A) := by
  let := functionFieldMapAlgebra (baseMap R A L)
  let := functionFieldMapAlgebra (Cover.pi a ha (baseMap R A L))
  let := ha
  let := Cover.b_fieldMap_isIso a ha (baseMap R A L)
  let eB : (Spec (.of B)).functionField ≃+* Y.functionField :=
    (asIso (CommRingCat.ofHom (functionFieldMap a))).commRingCatIsoToRingEquiv
  let eA : (Spec (.of A)).functionField ≃+*
      (Cover.normalization a ha (baseMap R A L)).functionField :=
    (asIso (CommRingCat.ofHom
      (functionFieldMap (Cover.b a ha (baseMap R A L))))).commRingCatIsoToRingEquiv
  have hs : (algebraMap Y.functionField
      (Cover.normalization a ha (baseMap R A L)).functionField).comp eB.toRingHom =
      eA.toRingHom.comp (algebraMap (Spec (.of B)).functionField
        (Spec (.of A)).functionField) := by
    change (functionFieldMap (Cover.pi a ha (baseMap R A L))).comp (functionFieldMap a) =
      (functionFieldMap (Cover.b a ha (baseMap R A L))).comp
        (functionFieldMap (baseMap R A L))
    rw [← functionFieldMap_comp, ← functionFieldMap_comp]
    congr 1
    exact Cover.square a ha (baseMap R A L)
  exact (Algebra.finrank_eq_of_equiv_equiv eB eA hs).symm.trans
    (baseMap_field_finrank R A L)

/-- The original generic lift is quasi-compact by its actual finite projection. -/
instance genericLift_isQuasiCompact : QuasiCompact (Cover.genericLift a ha (baseMap R A L)) := by
  let : QuasiCompact
      (Cover.genericLift a ha (baseMap R A L) ≫ pullback.fst a (baseMap R A L)) := by
    simpa only [Cover.genericLift, pullback.lift_fst] using
      (inferInstance : QuasiCompact (Cover.genericMap a ha (baseMap R A L)))
  exact QuasiCompact.of_comp _ (pullback.fst a (baseMap R A L))

/-- The original generic lift is quasi-separated by its original composite. -/
instance genericLift_isQuasiSeparated :
    QuasiSeparated (Cover.genericLift a ha (baseMap R A L)) := by
  let : QuasiSeparated
      (Cover.genericLift a ha (baseMap R A L) ≫ pullback.fst a (baseMap R A L)) := by
    simpa only [Cover.genericLift, pullback.lift_fst] using
      (inferInstance : QuasiSeparated (Cover.genericMap a ha (baseMap R A L)))
  exact QuasiSeparated.of_comp _ (pullback.fst a (baseMap R A L))

/-- This is the normalization of the original dominating generic component in
its literal pullback, not a replacement cover or a selected resolution of A. -/
def pullbackNormalizationIso : Cover.normalization a ha (baseMap R A L) ≅
    (Cover.genericLift a ha (baseMap R A L)).normalization :=
  (Hom.normalizationSourceIso (Iso.refl _)
    (Cover.genericMap a ha (baseMap R A L))
    (Cover.genericLift a ha (baseMap R A L) ≫ pullback.fst a (baseMap R A L))
    (by simp only [Iso.refl_hom, Category.id_comp, Cover.genericLift, pullback.lift_fst])).trans
      (Hom.normalizationIntegralFactorIso (Cover.genericLift a ha (baseMap R A L))
        (pullback.fst a (baseMap R A L)))

/-- The comparison retains the original generic arrow, on the same original field. -/
@[reassoc]
theorem pullbackNormalizationIso_generic :
    Cover.eta a ha (baseMap R A L) ≫ (pullbackNormalizationIso R A L a ha).hom =
      (Cover.genericLift a ha (baseMap R A L)).toNormalization := by
  let f := Cover.genericMap a ha (baseMap R A L)
  let j := Cover.genericLift a ha (baseMap R A L)
  let g := pullback.fst a (baseMap R A L)
  have hg : j ≫ g = f := pullback.lift_fst _ _ _
  let e₀ := Hom.normalizationSourceIso (Iso.refl _) f (j ≫ g)
    ((Category.id_comp _).trans hg)
  let e₁ := Hom.normalizationIntegralFactorIso j g
  have h₀ : f.toNormalization ≫ e₀.hom = (j ≫ g).toNormalization :=
    (Hom.normalizationSourceIso_hom_generic (Iso.refl _) f (j ≫ g)
      ((Category.id_comp _).trans hg)).trans (Category.id_comp _)
  have h₁ : (j ≫ g).toNormalization ≫ e₁.hom = j.toNormalization :=
    (j ≫ g).toNormalization_normalizationDesc j.toNormalization
      (j.fromNormalization ≫ g) (by simp only [Hom.toNormalization_fromNormalization_assoc])
  have h := (Category.assoc f.toNormalization e₀.hom e₁.hom).symm.trans
    ((congrArg (fun k : Spec (Spec (.of A)).functionField ⟶ (j ≫ g).normalization =>
      k ≫ e₁.hom) h₀).trans h₁)
  exact h

/-- The comparison's projection is exactly the existing Cover.toPullback. -/
@[reassoc]
theorem pullbackNormalizationIso_over :
    (pullbackNormalizationIso R A L a ha).hom ≫
      (Cover.genericLift a ha (baseMap R A L)).fromNormalization =
        Cover.toPullback a ha (baseMap R A L) := by
  let f := Cover.genericMap a ha (baseMap R A L)
  let j := Cover.genericLift a ha (baseMap R A L)
  let g := pullback.fst a (baseMap R A L)
  have hg : j ≫ g = f := pullback.lift_fst _ _ _
  let e₀ := Hom.normalizationSourceIso (Iso.refl _) f (j ≫ g)
    ((Category.id_comp _).trans hg)
  let e₁ := Hom.normalizationIntegralFactorIso j g
  let d := f.normalizationDesc j g hg.symm
  have hgen : f.toNormalization ≫ (e₀.hom ≫ e₁.hom) = j.toNormalization :=
    pullbackNormalizationIso_generic R A L a ha
  have he : (e₀.hom ≫ e₁.hom) ≫ j.fromNormalization = d := by
    apply Hom.normalization.hom_ext f _ _ g
    · exact (Category.assoc f.toNormalization (e₀.hom ≫ e₁.hom) j.fromNormalization).symm.trans
        ((congrArg (fun k : Spec (Spec (.of A)).functionField ⟶ j.normalization =>
          k ≫ j.fromNormalization) hgen).trans
          ((j.toNormalization_fromNormalization).trans
            (f.toNormalization_normalizationDesc j g hg.symm).symm))
    · calc
        ((e₀.hom ≫ e₁.hom) ≫ j.fromNormalization) ≫ g =
            e₀.hom ≫ (e₁.hom ≫ j.fromNormalization ≫ g) := by
              simp only [Category.assoc]
        _ = e₀.hom ≫ (j ≫ g).fromNormalization :=
          congrArg (fun k : (j ≫ g).normalization ⟶ _ => e₀.hom ≫ k)
            (Hom.normalizationIntegralFactorIso_hom_over j g)
        _ = f.fromNormalization := Hom.normalizationSourceIso_hom_over (Iso.refl _) f
          (j ≫ g) ((Category.id_comp _).trans hg)
    · exact f.normalizationDesc_comp j g hg.symm
  exact he

section CompleteBase

variable [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] [Ring.KrullDimLE 2 R] [IsProper a]

include R A L a ha in
omit [IsIntegrallyClosed A] in
/-- Every actual nonempty affine chart of the supplied birational model is
Nagata and has dimension at most two, by the original adapted chart map. -/
theorem affineChart_nagata_and_dimension (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsNagataRing.{u, 0} Γ(Y, U) ∧ ringKrullDim Γ(Y, U) ≤ 2 := by
  let : Module.Finite R B := integralClosure.completeIntermediate_finite R A L
  have hB : IsNagataRing.{u, 0} B := (IsNagataRing.of_complete_local_dimLE_two R).of_finite
  let : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R L
  have hdB : ringKrullDim B ≤ 2 := by
    have hBR : ringKrullDim B ≤ ringKrullDim R := by
      apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R B))
      intro p q hpq
      exact Ideal.IsIntegral.under_lt_under (R := R) hpq
    exact hBR.trans (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R))
  have hbase : IsNagataRing.{u, 0} Γ(Spec (.of B), ⊤) := by
    let e : B ≃+* Γ(Spec (.of B), ⊤) :=
      (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv
    let : Algebra B Γ(Spec (.of B), ⊤) := e.toRingHom.toAlgebra
    let : Module.Finite B Γ(Spec (.of B), ⊤) :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    exact hB.of_finite
  have hdim : topologicalKrullDim (Spec (.of B)) ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum B) ≤ 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hdB
  let : Nonempty (⊤ : (Spec (.of B)).Opens) :=
    ⟨⟨genericPoint (Spec (.of B)), trivial⟩⟩
  exact NormalizedPointDomination.adaptedChart_nagata_and_dimension a ⊤ U le_top
    (isAffineOpen_top _) hU hbase hdim ha

/-- The existing Cover.pi is finite without a separability or chart-Nagata premise. -/
theorem pi_isFinite : IsFinite (Cover.pi a ha (baseMap R A L)) := by
  apply Cover.Nagata.pi_isFinite a ha (baseMap R A L) (baseMap_field_finite R A L)
  intro U hne
  let := hne
  exact (affineChart_nagata_and_dimension R A L a ha U.1 U.2).1

/-- Local Noetherianity belongs to the same actual normalized model. -/
theorem normalization_isLocallyNoetherian :
    IsLocallyNoetherian (Cover.normalization a ha (baseMap R A L)) := by
  let : IsNoetherianRing B := integralClosure.completeIntermediate_noetherian R A L
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian a
  let : IsFinite (Cover.pi a ha (baseMap R A L)) := pi_isFinite R A L a ha
  exact LocallyOfFiniteType.isLocallyNoetherian (Cover.pi a ha (baseMap R A L))

/-- The existing original map back to Spec A is proper and birational.
Its square and generic triangle are unchanged Cover.square and Cover.eta_b. -/
theorem b_proper_birational : IsProper (Cover.b a ha (baseMap R A L)) ∧
    IsIso (CommRingCat.ofHom (functionFieldMap (Cover.b a ha (baseMap R A L)))) := by
  let : IsFinite (Cover.pi a ha (baseMap R A L)) := pi_isFinite R A L a ha
  exact ⟨Cover.b_isProper a ha (baseMap R A L), Cover.b_fieldMap_isIso a ha (baseMap R A L)⟩

end CompleteBase

end AlgebraicGeometry.Scheme.IntermediateFieldModel
