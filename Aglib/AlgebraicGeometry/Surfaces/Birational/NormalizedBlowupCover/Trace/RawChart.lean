/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.BirationalCharts
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FiniteType
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover.ChartSections
public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Aglib.RingTheory.Kaehler.PureDegreePTrace.IntegralClosure
public import Mathlib.LinearAlgebra.ExteriorPower.Basis


/-!
# The original finite-cover trace on raw chart forms

The actual normalized-cover chart retains its original eta field map,
coefficient and closure actions, generic exterior maps and integral trace.
The complete generic-value law uses the same supplied fraction fields,
prime degree and root presentation. The module-sheaf arrow and its section
coordinates belong to the importing affine owner, not this raw-chart family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Polynomial
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped nonZeroDivisors ModuleCat.Algebra

universe u vK vL


open AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.ChartSections
open AlgebraicGeometry.Scheme.FunctionField.BirationalCharts
open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.FiniteCoverTrace


section OriginalCharts

variable {Λ A B : CommRingCat.{u}} [IsDomain A] [IsDomain B] [Algebra A B]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type vL) [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [Algebra Λ A] [Algebra Λ K] [Algebra Λ L]
  [IsScalarTower Λ A K] [IsScalarTower Λ K L]
  (ρ : Λ ⟶ A) (hρ : ρ.hom = algebraMap Λ A)
  {X : Scheme.{u}} [IsIntegral X]
  (β : X ⟶ Spec A) [IsDominant β]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (s : Spec B ⟶ Spec A) [IsDominant s]
  (hs : s = Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (U : X.affineOpens) [Nonempty U.val]

local notation "Y" => Cover.normalization β hβ s
local notation "π" => Cover.pi β hβ s
local notation "R" => X.presheaf.obj (op (U : X.Opens))
local notation "Cₛ" => (Functor.obj
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace Y))))
  (op (Functor.obj (Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) (U : X.Opens))) : CommRingCat)
local notation "aX" => β ≫ Spec.map ρ
local notation "jR" => IsAffineOpen.fromSpec U.property
local notation "jC" => IsAffineOpen.fromSpec (IsAffineOpen.preimage U.property π)
local notation "αR" => Spec.preimage (jR ≫ aX)
local notation "αC" => Spec.preimage (jC ≫ (π ≫ aX))
local notation "κR" => chartFractionMap A K β hβ U
local notation "λR" => chartExtensionMap A K L β hβ U

local instance coverAffine : IsAffineHom π := coverPi_isAffineHom β hβ s

local instance originalBaseFromSpec_isOpenImmersion : IsOpenImmersion jR :=
  IsAffineOpen.isOpenImmersion_fromSpec U.property

local instance originalPreimageFromSpec_isOpenImmersion : IsOpenImmersion jC :=
  IsAffineOpen.isOpenImmersion_fromSpec (U.property.preimage π)

/-- The chart's actual generic source map, through the original eta and original eF.
No spectrum of the supplied L or of a literal integral closure is introduced. -/
def sourceFieldMap : Cₛ →+* L :=
  (affineFunctionFieldEquiv B L).toRingHom.comp
    ((coverChartFieldIso β hβ s U).hom.hom.comp
      ((Cover.eta β hβ s).appLE (π ⁻¹ᵁ U) ((Cover.genericMap β hβ s) ⁻¹ᵁ U) (by
        simp only [← Scheme.Hom.comp_preimage, Cover.eta_pi, le_refl])).hom)

/-- The original eta map is the ambient inclusion after the SAME N2 chart equivalence. -/
theorem sourceFieldMap_eq :
    letI := ((π).app U).hom.toAlgebra
    letI := (λR).toAlgebra
    sourceFieldMap L β hβ s U =
      (algebraMap (integralClosure R L) L).comp
        (normalizedChartSectionsEquiv K L β hβ s hs U U.property).toRingHom := by
  let := ((π).app U).hom.toAlgebra
  let := (λR).toAlgebra
  have hVal : algebraMap (integralClosure R L) L =
      (integralClosure R L).val.toRingHom := by
    rw [Subalgebra.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp,
      AlgHom.toRingHom_eq_coe]
  rw [hVal]
  dsimp only [sourceFieldMap]
  exact (normalizedChartSectionsEquiv_val_comp K L β hβ s hs U U.property).symm

include hρ in
private theorem coefficientFractionTower :
    letI := (αR).hom.toAlgebra
    letI := (κR).toAlgebra
    IsScalarTower Λ R K := by
  let := (αR).hom.toAlgebra
  let := (κR).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro z
  have hz := RingHom.congr_fun
    (chartFractionMap_coefficientBase A K β hβ ρ U U.property) z
  change κR (αR z) = algebraMap A K (ρ z) at hz
  have hρz : ρ z = algebraMap Λ A z := RingHom.congr_fun hρ z
  rw [hρz, ← IsScalarTower.algebraMap_apply Λ A K] at hz
  exact hz.symm

include hρ in
omit [Algebra A L] [IsScalarTower A K L] in
private theorem coefficientExtensionTower :
    letI := (αR).hom.toAlgebra
    letI := (κR).toAlgebra
    letI := (λR).toAlgebra
    IsScalarTower Λ R L := by
  let := (αR).hom.toAlgebra
  let := (κR).toAlgebra
  let := (λR).toAlgebra
  let := chartExtensionMap_isScalarTower A K L β hβ U
  let := coefficientFractionTower K ρ hρ β hβ U
  exact IsScalarTower.to₁₂₄ Λ R K L

omit [Algebra A B] [Algebra Λ A] [Nonempty U.val] in
private theorem coefficientSourceTower :
    letI := (αR).hom.toAlgebra
    letI := (αC).hom.toAlgebra
    letI := ((π).app U).hom.toAlgebra
    IsScalarTower Λ R Cₛ := by
  let := (αR).hom.toAlgebra
  let := (αC).hom.toAlgebra
  let := ((π).app U).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  rw [RingHom.algebraMap_toAlgebra (αC).hom,
    RingHom.algebraMap_toAlgebra ((π).app U).hom,
    RingHom.algebraMap_toAlgebra (αR).hom]
  simpa only [Category.assoc] using normalizedChart_coefficientBase β hβ s aX U U.property

private theorem closureSourceTower :
    letI := ((π).app U).hom.toAlgebra
    letI := (λR).toAlgebra
    let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
    letI := E.toRingHom.toAlgebra
    IsScalarTower R Cₛ (integralClosure R L) := by
  let := ((π).app U).hom.toAlgebra
  let := (λR).toAlgebra
  let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
  let := E.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun z => (E.commutes z).symm

include hρ in
private theorem closureCoefficientTower :
    letI := (αR).hom.toAlgebra
    letI := (αC).hom.toAlgebra
    letI := ((π).app U).hom.toAlgebra
    letI := (λR).toAlgebra
    letI := (κR).toAlgebra
    letI := coefficientExtensionTower K L ρ hρ β hβ U
    let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
    letI := E.toRingHom.toAlgebra
    IsScalarTower Λ Cₛ (integralClosure R L) := by
  let := (αR).hom.toAlgebra
  let := (αC).hom.toAlgebra
  let := ((π).app U).hom.toAlgebra
  let := (λR).toAlgebra
  let := (κR).toAlgebra
  let := coefficientExtensionTower K L ρ hρ β hβ U
  let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
  let := E.toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro z
  have hz := RingHom.congr_fun
    (normalizedChartSectionsEquiv_coefficientBase K L β hβ s hs aX U U.property) z
  have hz' : E (αC z) = algebraMap R (integralClosure R L) (αR z) := by
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, CommRingCat.Hom.hom,
      Category.assoc] using hz
  exact (IsScalarTower.algebraMap_apply Λ R (integralClosure R L) z).trans hz'.symm

private theorem sourceClosureFieldTower :
    letI := ((π).app U).hom.toAlgebra
    letI := (λR).toAlgebra
    let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
    letI := E.toRingHom.toAlgebra
    letI := (sourceFieldMap L β hβ s U).toAlgebra
    IsScalarTower Cₛ (integralClosure R L) L := by
  let := ((π).app U).hom.toAlgebra
  let := (λR).toAlgebra
  let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
  let := E.toRingHom.toAlgebra
  let := (sourceFieldMap L β hβ s U).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c =>
    RingHom.congr_fun (sourceFieldMap_eq K L β hβ s hs U) c

include K hρ hs in
private theorem sourceCoefficientFieldTower :
    letI := (αC).hom.toAlgebra
    letI := (sourceFieldMap L β hβ s U).toAlgebra
    IsScalarTower Λ Cₛ L := by
  let := (αC).hom.toAlgebra
  let := (sourceFieldMap L β hβ s U).toAlgebra
  let := (αR).hom.toAlgebra
  let := ((π).app U).hom.toAlgebra
  let := (κR).toAlgebra
  let := (λR).toAlgebra
  let := coefficientExtensionTower K L ρ hρ β hβ U
  let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
  let := E.toRingHom.toAlgebra
  let : IsScalarTower Λ Cₛ (integralClosure R L) :=
    closureCoefficientTower K L ρ hρ β hβ s hs U
  let : IsScalarTower Cₛ (integralClosure R L) L :=
    sourceClosureFieldTower K L β hβ s hs U
  let : IsScalarTower Λ (integralClosure R L) L :=
    Subalgebra.isScalarTower_mid (integralClosure R L)
  exact IsScalarTower.to₁₂₄ Λ Cₛ (integralClosure R L) L

include K hρ hs in
/-- The generic raw coordinate uses the actual eta field map, not a new generic model. -/
def sourceGenericMap (n : ℕ) :
    letI := (αC).hom.toAlgebra
    letI := (sourceFieldMap L β hβ s U).toAlgebra
    (⋀[Cₛ]^(n + 1) (KaehlerDifferential Λ Cₛ)) →ₗ[Cₛ]
      ⋀[L]^(n + 1) (KaehlerDifferential Λ L) := by
  let := (αC).hom.toAlgebra
  let := (sourceFieldMap L β hβ s U).toAlgebra
  let : IsScalarTower Λ Cₛ L := by
    exact sourceCoefficientFieldTower K L ρ hρ β hβ s hs U
  exact KaehlerDifferential.mapExterior Λ Cₛ L (n + 1)

include K hρ hs in
/-- The whole generic source function is its original exterior field map. -/
theorem sourceGenericMap_coe (n : ℕ) :
    letI := (αC).hom.toAlgebra
    letI := (sourceFieldMap L β hβ s U).toAlgebra
    letI : IsScalarTower Λ Cₛ L := by
      exact sourceCoefficientFieldTower K L ρ hρ β hβ s hs U
    (fun ω : ⋀[Cₛ]^(n + 1) (KaehlerDifferential Λ Cₛ) =>
      sourceGenericMap K L ρ hρ β hβ s hs U n ω) =
        (fun ω => KaehlerDifferential.mapExterior Λ Cₛ L (n + 1) ω) := by
  rfl

section TargetGeneric

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (β ≫ Spec.map ρ)]

include hρ in
/-- The original target bidual, mapped to its original fraction-field exterior module. -/
def targetGenericMap (n : ℕ) :
    letI := (αR).hom.toAlgebra
    letI := (κR).toAlgebra
    Module.Dual R (Module.Dual R (⋀[R]^(n + 1) (KaehlerDifferential Λ R))) →ₗ[R]
      ⋀[K]^(n + 1) (KaehlerDifferential Λ K) := by
  let := (αR).hom.toAlgebra
  let := (κR).toAlgebra
  let := chartFractionMap_isFractionRing A K β hβ U U.property
  let : IsScalarTower Λ R K := by
    exact coefficientFractionTower K ρ hρ β hβ U
  let : IsNoetherianRing R := Coherent.noetherian_affineChart R jR
  let : Module.Finite R (KaehlerDifferential Λ R) :=
    finite_kaehler_of_locallyOfFiniteType aX jR
  let : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
  let : Module.FinitePresentation R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) :=
    Module.finitePresentation_of_finite R _
  let := KaehlerDifferential.finiteExteriorAtFraction Λ R K n
  let := KaehlerDifferential.mapExterior_isLocalizedModule Λ R K R⁰ (n + 1)
  exact Module.Dual.doubleDualToFraction (K := K)
    (KaehlerDifferential.mapExterior Λ R K (n + 1))

include hρ in
/-- The whole target generic function is the original bidual localization map. -/
theorem targetGenericMap_coe (n : ℕ) :
    letI := (αR).hom.toAlgebra
    letI := (κR).toAlgebra
    letI := chartFractionMap_isFractionRing A K β hβ U U.property
    letI : IsScalarTower Λ R K := by
      exact coefficientFractionTower K ρ hρ β hβ U
    letI : IsNoetherianRing R := Coherent.noetherian_affineChart R jR
    letI : Module.Finite R (KaehlerDifferential Λ R) :=
      finite_kaehler_of_locallyOfFiniteType aX jR
    letI : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
    letI : Module.FinitePresentation R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) :=
      Module.finitePresentation_of_finite R _
    letI := KaehlerDifferential.finiteExteriorAtFraction Λ R K n
    letI := KaehlerDifferential.mapExterior_isLocalizedModule Λ R K R⁰ (n + 1)
    (fun z : Module.Dual R
        (Module.Dual R (⋀[R]^(n + 1) (KaehlerDifferential Λ R))) =>
      targetGenericMap K ρ hρ β hβ U n z) =
        (fun z => Module.Dual.doubleDualToFraction (K := K)
          (KaehlerDifferential.mapExterior Λ R K (n + 1)) z) := by
  rfl

end TargetGeneric

private theorem chartNormal (hNormal : NormalStalks X) : IsIntegrallyClosed R := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hNormal x).2
  exact X.isIntegrallyClosed_sections_of_isAffineOpen U U.property

section ChartFinite

variable [IsFinite (Cover.pi β hβ s)]

include hs in
private theorem closureFinite :
    letI := (λR).toAlgebra
    Module.Finite R (integralClosure R L) := by
  let := (λR).toAlgebra
  let := ((π).app U).hom.toAlgebra
  let : Module.Finite R Cₛ := (π).finite_app U U.property
  exact Module.Finite.equiv
    (normalizedChartSectionsEquiv K L β hβ s hs U U.property).toLinearEquiv

end ChartFinite

section Trace

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (β ≫ Spec.map ρ)]
  [IsFinite (Cover.pi β hβ s)] [IsPurelyInseparable K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] {a₀ : K}
  (hNormal : NormalStalks X) (n : ℕ)
  (hdegree : Module.finrank K L = p)
  (h : IsAdjoinRootMonic L ((Polynomial.X : K[X]) ^ p - Polynomial.C a₀))

include hρ hs hNormal hdegree h in
/-- The SAME forward exterior map to the literal closure, followed by the
original integral trace. Its source remains the actual normalization chart ring. -/
def rawChartTrace :
    letI := (αR).hom.toAlgebra
    letI := (αC).hom.toAlgebra
    letI := ((π).app U).hom.toAlgebra
    (⋀[Cₛ]^(n + 1) (KaehlerDifferential Λ Cₛ)) →ₗ[R]
      Module.Dual R (Module.Dual R (⋀[R]^(n + 1) (KaehlerDifferential Λ R))) := by
  let := (αR).hom.toAlgebra
  let := (αC).hom.toAlgebra
  let := ((π).app U).hom.toAlgebra
  let := (κR).toAlgebra
  let := (λR).toAlgebra
  let := chartFractionMap_isFractionRing A K β hβ U U.property
  let := chartExtensionMap_isScalarTower A K L β hβ U
  let : IsScalarTower Λ R K := by
    exact coefficientFractionTower K ρ hρ β hβ U
  let : IsScalarTower Λ R L := by
    exact coefficientExtensionTower K L ρ hρ β hβ U
  let : IsScalarTower Λ R Cₛ := by
    exact coefficientSourceTower ρ β hβ s U
  let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
  let := E.toRingHom.toAlgebra
  let : IsScalarTower R Cₛ (integralClosure R L) := by
    exact closureSourceTower K L β hβ s hs U
  let : IsScalarTower Λ Cₛ (integralClosure R L) := by
    exact closureCoefficientTower K L ρ hρ β hβ s hs U
  let : IsNoetherianRing R := Coherent.noetherian_affineChart R jR
  let : IsIntegrallyClosed R := by exact chartNormal U hNormal
  let : Module.Finite R (integralClosure R L) := by
    exact closureFinite K L β hβ s hs U
  let : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
    (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
  let : Module.Finite R (KaehlerDifferential Λ R) :=
    finite_kaehler_of_locallyOfFiniteType aX jR
  let : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
  exact (KaehlerDifferential.integralClosureRawTrace Λ R K L n hdegree h).comp
    ((KaehlerDifferential.mapExterior Λ Cₛ (integralClosure R L) (n + 1)).restrictScalars R)

include hρ hs hNormal hdegree h in
/-- The whole raw chart trace is its original native linear composite. -/
theorem rawChartTrace_eq :
    letI := (αR).hom.toAlgebra
    letI := (αC).hom.toAlgebra
    letI := ((π).app U).hom.toAlgebra
    letI := (κR).toAlgebra
    letI := (λR).toAlgebra
    letI := chartFractionMap_isFractionRing A K β hβ U U.property
    letI := chartExtensionMap_isScalarTower A K L β hβ U
    letI : IsScalarTower Λ R K := by
      exact coefficientFractionTower K ρ hρ β hβ U
    letI : IsScalarTower Λ R L := by
      exact coefficientExtensionTower K L ρ hρ β hβ U
    letI : IsScalarTower Λ R Cₛ := by
      exact coefficientSourceTower ρ β hβ s U
    let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
    letI := E.toRingHom.toAlgebra
    letI : IsScalarTower R Cₛ (integralClosure R L) := by
      exact closureSourceTower K L β hβ s hs U
    letI : IsScalarTower Λ Cₛ (integralClosure R L) := by
      exact closureCoefficientTower K L ρ hρ β hβ s hs U
    letI : IsNoetherianRing R := Coherent.noetherian_affineChart R jR
    letI : IsIntegrallyClosed R := by exact chartNormal U hNormal
    letI : Module.Finite R (integralClosure R L) := by
      exact closureFinite K L β hβ s hs U
    letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
      (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
    letI : Module.Finite R (KaehlerDifferential Λ R) :=
      finite_kaehler_of_locallyOfFiniteType aX jR
    letI : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
    rawChartTrace K L ρ hρ β hβ s hs U hNormal n hdegree h =
      (KaehlerDifferential.integralClosureRawTrace Λ R K L n hdegree h).comp
        ((KaehlerDifferential.mapExterior Λ Cₛ (integralClosure R L)
          (n + 1)).restrictScalars R) := by
  rfl

include hρ hs hNormal hdegree h in
/-- The whole raw chart trace function is its same original trace composite. -/
theorem rawChartTrace_coe :
    letI := (αR).hom.toAlgebra
    letI := (αC).hom.toAlgebra
    letI := ((π).app U).hom.toAlgebra
    letI := (κR).toAlgebra
    letI := (λR).toAlgebra
    letI := chartFractionMap_isFractionRing A K β hβ U U.property
    letI := chartExtensionMap_isScalarTower A K L β hβ U
    letI : IsScalarTower Λ R K := by
      exact coefficientFractionTower K ρ hρ β hβ U
    letI : IsScalarTower Λ R L := by
      exact coefficientExtensionTower K L ρ hρ β hβ U
    letI : IsScalarTower Λ R Cₛ := by
      exact coefficientSourceTower ρ β hβ s U
    let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
    letI := E.toRingHom.toAlgebra
    letI : IsScalarTower R Cₛ (integralClosure R L) := by
      exact closureSourceTower K L β hβ s hs U
    letI : IsScalarTower Λ Cₛ (integralClosure R L) := by
      exact closureCoefficientTower K L ρ hρ β hβ s hs U
    letI : IsNoetherianRing R := Coherent.noetherian_affineChart R jR
    letI : IsIntegrallyClosed R := by exact chartNormal U hNormal
    letI : Module.Finite R (integralClosure R L) := by
      exact closureFinite K L β hβ s hs U
    letI : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
      (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
    letI : Module.Finite R (KaehlerDifferential Λ R) :=
      finite_kaehler_of_locallyOfFiniteType aX jR
    letI : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
    (fun ω : ⋀[Cₛ]^(n + 1) (KaehlerDifferential Λ Cₛ) =>
      rawChartTrace K L ρ hρ β hβ s hs U hNormal n hdegree h ω) =
        (fun ω => KaehlerDifferential.integralClosureRawTrace Λ R K L n hdegree h
          (KaehlerDifferential.mapExterior Λ Cₛ (integralClosure R L) (n + 1) ω)) := by
  have hMap := rawChartTrace_eq K L ρ hρ β hβ s hs U hNormal n hdegree h
  have hFun := congrArg DFunLike.coe hMap
  simpa only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_def] using hFun

/-- Every raw chart form has the prescribed original field-trace value. -/
theorem rawChartTrace_generic :
    letI := (αR).hom.toAlgebra
    letI := (αC).hom.toAlgebra
    letI := ((π).app U).hom.toAlgebra
    letI := (κR).toAlgebra
    letI := (sourceFieldMap L β hβ s U).toAlgebra
    ∀ ω : ⋀[Cₛ]^(n + 1) (KaehlerDifferential Λ Cₛ),
      targetGenericMap K ρ hρ β hβ U n
        (rawChartTrace K L ρ hρ β hβ s hs U hNormal n hdegree h ω) =
      KaehlerDifferential.pureDegreePTraceExterior (Λ := Λ) h n
        (sourceGenericMap K L ρ hρ β hβ s hs U n ω) := by
  let := (αR).hom.toAlgebra
  let := (αC).hom.toAlgebra
  let := ((π).app U).hom.toAlgebra
  let := (κR).toAlgebra
  let := (λR).toAlgebra
  let := chartFractionMap_isFractionRing A K β hβ U U.property
  let := chartExtensionMap_isScalarTower A K L β hβ U
  let := coefficientFractionTower K ρ hρ β hβ U
  let := coefficientExtensionTower K L ρ hρ β hβ U
  let := coefficientSourceTower ρ β hβ s U
  let E := normalizedChartSectionsEquiv K L β hβ s hs U U.property
  let := E.toRingHom.toAlgebra
  let := closureSourceTower K L β hβ s hs U
  let := closureCoefficientTower K L ρ hρ β hβ s hs U
  let := (sourceFieldMap L β hβ s U).toAlgebra
  let := sourceClosureFieldTower K L β hβ s hs U
  let := sourceCoefficientFieldTower K L ρ hρ β hβ s hs U
  let : IsNoetherianRing R := Coherent.noetherian_affineChart R jR
  let : IsIntegrallyClosed R := chartNormal U hNormal
  let : Module.Finite R (integralClosure R L) := closureFinite K L β hβ s hs U
  let : FiniteDimensional K L := FiniteDimensional.of_finrank_pos
    (by rw [hdegree]; exact (Fact.out : p.Prime).pos)
  let : Module.Finite R (KaehlerDifferential Λ R) :=
    finite_kaehler_of_locallyOfFiniteType aX jR
  let : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
  let : Module.FinitePresentation R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) :=
    Module.finitePresentation_of_finite R _
  let := KaehlerDifferential.finiteExteriorAtFraction Λ R K n
  let := KaehlerDifferential.mapExterior_isLocalizedModule Λ R K R⁰ (n + 1)
  intro ω
  have hg := KaehlerDifferential.integralClosureRawTrace_generic Λ R K L n hdegree h
    (KaehlerDifferential.mapExterior Λ Cₛ (integralClosure R L) (n + 1) ω)
  refine (congrFun (targetGenericMap_coe K ρ hρ β hβ U n) _).trans ?_
  refine (congrArg
    (Module.Dual.doubleDualToFraction (K := K)
      (KaehlerDifferential.mapExterior Λ R K (n + 1)))
    (congrFun (rawChartTrace_coe K L ρ hρ β hβ s hs U hNormal n hdegree h) ω)).trans ?_
  refine Eq.trans ?_ (congrArg (KaehlerDifferential.pureDegreePTraceExterior (Λ := Λ) h n)
    (congrFun (sourceGenericMap_coe K L ρ hρ β hβ s hs U n) ω).symm)
  exact (hg.trans (KaehlerDifferential.integralClosureRawTraceAtFraction_apply
    Λ R K L h n
      (KaehlerDifferential.mapExterior Λ Cₛ (integralClosure R L) (n + 1) ω))).trans
        (congrArg (KaehlerDifferential.pureDegreePTraceExterior (Λ := Λ) h n)
          (KaehlerDifferential.mapExterior_tower_apply
            Λ Cₛ (integralClosure R L) L (n + 1) ω))

end Trace
end OriginalCharts

end AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.FiniteCoverTrace
