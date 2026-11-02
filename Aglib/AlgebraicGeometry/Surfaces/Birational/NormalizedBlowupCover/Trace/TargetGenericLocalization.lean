/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.BirationalCharts
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover.Trace.RawChart
public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Aglib.RingTheory.Kaehler.PureDegreePTrace.Localization


/-!
# Original target generic coordinates under chart localization

The complete original bidual output is compared over the same fraction field.
No normalization cover, extension field or trace presentation is used.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped nonZeroDivisors ModuleCat.Algebra

universe u vK


open AlgebraicGeometry.Scheme.FunctionField.BirationalCharts
open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.FiniteCoverTrace


variable {A : CommRingCat.{u}} [IsDomain A]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} [IsIntegral X]
  (β : X ⟶ Spec A) [IsDominant β]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (U V : X.affineOpens) [Nonempty U.val] [Nonempty V.val] (hVU : V.val ≤ U.val)
  {Λ : CommRingCat.{u}} [Algebra Λ A] [Algebra Λ K] [IsScalarTower Λ A K]
  (ρ : Λ ⟶ A) (hρ : ρ.hom = algebraMap Λ A)

local notation "R" => X.presheaf.obj (op (U : X.Opens))
local notation "D" => X.presheaf.obj (op (V : X.Opens))
local notation "aX" => β ≫ Spec.map ρ
local notation "αR" => Spec.preimage (IsAffineOpen.fromSpec U.property ≫ aX)
local notation "αD" => Spec.preimage (IsAffineOpen.fromSpec V.property ≫ aX)
local notation "κR" => chartFractionMap A K β hβ U
local notation "κD" => chartFractionMap A K β hβ V

omit [IsDomain A] [IsIntegral X] [IsDominant β]
  [Nonempty U.val] [Nonempty V.val] [Algebra Λ A] in
/-- Actual base-chart restriction preserves the original coefficient map. -/
theorem baseRestrictionCoefficient :
    αD = αR ≫ X.presheaf.map (homOfLE hVU).op := by
  rw [← U.property.map_fromSpec V.property (homOfLE hVU).op,
    Category.assoc, Spec.preimage_comp, Spec.preimage_map]

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (β ≫ Spec.map ρ)]

/-- The original target generic coordinate is injective on the entire chart bidual. -/
theorem targetGenericMap_injective (n : ℕ) :
    letI := (αR).hom.toAlgebra
    letI := (κR).toAlgebra
    Function.Injective (targetGenericMap K ρ hρ β hβ U n) := by
  let := (αR).hom.toAlgebra
  let := (κR).toAlgebra
  let : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  let := chartFractionMap_isFractionRing A K β hβ U U.property
  let : IsScalarTower Λ R K := IsScalarTower.of_algebraMap_eq' (by
    have hc := chartFractionMap_coefficientBase A K β hβ ρ U U.property
    rw [hρ, ← IsScalarTower.algebraMap_eq Λ A K] at hc
    exact hc.symm)
  let : IsNoetherianRing R := Coherent.noetherian_affineChart R U.property.fromSpec
  let : Module.Finite R (KaehlerDifferential Λ R) :=
    finite_kaehler_of_locallyOfFiniteType aX U.property.fromSpec
  let : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
  let : Module.FinitePresentation R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) :=
    Module.finitePresentation_of_finite R _
  let := KaehlerDifferential.finiteExteriorAtFraction Λ R K n
  let := KaehlerDifferential.mapExterior_isLocalizedModule Λ R K R⁰ (n + 1)
  intro x y hxy
  apply Module.Dual.doubleDualToFraction_injective (K := K)
    (KaehlerDifferential.mapExterior Λ R K (n + 1))
  exact (congrFun (targetGenericMap_coe K ρ hρ β hβ U n) x).symm.trans
    (hxy.trans (congrFun (targetGenericMap_coe K ρ hρ β hβ U n) y))

/-- Every original bidual value retains its original generic coordinate under
localization of the actual base-section restriction. -/
theorem targetGenericMap_localization (n : ℕ) (S : Submonoid R) :
    letI := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    ∀ [_localization : IsLocalization S D],
    letI := (αR).hom.toAlgebra
    letI := (αD).hom.toAlgebra
    letI : IsScalarTower Λ R D := IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (baseRestrictionCoefficient β U V hVU ρ))
    letI : IsOpenImmersion U.property.fromSpec :=
      IsAffineOpen.isOpenImmersion_fromSpec U.property
    letI : IsNoetherianRing R := Coherent.noetherian_affineChart R U.property.fromSpec
    letI : Module.Finite R (KaehlerDifferential Λ R) :=
      finite_kaehler_of_locallyOfFiniteType aX U.property.fromSpec
    letI : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
    letI := (κR).toAlgebra
    letI := (κD).toAlgebra
    ∀ z : Module.Dual R (Module.Dual R (⋀[R]^(n + 1) (KaehlerDifferential Λ R))),
      targetGenericMap K ρ hρ β hβ V n
        (KaehlerDifferential.mapExteriorBidualLocalization Λ R D S (n + 1) z) =
      targetGenericMap K ρ hρ β hβ U n z := by
  let := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  intro hLocalization
  let := (αR).hom.toAlgebra
  let := (αD).hom.toAlgebra
  let : IsScalarTower Λ R D := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (baseRestrictionCoefficient β U V hVU ρ))
  let : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  let : IsOpenImmersion V.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec V.property
  let : IsNoetherianRing R := Coherent.noetherian_affineChart R U.property.fromSpec
  let : IsNoetherianRing D := Coherent.noetherian_affineChart D V.property.fromSpec
  let : Module.Finite R (KaehlerDifferential Λ R) :=
    finite_kaehler_of_locallyOfFiniteType aX U.property.fromSpec
  let : Module.Finite D (KaehlerDifferential Λ D) :=
    finite_kaehler_of_locallyOfFiniteType aX V.property.fromSpec
  let : Module.Finite R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) := inferInstance
  let : Module.Finite D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) := inferInstance
  let := (κR).toAlgebra
  let := (κD).toAlgebra
  let := chartFractionMap_isFractionRing A K β hβ U U.property
  let := chartFractionMap_isFractionRing A K β hβ V V.property
  let : IsScalarTower Λ R K := IsScalarTower.of_algebraMap_eq' (by
    have hc := chartFractionMap_coefficientBase A K β hβ ρ U U.property
    rw [hρ, ← IsScalarTower.algebraMap_eq Λ A K] at hc
    exact hc.symm)
  let : IsScalarTower Λ D K := IsScalarTower.of_algebraMap_eq' (by
    have hc := chartFractionMap_coefficientBase A K β hβ ρ V V.property
    rw [hρ, ← IsScalarTower.algebraMap_eq Λ A K] at hc
    exact hc.symm)
  let : IsScalarTower R D K := IsScalarTower.of_algebraMap_eq' (by
    exact (chartFractionMap_restriction A K β hβ U V hVU).symm)
  let : Module.FinitePresentation R (⋀[R]^(n + 1) (KaehlerDifferential Λ R)) :=
    Module.finitePresentation_of_finite R _
  let : Module.FinitePresentation D (⋀[D]^(n + 1) (KaehlerDifferential Λ D)) :=
    Module.finitePresentation_of_finite D _
  let := KaehlerDifferential.mapExterior_isLocalizedModule Λ R K R⁰ (n + 1)
  let := KaehlerDifferential.mapExterior_isLocalizedModule Λ D K D⁰ (n + 1)
  let := KaehlerDifferential.finiteExteriorAtFraction Λ R K n
  intro z
  have hb := LinearMap.congr_fun
    (KaehlerDifferential.mapExteriorBidualLocalization_generic Λ R D K S n) z
  exact (congrFun (targetGenericMap_coe K ρ hρ β hβ V n) _).trans
    (hb.trans (congrFun (targetGenericMap_coe K ρ hρ β hβ U n) z).symm)

end AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.FiniteCoverTrace
