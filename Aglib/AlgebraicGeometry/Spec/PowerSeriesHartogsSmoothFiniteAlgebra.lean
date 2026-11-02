/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsSmoothFiniteAlgebraRecovery
public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsEtaleAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.Etale.AffinePointwiseFlatBaseChange

/-! # Actual power-series effectivity for the same finite normal algebra

The restricted morphism of the literal tensor algebra is the finite-etale
cover supplied to the existing effectivity construction. Its resulting
section-algebra etaleness is transferred through the proved canonical scalar
isomorphism, not assumed. Pointwise flat descent then concerns the actual
image of each specified tensor-product point. The Hartogs-open, zero-section,
and geometric membership inputs remain explicit until supplied by the
original relative-purity construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

variable (A B C R : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing R]
  [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
  [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
  [FaithfulSMul B C] [Module.Finite B C]
  [IsLocalRing R] [IsNoetherianRing R] (σ : Type) [Finite σ]
  [Algebra B (MvPowerSeries σ R)] [Module.Flat B (MvPowerSeries σ R)]

local notation "PS" => MvPowerSeries σ R
local notation "T" => PS ⊗[B] C
local notation "t" => Spec.algebraMap PS T

/-- The actual restricted same-tensor-algebra cover supplies the global-section
etaleness required by canonical Hartogs recovery. No intermediate etaleness
certificate is a hypothesis. -/
theorem powerSeriesHartogsSmoothFiniteTensor_etale
    (hdim : 2 ≤ ringKrullDim A)
    (U : (Spec (.of R)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of PS)).Opens)
    (hbase : Spec.algebraMap B PS ⁻¹ᵁ
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A) ≤ V)
    (hUV : Spec.map (CommRingCat.ofHom (MvPowerSeries.C : R →+* PS)) ⁻¹ᵁ U ≤ V)
    (hzero : Spec.map (CommRingCat.ofHom (constantCoeff : PS →+* R)) ⁻¹ᵁ V = U)
    [Etale (t ∣_ V)] (hmem : powerSeriesClosedFiberPoint σ R ∈ V) :
    (algebraMap PS T).Etale := by
  let : IsFinite t := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let D : FiniteEtale V.toScheme :=
    ⟨Over.mk (t ∣_ V), (show IsFinite (t ∣_ V) from inferInstance),
      (show Etale (t ∣_ V) from inferInstance)⟩
  have he : (affineScalarMap ((t ∣_ V) ≫ V.ι)).Etale :=
    (powerSeriesHartogsAmbientScalar_finite_etale_of_extendedMaximal_mem
      U hU V hUV hzero D hmem).2
  exact smoothFiniteTensor_etale_of_sectionScalar_etale A B C PS hdim V hbase he

/-- Actual pointwise descent back to the original finite algebra. The point
Q and its literal include-right image are retained; no point or comparison
is chosen by the theorem. -/
theorem powerSeriesHartogsSmoothFiniteTensor_etaleAt_image
    (hdim : 2 ≤ ringKrullDim A)
    (U : (Spec (.of R)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of PS)).Opens)
    (hbase : Spec.algebraMap B PS ⁻¹ᵁ
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A) ≤ V)
    (hUV : Spec.map (CommRingCat.ofHom (MvPowerSeries.C : R →+* PS)) ⁻¹ᵁ U ≤ V)
    (hzero : Spec.map (CommRingCat.ofHom (constantCoeff : PS →+* R)) ⁻¹ᵁ V = U)
    [Etale (t ∣_ V)] (hmem : powerSeriesClosedFiberPoint σ R ∈ V)
    (Q : Spec (.of T)) :
    (Spec.algebraMap B C).etaleAt
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[B] T).toRingHom) Q) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : Algebra.FinitePresentation B C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Etale t := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (powerSeriesHartogsSmoothFiniteTensor_etale A B C R σ hdim U hU V
      hbase hUV hzero hmem)
  exact Hom.specAlgebraMap_etaleAt_of_flat_baseChange B C PS Q
    (show (t).etaleAt Q from ⟨⊤, trivial, inferInstance⟩)

end AlgebraicGeometry.Scheme
