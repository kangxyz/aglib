/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsEtaleAlgebra

/-! # The original finite-etale Hartogs extension and its recovery

The extension is literally Spec of the original cover's global section ring.
Its restriction is recovered by the previously proved original affinization
square. The power-series specialization supplies etaleness through the actual
comparison and the prescribed extended-maximal-ideal point. This is not a
general depth-only effectivity or global relative-purity statement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u

/-- The original section algebra, with its original structural scalar map,
viewed as a finite-etale cover after that same map is proved etale. -/
def originalHartogsFiniteEtaleExtension
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (V : (Spec (.of B)).Opens) (hV : Function.Bijective (affineScalarMap V.ι))
    (D : FiniteEtale V.toScheme) (he : (affineScalarMap (D.obj.hom ≫ V.ι)).Etale) :
    FiniteEtale (Spec (.of B)) :=
  ⟨Over.mk (Spec.map (CommRingCat.ofHom (affineScalarMap (D.obj.hom ≫ V.ι)))),
    (IsFinite.SpecMap_iff _).mpr
      (affineScalarMap_finite_of_hartogs_finiteFlat B V hV D.obj.hom),
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he⟩

/-- The actual original affinization square gives the actual cover-category
recovery isomorphism, without a different affine realization. -/
def originalHartogsFiniteEtaleExtensionRecovery
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (V : (Spec (.of B)).Opens) (hV : Function.Bijective (affineScalarMap V.ι))
    (D : FiniteEtale V.toScheme) (he : (affineScalarMap (D.obj.hom ≫ V.ι)).Etale) :
    D ≅ (FiniteEtale.baseChange V.ι).obj
      (originalHartogsFiniteEtaleExtension B V hV D he) :=
  ObjectProperty.isoMk _ (Over.isoMk
    (isPullback_hartogs_finiteAlgebra B V hV D.obj.hom).flip.isoPullback
    (isPullback_hartogs_finiteAlgebra B V hV D.obj.hom).flip.isoPullback_hom_snd)

/-- The forward recovery map retains the original affinization projection. -/
theorem originalHartogsFiniteEtaleExtension_recovery_hom_fst
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (V : (Spec (.of B)).Opens) (hV : Function.Bijective (affineScalarMap V.ι))
    (D : FiniteEtale V.toScheme) (he : (affineScalarMap (D.obj.hom ≫ V.ι)).Etale) :
    (originalHartogsFiniteEtaleExtensionRecovery B V hV D he).hom.hom.left ≫
      pullback.fst (originalHartogsFiniteEtaleExtension B V hV D he).obj.hom V.ι =
        D.obj.left.toSpecΓ :=
  (isPullback_hartogs_finiteAlgebra B V hV D.obj.hom).flip.isoPullback_hom_fst

/-- The inverse recovery map has precisely the original first projection. -/
theorem originalHartogsFiniteEtaleExtension_recovery_inv_affinization
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (V : (Spec (.of B)).Opens) (hV : Function.Bijective (affineScalarMap V.ι))
    (D : FiniteEtale V.toScheme) (he : (affineScalarMap (D.obj.hom ≫ V.ι)).Etale) :
    (originalHartogsFiniteEtaleExtensionRecovery B V hV D he).inv.hom.left ≫
        D.obj.left.toSpecΓ =
      pullback.fst (originalHartogsFiniteEtaleExtension B V hV D he).obj.hom V.ι :=
  (isPullback_hartogs_finiteAlgebra B V hV D.obj.hom).flip.isoPullback_inv_fst

variable {σ : Type} [Finite σ] {A : Type u} [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]

local notation "B" => MvPowerSeries σ A
local notation "c" => Spec.map (CommRingCat.ofHom (C : A →+* B))
local notation "z" => Spec.map (CommRingCat.ofHom (constantCoeff : B →+* A))

/-- The actual extension under the explicit Hartogs and mB hypotheses. -/
def powerSeriesHartogsCoverExtension
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (hmem : powerSeriesClosedFiberPoint σ A ∈ V) : FiniteEtale (Spec (.of B)) :=
  originalHartogsFiniteEtaleExtension B V
    (powerSeriesAffineScalar_bijective_of_baseOpen_le U hU V hUV) D
    (powerSeriesHartogsAmbientScalar_finite_etale_of_extendedMaximal_mem
      U hU V hUV hzero D hmem).2

/-- Restricting the same actual extension recovers the original cover. -/
def powerSeriesHartogsCoverExtensionRecovery
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (hmem : powerSeriesClosedFiberPoint σ A ∈ V) :
    D ≅ (FiniteEtale.baseChange V.ι).obj
      (powerSeriesHartogsCoverExtension U hU V hUV hzero D hmem) :=
  originalHartogsFiniteEtaleExtensionRecovery B V
    (powerSeriesAffineScalar_bijective_of_baseOpen_le U hU V hUV) D
    (powerSeriesHartogsAmbientScalar_finite_etale_of_extendedMaximal_mem
      U hU V hUV hzero D hmem).2

end AlgebraicGeometry.Scheme
