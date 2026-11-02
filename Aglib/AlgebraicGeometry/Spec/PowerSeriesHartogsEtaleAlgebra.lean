/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsAlgebraComparison
public import Aglib.AlgebraicGeometry.Spec.HartogsFiniteAlgebraEtaleDetection
public import Aglib.AlgebraicGeometry.Spec.PowerSeriesClosedFiberPoint

/-! # Etaleness of the original power-series Hartogs cover algebra

The actual tensor comparison supplies the detector's algebra equivalence.
A point in the original open above the coefficient closed point remains an
explicit input. The coefficient and ambient algebras are the original global
section rings; neither is replaced by a normalization or an auxiliary cover.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MvPowerSeries
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u
variable {σ : Type} [Finite σ] {A : Type u} [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]

local notation "B" => MvPowerSeries σ A
local notation "c" => Spec.map (CommRingCat.ofHom (C : A →+* B))
local notation "z" => Spec.map (CommRingCat.ofHom (constantCoeff : B →+* A))

/-- The original section algebra is etale over the coefficient ring, by
its constructed tensor comparison and the original closed-fibre stalk. -/
theorem powerSeriesHartogsSectionScalar_etale
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (q : Spec (.of B)) (hq : q ∈ V) (hqA : c q = IsLocalRing.closedPoint A) :
    (affineScalarMap ((powerSeriesHartogsSectionCover U V hzero D).obj.hom ≫ U.ι)).Etale := by
  have hflat : (C : A →+* B).Flat := by
    change (algebraMap A B).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact MvPowerSeries.flat_of_isNoetherian σ A
  let D₀ := powerSeriesHartogsSectionCover U V hzero D
  let := (C : A →+* B).toAlgebra
  let : Module A B := Algebra.toModule
  let : Module.Flat A B := hflat
  let := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
  have hV := powerSeriesAffineScalar_bijective_of_baseOpen_le U hU V hUV
  exact (RingHom.etale_algebraMap).mpr
    (etale_coefficient_of_hartogs_tensor_comparison A B Γ(D₀.obj.left, ⊤) V hV D
      (powerSeriesHartogsAlgebraComparison U hU V hUV hzero D) q hq hqA)

/-- The same original ambient global-section algebra is etale over the
power-series ring. Etaleness is transported through the actual B-algebra
comparison after the coefficient algebra has been proved etale. -/
theorem powerSeriesHartogsAmbientScalar_etale
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (q : Spec (.of B)) (hq : q ∈ V) (hqA : c q = IsLocalRing.closedPoint A) :
    (affineScalarMap (D.obj.hom ≫ V.ι)).Etale := by
  let D₀ := powerSeriesHartogsSectionCover U V hzero D
  let := (C : A →+* B).toAlgebra
  let : Module A B := Algebra.toModule
  let := (affineScalarMap (D₀.obj.hom ≫ U.ι)).toAlgebra
  let := (affineScalarMap (D.obj.hom ≫ V.ι)).toAlgebra
  let : Algebra.Etale A Γ(D₀.obj.left, ⊤) :=
    powerSeriesHartogsSectionScalar_etale U hU V hUV hzero D q hq hqA
  exact (RingHom.etale_algebraMap).mpr
    (Algebra.Etale.of_equiv (powerSeriesHartogsAlgebraComparison U hU V hUV hzero D))

/-- Finiteness and etaleness hold for the very same original ambient scalar
map. Its original cover-recovery square is retained independently below. -/
theorem powerSeriesHartogsAmbientScalar_finite_etale
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (q : Spec (.of B)) (hq : q ∈ V) (hqA : c q = IsLocalRing.closedPoint A) :
    (affineScalarMap (D.obj.hom ≫ V.ι)).Finite ∧
      (affineScalarMap (D.obj.hom ≫ V.ι)).Etale :=
  ⟨affineScalarMap_finite_of_hartogs_finiteFlat B V
      (powerSeriesAffineScalar_bijective_of_baseOpen_le U hU V hUV) D.obj.hom,
    powerSeriesHartogsAmbientScalar_etale U hU V hUV hzero D q hq hqA⟩

/-- The prescribed original mB point supplies the closed-fibre equation.
Its membership in the original open remains the explicit geometric input. -/
theorem powerSeriesHartogsAmbientScalar_finite_etale_of_extendedMaximal_mem
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of B)).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme)
    (hmem : powerSeriesClosedFiberPoint σ A ∈ V) :
    (affineScalarMap (D.obj.hom ≫ V.ι)).Finite ∧
      (affineScalarMap (D.obj.hom ≫ V.ι)).Etale :=
  powerSeriesHartogsAmbientScalar_finite_etale U hU V hUV hzero D
    (powerSeriesClosedFiberPoint σ A) hmem (powerSeriesClosedFiberPoint_image σ A)

end AlgebraicGeometry.Scheme
