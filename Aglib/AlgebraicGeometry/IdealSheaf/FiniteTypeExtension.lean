/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteType
public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Global

/-!
# Finite-type ideal extension inside a specified ambient ideal

On a qcqs scheme, a finite-type ideal on a compact open extends to a finite-type
ideal inside any prescribed ambient ideal restricting above it. Schematic closure
is used only to construct a quasicoherent ambient ideal with the exact restriction;
it is not asserted to be finite type. Actual finite-type module approximation and
its inclusion map supply the smaller, finitely generated image ideal.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Open restriction preserves intersections. This is not a claim about arbitrary,
possibly nonflat inverse images of ideals. -/
theorem comap_inf_of_isOpenImmersion {U X : Scheme.{u}}
    (I J : X.IdealSheafData) (j : U ⟶ X) [IsOpenImmersion j] :
    (I ⊓ J).comap j = I.comap j ⊓ J.comap j := by
  ext V
  simp only [ideal_comap_of_isOpenImmersion, ideal_inf, Pi.inf_apply, Ideal.comap_inf]

/-- Finite generation of the native restricted ideal gives finite-type
quasicoherence of the actual restricted ideal module. -/
theorem affineLocallyFiniteType_restrict_idealModule
    {U X : Scheme.{u}} (I : X.IdealSheafData)
    (j : U ⟶ X) [IsOpenImmersion j] (hI : (I.comap j).AffineLocallyFG) :
    affineLocallyFiniteType U ((idealModule I.subschemeι).restrict j) := by
  let := I.idealModule_isQuasicoherent
  let ψ : (idealModule I.subschemeι).restrict j ⟶
      SheafOfModules.unit U.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor j).map (idealInclusion I.subschemeι) ≫ (restrictUnitIso j).hom
  have himage : imageIdealData ψ = I.comap j := by
    rw [imageIdealData_restrict, imageIdealData_idealInclusion, I.ker_subschemeι]
  let hlocal := imageIdealLocalizes_of_isQuasicoherent ψ
  let : IsIso (zeroIdealFactor ψ hlocal) := zeroIdealFactor_isIso ψ hlocal
  have htarget : affineLocallyFiniteType U (idealModule (zeroInclusion ψ)) := by
    change affineLocallyFiniteType U (idealModule (imageIdealData ψ).subschemeι)
    rw [himage]
    exact (affineLocallyFG_iff_affineLocallyFiniteType _).mp hI
  exact (affineLocallyFiniteType U).prop_of_iso (asIso (zeroIdealFactor ψ hlocal)).symm
    htarget

/-- A finite-type ideal on a compact open of a qcqs scheme extends inside its
specified ambient ideal, with literal equality of the original restricted ideals. -/
theorem exists_affineLocallyFG_extension_le
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (I : X.IdealSheafData) (K : U.toScheme.IdealSheafData)
    (hK : K.AffineLocallyFG) (hKI : K ≤ I.comap U.ι) :
    ∃ J : X.IdealSheafData, J ≤ I ∧ J.AffineLocallyFG ∧ J.comap U.ι = K := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let L := I ⊓ K.map U.ι
  have hL : L.comap U.ι = K := by
    dsimp only [L]
    rw [comap_inf_of_isOpenImmersion, comap_map_of_isOpenImmersion,
      inf_eq_right.mpr hKI]
  let := L.idealModule_isQuasicoherent
  have hLU : affineLocallyFiniteType U.toScheme ((idealModule L.subschemeι).restrict U.ι) :=
    affineLocallyFiniteType_restrict_idealModule L U.ι (by rw [hL]; exact hK)
  obtain ⟨N, s, hs, hsU⟩ := exists_finiteType_subsheaf_restrict_isIso_of_qcqs
    (idealModule L.subschemeι) U hU hLU
  let : Mono s := hs
  let : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s) := hsU
  let : N.obj.IsQuasicoherent :=
    quasicoherent_of_affineCharts N.obj (fun R j _ => (N.property R j).1)
  let φ := s ≫ idealInclusion L.subschemeι
  have hJL : imageIdealData φ ≤ L := by
    intro V a ha
    rw [imageIdealData_eq φ (imageIdealLocalizes_of_isQuasicoherent φ) V] at ha
    obtain ⟨n, rfl⟩ := ha
    have hmem : (φ.val.app (op V.val)) n ∈
        sectionImageIdeal (idealInclusion L.subschemeι) V.val :=
      ⟨s.val.app (op V.val) n, rfl⟩
    rw [sectionImageIdeal_idealInclusion, L.ker_subschemeι_app V] at hmem
    exact hmem
  refine ⟨imageIdealData φ, hJL.trans inf_le_left,
    imageIdealData_affineLocallyFG φ N.property, ?_⟩
  rw [← imageIdealData_restrict U.ι φ]
  change imageIdealData
    ((Scheme.Modules.restrictFunctor U.ι).map (s ≫ idealInclusion L.subschemeι) ≫
    (restrictUnitIso U.ι).hom) = K
  rw [Functor.map_comp, Category.assoc]
  have he := imageIdealData_precomp_iso (asIso ((Scheme.Modules.restrictFunctor U.ι).map s))
    ((Scheme.Modules.restrictFunctor U.ι).map (idealInclusion L.subschemeι) ≫
      (restrictUnitIso U.ι).hom)
  change imageIdealData ((Scheme.Modules.restrictFunctor U.ι).map s ≫
    (Scheme.Modules.restrictFunctor U.ι).map (idealInclusion L.subschemeι) ≫
      (restrictUnitIso U.ι).hom) =
      imageIdealData ((Scheme.Modules.restrictFunctor U.ι).map (idealInclusion L.subschemeι) ≫
        (restrictUnitIso U.ι).hom) at he
  rw [he, imageIdealData_restrict, imageIdealData_idealInclusion, L.ker_subschemeι, hL]

end AlgebraicGeometry.Scheme.IdealSheafData
