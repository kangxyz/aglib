/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Normality
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Supported

/-!
# The original point-blowup derived unit from rationality at its centre

Rationality of the actual centre stalk kills H1 on its same ordinary local
blowup. The original Cartesian localization square identifies this with the
centre stalk of the original global R1. The actual away-centre restriction
kills every other stalk. The existing proper-birational surface theorem then
makes the original derived structure unit invertible.

The source dimension bound is explicit. No globally rational earlier base,
canonical frame, completion of the centre stalk or finiteness of that stalk
over an earlier base is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

open Cohomology

local instance pointBlowupStructureDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original centre H1 and the unchanged complement kill the original R1.
Only this intermediate lemma takes the actual local cohomology as input. -/
private theorem pointBlowup_firstHigherImage_isZero
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    [QuasiCompact B.map] [QuasiSeparated B.map]
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf
        (blowupDatum (affineCenter (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))).Y
        (SheafOfModules.unit
          (blowupDatum (affineCenter (X.presheaf.stalk x)
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))).Y.ringCatSheaf)) 1)) :
    IsZero (((pushforward B.map).rightDerived 1).obj
      (show B.Y.Modules from SheafOfModules.unit B.Y.ringCatSheaf)) := by
  let D := blowupDatum (affineCenter (X.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
  let a := BaseChange.map (X.fromSpecStalk x)
    (RegularPoint.pointCentre_comap_fromSpecStalk X x hx) B D
  let H := BaseChange.isPullback_of_flat (X.fromSpecStalk x)
    (Scheme.fromSpecStalk_flat X x)
    (RegularPoint.pointCentre_comap_fromSpecStalk X x hx) B D
  let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hdisjoint : Disjoint (U : Set X) ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact Set.disjoint_left.mpr fun y hy hy' => hy hy'
  have hU : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hdisjoint
  exact firstHigherImage_isZero_of_localStructureH1_of_isIso_complement
    B.map x hx a D.map H hU hH

/-- Rationality of the actual closed centre makes the SAME original global
point-blowup derived structure unit invertible. The actual source dimension
bound is retained, without any global rationality or canonical-frame premise. -/
theorem isIso_moduleDerivedPushforwardUnit_pointBlowup_of_rational_stalk
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hX : NormalStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (hNagata : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : letI : IsDomain (X.presheaf.stalk x) := (hX x).1;
      NormalModificationH1Vanishing (X.presheaf.stalk x))
    (hdB : topologicalKrullDim B.Y ≤ 2) :
    IsIso (moduleDerivedPushforwardUnit X B.map) := by
  let S := X.presheaf.stalk x
  let : IsDomain S := (hX x).1
  let : IsIntegrallyClosed S := (hX x).2
  let : IsNoetherianRing S := hNagata.isNoetherianRing
  let D := MaximalIdealBlowup.datum S
  let : IsIntegral D.Y := MaximalIdealBlowup.source_isIntegral S hd
  let : IsProper D.map := MaximalIdealBlowup.map_isProper S hd
  let : IsDominant D.map := MaximalIdealBlowup.map_isDominant S hd
  have hD : NormalStalks D.Y :=
    MaximalIdealBlowup.ordinary_normalStalks S hd hNagata hRat
  have hDff : IsIso (CommRingCat.ofHom (functionFieldMap D.map)) :=
    MaximalIdealBlowup.map_fieldMap_isIso S hd
  have hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf D.Y (SheafOfModules.unit D.Y.ringCatSheaf)) 1) :=
    hRat D.Y D.map hD hDff
  have hxne : x ≠ genericPoint X := by
    intro he
    have hf : IsField (X.presheaf.stalk x) := he.symm ▸ Field.toIsField X.functionField
    have hh := ringKrullDim_eq_zero_of_isField hf
    rw [hd] at hh
    norm_num at hh
  have hcentre := genericPoint_not_mem_pointCentre x hx hxne
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hcentre
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hcentre
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  have hff : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
    B.functionFieldMap_isIso hcentre
  have hR1 := pointBlowup_firstHigherImage_isZero x hx B hH
  exact isIso_moduleDerivedPushforwardUnit_of_surface_R1_isZero B.map hX hff hdB hR1

end AlgebraicGeometry.Scheme.RationalSingularities
