/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.OrdinaryStages
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.DerivedUnit
public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity

/-!
# Original derived structure units of the actual ordinary and normalization steps

The ordinary blowdown uses genuine centre rationality only above the original
supported point in dimension two. In the other cases its original morphism
is an isomorphism. The literal normalization arrow is also an isomorphism.
Actual affine acyclicity and the existing surface R1 theorem supply those
isomorphism cases; no cancellation through pushforward is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

local instance stepStructureDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

private theorem structureUnit_isIso_of_original_iso
    {Y X : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (g : Y ⟶ X) [IsIso g] (hX : NormalStalks X)
    (hdY : topologicalKrullDim Y ≤ 2) :
    IsIso (moduleDerivedPushforwardUnit X g) := by
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let : O.IsQuasicoherent := isQuasicoherent_unit Y
  exact isIso_moduleDerivedPushforwardUnit_of_surface_R1_isZero g hX
    (functionFieldMap_isIso_of_flat_preimmersion g) hdY
    (isZero_rightDerived_pushforward_succ g O 0)

/-- The SAME ordinary blowdown and literal normalization arrow have invertible
original derived structure units. Rationality is assumed only at the original
supported target stalk; no per-stage unit or arbitrary-centre rationality is an input. -/
theorem isIso_moduleDerivedPushforwardUnit_ordinaryDatum_and_normalizationMap
    {Z X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : Z ⟶ X} (c : NormalizedPointBlowupChain f) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (hU : IsIso (f ∣_ LocalModification.pointComplement x hx))
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hS : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hdS : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : RationalSingularities.NormalModificationH1Vanishing (X.presheaf.stalk x))
    (j : Fin c.length) :
    IsIso (moduleDerivedPushforwardUnit (c.stage j.castSucc) (c.ordinaryDatum j).map) ∧
      IsIso (moduleDerivedPushforwardUnit (c.ordinaryDatum j).Y (c.normalizationMap j)) := by
  let Xi := c.stage j.castSucc
  let fi := c.toBase j.castSucc
  let z := c.center j
  let B := c.ordinaryDatum j
  let ν := c.normalizationMap j
  obtain ⟨hXi, _, hfiD, _, _, hfiP, _, hNoeth, _, _,
    _, _, _, hff, _, _, _, _, hdXi⟩ :=
    c.localStage_geometry x hx hxη hU hdX hS j.castSucc
  let : IsIntegral Xi := hXi
  let : IsDominant fi := hfiD
  let : IsProper fi := hfiP
  let : IsLocallyNoetherian Xi := hNoeth
  let : IsIntegral (c.stage j.succ) := (c.«prefix» j.succ).isIntegral inferInstance
  have hXiN : NormalStalks Xi := (c.«prefix» j.castSucc).normalStalks hX
  have hz : IsClosed ({z} : Set Xi) := c.center_isClosed j
  have hzη : z ≠ genericPoint Xi := c.center_ne_genericPoint j
  let : IsIntegral B.Y := pointBlowup_isIntegral Xi z hz hzη
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  obtain ⟨⟨hBN, hν⟩, hiso⟩ :=
    c.ordinaryDatum_classification x hx hxη hU hX hdX hS hdS hRat j
  let : IsIso ν := hν
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdNext⟩ :=
    c.localStage_geometry x hx hxη hU hdX hS j.succ
  have hdB : topologicalKrullDim B.Y ≤ 2 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (asIso ν).hom.homeomorph.isHomeomorph).symm.le.trans
      hdNext
  have hBunit : IsIso (moduleDerivedPushforwardUnit Xi B.map) := by
    by_cases hover : fi z = x
    · by_cases hd : ringKrullDim (Xi.presheaf.stalk z) = 2
      · obtain ⟨hNagata, hRatz⟩ :=
          RationalSingularities.stalk_isNagata_and_normalModificationH1Vanishing_of_target_stalk
            fi hXiN hff x hS hdS hRat z hz hzη hover
        exact RationalSingularities.isIso_moduleDerivedPushforwardUnit_pointBlowup_of_rational_stalk
          Xi hXiN z hz B hNagata hd hRatz hdB
      · have hle : ringKrullDim (Xi.presheaf.stalk z) ≤ 2 :=
          (le_iSup (fun y : Xi => ringKrullDim (Xi.presheaf.stalk y)) z).trans
            ((topologicalKrullDim_eq_iSup_stalk Xi).symm.le.trans hdXi)
        have hlt : ringKrullDim (Xi.presheaf.stalk z) < 2 := lt_of_le_of_ne hle hd
        have hsmall : ringKrullDim (Xi.presheaf.stalk z) ≤ 1 :=
          (ENat.WithBot.lt_add_one_iff (m := 1)).mp (by
            convert hlt using 1
            norm_num)
        let : IsIso B.map := hiso (Or.inr hsmall)
        exact structureUnit_isIso_of_original_iso B.map hXiN hdB
    · let : IsIso B.map := hiso (Or.inl hover)
      exact structureUnit_isIso_of_original_iso B.map hXiN hdB
  exact ⟨hBunit, structureUnit_isIso_of_original_iso ν hBN hdNext⟩

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
