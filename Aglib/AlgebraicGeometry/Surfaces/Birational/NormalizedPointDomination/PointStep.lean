/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.FiniteNormalization
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Proper normalized point steps over the original Nagata surface

Keep the actual accumulated proper birational map to the original base.
Finite normalization of the ordinary point blowup follows from adapted GF2
charts over that base. Thus each literal normalized point step is proper,
Noetherian and of dimension at most two, without a regularity assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

open Blowup

variable {X P : Scheme.{u}} [IsIntegral X] [IsIntegral P] [IsNoetherian P]
  (b : X ⟶ P) [IsProper b] [IsDominant b]
  (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
  (hdP : topologicalKrullDim P ≤ 2)
  (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
  (x : X) (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X)

include b hNagata hdP hb

/-- Properness of the literal normalized point step, derived from the original
base's Nagata charts. A regular centre is permitted but not required. -/
theorem normalizedPointBlowupMap_isProper_over_base :
    IsProper (normalizedPointBlowupMap X x hx hne) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian b
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  let : IsDominant B.map := pointBlowup_isDominant X x hx hne
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
    B.functionFieldMap_isIso (genericPoint_not_mem_pointCentre x hx hne)
  let := hb
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (B.map ≫ b))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  let : IsFinite (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization :=
    genericNormalization_isFinite_of_birational (B.map ≫ b) hNagata hdP hcomp
  change IsProper ((B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization ≫ B.map)
  infer_instance

/-- Noetherianity of the constructed point normalization is derived from
properness over the original Noetherian base. -/
theorem normalizedPointBlowup_isNoetherian_over_base :
    IsNoetherian (normalizedPointBlowup X x hx hne) := by
  let : IsProper (normalizedPointBlowupMap X x hx hne) :=
    normalizedPointBlowupMap_isProper_over_base b hNagata hdP hb x hx hne
  let a := normalizedPointBlowupMap X x hx hne ≫ b
  let : IsLocallyNoetherian (normalizedPointBlowup X x hx hne) :=
    LocallyOfFiniteType.isLocallyNoetherian a
  let : CompactSpace (normalizedPointBlowup X x hx hne) :=
    QuasiCompact.compactSpace_of_compactSpace a
  exact ⟨⟩

/-- The dimension bound concerns the actual new source and its accumulated
original function-field map, not an abstract birational replacement. -/
theorem normalizedPointBlowup_dimension_over_base :
    topologicalKrullDim (normalizedPointBlowup X x hx hne) ≤ 2 := by
  let : IsIntegral (normalizedPointBlowup X x hx hne) :=
    normalizedPointBlowup_isIntegral X x hx hne
  let : IsDominant (normalizedPointBlowupMap X x hx hne) :=
    normalizedPointBlowupMap_isDominant X x hx hne
  let : IsProper (normalizedPointBlowupMap X x hx hne) :=
    normalizedPointBlowupMap_isProper_over_base b hNagata hdP hb x hx hne
  let : IsIso (CommRingCat.ofHom (functionFieldMap (normalizedPointBlowupMap X x hx hne))) :=
    normalizedPointBlowupMap_functionFieldMap_isIso X x hx hne
  let := hb
  have hcomp : IsIso (CommRingCat.ofHom
      (functionFieldMap (normalizedPointBlowupMap X x hx hne ≫ b))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  exact dimension_le_two_of_birational (normalizedPointBlowupMap X x hx hne ≫ b)
    hNagata hdP hcomp

end AlgebraicGeometry.Scheme.NormalizedPointDomination
