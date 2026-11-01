/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.LocalRing
public import Aglib.RingTheory.Localization.ResiduePoint
public import Mathlib.RingTheory.Smooth.Flat

/-! # The original local stages of the geometric etale colimit

Localize each genuine neighborhood at the kernel of its original point.
The original stage maps and pointed transitions retain this one localization,
its residue point and the unchanged colimit. These local stages are essentially
etale; no finite presentation, Noetherianity or domain claim is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace GeometricEtaleColimit

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The native localization of a stage at its specified field-valued point. -/
abbrev stageLocalRing (X : GeometricEtaleNeighborhood R Ω) :=
  Localization.ResiduePoint.Ring X.point.toRingHom

instance stageLocalRing_base_local [IsLocalHom (algebraMap R Ω)]
    (X : GeometricEtaleNeighborhood R Ω) :
    IsLocalHom (algebraMap R (stageLocalRing R Ω X)) := by
  constructor
  intro r hr
  apply isUnit_of_map_unit (algebraMap R Ω) r
  have h := hr.map (Localization.ResiduePoint.point X.point.toRingHom)
  rw [IsScalarTower.algebraMap_apply R X.algebra (stageLocalRing R Ω X),
    Localization.ResiduePoint.point_algebraMap] at h
  change IsUnit (X.point (algebraMap R X.algebra r)) at h
  simpa only [AlgHom.commutes] using h

instance stageLocalRing_essFiniteType (X : GeometricEtaleNeighborhood R Ω) :
    Algebra.EssFiniteType R (stageLocalRing R Ω X) :=
  Algebra.EssFiniteType.comp R X.algebra (stageLocalRing R Ω X)

/-- The canonical map from the local stage into the unchanged colimit. -/
def stageLocalMap (X : GeometricEtaleNeighborhood R Ω) :
    stageLocalRing R Ω X →ₐ[R] GeometricEtaleColimit R Ω :=
  IsLocalization.liftAlgHom (f := ι R Ω X)
    (fun s : (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl =>
      isUnit_of_residue_ne_zero R Ω _ (by
        have hs : X.point s ≠ 0 := s.property
        simpa only [← AlgHom.comp_apply, residue_comp_ι] using hs))

@[simp] theorem stageLocalMap_algebraMap (X : GeometricEtaleNeighborhood R Ω)
    (a : X.algebra) :
    stageLocalMap R Ω X (algebraMap X.algebra (stageLocalRing R Ω X) a) = ι R Ω X a :=
  IsLocalization.lift_eq _ _

/-- Localization of a pointed transition, with the original prime identity. -/
def stageLocalTransition {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    stageLocalRing R Ω X →+* stageLocalRing R Ω Y :=
  Localization.localRingHom _ _ f.val.toRingHom (by
    ext a
    change X.point a = 0 ↔ Y.point (f.val a) = 0
    rw [← AlgHom.comp_apply, f.property])

@[simp] theorem stageLocalTransition_algebraMap
    {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) (a : X.algebra) :
    stageLocalTransition R Ω f (algebraMap X.algebra (stageLocalRing R Ω X) a) =
      algebraMap Y.algebra (stageLocalRing R Ω Y) (f.val a) :=
  Localization.localRingHom_to_map _ _ _ _ _

/-- The whole original stage triangle, before evaluation on coefficients. -/
theorem stageLocalMap_comp (X : GeometricEtaleNeighborhood R Ω) :
    (stageLocalMap R Ω X).comp
      (IsScalarTower.toAlgHom R X.algebra (stageLocalRing R Ω X)) = ι R Ω X := by
  ext a
  exact stageLocalMap_algebraMap R Ω X a

/-- The whole original residue triangle at the selected prime localization. -/
theorem stageLocalMap_residue (X : GeometricEtaleNeighborhood R Ω) :
    ((residue R Ω).comp (stageLocalMap R Ω X)).toRingHom =
      Localization.ResiduePoint.point X.point.toRingHom := by
  apply IsLocalization.ringHom_ext
    (M := (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl)
  ext a
  change residue R Ω (stageLocalMap R Ω X
      (algebraMap X.algebra (stageLocalRing R Ω X) a)) =
    Localization.ResiduePoint.point X.point.toRingHom
      (algebraMap X.algebra (stageLocalRing R Ω X) a)
  rw [stageLocalMap_algebraMap, Localization.ResiduePoint.point_algebraMap]
  exact AlgHom.congr_fun (residue_comp_ι R Ω X) a

/-- The original local-stage maps commute with the original pointed transitions. -/
theorem stageLocalMap_transition {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (stageLocalMap R Ω Y).toRingHom.comp (stageLocalTransition R Ω f) =
      (stageLocalMap R Ω X).toRingHom := by
  apply IsLocalization.ringHom_ext
    (M := (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl)
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    stageLocalTransition_algebraMap, stageLocalMap_algebraMap]
  exact AlgHom.congr_fun (ι_naturality f) a

/-- The original stage-local map is local, by its exact original residue triangle. -/
instance stageLocalMap_isLocalHom (X : GeometricEtaleNeighborhood R Ω) :
    IsLocalHom (stageLocalMap R Ω X).toRingHom := by
  let : IsLocalHom ((residue R Ω).toRingHom.comp (stageLocalMap R Ω X).toRingHom) := by
    change IsLocalHom ((residue R Ω).comp (stageLocalMap R Ω X)).toRingHom
    rw [stageLocalMap_residue]
    infer_instance
  exact isLocalHom_of_comp (stageLocalMap R Ω X).toRingHom (residue R Ω).toRingHom

end GeometricEtaleColimit
