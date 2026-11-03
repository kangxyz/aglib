/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodRootLimit
public import Aglib.RingTheory.Kummer.RootMap
public import Aglib.RingTheory.Henselian.StrictHenselization.LocalStages

/-! # The original root cone through the actual pointed local stage

The native point localization and its original colimit map induce maps of
the literal root algebras. Their whole triangle is the existing root cone
projection; no second local stage or iterated-root model is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

open EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  (N : ℕ) (f : R) (Y : GeometricEtaleNeighborhood R Ω)

local notation "C" => GeometricEtaleColimit R Ω
local notation "S" => GeometricEtaleColimit.stageLocalRing R Ω Y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same cone projection, through the literal root map of its original coefficient map. -/
theorem rootCone_π_eq_rootMap :
    (rootCone R Ω N f).π.app (op Y) =
      Spec.map (CommRingCat.ofHom
        (rootMap (GeometricEtaleColimit.ι R Ω Y) N f).toRingHom) ≫
        (rootBaseChangeSpecIso R Y.algebra N f).hom := by
  apply pullback.hom_ext (f := Spec.algebraMap R Y.algebra)
    (g := Spec.algebraMap R (RootAlgebra N f))
  · rw [rootCone_π_fst, Category.assoc, rootBaseChangeSpecIso_hom_fst,
      specCone_π]
    change Spec.map (CommRingCat.ofHom (algebraMap C (RootAlgebra N (algebraMap R C f)))) ≫
        Spec.map (CommRingCat.ofHom (GeometricEtaleColimit.ι R Ω Y).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (rootMap (GeometricEtaleColimit.ι R Ω Y) N f).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Y.algebra (RootAlgebra N (algebraMap R Y.algebra f))))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (rootMap_comp_algebraMap
      (GeometricEtaleColimit.ι R Ω Y) N f).symm
  · rw [Category.assoc, rootBaseChangeSpecIso_hom_snd]
    change (rootCone R Ω N f).π.app (op Y) ≫ (rootStructure R Ω N f).app (op Y) = _
    rw [rootCone_π_structure, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom
      (rootMap_comp_rootBaseChangeHom (GeometricEtaleColimit.ι R Ω Y) N f)).symm

/-- The original point-localized root spectrum maps to the unchanged genuine stage. -/
def rootLocalStageMap :
    Spec (.of (RootAlgebra N (algebraMap R S f))) ⟶
      (rootDiagram R Ω N f).obj (op Y) :=
  Spec.map (CommRingCat.ofHom
    (rootMap (IsScalarTower.toAlgHom R Y.algebra S) N f).toRingHom) ≫
    (rootBaseChangeSpecIso R Y.algebra N f).hom

/-- The original stage-local map induces the original root-colimit projection. -/
def rootLocalConeMap :
    Spec (.of (RootAlgebra N (algebraMap R C f))) ⟶
      Spec (.of (RootAlgebra N (algebraMap R S f))) :=
  Spec.map (CommRingCat.ofHom
    (rootMap (GeometricEtaleColimit.stageLocalMap R Ω Y) N f).toRingHom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete triangle retains the existing root cone, not only its base projection. -/
@[reassoc]
theorem rootLocalConeMap_stage :
    rootLocalConeMap R Ω N f Y ≫ rootLocalStageMap R Ω N f Y =
      (rootCone R Ω N f).π.app (op Y) := by
  rw [rootCone_π_eq_rootMap]
  dsimp only [rootLocalConeMap, rootLocalStageMap]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  change ((rootMap (GeometricEtaleColimit.stageLocalMap R Ω Y) N f).comp
    (rootMap (IsScalarTower.toAlgHom R Y.algebra S) N f)).toRingHom = _
  rw [rootMap_comp, GeometricEtaleColimit.stageLocalMap_comp]
  rfl

/-- The point-localized lift has the original root-base map. -/
@[reassoc]
theorem rootLocalStageMap_structure :
    rootLocalStageMap R Ω N f Y ≫ (rootStructure R Ω N f).app (op Y) =
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom S N f).toRingHom) := by
  change (_ ≫ (rootBaseChangeSpecIso R Y.algebra N f).hom) ≫ pullback.snd _ _ = _
  rw [Category.assoc, rootBaseChangeSpecIso_hom_snd, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (rootMap_comp_rootBaseChangeHom (IsScalarTower.toAlgHom R Y.algebra S) N f))

end AlgebraicGeometry.Scheme.Kummer
