/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodRootLocalStages
public import Aglib.RingTheory.Kummer.RootMapPoint
public import Aglib.RingTheory.Henselian.StrictHenselization.RootPoint
public import Mathlib.AlgebraicGeometry.Stalk

/-! # The specified point on the original point-localized root stage

Locality of the original coefficient-induced root map identifies the actual
closed points. Evaluating the whole original cone triangle then retains the
specified point of a descended lift. No new field point or local model is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
  (N : ℕ) (hN : 0 < N) (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
  (Y : GeometricEtaleNeighborhood R Ω)

local notation "C" => GeometricEtaleColimit R Ω
local notation "S" => GeometricEtaleColimit.stageLocalRing R Ω Y

/-- The original local-root cone projection sends the actual closed point to
the actual closed point. -/
theorem rootLocalConeMap_closedPoint :
    letI : IsLocalRing (RootAlgebra N (algebraMap R S f)) :=
      parameterRoot_isLocalRing S (algebraMap R S f)
        (map_nonunit (algebraMap R S) f hf) N hN
    letI : IsLocalRing (RootAlgebra N (algebraMap R C f)) :=
      GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
    rootLocalConeMap R Ω N f Y (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint _ := by
  let : IsLocalRing (RootAlgebra N (algebraMap R S f)) :=
    parameterRoot_isLocalRing S (algebraMap R S f)
      (map_nonunit (algebraMap R S) f hf) N hN
  let : IsLocalRing (RootAlgebra N (algebraMap R C f)) :=
    GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
  let : IsLocalHom (rootMap (GeometricEtaleColimit.stageLocalMap R Ω Y) N f).toRingHom :=
    rootMap_isLocalHom (GeometricEtaleColimit.stageLocalMap R Ω Y) N hN f
  exact AlgebraicGeometry.Spec_closedPoint

/-- The unchanged descended lift retains its specified original point after
passing to the actual point localization, as well as its original base map. -/
theorem rootLocalStage_lift_point
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of (RootAlgebra N f)))
    (b : (rootDiagram R Ω N f).obj (op Y) ⟶ Z)
    (hb : b ≫ p = (rootStructure R Ω N f).app (op Y))
    (a : Spec (.of (RootAlgebra N (algebraMap R C f))) ⟶ Z)
    (hba : (rootCone R Ω N f).π.app (op Y) ≫ b = a) :
    letI : IsLocalRing (RootAlgebra N (algebraMap R S f)) :=
      parameterRoot_isLocalRing S (algebraMap R S f)
        (map_nonunit (algebraMap R S) f hf) N hN
    letI : IsLocalRing (RootAlgebra N (algebraMap R C f)) :=
      GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
    (rootLocalStageMap R Ω N f Y ≫ b) ≫ p =
        Spec.map (CommRingCat.ofHom (rootBaseChangeHom S N f).toRingHom) ∧
      (rootLocalStageMap R Ω N f Y ≫ b) (IsLocalRing.closedPoint _) =
        a (IsLocalRing.closedPoint _) := by
  let : IsLocalRing (RootAlgebra N (algebraMap R S f)) :=
    parameterRoot_isLocalRing S (algebraMap R S f)
      (map_nonunit (algebraMap R S) f hf) N hN
  let : IsLocalRing (RootAlgebra N (algebraMap R C f)) :=
    GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hb, rootLocalStageMap_structure]
  · have h := congrArg
      (fun q : Spec (.of (RootAlgebra N (algebraMap R C f))) ⟶ Z =>
        q (IsLocalRing.closedPoint _))
      ((rootLocalConeMap_stage_assoc R Ω N f Y b).trans hba)
    change (rootLocalStageMap R Ω N f Y ≫ b)
      (rootLocalConeMap R Ω N f Y (IsLocalRing.closedPoint _)) = _ at h
    rwa [rootLocalConeMap_closedPoint R Ω N hN f hf Y] at h

end AlgebraicGeometry.Scheme.Kummer
