/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodRootLocalPoint
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles

/-! # The original boundary lift into the genuine-stage ordinary pullback

The unchanged local root lift and its original base triangle construct a map
to the ordinary pullback of the original boundary scheme. Both projections
and the specified point are retained. Normalization is not base changed by
an assumed comparison, and no new pointed local ring is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
  (N : ℕ) (hN : 0 < N) (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
  (Y : GeometricEtaleNeighborhood R Ω)

local notation "S" => GeometricEtaleColimit.stageLocalRing R Ω Y
local notation "T" => RootAlgebra N f
local notation "TS" => RootAlgebra N (algebraMap R S f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the actual genuine-stage pullback lift from the original
normalization-map triangle and descended section, retaining the same point. -/
theorem exists_rootStageBoundaryLift
    {Z W : Scheme.{u}} (p : Z ⟶ Spec (.of R)) (q : W ⟶ Spec (.of T))
    (m : W ⟶ Z) (hm : m ≫ p = q ≫ Spec.algebraMap R T)
    (b : (rootDiagram R Ω N f).obj (op Y) ⟶ W)
    (hb : b ≫ q = (rootStructure R Ω N f).app (op Y)) :
    letI : IsLocalRing TS := parameterRoot_isLocalRing S (algebraMap R S f)
      (map_nonunit (algebraMap R S) f hf) N hN
    ∀ (x : Z), (rootLocalStageMap R Ω N f Y ≫ b ≫ m) (IsLocalRing.closedPoint TS) = x →
    ∃ d : Spec (.of TS) ⟶ pullback p (Spec.algebraMap R Y.algebra),
      d ≫ pullback.fst p (Spec.algebraMap R Y.algebra) =
        rootLocalStageMap R Ω N f Y ≫ b ≫ m ∧
      d ≫ pullback.snd p (Spec.algebraMap R Y.algebra) = Spec.algebraMap Y.algebra TS ∧
      pullback.fst p (Spec.algebraMap R Y.algebra) (d (IsLocalRing.closedPoint TS)) = x := by
  let : IsLocalRing TS := parameterRoot_isLocalRing S (algebraMap R S f)
    (map_nonunit (algebraMap R S) f hf) N hN
  intro x hx
  have h : (rootLocalStageMap R Ω N f Y ≫ b ≫ m) ≫ p =
      Spec.algebraMap Y.algebra TS ≫ Spec.algebraMap R Y.algebra := by
    rw [Category.assoc, Category.assoc, hm, ← Category.assoc b, hb,
      ← Category.assoc, rootLocalStageMap_structure]
    rw [Spec.map_algHom_algebraMap]
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  let d := pullback.lift (rootLocalStageMap R Ω N f Y ≫ b ≫ m)
    (Spec.algebraMap Y.algebra TS) h
  refine ⟨d, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  exact (congrArg (fun a : Spec (.of TS) ⟶ Z => a (IsLocalRing.closedPoint TS))
    (pullback.lift_fst _ _ _)).trans hx

end AlgebraicGeometry.Scheme.Kummer
