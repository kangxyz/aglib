/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Vanishing across a surjective closed immersion

The actual original adjunction unit is invertible: every original geometric
point lifts, and the existing closed-stalk calculation identifies its unit.
Exact finite direct image then compares vanishing for arbitrary abelian
coefficients. This includes reduction to the reduced induced closed scheme,
without a nilpotence exponent, torsion condition or Noetherian hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eZ

attribute [local instance] hasSheafifyLarge

/-- The original unit is invertible along any surjective closed immersion,
for every original abelian coefficient. -/
theorem closedDirectImage_unit_isIso_of_surjective
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((inverseImageAdjunction i).unit.app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 X)
  intro Ω _ _ η _
  obtain ⟨z, hz⟩ := i.surjective (η (default : Spec (.of Ω)))
  obtain ⟨ζ, hζ⟩ := exists_closedImmersion_pointLift i η ⟨z, hz⟩
  exact closedDirectImage_unit_stalk_isIso i ζ η hζ F

namespace Vanishing

/-- Surjective closed restriction preserves and reflects vanishing of original
cohomology, retaining independent source and target Ext universes. -/
theorem subsingleton_H_iff_of_surjective_closedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Subsingleton (Sheaf.H.{eX} F q) ↔
      Subsingleton (Sheaf.H.{eZ} ((inverseImage i).obj F) q) := by
  let : IsIso ((inverseImageAdjunction i).unit.app F) :=
    closedDirectImage_unit_isIso_of_surjective i F
  let d : F ≅ (directImage i).obj ((inverseImage i).obj F) :=
    asIso ((inverseImageAdjunction i).unit.app F)
  let E := Finite.finiteCohomologyDirectImageAddEquiv.{u, eZ, eX}
    i ((inverseImage i).obj F) q
  constructor
  · intro h
    let : Subsingleton (Sheaf.H.{eX} F q) := h
    let : Subsingleton (Sheaf.H.{eX}
        ((directImage i).obj ((inverseImage i).obj F)) q) :=
      (cohomologyMapIso_bijective d q).surjective.subsingleton
    exact E.surjective.subsingleton
  · intro h
    let : Subsingleton (Sheaf.H.{eZ} ((inverseImage i).obj F) q) := h
    let : Subsingleton (Sheaf.H.{eX}
        ((directImage i).obj ((inverseImage i).obj F)) q) :=
      E.injective.subsingleton
    exact (cohomologyMapIso_bijective d q).injective.subsingleton

end Vanishing

end AlgebraicGeometry.Scheme.EtaleCohomology
