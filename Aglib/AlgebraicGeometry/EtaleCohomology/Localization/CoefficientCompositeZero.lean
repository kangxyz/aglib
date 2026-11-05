/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientOpenZeroTransport
public import Aglib.CategoryTheory.Sites.SheafCohomology.MapIsoInjection

/-! # Restriction zero through an original coefficient isomorphism

Coefficient naturality and the original composition comparison give both
directions. The intermediate class is the actual pullback followed by the
specified isomorphism, not a newly chosen representative.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eY eZ eV

attribute [local instance] hasSheafifyLarge

/-- An isomorphic coefficient transport preserves and reflects zero after
the next restriction, with the unchanged original composite map and class. -/
theorem coefficient_iso_restriction_zero_iff_composite_zero
    {Y Z V : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    (v : Z ⟶ Y) (j : V ⟶ Z)
    (F : AbelianSheaf.{u, u + 1} Y) (G : AbelianSheaf.{u, u + 1} Z)
    (e : (inverseImage v).obj F ≅ G) (q : ℕ) (c : Sheaf.H.{eY} F q) :
    cohomologyPullback.{u, eZ, eV} j G q
        (Sheaf.H.map e.hom q (cohomologyPullback.{u, eY, eZ} v F q c)) = 0 ↔
      cohomologyPullback.{u, eY, eV} (j ≫ v) F q c = 0 := by
  constructor
  · intro h
    rw [cohomologyPullback_coefficientMap] at h
    have hiter : cohomologyPullback.{u, eZ, eV} j ((inverseImage v).obj F) q
        (cohomologyPullback.{u, eY, eZ} v F q c) = 0 := by
      apply Sheaf.H.map_injective_of_isIso ((inverseImage j).map e.hom) q
      exact h.trans (map_zero _).symm
    apply Sheaf.H.map_injective_of_isIso ((inverseImageComp v j).hom.app F) q
    exact (cohomologyPullback_comp v j F q c).trans
      (hiter.trans (map_zero _).symm)
  · exact coefficient_restriction_zero_of_composite_zero v j F G e.hom q c

end AlgebraicGeometry.Scheme.EtaleCohomology
