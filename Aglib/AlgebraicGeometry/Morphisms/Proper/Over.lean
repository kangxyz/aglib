/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness and immersions in the native over category

The structural equations are the actual equations of over-category maps.
No replacement source, target, or structural morphism is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A proper morphism to a proper object has proper original structure map. -/
theorem isProper_hom_of_isProper_over_map {S : Scheme.{u}} {Y X : Over S}
    (p : Y ⟶ X) [IsProper p.left] [IsProper X.hom] : IsProper Y.hom := by
  rw [← p.w]
  infer_instance

/-- An immersive map from a proper object to a separated object is closed. -/
theorem isClosedImmersion_of_immersion_over_proper {S : Scheme.{u}} {Y P : Over S}
    (q : Y ⟶ P) [IsProper Y.hom] [IsSeparated P.hom] [IsImmersion q.left] :
    IsClosedImmersion q.left := by
  have : IsProper (q.left ≫ P.hom) := by rw [q.w]; infer_instance
  have : IsProper q.left := IsProper.of_comp q.left P.hom
  exact IsClosedImmersion.of_isPreimmersion q.left q.left.isClosedMap.isClosed_range

/-- A surjective image of a proper object is proper if its original
structure map is separated and locally of finite type. -/
theorem isProper_of_surjective_over_proper {S : Scheme.{u}} {Y X : Over S}
    (p : Y ⟶ X) [Surjective p.left] [IsProper Y.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] : IsProper X.hom := by
  have : UniversallyClosed (p.left ≫ X.hom) := by rw [p.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective p.left X.hom
  exact ⟨⟩

end AlgebraicGeometry.Scheme
