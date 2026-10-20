/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.PointedMorphism
public import Aglib.AlgebraicGeometry.RationalPoint.ExtensionSource
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Translation of a proper-group morphism to a pointed morphism

Source: packet R5Lab.Aglib.AlgebraicGeometry.Group.PointedTranslation.
Properness and geometric integrality retain their original scope.
The extended identity equation descends along the actual field map.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Group.PointedMorphism
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {k K : Type u} [Field k] [Field K]

section Translation
variable {C D : FScheme k} [GrpObj C] [GrpObj D]

/-- Translate a scheme morphism by the inverse of its value at the identity. -/
def pointedTranslate (m : C ⟶ D) : C ⟶ D :=
  (toUnit C ≫ η[C] ≫ m)⁻¹ * m

theorem pointedTranslate_pointed (m : C ⟶ D) :
    η[C] ≫ pointedTranslate m = η[D] := by
  simp [pointedTranslate, comp_mul, GrpObj.comp_inv, Hom.one_def]

theorem pointedTranslate_isMonHom
    [IsProper C.hom] [IsProper D.hom] [GeometricallyIntegral C.hom] (m : C ⟶ D) :
    IsMonHom (pointedTranslate m) :=
  AlgebraicGeometry.Scheme.Group.PointedMorphism.isMonHom_of_geometricallyIntegral C D
    (pointedTranslate m) (pointedTranslate_pointed m)

theorem pointedTranslate_point_formula {S : FScheme k} (m : C ⟶ D)
    (x : S ⟶ C) :
    x ≫ pointedTranslate m = (toUnit S ≫ η[C] ≫ m)⁻¹ * (x ≫ m) := by
  simp [pointedTranslate, comp_mul, GrpObj.comp_inv]

end Translation

/-- Field extension is faithfully flat, so equality of extended rational
points descends to the original field. -/
theorem fieldExtensionSpec_epi (f : k →+* K) :
    Epi (Spec.map (CommRingCat.ofHom f)) := by
  let : Surjective (Spec.map (CommRingCat.ofHom f)) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/-- The origin identity is an equality of actual base-field scheme morphisms,
not merely an equality at one geometric point. -/
theorem pointed_of_extended_pointed {C D : FScheme k} [GrpObj C] [GrpObj D]
    (f : k →+* K) (m : C ⟶ D)
    (h : toUnit (extensionPointSource f) ≫ η[C] ≫ m = 1) : η[C] ≫ m = η[D] := by
  let := fieldExtensionSpec_epi f
  apply Over.OverMorphism.ext
  apply (cancel_epi (Spec.map (CommRingCat.ofHom f))).mp
  exact congrArg (fun z : extensionPointSource f ⟶ D => z.left) h


end AlgebraicGeometry.Scheme.Group.PointedMorphism
