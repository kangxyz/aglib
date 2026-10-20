/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Ranges of actual over-category pullback maps

The displayed ranges are inverse images under the original pullback
projection. The isomorphism comparison keeps its actual forward map;
open immersion is required only in the open-immersion theorem.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.UnitRange`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b0d400af861b147780c40c66ecbbffc8f316f4b9ecf4265eedb3a55c31edf22f`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Pullback

universe u
attribute [local instance] Over.cartesianMonoidalCategory

theorem range_pullbackMap {S T : Scheme.{u}} (s : S ⟶ T)
    {X Y : Over T} (f : X ⟶ Y) :
    Set.range ((Over.pullback s).map f).left =
      pullback.fst Y.hom s ⁻¹' Set.range f.left := by
  have heq : ((Over.pullback s).map f).left =
      pullback.map X.hom s Y.hom s f.left (𝟙 S) (𝟙 T)
        (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [heq]
  simpa using (Scheme.Pullback.range_map X.hom s Y.hom s f.left (𝟙 S) (𝟙 T)
    (by simp) (by simp))

theorem iso_pullback_openImmersion {S T : Scheme.{u}} (s : S ⟶ T)
    {X : Over S} {Y Z : Over T} (e : X ≅ (Over.pullback s).obj Y)
    (f : Y ⟶ Z) (hf : IsOpenImmersion f.left) :
    IsOpenImmersion (e.hom ≫ (Over.pullback s).map f).left := by
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let : IsOpenImmersion ((Over.pullback s).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) s f hf
  change IsOpenImmersion (e.hom.left ≫ _)
  infer_instance

theorem range_iso_pullback {S T : Scheme.{u}} (s : S ⟶ T)
    {X : Over S} {Y Z : Over T} (e : X ≅ (Over.pullback s).obj Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ (Over.pullback s).map f).left =
      pullback.fst Z.hom s ⁻¹' Set.range f.left := by
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  change Set.range (e.hom.left ≫ _) = _
  rw [range_eq_range_of_surjective _ _ e.hom.left rfl, range_pullbackMap]

end AlgebraicGeometry.Scheme.Pullback
