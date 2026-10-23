/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange

/-! # Composition and cancellation for the original derived exchange

The original vertical-pasting equation supplies composition and cancellation
of invertibility at an actual bounded-below coefficient. The higher-image
conclusion uses the original homology transport. All six derived-category
universes remain independent. No properness or cartesian hypothesis is needed
for these formal implications between the specified commuting squares.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u dS dX dY dS' dX' dY'

attribute [local instance] hasSheafifyLarge

section Vertical

variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dY'} (AbelianSheaf.{u, u + 1} Y')]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))

/-- Invertibility of both original adjacent exchanges implies invertibility
of the original composite exchange at the identical bounded-below coefficient. -/
theorem derivedBaseChangeMap_isIso_vComp
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} Y))
    [IsIso ((derivedBaseChangeMap f f' g g' h₁).app ((derivedDirectImage k).obj K))]
    [IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app K)] :
    IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app K) := by
  have hi : IsIso
      ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app K ≫
        (derivedDirectImageCompIso f' k').hom.app ((derivedInverseImage g'').obj K)) := by
    rw [← derivedBaseChangeMap_vComp f k f' k' g g' g'' h₁ h₂ h K]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

/-- If the inner and composite original exchanges are invertible, the outer
exchange is invertible on the actual derived direct image of the coefficient. -/
theorem derivedBaseChangeMap_isIso_of_vComp
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} Y))
    [IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app K)]
    [IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app K)] :
    IsIso ((derivedBaseChangeMap f f' g g' h₁).app ((derivedDirectImage k).obj K)) := by
  have hi : IsIso
      ((derivedInverseImage g).map ((derivedDirectImageCompIso f k).hom.app K) ≫
        (derivedBaseChangeMap f f' g g' h₁).app ((derivedDirectImage k).obj K) ≫
        (derivedDirectImage f').map ((derivedBaseChangeMap k k' g' g'' h₂).app K)) := by
    rw [derivedBaseChangeMap_vComp f k f' k' g g' g'' h₁ h₂ h K]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)

/-- Composition preserves invertibility of the whole original derived exchange,
without choosing any replacement natural transformation. -/
theorem derivedBaseChangeMap_isIso_vComp_natTrans
    [IsIso (derivedBaseChangeMap f f' g g' h₁)]
    [IsIso (derivedBaseChangeMap k k' g' g'' h₂)] :
    IsIso (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h) := by
  have (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} Y)) :
      IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app K) :=
    derivedBaseChangeMap_isIso_vComp f k f' k' g g' g'' h₁ h₂ h K
  exact NatIso.isIso_of_isIso_app _

end Vertical

section Transport

universe a₁ a₂ a₃ a₄ v₁ v₂ v₃ v₄

/-- Componentwise invertibility crosses the literal native whiskering recipe
behind its typed whole-transformation equation. -/
theorem isIso_app_of_whiskered_transport
    {A : Type a₁} [Category.{v₁} A] {B : Type a₂} [Category.{v₂} B]
    {C : Type a₃} [Category.{v₃} C] {D : Type a₄} [Category.{v₄} D]
    {J : A ⥤ B} {L M : B ⥤ C} {H : C ⥤ D} {U V : A ⥤ D}
    (s : U ≅ J ⋙ L ⋙ H) (β : L ⟶ M) (t : J ⋙ M ⋙ H ≅ V)
    (δ : U ⟶ V)
    (hδ : δ = s.hom ≫ Functor.whiskerLeft J (Functor.whiskerRight β H) ≫ t.hom)
    (X : A) [IsIso (β.app (J.obj X))] : IsIso (δ.app X) := by
  rw [hδ]
  change IsIso (s.hom.app X ≫ H.map (β.app (J.obj X)) ≫ t.hom.app X)
  infer_instance

end Transport

section Higher

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- Invertibility of the original derived exchange on the original single
coefficient gives invertibility of every original higher exchange component. -/
theorem higherBaseChangeMap_isIso_app_of_derived
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    [IsIso ((derivedBaseChangeMap f f' g g' h).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))] :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  exact isIso_app_of_whiskered_transport (higherBaseChangeSourceIso f g q)
    (derivedBaseChangeMap f f' g g' h) (higherBaseChangeTargetIso f' g' q)
    (higherBaseChangeMap f f' g g' h q) (higherBaseChangeMap_eq_transport f f' g g' h q) F

/-- The original higher exchange is invertible whenever the whole original
bounded-below derived exchange is invertible. -/
theorem higherBaseChangeMap_isIso_of_derived (q : ℕ)
    [IsIso (derivedBaseChangeMap f f' g g' h)] :
    IsIso (higherBaseChangeMap f f' g g' h q) := by
  rw [higherBaseChangeMap_eq_transport]
  infer_instance

end Higher

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
