/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SmoothBoundedStageClass

/-! # Geometric input of original smooth stage reconstruction

This structure records the actual affine limit and Cartesian smooth squares.
It contains no class representative, vanishing, or cohomological comparison
assumption. The original bounded class producer is applied with these fixed
carriers, avoiding a second conversion to expanded geometric expressions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e
attribute [local instance] hasSheafifyLarge

/-- Actual affine limit together with its original smooth coefficient squares. -/
structure SmoothAffineStageSystem (I : Type u) [Category.{u} I] where
  /-- The affine stages as a diagram of opposite schemes. -/
  diagram : I ⥤ Scheme.{u}ᵒᵖ
  /-- The original affine limit cone, viewed in opposite schemes. -/
  cone : Cocone diagram
  /-- The universal property of the opposite cone. -/
  isColimit : IsColimit cone
  affine : ∀ i, IsAffine (diagram.obj i).unop
  affineMap : ∀ {i j} (g : i ⟶ j), IsAffineHom (diagram.map g).unop
  /-- The coefficient base of the limit. -/
  base : Scheme.{u}
  /-- The original projection from the limit to its coefficient base. -/
  projection : cone.pt.unop ⟶ base
  /-- The coefficient base at each finite stage. -/
  stageBase : I → Scheme.{u}
  /-- The original restriction from the coefficient base to a stage base. -/
  baseLeg : ∀ i, base ⟶ stageBase i
  /-- The original smooth projection at each stage. -/
  stageProjection : ∀ i, (diagram.obj i).unop ⟶ stageBase i
  cartesian : ∀ i, IsPullback projection (cone.ι.app i).unop
    (baseLeg i) (stageProjection i)
  smooth : ∀ i, Smooth (stageProjection i)

namespace SmoothAffineStageSystem

/-- The complete original class reconstruction from geometric data alone. -/
theorem exists_stage_class {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : SmoothAffineStageSystem I)
    [hstage : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (D.diagram.obj i).unop)]
    [hapex : HasExt.{e} (AbelianSheaf.{u, u + 1} D.cone.pt.unop)]
    [HasColimitsOfShape I AddCommGrpCat.{e}] [UnivLE.{u, e}]
    (n : ℕ) (hn : 0 < n)
    (F : (boundedCoefficientProperty D.base n).FullSubcategory)
    (q : ℕ)
    (a : Sheaf.H.{e} (((boundedCoefficientProperty D.base n).ι ⋙
      inverseImage D.projection).obj F) q) :
    ∃ (i : I)
      (aᵢ : Sheaf.H.{e} ((boundedBaseChangeSource (D.baseLeg i)
        (D.stageProjection i) n).obj F) q),
      cohomologyTransfer (X := (D.diagram.obj i).unop) (Y := D.cone.pt.unop)
        (D.cone.ι.app i).unop
        ((inverseImageAdjunction (D.cone.ι.app i).unop).counit.app
          (((boundedCoefficientProperty D.base n).ι ⋙ inverseImage D.projection).obj F)) q
        (Sheaf.H.map ((boundedBaseChangeMap (D.baseLeg i) (D.cone.ι.app i).unop
          (D.stageProjection i) D.projection (D.cartesian i).w.symm n).app F) q aᵢ) = a :=
  @exists_smooth_bounded_stage_class I _ _ D.diagram D.cone D.isColimit
    D.affine D.affineMap hstage hapex _ _ D.base D.projection
    D.stageBase D.baseLeg D.stageProjection D.cartesian D.smooth n hn F q a

end SmoothAffineStageSystem
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
