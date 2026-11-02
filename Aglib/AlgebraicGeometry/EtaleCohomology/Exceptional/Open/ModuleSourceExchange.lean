/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate
public import Aglib.CategoryTheory.Adjunction.Mates.SourceChange

/-! # Original exchange for a change of source -/

@[expose] public noncomputable section

open CategoryTheory


universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

/-- The original counit equation for an arbitrary native inverse-image square. -/
theorem moduleExchange_counit {X X' S S' : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (α : moduleInverseImage g Λ ⋙ moduleInverseImage f' Λ ⟶
      moduleInverseImage f Λ ⋙ moduleInverseImage g' Λ) (M : ModuleSheaf X Λ) :
    (moduleInverseImage f' Λ).map
        (((mateEquiv (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
          (TwoSquare.mk _ _ _ _ α)).natTrans).app M) ≫
      (moduleInverseImageAdjunction f' Λ).counit.app
        ((moduleInverseImage g' Λ).obj M) =
    α.app ((moduleDirectImage f Λ).obj M) ≫
      (moduleInverseImage g' Λ).map ((moduleInverseImageAdjunction f Λ).counit.app M) :=
  mateEquiv_counit (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (TwoSquare.mk _ _ _ _ α) M

variable {V P Y : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  (p : P ⟶ Y) (e : V ⟶ P) (i : V ⟶ Y) (he : e ≫ p = i)

/-- The original inverse-image comparison for a factorization of the source map. -/
def moduleSourceInverseImageIso :
    moduleInverseImage i Λ ≅ moduleInverseImage p Λ ⋙ moduleInverseImage e Λ :=
  SourceChange.sourceComparison (fun k : V ⟶ Y => moduleInverseImage k Λ)
    he (moduleInverseImageCompIso Λ p e)

/-- The whole identity-side square retains the original source comparison. -/
theorem moduleInverseImageSquareIso_source_iso :
    moduleInverseImageSquareIso Λ (𝟙 Y) e p i
        (he.trans (Category.comp_id i).symm) ≪≫
      Functor.isoWhiskerRight (moduleInverseImageIdIso Λ Y) (moduleInverseImage i Λ) ≪≫
      Functor.leftUnitor (moduleInverseImage i Λ) =
    (moduleSourceInverseImageIso Λ p e i he).symm := by
  exact SourceChange.identitySource_square
    (fun k : V ⟶ Y => moduleInverseImage k Λ) he (Category.comp_id i)
    (moduleInverseImageCompIso Λ p e) (moduleInverseImageCompIso Λ (𝟙 Y) i)
    (moduleInverseImageIdIso Λ Y)
    (moduleInverseImageSquareIso Λ (𝟙 Y) e p i
      (he.trans (Category.comp_id i).symm)) rfl (moduleInverseImageCompIso_id_comp Λ i)

/-- The identity-side inverse-image square is the original source comparison. -/
@[reassoc]
theorem moduleInverseImageSquareIso_source (M : ModuleSheaf Y Λ) :
    (moduleInverseImageSquareIso Λ (𝟙 Y) e p i
        (he.trans (Category.comp_id i).symm)).hom.app M ≫
      (moduleInverseImage i Λ).map ((moduleInverseImageIdIso Λ Y).hom.app M) =
    (moduleSourceInverseImageIso Λ p e i he).inv.app M :=
  SourceChange.normalized_identity_square_app _ _ _
    (moduleInverseImageSquareIso_source_iso Λ p e i he) M

/-- A change of source retains the exact original unit of that source map. -/
@[reassoc]
theorem moduleBaseChangeMap_source (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ (𝟙 Y) e p i
      (he.trans (Category.comp_id i).symm)).app M =
    (moduleInverseImage p Λ).map ((moduleDirectImageIdIso Λ Y).hom.app M) ≫
      (moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage p Λ).obj M) ≫
      (moduleDirectImage e Λ).map ((moduleSourceInverseImageIso Λ p e i he).inv.app M) := by
  exact SourceChange.mate_source_unit
    (moduleInverseImageAdjunction (𝟙 Y) Λ) (moduleInverseImageAdjunction e Λ)
    (moduleInverseImage p Λ) (moduleInverseImage i Λ)
    (moduleInverseImageSquareIso Λ (𝟙 Y) e p i
      (he.trans (Category.comp_id i).symm)).hom
    (moduleInverseImageIdIso Λ Y) (moduleDirectImageIdIso Λ Y)
    (moduleSourceInverseImageIso Λ p e i he)
    (moduleInverseImageIdIso_counit Λ Y)
    (moduleInverseImageSquareIso_source Λ p e i he) M

end AlgebraicGeometry.Scheme.EtaleCohomology
