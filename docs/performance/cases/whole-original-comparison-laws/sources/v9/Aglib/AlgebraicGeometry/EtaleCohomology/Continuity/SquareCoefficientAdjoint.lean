/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramAdjointCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit

/-! # Original square coefficient maps under the two composite adjunctions -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- The selected adjunction is the original native inverse/direct-image adjunction. -/
lemma schemeAdjunction_eq_inverseImageAdjunction {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    schemeAdjunctionData.adj f = inverseImageAdjunction f.unop := rfl

/-- The selected right functor is literally the original native direct image. -/
lemma schemeRight_eq_directImage {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    schemeAdjunctionData.right f = directImage f.unop := rfl

/-- The selected right composition comparison is the original direct-image comparison. -/
lemma schemeRightCompIso_eq_directImageCompIso {X Y Z : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeAdjunctionData.compIso f g = (directImageCompIso f.unop g.unop).symm := rfl

/-- Whole right-adjoint equality transport is the original direct-image transport. -/
lemma schemeRight_eqToHom {X Y : Scheme.{u}ᵒᵖ} {f g : X ⟶ Y} (e : f = g) :
    eqToHom (congrArg schemeAdjunctionData.right e) =
      eqToHom (congrArg (fun k : Y.unop ⟶ X.unop => directImage k)
        (congrArg Quiver.Hom.unop e)) := by
  cases e
  rfl

/-- The generic whole right square is the original direct-image square. -/
lemma schemeSquareRightIso_eq_directImageSquareIso {S₀ X₀ S₁ X₁ : Scheme.{u}ᵒᵖ}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    schemeAdjunctionData.squareRightIso f₀ f₁ g h e =
      directImageSquareIso f₀.unop f₁.unop g.unop h.unop (congrArg Quiver.Hom.unop e) := by
  have ha : (schemeAdjunctionData.compIso f₀ h).symm =
      directImageCompIso f₀.unop h.unop := by
    simpa only [Iso.symm_symm_eq] using
      congrArg Iso.symm (schemeRightCompIso_eq_directImageCompIso f₀ h)
  have hm : eqToIso (congrArg schemeAdjunctionData.right e.symm) =
      eqToIso (congrArg (fun k : X₁.unop ⟶ S₀.unop => directImage k)
        (congrArg Quiver.Hom.unop e).symm) := by
    apply Iso.ext
    exact schemeRight_eqToHom e.symm
  exact congrArg₂
    (fun (a : directImage h.unop ⋙ directImage f₀.unop ≅
        directImage (h.unop ≫ f₀.unop))
      (b : directImage (h.unop ≫ f₀.unop) ≅
        directImage f₁.unop ⋙ directImage g.unop) => a ≪≫ b)
    ha (congrArg₂
      (fun (b : directImage (h.unop ≫ f₀.unop) ≅ directImage (f₁.unop ≫ g.unop))
        (c : directImage (f₁.unop ≫ g.unop) ≅
          directImage f₁.unop ⋙ directImage g.unop) => b ≪≫ c)
      hm (schemeRightCompIso_eq_directImageCompIso g f₁))

lemma directImageSquareIso_transpose {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    directImageSquareIso g g' f f' e.symm = (directImageSquareIso f f' g g' e).symm := by
  simpa only [schemeSquareRightIso_eq_directImageSquareIso, schemeRight_eq_directImage,
    Quiver.Hom.unop_op] using
    schemeAdjunctionData.squareRightIso_transpose f.op f'.op g.op g'.op
      (congrArg Quiver.Hom.op e)

lemma conjugate_inverseImageSquareIso_inv {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    conjugateEquiv ((inverseImageAdjunction g).comp (inverseImageAdjunction f'))
        ((inverseImageAdjunction f).comp (inverseImageAdjunction g'))
        (inverseImageSquareIso f f' g g' e).inv =
      (directImageSquareIso f f' g g' e).inv := by
  simpa only [schemeAdjunction_eq_inverseImageAdjunction, schemeSquareIso_eq_inverseImageSquareIso,
    schemeSquareRightIso_eq_directImageSquareIso, schemeRight_eq_directImage,
    Quiver.Hom.unop_op] using
    schemeAdjunctionData.conjugate_squareIso_inv f.op f'.op g.op g'.op
      (congrArg Quiver.Hom.op e)

lemma squareCoefficientMap_homEquiv {X₀ X₁ Y₀ Y₁ : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (he : v₁ ≫ f = h ≫ v₀)
    {F : AbelianSheaf.{u, u + 1} X₀} {G : AbelianSheaf.{u, u + 1} X₁}
    {K : AbelianSheaf.{u, u + 1} Y₁}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage v₁).obj G ⟶ K) :
    ((inverseImageAdjunction v₀).comp (inverseImageAdjunction h)).homEquiv _ _
        (squareCoefficientMap v₀ v₁ f h he φ ≫ ψ) =
      (inverseImageAdjunction f).homEquiv _ _ φ ≫
        (directImage f).map ((inverseImageAdjunction v₁).homEquiv _ _ ψ) ≫
          (directImageSquareIso v₀ v₁ f h he).inv.app K := by
  simpa only [Adjunction.CoefficientSquares.coefficientMap, squareCoefficientMap,
    Category.assoc] using
    Adjunction.CoefficientSquares.homEquiv (inverseImageAdjunction f)
      (inverseImageAdjunction v₀) (inverseImageAdjunction v₁) (inverseImageAdjunction h)
      (inverseImageSquareIso v₀ v₁ f h he) (directImageSquareIso v₀ v₁ f h he)
      (conjugate_inverseImageSquareIso_inv v₀ v₁ f h he) φ ψ

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
