/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CoefficientSquares

/-! # Original coefficient maps across commutative scheme squares -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- The selected identity comparison is the original native inverse-image identity. -/
lemma schemeLeftIdIso_eq_inverseImageId (X : Scheme.{u}ᵒᵖ) :
    schemeAdjunctionData.leftIdIso X = inverseImageId X.unop := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id (inverseImageAdjunction (𝟙 X.unop))).injective
  exact (Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _).trans
    (conjugateEquiv_inverseImageId_hom X.unop).symm

/-- Whole equality transport agrees with the original inverse-image transport. -/
lemma schemeLeft_eqToHom {X Y : Scheme.{u}ᵒᵖ} {f g : X ⟶ Y} (e : f = g) :
    eqToHom (congrArg schemeAdjunctionData.left e) =
      eqToHom (congrArg (fun k : Y.unop ⟶ X.unop => inverseImage k)
        (congrArg Quiver.Hom.unop e)) := by
  cases e
  rfl

/-- The generic whole square is precisely the original native square. -/
lemma schemeSquareIso_eq_inverseImageSquareIso {S₀ X₀ S₁ X₁ : Scheme.{u}ᵒᵖ}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    schemeAdjunctionData.squareIso f₀ f₁ g h e =
      inverseImageSquareIso f₀.unop f₁.unop g.unop h.unop (congrArg Quiver.Hom.unop e) := by
  have hm : eqToIso (congrArg schemeAdjunctionData.left e) =
      eqToIso (congrArg (fun k : X₁.unop ⟶ S₀.unop => inverseImage k)
        (congrArg Quiver.Hom.unop e)) := by
    apply Iso.ext
    exact schemeLeft_eqToHom e
  exact congrArg₂
    (fun (a : inverseImage (f₁.unop ≫ g.unop) ≅
        inverseImage g.unop ⋙ inverseImage f₁.unop)
      (b : inverseImage (f₁.unop ≫ g.unop) ≅
        inverseImage f₀.unop ⋙ inverseImage h.unop) => a.symm ≪≫ b)
    (schemeLeftCompIso_eq_inverseImageComp g f₁)
    (congrArg₂
      (fun (b : inverseImage (f₁.unop ≫ g.unop) ≅ inverseImage (h.unop ≫ f₀.unop))
        (c : inverseImage (h.unop ≫ f₀.unop) ≅
          inverseImage f₀.unop ⋙ inverseImage h.unop) => b ≪≫ c)
      hm (schemeLeftCompIso_eq_inverseImageComp f₀ h))

/-- The native square isomorphism transports a coefficient transition. -/
def squareCoefficientMap {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    (inverseImage h).obj ((inverseImage f₀).obj F) ⟶ (inverseImage f₁).obj G :=
  Adjunction.CoefficientSquares.coefficientMap (L_g := inverseImage g) (L_v₀ := inverseImage f₀)
    (L_v₁ := inverseImage f₁) (L_h := inverseImage h) (inverseImageSquareIso f₀ f₁ g h e) φ

/-- The shared generic constructor has the whole original native map as its literal value. -/
lemma squareCoefficientMap_eq_original {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareCoefficientMap f₀ f₁ g h e φ =
      (inverseImageSquareIso f₀ f₁ g h e).inv.app F ≫ (inverseImage f₁).map φ := rfl

/-- The generic coefficient map retains the whole original native coefficient map. -/
lemma schemeSquareCoefficientMap_eq_squareCoefficientMap {S₀ X₀ S₁ X₁ : Scheme.{u}ᵒᵖ}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h)
    {F : AbelianSheaf.{u, u + 1} S₀.unop} {G : AbelianSheaf.{u, u + 1} S₁.unop}
    (φ : (inverseImage g.unop).obj F ⟶ G) :
    schemeAdjunctionData.squareCoefficientMap f₀ f₁ g h e φ =
      squareCoefficientMap f₀.unop f₁.unop g.unop h.unop (congrArg Quiver.Hom.unop e) φ := by
  exact congrArg
    (fun s : inverseImage g.unop ⋙ inverseImage f₁.unop ≅
        inverseImage f₀.unop ⋙ inverseImage h.unop =>
      Adjunction.CoefficientSquares.coefficientMap (L_g := inverseImage g.unop)
        (L_v₀ := inverseImage f₀.unop) (L_v₁ := inverseImage f₁.unop)
        (L_h := inverseImage h.unop) s φ)
    (schemeSquareIso_eq_inverseImageSquareIso f₀ f₁ g h e)

section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Inverse form of the already proved original square-pasting equation. -/
lemma inverseImageSquareIso_inv_hComp (F : AbelianSheaf.{u, u + 1} S₀) :
    (inverseImageComp h₁ h₂).hom.app ((inverseImage f₀).obj F) ≫
        (inverseImage h₂).map ((inverseImageSquareIso f₀ f₁ g₁ h₁ e₁).inv.app F) ≫
        (inverseImageSquareIso f₁ f₂ g₂ h₂ e₂).inv.app ((inverseImage g₁).obj F) =
      (inverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).inv.app F ≫
        (inverseImage f₂).map ((inverseImageComp g₁ g₂).hom.app F) := by
  simpa only [schemeLeftCompIso_eq_inverseImageComp, schemeSquareIso_eq_inverseImageSquareIso,
    schemeLeft_eq_inverseImage, unop_comp, Quiver.Hom.unop_op] using
    schemeAdjunctionData.squareIso_inv_hComp schemeAdjunctionData_coherent
      f₀.op f₁.op f₂.op g₁.op g₂.op h₁.op h₂.op
      (congrArg Quiver.Hom.op e₁) (congrArg Quiver.Hom.op e₂) (congrArg Quiver.Hom.op e) F

/-- Two native coefficient-square maps compose with the original inverse-image comparisons. -/
lemma squareCoefficientMap_hComp
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    {H : AbelianSheaf.{u, u + 1} S₂}
    (φ : (inverseImage g₁).obj F ⟶ G) (ψ : (inverseImage g₂).obj G ⟶ H) :
    (inverseImageComp h₁ h₂).hom.app ((inverseImage f₀).obj F) ≫
        (inverseImage h₂).map (squareCoefficientMap f₀ f₁ g₁ h₁ e₁ φ) ≫
        squareCoefficientMap f₁ f₂ g₂ h₂ e₂ ψ =
      squareCoefficientMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e
        ((inverseImageComp g₁ g₂).hom.app F ≫ (inverseImage g₂).map φ ≫ ψ) := by
  simpa only [schemeLeftCompIso_eq_inverseImageComp,
    schemeSquareCoefficientMap_eq_squareCoefficientMap, schemeLeft_eq_inverseImage,
    unop_comp, Quiver.Hom.unop_op] using
    schemeAdjunctionData.squareCoefficientMap_hComp schemeAdjunctionData_coherent
      f₀.op f₁.op f₂.op g₁.op g₂.op h₁.op h₂.op
      (congrArg Quiver.Hom.op e₁) (congrArg Quiver.Hom.op e₂) (congrArg Quiver.Hom.op e) φ ψ

end Horizontal
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
