/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSectionNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor

/-! # Native coefficient-system morphisms at the specified limit cone -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

lemma triangleCoefficientMap_naturality {Y Z T : Scheme.{u}} (f : Z ⟶ Y)
    (p : T ⟶ Y) (q : T ⟶ Z) (e : q ≫ f = p)
    {F F' : AbelianSheaf.{u, u + 1} Y} {G G' : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage f).obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : (inverseImage f).map a ≫ ψ = φ ≫ b) :
    triangleCoefficientMap f p q e φ ≫ (inverseImage q).map b =
      (inverseImage p).map a ≫ triangleCoefficientMap f p q e ψ :=
  Adjunction.triangleCoefficientMap_naturality (pullbackTriangleIso p f q e) φ ψ a b h

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
  {F G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)

/-- The original inverse-image maps define a morphism of the actual cone coefficient diagrams. -/
def coneCoefficientNatTrans : coneCoefficientFunctor X c F ⟶ coneCoefficientFunctor X c G :=
  (diagramConeAdjunctionData X c).coefficientNatTrans η

/-- The shared cone transformation has its literal original inverse-image value. -/
lemma coneCoefficientNatTrans_app (i : I) :
    (coneCoefficientNatTrans X c η).app i =
      (inverseImage (c.ι.app i).unop).map (η.app i) := rfl

variable [HasColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop)]

/-- The resulting map on the actual coefficient colimits. -/
def coneCoefficientColimitMap : colimit (coneCoefficientFunctor X c F) ⟶
    colimit (coneCoefficientFunctor X c G) :=
  (diagramConeAdjunctionData X c).coefficientColimitMap η

/-- The colimit map is induced by that same actual coefficient transformation. -/
lemma coneCoefficientColimitMap_eq_colim_map :
    coneCoefficientColimitMap X c η = colim.map (coneCoefficientNatTrans X c η) := rfl

@[reassoc]
lemma coneCoefficientColimitMap_ι (i : I) :
    colimit.ι (coneCoefficientFunctor X c F) i ≫ coneCoefficientColimitMap X c η =
      (inverseImage (c.ι.app i).unop).map (η.app i) ≫
        colimit.ι (coneCoefficientFunctor X c G) i :=
  (diagramConeAdjunctionData X c).coefficientColimitMap_ι η i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
