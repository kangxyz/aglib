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
      (inverseImage p).map a ≫ triangleCoefficientMap f p q e ψ := by
  have hn := (pullbackTriangleIso p f q e).hom.naturality a
  change (inverseImage p).map a ≫ (pullbackTriangleIso p f q e).hom.app F' =
    (pullbackTriangleIso p f q e).hom.app F ≫
      (inverseImage q).map ((inverseImage f).map a) at hn
  dsimp only [triangleCoefficientMap]
  rw [Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp, ← Category.assoc, ← hn,
    Category.assoc]

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
  {F G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)

/-- The original inverse-image maps define a morphism of the actual cone coefficient diagrams. -/
def coneCoefficientNatTrans : coneCoefficientFunctor X c F ⟶ coneCoefficientFunctor X c G where
  app i := (inverseImage (c.ι.app i).unop).map (η.app i)
  naturality i j a := triangleCoefficientMap_naturality (X.map a).unop
    (c.ι.app i).unop (c.ι.app j).unop
    (congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a))
    (diagramInverseTransition X F a) (diagramInverseTransition X G a)
    (η.app _) (η.app _) (diagramInverseTransition_naturality X η a)

variable [HasColimitsOfShape I (AbelianSheaf.{u, u + 1} c.pt.unop)]

/-- The resulting map on the actual coefficient colimits. -/
def coneCoefficientColimitMap : colimit (coneCoefficientFunctor X c F) ⟶
    colimit (coneCoefficientFunctor X c G) :=
  colim.map (coneCoefficientNatTrans X c η)

@[reassoc]
lemma coneCoefficientColimitMap_ι (i : I) :
    colimit.ι (coneCoefficientFunctor X c F) i ≫ coneCoefficientColimitMap X c η =
      (inverseImage (c.ι.app i).unop).map (η.app i) ≫
        colimit.ι (coneCoefficientFunctor X c G) i :=
  colimit.ι_map (coneCoefficientNatTrans X c η) i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
