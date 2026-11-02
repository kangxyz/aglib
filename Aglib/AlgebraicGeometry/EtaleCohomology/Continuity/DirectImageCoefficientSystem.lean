/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramDirectImageTriangleComp

/-! # Original direct-image coefficients and their counit cocone

An arbitrary coefficient on the actual cone point determines its original
direct images at all stages. The original right triangles give the system
laws and the original adjunction counits form its coefficient cocone.
No injectivity, torsion, scheme-limit continuity or colimit comparison
isomorphism is assumed or asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Cone

universe uI vI uA vA uB vB

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  {D : AdjunctionData A} {B : Type uB} [Category.{vB} B]
  (P : D.Cone B)

/-- An original apex object gives the system of its actual right images. -/
def rightImageSystem (K : B) : System D where
  obj i := (P.right i).obj K
  map a := (P.rightTriangle a).inv.app K
  map_id i := by
    rw [← P.right_id i K]
    exact (P.rightTriangle (𝟙 i)).inv_hom_id_app K
  map_comp {i j k} a b := by
    have h : (D.right a).mapIso ((P.rightTriangle b).app K) ≪≫
        (P.rightTriangle a).app K =
        (D.compIso a b).symm.app ((P.right k).obj K) ≪≫
          (P.rightTriangle (a ≫ b)).app K := by
      apply Iso.ext
      exact P.right_comp a b K
    have hi := congrArg Iso.inv h
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] using hi.symm

/-- Identity right-adjoint legs are compatible for the same original right-image system. -/
def rightImageIdentityFamily (K : B) : P.AdjointFamily (P.rightImageSystem K) K :=
  ⟨fun _ => 𝟙 _, fun {i j} a => by
    let e : (D.right a).obj ((P.right j).obj K) ≅ (P.right i).obj K :=
      (P.rightTriangle a).app K
    change 𝟙 ((P.right i).obj K) =
      e.inv ≫ (D.right a).map (𝟙 ((P.right j).obj K)) ≫ e.hom
    exact ((congrArg
      (fun f : (D.right a).obj ((P.right j).obj K) ⟶
          (D.right a).obj ((P.right j).obj K) => e.inv ≫ f ≫ e.hom)
      ((D.right a).map_id ((P.right j).obj K))).trans
        ((congrArg (fun f => e.inv ≫ f) (Category.id_comp e.hom)).trans
          e.inv_hom_id)).symm⟩

/-- The coefficient cocone is the transpose of the identity right-adjoint family. -/
def rightImageCounitCocone (K : B) : Cocone (P.coefficientFunctor (P.rightImageSystem K)) where
  pt := K
  ι := (P.coconeAdjointEquiv (P.rightImageSystem K) K).symm (P.rightImageIdentityFamily K)

/-- Each original cocone leg is exactly the original adjunction counit. -/
theorem rightImageCounitCocone_ι (K : B) (i : I) :
    (P.rightImageCounitCocone K).ι.app i = (P.adj i).counit.app K := by
  change ((P.adj i).homEquiv _ K).symm (𝟙 _) = _
  exact (P.adj i).homEquiv_symm_id K

end CategoryTheory.InjectiveSystem.AdjunctionData.Cone

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

/-- The coefficients are the actual direct images of the original apex sheaf. -/
def directImageCoefficientSystem (F : AbelianSheaf.{u, u + 1} c.pt.unop) :
    DiagramCoefficientSystem X :=
  (diagramConeAdjunctionData X c).rightImageSystem F

/-- The actual original stage coefficient, without changing its realization. -/
theorem directImageCoefficientSystem_obj (F : AbelianSheaf.{u, u + 1} c.pt.unop) (i : I) :
    (directImageCoefficientSystem X c F).obj i =
      (directImage (c.ι.app i).unop).obj F := rfl

/-- The system transition is the original inverse direct-image triangle. -/
theorem directImageCoefficientSystem_map (F : AbelianSheaf.{u, u + 1} c.pt.unop)
    {i j : I} (a : i ⟶ j) :
    (directImageCoefficientSystem X c F).map a =
      (diagramDirectImageTriangle X c a).inv.app F := rfl

/-- The original counit family on the original coefficient functor. -/
def directImageCounitCocone (F : AbelianSheaf.{u, u + 1} c.pt.unop) :
    Cocone (coneCoefficientFunctor X c (directImageCoefficientSystem X c F)) :=
  (diagramConeAdjunctionData X c).rightImageCounitCocone F

/-- The native leg is literally the original inverse/direct-image counit. -/
theorem directImageCounitCocone_ι (F : AbelianSheaf.{u, u + 1} c.pt.unop) (i : I) :
    (directImageCounitCocone X c F).ι.app i =
      (inverseImageAdjunction (c.ι.app i).unop).counit.app F :=
  (diagramConeAdjunctionData X c).rightImageCounitCocone_ι F i

/-- The original canonical comparison; no invertibility is assumed. -/
def directImageCounitComparison (F : AbelianSheaf.{u, u + 1} c.pt.unop)
    [HasColimit (coneCoefficientFunctor X c (directImageCoefficientSystem X c F))] :
    colimit (coneCoefficientFunctor X c (directImageCoefficientSystem X c F)) ⟶ F :=
  colimit.desc _ (directImageCounitCocone X c F)

/-- Every insertion followed by the canonical comparison is the original counit. -/
@[reassoc]
theorem ι_directImageCounitComparison (F : AbelianSheaf.{u, u + 1} c.pt.unop)
    [HasColimit (coneCoefficientFunctor X c (directImageCoefficientSystem X c F))] (i : I) :
    colimit.ι (coneCoefficientFunctor X c (directImageCoefficientSystem X c F)) i ≫
      directImageCounitComparison X c F =
        (inverseImageAdjunction (c.ι.app i).unop).counit.app F := by
  exact (colimit.ι_desc (directImageCounitCocone X c F) i).trans
    (directImageCounitCocone_ι X c F i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
