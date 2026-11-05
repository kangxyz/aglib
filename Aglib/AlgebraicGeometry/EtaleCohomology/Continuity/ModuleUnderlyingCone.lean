/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleRightTail
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor

/-! # Original cone coefficient diagrams after forgetting scalars

The native image-adjunction Hom equation compares the actual coefficient maps,
using only original right triangles. This avoids requiring a separately chosen
left triangle to be definitionally equal to the abelian triangle.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R] {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

/-- The original direct-image composition arrow retains its underlying abelian arrow. -/
theorem underlying_directImageCompIso_hom {S T V : Scheme.{u}}
    (f : T ⟶ S) (g : V ⟶ T) (F : Coefficient R V) :
    (underlying R S).map ((directImageCompIso R f g).hom.app F) =
      (EtaleCohomology.directImageCompIso f g).hom.app ((underlying R V).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- The actual right triangle, including the cone equation transport, is unchanged. -/
theorem underlying_cone_rightTriangle_hom {i j : I} (a : i ⟶ j)
    (F : Coefficient R c.pt.unop) :
    (underlying R (X.obj i).unop).map
        (((diagramConeAdjunctionData R X c).rightTriangle a).hom.app F) =
      ((Continuity.diagramConeAdjunctionData X c).rightTriangle a).hom.app
        ((underlying R c.pt.unop).obj F) := by
  simp only [diagramConeAdjunctionData, Continuity.diagramConeAdjunctionData,
    InjectiveSystem.AdjunctionData.Cone.ofCocone,
    InjectiveSystem.AdjunctionData.Cone.coconeRightTriangle,
    schemeAdjunctionData, Continuity.schemeAdjunctionData, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToHom_app,
    Functor.map_comp, eqToHom_map, underlying_directImageCompIso_hom]
  rfl

/-- The original inverse-image comparison on the actual coefficient at a cone stage. -/
def coneCoefficientUnderlyingIsoApp (F : DiagramCoefficientSystem R X) (i : I) :
    (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F)).obj i ≅
      (underlying R c.pt.unop).obj ((coneCoefficientFunctor R X c F).obj i) := by
  let f : c.pt.unop ⟶ (X.obj i).unop := (c.ι.app i).unop
  exact ((ModuleCat.Sheaf.pullbackUnderlyingIso R (siteBaseChange f)
    (X.obj i).unop.smallEtaleTopology c.pt.unop.smallEtaleTopology).app (F.obj i)).symm

/-- The original coefficient maps commute with scalar forgetting, by transposing
both sides through the same original stage-to-apex adjunction. -/
theorem coneCoefficientUnderlyingIsoApp_naturality (F : DiagramCoefficientSystem R X)
    {i j : I} (a : i ⟶ j) :
    (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F)).map a ≫
        (coneCoefficientUnderlyingIsoApp R X c F j).hom =
      (coneCoefficientUnderlyingIsoApp R X c F i).hom ≫
        (underlying R c.pt.unop).map ((coneCoefficientFunctor R X c F).map a) := by
  let PM := diagramConeAdjunctionData R X c
  let PA := Continuity.diagramConeAdjunctionData X c
  apply ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _).injective
  have ha := PA.coefficientMap_homEquiv (underlyingSystem R X F) a
    (coneCoefficientUnderlyingIsoApp R X c F j).hom
  have hi := underlying_homEquiv R (c.ι.app i).unop (F.obj i)
    ((coneCoefficientFunctor R X c F).obj j) ((coneCoefficientFunctor R X c F).map a)
  have hm := PM.coefficientMap_homEquiv F a (𝟙 ((coneCoefficientFunctor R X c F).obj j))
  erw [Category.comp_id] at hm
  have hm' := congrArg ((underlying R (X.obj i).unop).map) hm
  rw [(underlying R (X.obj i).unop).map_comp,
    (underlying R (X.obj i).unop).map_comp] at hm'
  have ht := underlying_cone_rightTriangle_hom R X c a
    ((coneCoefficientFunctor R X c F).obj j)
  have hmt := congrArg (fun q =>
    (underlying R (X.obj i).unop).map (F.map a) ≫
      (underlying R (X.obj i).unop).map (((diagramAdjunctionData R X).right a).map
        ((PM.adj j).homEquiv _ _ (𝟙 ((coneCoefficientFunctor R X c F).obj j)))) ≫ q) ht
  have hj := underlying_homEquiv R (c.ι.app j).unop (F.obj j)
    ((coneCoefficientFunctor R X c F).obj j) (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hj
  have hja := congrArg (fun q =>
    (underlyingSystem R X F).map a ≫
      ((Continuity.diagramAdjunctionData X).right a).map q ≫
      (PA.rightTriangle a).hom.app
        ((underlying R c.pt.unop).obj ((coneCoefficientFunctor R X c F).obj j))) hj.symm
  exact ha.trans (hja.trans ((hm'.trans hmt).symm.trans hi))

/-- The actual native cone coefficient diagram has precisely its original
abelian coefficient diagram after forgetting scalars. -/
def coneCoefficientUnderlyingIso (F : DiagramCoefficientSystem R X) :
    Continuity.coneCoefficientFunctor X c (underlyingSystem R X F) ≅
      coneCoefficientFunctor R X c F ⋙ underlying R c.pt.unop :=
  NatIso.ofComponents (coneCoefficientUnderlyingIsoApp R X c F)
    (fun a => coneCoefficientUnderlyingIsoApp_naturality R X c F a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
