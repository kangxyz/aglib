/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Coefficient comparison for the original slice lower shriek

The comparison uses the existing hom-indexed coproduct extension and native
sheafification. Only coproducts at the site-hom universe are required.
-/

@[expose] public noncomputable section

universe v u vA uA vB uB

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  [HasCoproducts.{v} A] [HasCoproducts.{v} B]
  (F : A ⥤ B) [∀ (ι : Type v), PreservesColimitsOfShape (Discrete ι) F] (U : C)

-- Native coproduct choices agree through proof instances under opaque colimit selection.
set_option backward.isDefEq.respectTransparency false in
/-- The coefficient comparison on the original coproduct presheaf. -/
def coproductExtensionCoefficientMap (G : (Over U)ᵒᵖ ⥤ A) :
    coproductExtensionObj U (G ⋙ F) ⟶ coproductExtensionObj U G ⋙ F where
  app V := Limits.Sigma.desc (fun f : V.unop ⟶ U ↦
    F.map (Limits.Sigma.ι (summands U G V.unop) f))
  naturality {V W} h := by
    apply Limits.Sigma.hom_ext
    intro f
    change Limits.Sigma.ι (summands U (G ⋙ F) V.unop) f ≫
      (coproductRestriction U (G ⋙ F) h.unop ≫
        Limits.Sigma.desc (fun g : W.unop ⟶ U ↦
          F.map (Limits.Sigma.ι (summands U G W.unop) g))) =
      Limits.Sigma.ι (summands U (G ⋙ F) V.unop) f ≫
        (Limits.Sigma.desc (fun g : V.unop ⟶ U ↦
          F.map (Limits.Sigma.ι (summands U G V.unop) g)) ≫
          F.map (coproductRestriction U G h.unop))
    rw [ι_coproductRestriction_assoc, Limits.Sigma.ι_comp_desc,
      Limits.Sigma.ι_comp_desc_assoc]
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (ι_coproductRestriction U G h.unop f)).symm.trans
        (F.map_comp _ _))

-- Native coproduct choices agree through proof instances under opaque colimit selection.
set_option backward.isDefEq.respectTransparency false in
instance (G : (Over U)ᵒᵖ ⥤ A) :
    IsIso (coproductExtensionCoefficientMap F U G) := by
  let (V : Cᵒᵖ) : IsIso ((coproductExtensionCoefficientMap F U G).app V) := by
    change IsIso (sigmaComparison F (summands U G V.unop))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

-- Native coproduct choices agree through proof instances under opaque colimit selection.
set_option backward.isDefEq.respectTransparency false in
/-- Coefficient change commutes with the native hom-sized coproduct extension. -/
def coproductExtensionCoefficientIso :
    (Functor.whiskeringRight (Over U)ᵒᵖ A B).obj F ⋙ coproductExtension U ≅
      coproductExtension U ⋙ (Functor.whiskeringRight Cᵒᵖ A B).obj F :=
  NatIso.ofComponents (fun G ↦ asIso (coproductExtensionCoefficientMap F U G)) (by
    intro G H α
    ext V
    apply Limits.Sigma.hom_ext
    intro f
    change Limits.Sigma.ι _ f ≫
      (Limits.Sigma.map (fun g ↦ F.map (α.app (op (Over.mk g)))) ≫
        sigmaComparison F (summands U H V.unop)) =
      Limits.Sigma.ι _ f ≫ (sigmaComparison F (summands U G V.unop) ≫
        F.map (Limits.Sigma.map (fun g ↦ α.app (op (Over.mk g)))))
    dsimp only [summands, Functor.comp_obj]
    simp only [Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison,
      ι_comp_sigmaComparison_assoc, ← F.map_comp, Limits.Sigma.ι_map])

variable (J : GrothendieckTopology C)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  [J.HasSheafCompose F] [(J.over U).HasSheafCompose F]
  [J.PreservesSheafification F]

/-- The original slice lower shriek commutes with coefficient change. -/
def lowerShriekCoefficientIso :
    sheafCompose (J.over U) F ⋙ lowerShriek J B U ≅
      lowerShriek J A U ⋙ sheafCompose J F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sheafToPresheaf (J.over U) A)
        (coproductExtensionCoefficientIso F U)) (presheafToSheaf J B) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (J.over U) A ⋙ coproductExtension U)
      (sheafComposeNatIso J F (sheafificationAdjunction J A)
        (sheafificationAdjunction J B)) ≪≫
    (Functor.associator _ _ _).symm

-- Native coproduct choices agree through proof instances under opaque colimit selection.
set_option backward.isDefEq.respectTransparency false in
/-- The actual lower-shriek unit is the designated summand followed by sheafification. -/
theorem lowerShriekAdjunction_unit_app (G : Sheaf (J.over U) A)
    (V : (Over U)ᵒᵖ) :
    ((lowerShriekAdjunction J A U).unit.app G).hom.app V =
      Limits.Sigma.ι (summands U G.obj V.unop.left) V.unop.hom ≫
        (toSheafify J (coproductExtensionObj U G.obj)).app (op V.unop.left) := by
  rw [← (lowerShriekAdjunction J A U).homEquiv_id G,
    lowerShriekAdjunction_homEquiv_app]
  exact congrArg
    (fun α ↦ Limits.Sigma.ι (summands U G.obj V.unop.left) V.unop.hom ≫
      α.app (op V.unop.left))
    ((sheafificationAdjunction J A).homEquiv_id (coproductExtensionObj U G.obj))

-- Native coproduct choices agree through proof instances under opaque colimit selection.
set_option backward.isDefEq.respectTransparency false in
/-- Coefficient comparison retains the original lower-shriek adjunction unit. -/
theorem lowerShriekCoefficientIso_unit (G : Sheaf (J.over U) A) :
    (lowerShriekAdjunction J B U).unit.app ((sheafCompose (J.over U) F).obj G) ≫
        (J.overPullback B U).map ((lowerShriekCoefficientIso F U J).hom.app G) =
      (sheafCompose (J.over U) F).map ((lowerShriekAdjunction J A U).unit.app G) := by
  ext V
  change ((lowerShriekAdjunction J B U).unit.app
      ((sheafCompose (J.over U) F).obj G)).hom.app V ≫
      ((lowerShriekCoefficientIso F U J).hom.app G).hom.app (op V.unop.left) =
    F.map (((lowerShriekAdjunction J A U).unit.app G).hom.app V)
  rw [lowerShriekAdjunction_unit_app, lowerShriekAdjunction_unit_app]
  simp only [lowerShriekCoefficientIso, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, NatTrans.id_app]
  erw [Category.id_comp]
  change (Limits.Sigma.ι (summands U (G.obj ⋙ F) V.unop.left) V.unop.hom ≫
      (toSheafify J (coproductExtensionObj U (G.obj ⋙ F))).app (op V.unop.left)) ≫
      ((sheafifyMap J (coproductExtensionCoefficientMap F U G.obj)).app
        (op V.unop.left) ≫
        (sheafifyComposeIso J F (coproductExtensionObj U G.obj)).hom.app
          (op V.unop.left)) = _
  have hn := congrArg (fun α ↦ α.app (op V.unop.left))
    (toSheafify_naturality J (coproductExtensionCoefficientMap F U G.obj))
  have hc := congrArg (fun α ↦ α.app (op V.unop.left))
    (sheafComposeIso_hom_fac J F (coproductExtensionObj U G.obj))
  simp only [NatTrans.comp_app] at hn hc
  simp only [Category.assoc]
  rw [← Category.assoc ((toSheafify J _).app (op V.unop.left)), ← hn]
  simp only [Category.assoc]
  rw [hc]
  simp only [Functor.whiskerRight_app, coproductExtensionCoefficientMap,
    Limits.Sigma.ι_comp_desc_assoc, F.map_comp]

end CategoryTheory.Sheaf.SliceCohomology
