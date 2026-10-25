/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackSectionsBase
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients

/-! # Original coefficient triangles evaluated on a fixed étale test object -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
private lemma mapped_coefficient_triangle {C D : Type*} [Category C] [Category D]
    (Γ : C ⥤ D) {A B E H : C} {V W : D}
    (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ H) (d : H ⟶ E)
    (v : Γ.obj E ⟶ V) (w : Γ.obj H ⟶ W) (z : W ⟶ V)
    (h : a ≫ b = c ≫ d) (hn : Γ.map d ≫ v = w ≫ z) :
    Γ.map a ≫ (Γ.map b ≫ v) = (Γ.map c ≫ w) ≫ z := by
  rw [← Category.assoc, ← Γ.map_comp, h, Γ.map_comp, Category.assoc, hn, Category.assoc]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- The component of the actual relative-base comparison is the original composition map. -/
lemma pullbackSectionsBaseIso_hom_app {X S : Scheme.{u}} (p : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (U : Over S) :
    (pullbackSectionsBaseIso p F).hom.app (op U) =
      (globalSections U.left).map ((inverseImageComp p U.hom).hom.app F) := by
  change (𝟙 _ ≫ 𝟙 _ ≫
    (globalSections U.left).map ((inverseImageComp p U.hom).hom.app F) ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- The fixed-test-object comparison retains the original inverse-image composition map. -/
lemma pullbackSectionsBaseEtaleIso_hom_app {X S : Scheme.{u}} (p : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (U : S.Etale) :
    (pullbackSectionsBaseEtaleIso p F).hom.app (op U) =
      (globalSections U.left).map ((inverseImageComp p U.hom).hom.app F) ≫
        (pullbackSectionsEtaleEvaluationIso ((inverseImage p).obj F) U).hom := by
  change (𝟙 _ ≫ (pullbackSectionsBaseIso p F).hom.app
    (op ((Scheme.Etale.forget S).obj U)) ≫
      (pullbackSectionsEtaleEvaluationIso ((inverseImage p).obj F) U).hom) = _
  rw [Category.id_comp, pullbackSectionsBaseIso_hom_app]
  rfl

/-- A coefficient triangle commutes with further pullback along an actual scheme map. -/
lemma triangleCoefficientMap_postcompose {X Y S V : Scheme.{u}}
    (f : Y ⟶ X) (p : S ⟶ X) (q : S ⟶ Y) (h : q ≫ f = p) (l : V ⟶ S)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) :
    triangleCoefficientMap f (l ≫ p) (l ≫ q)
        ((Category.assoc l q f).trans (congrArg (fun t => l ≫ t) h)) φ ≫
        (inverseImageComp q l).hom.app G =
      (inverseImageComp p l).hom.app F ≫
        (inverseImage l).map (triangleCoefficientMap f p q h φ) := by
  subst p
  have ht := triangleCoefficientMap_comp f q (l ≫ (q ≫ f)) (l ≫ q) l
    (Category.assoc l q f) rfl φ (𝟙 ((inverseImage q).obj G))
  have hid := (inverseImage l).map_id ((inverseImage q).obj G)
  have hc : (inverseImageComp q l).hom.app G ≫
      𝟙 ((inverseImage l).obj ((inverseImage q).obj G)) =
        (inverseImageComp q l).hom.app G := Category.comp_id _
  simpa only [triangleCoefficientMap, pullbackTriangleIso, Iso.trans_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, eqToHom_refl, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc, hid, hc] using ht

/-- Changing the coefficient stage commutes with the original fixed-chart comparison. -/
lemma triangleCoefficientMap_baseEtale {X Y S : Scheme.{u}}
    (f : Y ⟶ X) (p : S ⟶ X) (q : S ⟶ Y) (h : q ≫ f = p)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (U : S.Etale) :
    (globalSections U.left).map (triangleCoefficientMap f (U.hom ≫ p) (U.hom ≫ q)
        ((Category.assoc U.hom q f).trans (congrArg (fun t => U.hom ≫ t) h)) φ) ≫
        (pullbackSectionsBaseEtaleIso q G).hom.app (op U) =
      (pullbackSectionsBaseEtaleIso p F).hom.app (op U) ≫
        (triangleCoefficientMap f p q h φ).hom.app (op U) := by
  rw [pullbackSectionsBaseEtaleIso_hom_app, pullbackSectionsBaseEtaleIso_hom_app]
  exact mapped_coefficient_triangle (globalSections U.left) _ _ _ _ _ _ _
    (triangleCoefficientMap_postcompose f p q h U.hom φ)
    (pullbackSectionsEtaleEvaluationIso_naturality (triangleCoefficientMap f p q h φ) U)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
