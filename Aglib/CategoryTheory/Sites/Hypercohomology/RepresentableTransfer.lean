/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoverEffacement

/-! # Natural section maps induced by free representables

An arrow between the original free abelian representables induces a natural
additive transformation between the original evaluation functors. This is an
ordinary sheaf construction: neither an Ext universe nor a derived category
is used. It also applies to sheaves obtained by restricting along product tests.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Hypercohomology

universe c h t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h t}]

/-- Precomposition with an original free-source arrow, evaluated additively. -/
def representedSectionsMap {T U : C}
    (a : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U) :
    (sheafSections J AddCommGrpCat.{max h t}).obj (op U) ⟶
      (sheafSections J AddCommGrpCat.{max h t}).obj (op T) where
  app F := AddCommGrpCat.ofHom <|
    (sectionsAddEquiv J T F).toAddMonoidHom.comp
      ((Preadditive.leftComp F a).comp (sectionsAddEquiv J U F).symm.toAddMonoidHom)
  naturality F G g := by
    ext x
    let b := (sectionsAddEquiv J U F).symm x
    have hb : (sectionsAddEquiv J U G).symm (g.hom.app (op U) x) = b ≫ g := by
      apply (sectionsAddEquiv J U G).injective
      exact ((sectionsAddEquiv J U G).apply_symm_apply _).trans
        ((sectionsEquiv_naturality J U b g).trans
          (congrArg (g.hom.app (op U))
            ((sectionsAddEquiv J U F).apply_symm_apply x))).symm
    change sectionsAddEquiv J T G
        (a ≫ (sectionsAddEquiv J U G).symm (g.hom.app (op U) x)) =
      g.hom.app (op T) (sectionsAddEquiv J T F (a ≫ b))
    rw [hb, ← Category.assoc]
    exact sectionsEquiv_naturality J T (a ≫ b) g

/-- The natural section transformation retains the exact represented arrow. -/
theorem representedSectionsMap_apply {T U : C}
    (a : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U)
    (F : Sheaf J AddCommGrpCat.{max h t}) (x : F.obj.obj (op U)) :
    (representedSectionsMap J a).app F x =
      sectionsAddEquiv J T F (a ≫ (sectionsAddEquiv J U F).symm x) := rfl

/-- Applying an actual represented site arrow is original restriction. -/
theorem representedSectionsMap_freeMap {T U : C} (f : T ⟶ U) :
    representedSectionsMap J ((freeAbelianSheafFunctor.{t} J).map f) =
      (sheafSections J AddCommGrpCat.{max h t}).map f.op := by
  ext F x
  exact (BasisAcyclicity.sectionsEquiv_precomp J f F
    ((sectionsAddEquiv J U F).symm x)).trans
      (congrArg (F.obj.map f.op) ((sectionsAddEquiv J U F).apply_symm_apply x))

/-- The source relation gives the rank relation on every original section group. -/
theorem representedSectionsMap_rank {T U : C}
    (a : freeAbelianSheaf.{t} J T ⟶ freeAbelianSheaf.{t} J U)
    (p : U ⟶ T) (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{t} J).map p = n • 𝟙 _)
    (F : Sheaf J AddCommGrpCat.{max h t}) :
    F.obj.map p.op ≫ (representedSectionsMap J a).app F = n • 𝟙 _ := by
  ext x
  let b := (sectionsAddEquiv J T F).symm x
  have hb : (sectionsAddEquiv J U F).symm (F.obj.map p.op x) =
      (freeAbelianSheafFunctor J).map p ≫ b := by
    apply (sectionsAddEquiv J U F).injective
    exact ((sectionsAddEquiv J U F).apply_symm_apply _).trans
      ((BasisAcyclicity.sectionsEquiv_precomp J p F b).trans
        (congrArg (F.obj.map p.op) ((sectionsAddEquiv J T F).apply_symm_apply x))).symm
  change sectionsAddEquiv J T F
    (a ≫ (sectionsAddEquiv J U F).symm (F.obj.map p.op x)) = n • x
  rw [hb, ← Category.assoc, ha, Preadditive.nsmul_comp, Category.id_comp,
    map_nsmul, AddEquiv.apply_symm_apply]

end CategoryTheory.Sheaf.Hypercohomology
