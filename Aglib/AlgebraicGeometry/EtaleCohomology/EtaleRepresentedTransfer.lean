/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleProductTests
public import Aglib.CategoryTheory.Sites.Hypercohomology.RepresentableTransfer

/-! # Represented transfers induce natural sheaf transfers

A map from the free terminal sheaf to the free sheaf on an actual etale object
acts on product-test sheaves. Product symmetry and the terminal product
comparison turn this into a natural transformation from original restriction
followed by direct image to the identity. Its rank equation is normalized by
the original inverse-image/direct-image adjunction unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.Hypercohomology

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)
  (a : freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) (etaleTerminal X) ⟶
    freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) U)

/-- Evaluation of a fixed represented transfer on original product-test sheaves. -/
def etaleRepresentedRestrictionTrace :
    etaleProductSheaf U ⟶ 𝟭 (AbelianSheaf.{u, u + 1} X) where
  app F := ⟨{
    app V := F.obj.map (etaleProductSymmetry V.unop U).hom.op ≫
      (representedSectionsMap (Scheme.smallEtaleTopology X) a).app
        ((etaleProductSheaf V.unop).obj F) ≫
      F.obj.map (etaleProductTerminalIso V.unop).inv.op
    naturality V W f := by
      let R := representedSectionsMap (Scheme.smallEtaleTopology X) a
      have hs :
          F.obj.map ((etaleProductTest U).map f.unop).op ≫
            F.obj.map (etaleProductSymmetry W.unop U).hom.op =
          F.obj.map (etaleProductSymmetry V.unop U).hom.op ≫
            F.obj.map ((etaleProductMap f.unop).app U).op := by
        rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
          etaleProductSymmetry_naturality]
      have ht :
          F.obj.map ((etaleProductMap f.unop).app (etaleTerminal X)).op ≫
            F.obj.map (etaleProductTerminalIso W.unop).inv.op =
          F.obj.map (etaleProductTerminalIso V.unop).inv.op ≫ F.obj.map f := by
        simpa only [op_comp, F.obj.map_comp, Quiver.Hom.op_unop] using
          congrArg (fun k => F.obj.map k.op)
            (etaleProductTerminalIso_inv_naturality f.unop)
      have hr := R.naturality ((etaleProductSheafMap f.unop).app F)
      change F.obj.map ((etaleProductTest U).map f.unop).op ≫
          (F.obj.map (etaleProductSymmetry W.unop U).hom.op ≫
            R.app ((etaleProductSheaf W.unop).obj F) ≫
            F.obj.map (etaleProductTerminalIso W.unop).inv.op) =
        (F.obj.map (etaleProductSymmetry V.unop U).hom.op ≫
          R.app ((etaleProductSheaf V.unop).obj F) ≫
          F.obj.map (etaleProductTerminalIso V.unop).inv.op) ≫ F.obj.map f
      change F.obj.map ((etaleProductMap f.unop).app U).op ≫
          R.app ((etaleProductSheaf W.unop).obj F) =
        R.app ((etaleProductSheaf V.unop).obj F) ≫
          F.obj.map ((etaleProductMap f.unop).app (etaleTerminal X)).op at hr
      exact ((CommSq.mk hs.symm).horiz_comp
        ((CommSq.mk hr.symm).horiz_comp (CommSq.mk ht.symm))).w.symm }⟩
  naturality F G g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hs := g.hom.naturality (etaleProductSymmetry V.unop U).hom.op
    have ht := g.hom.naturality (etaleProductTerminalIso V.unop).inv.op
    have hr := (representedSectionsMap (Scheme.smallEtaleTopology X) a).naturality
      ((etaleProductSheaf V.unop).map g)
    change g.hom.app (op ((etaleProductTest U).obj V.unop)) ≫
        (G.obj.map (etaleProductSymmetry V.unop U).hom.op ≫ _ ≫ _) =
      (F.obj.map (etaleProductSymmetry V.unop U).hom.op ≫ _ ≫ _) ≫ g.hom.app V
    change g.hom.app (op ((etaleProductTest V.unop).obj U)) ≫
        (representedSectionsMap (Scheme.smallEtaleTopology X) a).app
          ((etaleProductSheaf V.unop).obj G) =
      (representedSectionsMap (Scheme.smallEtaleTopology X) a).app
          ((etaleProductSheaf V.unop).obj F) ≫
        g.hom.app (op ((etaleProductTest V.unop).obj (etaleTerminal X))) at hr
    exact ((CommSq.mk hs).horiz_comp
      ((CommSq.mk hr.symm).horiz_comp (CommSq.mk ht))).w.symm

/-- The represented rank relation gives the actual restriction-adjunction unit relation. -/
theorem etaleRepresentedRestrictionTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
      ((etaleTerminalIsTerminal X).from U) = n • 𝟙 _)
    (F : AbelianSheaf.{u, u + 1} X) :
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) (Scheme.smallEtaleTopology U.left)
      (Scheme.smallEtaleTopology X)).unit.app F ≫
        (etaleRepresentedRestrictionTrace U a).app F = n • 𝟙 F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let R := representedSectionsMap (Scheme.smallEtaleTopology X) a
  let e := etaleProductTerminalIso V.unop
  let r : F.obj.obj (op ((etaleProductTest V.unop).obj U)) ⟶
      F.obj.obj (op ((etaleProductTest V.unop).obj (etaleTerminal X))) :=
    R.app ((etaleProductSheaf V.unop).obj F)
  let m : F.obj.obj (op ((etaleProductTest V.unop).obj (etaleTerminal X))) ⟶
      F.obj.obj (op ((etaleProductTest V.unop).obj U)) :=
    F.obj.map ((etaleProductTest V.unop).map ((etaleTerminalIsTerminal X).from U)).op
  have hp :
      F.obj.map ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).counit.app V.unop).op ≫
        F.obj.map (etaleProductSymmetry V.unop U).hom.op =
      F.obj.map e.hom.op ≫ m := by
    rw [← F.obj.map_comp, ← op_comp, etaleProductSymmetry_counit]
    change F.obj.map (etaleProductSnd V.unop U).op =
      F.obj.map e.hom.op ≫
        F.obj.map ((etaleProductTest V.unop).map ((etaleTerminalIsTerminal X).from U)).op
    rw [← F.obj.map_comp, ← op_comp, etaleProductTest_terminal]
  have hr := representedSectionsMap_rank (Scheme.smallEtaleTopology X) a
    ((etaleTerminalIsTerminal X).from U) n ha ((etaleProductSheaf V.unop).obj F)
  change m ≫ r =
    n • 𝟙 (F.obj.obj (op ((etaleProductTest V.unop).obj (etaleTerminal X)))) at hr
  change F.obj.map
      ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).counit.app V.unop).op ≫
      (F.obj.map (etaleProductSymmetry V.unop U).hom.op ≫ r ≫ F.obj.map e.inv.op) =
        n • 𝟙 (F.obj.obj V)
  rw [← Category.assoc, hp, Category.assoc, ← Category.assoc _ _ (F.obj.map e.inv.op), hr]
  rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    ← F.obj.map_comp, ← op_comp, e.inv_hom_id, op_id, F.obj.map_id]

/-- The natural sheaf transfer with the original inverse image, not a replacement restriction. -/
def etaleRepresentedTrace :
    inverseImage (X := X) (S := U.left) U.hom ⋙
      directImage (X := X) (S := U.left) U.hom ⟶ 𝟭 (AbelianSheaf.{u, u + 1} X) :=
  Functor.whiskerRight (inverseImageEtaleIso (X := X) (S := U.left) U.hom).hom
    (directImage (X := X) (S := U.left) U.hom) ≫
    etaleRepresentedRestrictionTrace U a

/-- The exact original adjunction unit has composite equal to the represented rank. -/
theorem etaleRepresentedTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
      ((etaleTerminalIsTerminal X).from U) = n • 𝟙 _)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageAdjunction (X := X) (S := U.left) U.hom).unit.app F ≫
      (etaleRepresentedTrace U a).app F = n • 𝟙 F := by
  change (inverseImageAdjunction (X := X) (S := U.left) U.hom).unit.app F ≫
    ((directImage (X := X) (S := U.left) U.hom).map
      ((inverseImageEtaleIso (X := X) (S := U.left) U.hom).hom.app F) ≫
      (etaleRepresentedRestrictionTrace U a).app F) = _
  rw [← Category.assoc, inverseImageEtaleIso_unit]
  exact etaleRepresentedRestrictionTrace_rank U a n ha F

end AlgebraicGeometry.Scheme.EtaleCohomology
