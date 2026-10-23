/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSections

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveTransport

/-! # Additive restriction of the original section coefficient -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent]

/-- The original Hom restriction comparison has the original pullback-composition components. -/
theorem homBaseRestrictionIso_hom_hom (T : Over Y)
    (h : (homPresheaf X F).obj (op ((Over.map f).obj T))) :
    (((homBaseRestrictionIso f F).hom.app (op T)) h).hom =
      (pullback T.hom).map (pullbackUnitIso f).inv ≫
        (pullbackComp T.hom f).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        h.hom ≫ (pullbackComp T.hom f).inv.app F := by
  change (pullback T.hom).map (pullbackUnitIso f).inv ≫
    (pullbackPseudofunctor.mapComp' f.op.toLoc T.hom.op.toLoc
      (T.hom ≫ f).op.toLoc).inv.toNatTrans.app (SheafOfModules.unit X.ringCatSheaf) ≫
    h.hom ≫ (pullbackPseudofunctor.mapComp' f.op.toLoc T.hom.op.toLoc
      (T.hom ≫ f).op.toLoc).hom.toNatTrans.app F = _
  have h₁ := pullbackPseudofunctor_mapComp'_inv_app f T.hom (T.hom ≫ f) rfl
    (SheafOfModules.unit X.ringCatSheaf)
  have h₂ := pullbackPseudofunctor_mapComp'_hom_app f T.hom (T.hom ≫ f) rfl F
  refine (congrArg₂ (fun p q => (pullback T.hom).map (pullbackUnitIso f).inv ≫
    p ≫ h.hom ≫ q) h₁ h₂).trans ?_
  simp [pullbackCongr]

/-- The original base restriction on sections is evaluation of the native composition inverse. -/
theorem sectionsBaseRestrictionIso_hom_apply (T : Over Y)
    (s : Γ((pullback (T.hom ≫ f)).obj F, ⊤)) :
    (sectionsBaseRestrictionIso f F).hom.app (op T) s =
      Scheme.Modules.Hom.app ((pullbackComp T.hom f).inv.app F) ⊤ s := by
  change sectionsEquiv Y ((pullback f).obj F) T
    ((homBaseRestrictionIso f F).hom.app (op T)
      ((sectionsEquiv X F ((Over.map f).obj T)).symm s)) = _
  rw [sectionsEquiv_apply, homBaseRestrictionIso_hom_hom]
  change unitHomGlobalSectionsEquiv T.left ((pullback T.hom).obj ((pullback f).obj F))
    ((pullbackUnitIso T.hom).inv ≫ (pullback T.hom).map (pullbackUnitIso f).inv ≫
      (pullbackComp T.hom f).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      ((pullbackUnitIso (T.hom ≫ f)).hom ≫
        (unitHomGlobalSectionsEquiv T.left ((pullback (T.hom ≫ f)).obj F)).symm s) ≫
      (pullbackComp T.hom f).inv.app F) = _
  rw [← Category.assoc, ← pullbackUnitIso_inv_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc]
  rw [unitHomGlobalSectionsEquiv_naturality, Equiv.apply_symm_apply]
  rfl

/-- The section formula with an arbitrary opposite-category index. -/
theorem sectionsBaseRestrictionIso_hom_apply_op (T : (Over Y)ᵒᵖ)
    (s : Γ((pullback (T.unop.hom ≫ f)).obj F, ⊤)) :
    (sectionsBaseRestrictionIso f F).hom.app T s =
      Scheme.Modules.Hom.app ((pullbackComp T.unop.hom f).inv.app F) ⊤ s :=
  sectionsBaseRestrictionIso_hom_apply f F T.unop s

/-- Each additive component is the actual composition isomorphism evaluated on sections. -/
def baseRestrictionSectionsAddEquiv (T : Over Y) :
    Γ((pullback (T.hom ≫ f)).obj F, ⊤) ≃+
      Γ((pullback T.hom).obj ((pullback f).obj F), ⊤) :=
  ((SheafOfModules.evaluation T.left.ringCatSheaf (op ⊤)).mapIso
    ((pullbackComp T.hom f).app F).symm).toLinearEquiv.toAddEquiv

omit [F.IsQuasicoherent] in
/-- Evaluation of the additive equivalence is the original composition inverse. -/
theorem baseRestrictionSectionsAddEquiv_apply (T : Over Y)
    (s : Γ((pullback (T.hom ≫ f)).obj F, ⊤)) :
    baseRestrictionSectionsAddEquiv f F T s =
      Scheme.Modules.Hom.app ((pullbackComp T.hom f).inv.app F) ⊤ s := by
  change ((SheafOfModules.evaluation T.left.ringCatSheaf (op ⊤)).mapIso
    ((pullbackComp T.hom f).app F).symm).toLinearEquiv s = _
  rw [CategoryTheory.Iso.toLinearEquiv_apply, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
  rfl

/-- The genuine additive coefficient restricts to the coefficient of the native pullback. -/
def additiveBaseRestrictionIso :
    (Over.map f).op ⋙ additiveSectionsPresheaf X F ≅
      additiveSectionsPresheaf Y ((pullback f).obj F) :=
  liftTransportIsoOfTypeIso (homPresheaf X F)
    (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj F, ⊤))
    (sectionsEquiv X F) (fun k => sectionsAddHom X F k)
    (fun k s => sectionsAddHom_apply X F k s)
    (homPresheaf Y ((pullback f).obj F))
    (fun T => AddCommGrpCat.of Γ((pullback T.hom).obj ((pullback f).obj F), ⊤))
    (sectionsEquiv Y ((pullback f).obj F))
    (fun k => sectionsAddHom Y ((pullback f).obj F) k)
    (fun k s => sectionsAddHom_apply Y ((pullback f).obj F) k s)
    (Over.map f) (sectionsBaseRestrictionIso f F) (baseRestrictionSectionsAddEquiv f F)
    (fun T s => (baseRestrictionSectionsAddEquiv_apply f F T s).trans
      (sectionsBaseRestrictionIso_hom_apply f F T s).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
