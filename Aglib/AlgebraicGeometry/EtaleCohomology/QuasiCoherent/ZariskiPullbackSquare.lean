/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiBaseChangeValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiPullbackSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiModuleCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionValues

/-! # The whole original coefficient/unit square across Zariski and étale sites

This is an equation of native sheaf maps. It retains the actual module unit,
the actual value lift and the actual geometric direct-image comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]

/-- The whole geometric coefficient formula on an arbitrary original open section. -/
theorem zariskiModuleIso_pullbackUnit_app (U : Y.Opens)
    (s : ((additiveCoefficient Y M).obj.obj (op ((opensToEtale Y).obj U)))) :
    (((zariskiModuleIso X ((pullback f).obj M)).hom.hom.app (op (f ⁻¹ᵁ U)))
      ((additiveBaseRestrictionIso f M).hom.app
        (op ((Scheme.Etale.forget X).obj ((opensToEtale X).obj (f ⁻¹ᵁ U))))
        ((additiveSectionsPresheaf Y M).map
          (Over.homMk (f ∣_ U) (morphismRestrict_ι f U)).op s))).down =
      ((pullbackPushforwardAdjunction f).unit.app M).app U
        ((((zariskiModuleIso Y M).hom.hom.app (op U)) s).down) := by
  rw [zariskiModuleIso_hom_down, additiveBaseRestrictionIso_hom_down,
    additiveSectionsPresheaf_map_down]
  rw [zariskiModuleIso_hom_down, baseRestrictionSectionsAddEquiv_apply,
    sectionsPresheaf_map_eq]
  change (openPullbackSectionsIso X ((pullback f).obj M) (f ⁻¹ᵁ U)).hom
    (Scheme.Modules.Hom.app
      ((pullbackComp (f ∣_ U) U.ι).hom.app M ≫
        (pullbackCongr (morphismRestrict_ι f U)).hom.app M ≫
        (pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M) ⊤
      ((((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((pullback U.ι).obj M)).app ⊤) s.down)) = _
  rw [← nativeSectionPullback_eq_unit]
  exact openPullbackSectionsIso_geometric f U M s.down


/-- The original module/étale coefficient comparison commutes with the full
geometric unit square, before applying any cohomology functor. -/
theorem zariskiModuleIso_pullbackUnit :
    (zariskiRestriction Y).map (additiveCoefficientPullbackUnit f M) ≫
      (zariskiRestrictionDirectImageIso f).hom.app
        (additiveCoefficient X ((pullback f).obj M)) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base).map
        (zariskiModuleIso X ((pullback f).obj M)).hom =
    (zariskiModuleIso Y M).hom ≫
      (Sheaf.BasisAcyclicity.valueLift.{u, u, u, u + 1}
        (Opens.grothendieckTopology Y)).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app M)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (additiveCoefficientPullbackUnit f M).hom.app
      (op ((opensToEtale Y).obj U.unop)) ≫
    ((zariskiRestrictionDirectImageIso f).hom.app
      (additiveCoefficient X ((pullback f).obj M))).hom.app U ≫
    (zariskiModuleIso X ((pullback f).obj M)).hom.hom.app
      (op (f ⁻¹ᵁ U.unop)) =
    (zariskiModuleIso Y M).hom.hom.app U ≫
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app M)).hom.app U)
  rw [zariskiRestrictionDirectImageIso_hom_app, ← Category.assoc,
    additiveCoefficientPullbackUnit_preimage]
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  simp only [AddCommGrpCat.comp_apply]
  have hmap {A B : AddCommGrpCat.{u}} (g : A ⟶ B) (t : ULift.{u + 1} A) :
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}.map g) t).down = g t.down := rfl
  have hforget {F G : Y.Modules} (g : F ⟶ G) (V : Y.Opens) (t : Γ(F, V)) :
      (((SheafOfModules.toSheaf Y.ringCatSheaf).map g).hom.app (op V)) t =
        g.app V t := rfl
  have hr := (hmap
    (((SheafOfModules.toSheaf Y.ringCatSheaf).map
      ((pullbackPushforwardAdjunction f).unit.app M)).hom.app U)
    (((zariskiModuleIso Y M).hom.hom.app U) s)).trans
      (hforget ((pullbackPushforwardAdjunction f).unit.app M) U.unop
        ((((zariskiModuleIso Y M).hom.hom.app U) s).down))
  have hl := zariskiModuleIso_pullbackUnit_app f M U.unop s
  simp only [op_unop] at hl
  have h := hl.trans hr.symm
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
