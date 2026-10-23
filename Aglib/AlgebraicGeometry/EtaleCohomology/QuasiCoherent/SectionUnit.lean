/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsNaturality

/-! # The original geometric unit on pullback sections -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The unit-Hom description of section pullback has the original geometric adjoint. -/
theorem nativeSectionPullback_adjoint {U V : Scheme.{u}} (f : U ⟶ V) (M : V.Modules)
    (s : SheafOfModules.unit V.ringCatSheaf ⟶ M) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (pushforward f).map ((pullbackUnitIso f).inv ≫ (pullback f).map s) =
      s ≫ (pullbackPushforwardAdjunction f).unit.app M := by
  have hu := pullbackUnitIso_homEquiv f
  change (pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit V.ringCatSheaf) ≫
    (pushforward f).map (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom at hu
  rw [← hu, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]
  exact ((pullbackPushforwardAdjunction f).unit.naturality s).symm

/-- The section restriction is evaluation of the original pullback/pushforward unit. -/
theorem nativeSectionPullback_eq_unit {U V : Scheme.{u}} (f : U ⟶ V) (M : V.Modules)
    (s : Γ(M, ⊤)) :
    nativeSectionPullback f M s =
      (((pullbackPushforwardAdjunction f).unit.app M).app ⊤) s := by
  have h := nativeSectionPullback_adjoint f M ((unitHomGlobalSectionsEquiv V M).symm s)
  have he := congrArg (fun k : SheafOfModules.unit V.ringCatSheaf ⟶
      (pushforward f).obj ((pullback f).obj M) =>
    unitHomGlobalSectionsEquiv V ((pushforward f).obj ((pullback f).obj M)) k) h
  change Scheme.Modules.Hom.app
      ((pullbackUnitIso f).inv ≫
        (pullback f).map ((unitHomGlobalSectionsEquiv V M).symm s)) ⊤
        (f.appTop.hom 1) =
    (((pullbackPushforwardAdjunction f).unit.app M).app ⊤)
      (unitHomGlobalSectionsEquiv V M ((unitHomGlobalSectionsEquiv V M).symm s)) at he
  simpa only [map_one, Equiv.apply_symm_apply, nativeSectionPullback,
    unitHomGlobalSectionsEquiv_apply] using he

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
