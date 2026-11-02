/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UnitFrobenius
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.EtalePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionValues
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitInverse

/-! # The original unit Frobenius under étale coefficient pullback

Native unit-module composition preserves the actual structure-section
coordinates on every chart. Frobenius compatibility follows from the literal
prime-power formula and the original inverse-image/restriction comparison.
No flatness of Frobenius or replacement structure sheaf is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge isQuasicoherent_unit

variable {X Y : Scheme.{u}} (a : Y ⟶ X) [Etale a]

/-- Literal restriction followed by the original unit-module comparison
preserves the original structure-section coordinates. -/
theorem additiveUnitEtaleRestriction_structure_down (U : Y.Etale)
    (s : ((etaleRestriction a).obj
      (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf))).obj.obj (op U)) :
    ((additiveUnitStructureIso Y).hom.hom.app (op U)
      ((additiveCoefficientMap Y (pullbackUnitIso a).hom).hom.app (op U)
        ((additiveCoefficientEtaleRestrictionIso a
          (SheafOfModules.unit X.ringCatSheaf)).hom.hom.app (op U) s))).down =
    ((additiveUnitStructureIso X).hom.hom.app (op ((siteEtalePostcompose a).obj U)) s).down := by
  let s₁ : ULift.{u + 1}
      Γ((pullback U.hom).obj ((pullback a).obj (SheafOfModules.unit X.ringCatSheaf)), ⊤) :=
    (additiveBaseRestrictionIso a (SheafOfModules.unit X.ringCatSheaf)).hom.app
      (op (Over.mk U.hom)) s
  let s₂ : (additiveCoefficient Y (SheafOfModules.unit Y.ringCatSheaf)).obj.obj (op U) :=
    (additiveCoefficientMap Y (pullbackUnitIso a).hom).hom.app (op U) s₁
  have h₁ : s₁.down = Scheme.Modules.Hom.app
      ((pullbackComp U.hom a).inv.app (SheafOfModules.unit X.ringCatSheaf)) ⊤ s.down :=
    (additiveBaseRestrictionIso_hom_down a (SheafOfModules.unit X.ringCatSheaf)
      (Over.mk U.hom) s).trans
        (baseRestrictionSectionsAddEquiv_apply a (SheafOfModules.unit X.ringCatSheaf)
          (Over.mk U.hom) s.down)
  have h₂ : s₂.down = Scheme.Modules.Hom.app
      ((pullback U.hom).map (pullbackUnitIso a).hom) ⊤ s₁.down :=
    additiveCoefficientMap_down Y (pullbackUnitIso a).hom U s₁
  have hY := additiveUnitStructureIso_hom_down Y U s₂
  have hX := additiveUnitStructureIso_hom_down X ((siteEtalePostcompose a).obj U) s
  change ((additiveUnitStructureIso Y).hom.hom.app (op U) s₂).down = _
  refine hY.trans (?_ : Scheme.Modules.Hom.app (pullbackUnitIso U.hom).hom ⊤ s₂.down = _)
  rw [h₂, h₁]
  have hc := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ s.down)
    (pullbackUnitIso_comp_inv U.hom a)
  exact hc.trans hX.symm

variable (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)

/-- Frobenius commutes with the original literal-restriction coefficient arrow
and the actual pulled-back unit comparison. -/
theorem unitFrobenius_etaleRestriction :
    (etaleRestriction a).map (unitFrobenius X p hp hX) ≫
      (additiveCoefficientEtaleRestrictionIso a (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      additiveCoefficientMap Y (pullbackUnitIso a).hom =
    (additiveCoefficientEtaleRestrictionIso a (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      additiveCoefficientMap Y (pullbackUnitIso a).hom ≫ unitFrobenius Y p hp hY := by
  apply (cancel_mono (additiveUnitStructureIso Y).hom).mp
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  let s' := (unitFrobenius X p hp hX).hom.app (op ((siteEtalePostcompose a).obj U.unop)) s
  let t := (additiveCoefficientMap Y (pullbackUnitIso a).hom).hom.app U
    ((additiveCoefficientEtaleRestrictionIso a
      (SheafOfModules.unit X.ringCatSheaf)).hom.hom.app U s)
  change ((additiveUnitStructureIso Y).hom.hom.app U
    ((additiveCoefficientMap Y (pullbackUnitIso a).hom).hom.app U
      ((additiveCoefficientEtaleRestrictionIso a
        (SheafOfModules.unit X.ringCatSheaf)).hom.hom.app U s'))).down =
    ((additiveUnitStructureIso Y).hom.hom.app U
      ((unitFrobenius Y p hp hY).hom.app U t)).down
  exact (additiveUnitEtaleRestriction_structure_down a U.unop s').trans
    ((unitFrobenius_structure_apply X p hp hX ((siteEtalePostcompose a).obj U.unop) s).trans
      ((congrArg (fun z : Γ(U.unop.left, ⊤) => z ^ p)
        (additiveUnitEtaleRestriction_structure_down a U.unop s).symm).trans
          (unitFrobenius_structure_apply Y p hp hY U.unop t).symm))

/-- The whole original additive Frobenius square for étale inverse image. -/
theorem unitFrobenius_pullback :
    (inverseImage a).map (unitFrobenius X p hp hX) ≫
      additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf) ≫
      additiveCoefficientMap Y (pullbackUnitIso a).hom =
    additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf) ≫
      additiveCoefficientMap Y (pullbackUnitIso a).hom ≫ unitFrobenius Y p hp hY := by
  rw [additiveCoefficientPullback_eq_etaleRestriction]
  simp only [Category.assoc]
  rw [(inverseImageEtaleIso a).hom.naturality_assoc,
    unitFrobenius_etaleRestriction]

omit [Etale a] in
include a hX in
/-- The characteristic equation is transported by the actual global ring map. -/
theorem primeCast_eq_zero_appTop : (p : Γ(Y, ⊤)) = 0 := by
  have h := congrArg a.appTop.hom hX
  simpa only [map_natCast, map_zero] using h

/-- The same whole square, with the target characteristic proof supplied by
the actual global-section ring map rather than an extra geometric hypothesis. -/
theorem unitFrobenius_pullback_appTop :
    (inverseImage a).map (unitFrobenius X p hp hX) ≫
      additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf) ≫
      additiveCoefficientMap Y (pullbackUnitIso a).hom =
    additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf) ≫
      additiveCoefficientMap Y (pullbackUnitIso a).hom ≫
        unitFrobenius Y p hp (primeCast_eq_zero_appTop a p hX) :=
  unitFrobenius_pullback a p hp hX (primeCast_eq_zero_appTop a p hX)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
