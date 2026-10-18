/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.Source

/-!
# Principal localization of the original coefficient-normalized top class

The original exact scalar-extension theorem is postcomposed with the actual
coefficient frame and original affine restriction comparison. The localized
coefficient frame is constructed from those same arrows. The formula keeps
the original quotient comparison and the actual same-list length cast.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (r : A)

/-- The localized frame uses the same scalar extension, affine coefficient comparison and
native scalar-extension unit at the coefficient ring. -/
def regularListPrincipalCoefficientFrame
    {L : ModuleCat.{u} A} {L' : ModuleCat.{u} (Localization.Away r)}
    (e : L ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars (algebraMap A (Localization.Away r))).obj L ≅ L') :
    L' ≅ ModuleCat.of (Localization.Away r) (Localization.Away r) :=
  θ.symm ≪≫ (ModuleCat.extendScalars (algebraMap A (Localization.Away r))).mapIso e ≪≫
    ModuleCat.extendScalarsAlgebraObjIso A (Localization.Away r) (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A (Localization.Away r)
      (Localization.Away r)).toModuleIso

variable [HasExt.{w} (ModuleCat.{u} A)]
  [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

/-- The original localized top class retains the original inverse coefficient frame. -/
theorem regularListPrincipalTopExtClass_coefficients
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s) (x : A)
    {L : ModuleCat.{u} A} {L' : ModuleCat.{u} (Localization.Away r)}
    (e : L ≅ ModuleCat.of A A)
    (θ : (ModuleCat.extendScalars (algebraMap A (Localization.Away r))).obj L ≅ L') :
    let S := Localization.Away r
    let φ := algebraMap A S
    let F : ModuleCat.{u} A ⥤ ModuleCat.{u} S := ModuleCat.extendScalars φ
    let : Module.Flat A S := IsLocalization.flat S (Submonoid.powers r)
    let : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat φ
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers r)))
    let : PreservesFiniteColimits F := ModuleCat.extendScalars_preservesFiniteColimits_of_flat φ
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers r)))
    let e' := regularListPrincipalCoefficientFrame r e θ
    ((Ext.mk₀ (ChainComplex.Koszul.scalarExtensionQuotientIso (S := S) s).inv).comp
      (((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).comp
        (Ext.mk₀ e.inv) (add_zero s.length)).mapExactFunctor F) (zero_add s.length)).comp
      (Ext.mk₀ θ.hom) (add_zero s.length) =
    (cast (congrArg (fun k => Ext.{z}
      (ModuleCat.of S (S ⧸ Ideal.ofList (s.map φ))) (ModuleCat.of S S) k)
      (List.length_map (as := s) φ))
      (ChainComplex.Koszul.topExtClass (s.map φ) (hs.of_flat (S := S))
        (ModuleCat.of S S) (φ x))).comp (Ext.mk₀ e'.inv) (add_zero s.length) := by
  intro S φ F hflat hlim hcol e'
  let ε := ModuleCat.extendScalarsAlgebraObjIso A S (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A S S).toModuleIso
  have hbase := ChainComplex.Koszul.topExtClass_map_principal r s hs x
  change ((Ext.mk₀ (ChainComplex.Koszul.scalarExtensionQuotientIso (S := S) s).inv).comp
      ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) x).mapExactFunctor F)
      (zero_add s.length)).comp (Ext.mk₀ ε.hom) (add_zero s.length) = _ at hbase
  have he := congrArg (fun ξ => ξ.comp (Ext.mk₀ e'.inv) (add_zero s.length)) hbase
  have hε : ε.hom ≫ e'.inv = F.map e.inv ≫ θ.hom := by
    change ε.hom ≫ (ε.inv ≫ F.map e.inv ≫ θ.hom) = _
    rw [Iso.hom_inv_id_assoc]
  simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hε] using he

end AlgebraicGeometry.Scheme.Modules
