/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic

/-! # The original native module unit controls scalar compatibility

The native unit is linear for the original constant scalars. Its underlying
inverse is the original abelian sheafification counit, so that counit is
compatible with noncentral left scalars without a linear coefficient category.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat.Sheaf.ConstantRing
universe u v r w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
/-- The actual underlying comparison carries original scalar sections to original scalars. -/
theorem constantModuleSheafificationUnderlyingIso_hom_smul
    (M : (moduleSheafProperty.{u, v, r, w} J
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).FullSubcategory)
    (U : Cᵒᵖ) (a : Λ)
    (x : ((constantModuleSheafificationEquivalence J Λ).functor.obj M).val.obj U) :
    (((constantModuleSheafificationUnderlyingIso J Λ).hom.app M).hom.app U)
        ((constantRingUnit J Λ).app U a • x) =
      a • (show M.obj.obj U from
        (((constantModuleSheafificationUnderlyingIso J Λ).hom.app M).hom.app U) x) := by
  let L := (constantModuleSheafificationEquivalence J Λ).functor.obj M
  let e := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso
    ((constantModuleSheafificationUnderlyingIso J Λ).app M)).app U
  let j := ((PresheafOfModules.sheafificationAdjunction
    (constantRingUnit J Λ)).unit.app M.obj).app U
  let jA : AddCommGrpCat.of (M.obj.obj U) ⟶ AddCommGrpCat.of (L.val.obj U) :=
    AddCommGrpCat.ofHom j.hom.toAddMonoidHom
  have hu : jA ≫ e.hom = 𝟙 _ :=
    NatTrans.congr_app (constantModuleUnit_underlying_comparison J Λ M) U
  have hj : jA = e.inv := by
    apply (cancel_mono e.hom).1
    rw [hu, Iso.inv_hom_id]
  have : IsIso jA := by rw [hj]; infer_instance
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso jA).2 x
  have hlin : jA (a • y) =
      (constantRingUnit J Λ).app U a • (show L.val.obj U from jA y) :=
    j.hom.map_smul a y
  have hval (z : M.obj.obj U) : e.hom (jA z) = z :=
    ConcreteCategory.congr_hom hu z
  change e.hom ((constantRingUnit J Λ).app U a • (show L.val.obj U from jA y)) =
    a • (show M.obj.obj U from e.hom (jA y))
  rw [← hlin, hval, hval]

end ModuleCat.Sheaf.ConstantRing
