/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleScalarPresheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantActionSheafification

/-! # Original constant-module sheafification comparison preserves scalars

The three original factors are used unchanged: native module sheafification,
original resized coefficient comparison, and original higher-image
sheafification. Their actual scalar squares compose to the required square.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u r w s e
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  ModuleCat.Sheaf.forget_preservesSheafification
variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type r) [Ring Λ]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- The original whole sheafification comparison intertwines noncentral scalars. -/
theorem constantModuleCohomologySheafificationUnderlyingIso_scalar
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) (a : Λ) :
    (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a).app
        ((constantModuleCohomologySheafificationFunctor f Λ q).obj M) ≫
      (constantModuleCohomologySheafificationUnderlyingIso f Λ q).hom.app M =
    (constantModuleCohomologySheafificationUnderlyingIso f Λ q).hom.app M ≫
      (higherDirectImage f q).map
        ((constantModuleUnderlyingScalar (X := X) Λ a).app M) := by
  let P := (smallConstantModuleCohomologyFunctor.{u, r, w, s, e} f Λ q).obj M
  let L := presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let α := (constantModuleUnderlyingScalar (X := X) Λ a).app M
  let t := Functor.whiskerLeft P (ModuleCat.forgetScalar Λ a)
  let E := (sheafComposeNatIso S.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (sheafificationAdjunction S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})).app P
  let I := (smallConstantModuleCohomologyUnderlyingIso.{u, r, w, s, e} f Λ q).app M
  let C := (fibreProductCohomologySheafificationNatIso f q).app
    ((constantModuleUnderlying (X := X) Λ).obj M)
  let σ := (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a).app
    ((constantModuleCohomologySheafificationFunctor f Λ q).obj M)
  have hE : E.hom ≫ σ = L.map t ≫ E.hom :=
    ModuleCat.Sheaf.sheafificationUnderlyingIso_scalar S.smallEtaleTopology Λ P a
  have hEinv : σ ≫ E.inv = E.inv ≫ L.map t := by
    apply (cancel_mono E.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hE]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hI : L.map t ≫ L.map I.hom =
      L.map I.hom ≫ L.map ((smallFibreProductCohomologyFunctor f q).map α) := by
    have hi := smallConstantModuleCohomologyUnderlyingIso_scalar.{u, r, w, s, e}
      f Λ q M a
    change t ≫ I.hom = I.hom ≫ (smallFibreProductCohomologyFunctor f q).map α at hi
    simpa only [Functor.map_comp] using congrArg L.map hi
  have hC : L.map ((smallFibreProductCohomologyFunctor f q).map α) ≫ C.hom =
      C.hom ≫ (higherDirectImage f q).map α :=
    (fibreProductCohomologySheafificationNatIso f q).hom.naturality α
  simp only [constantModuleCohomologySheafificationUnderlyingIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  change σ ≫ E.inv ≫ L.map I.hom ≫ C.hom =
    E.inv ≫ L.map I.hom ≫ C.hom ≫ (higherDirectImage f q).map α
  rw [← Category.assoc σ E.inv, hEinv, Category.assoc,
    ← Category.assoc (L.map t), hI]
  simp only [Category.assoc]
  rw [hC]

end AlgebraicGeometry.Scheme.EtaleCohomology
