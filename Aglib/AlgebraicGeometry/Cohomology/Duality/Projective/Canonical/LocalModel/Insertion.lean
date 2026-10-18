/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction.Insertion

/-!
# The original model class after normal insertion

The original ordered Koszul class, inverse normal section, and native
evaluation one identify the canonical model arrow after insertion with
its original pulled coefficient frame. The determinant remains the same
actual normal-first determinant throughout.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w
namespace AlgebraicGeometry.Scheme.Modules

variable {A R : CommRingCat.{u}} (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]
  (α : R ⟶ A) (J : InjectiveResolution L)
  {Q : (Spec (regularListQuotientRing s)).Modules}
  (Δ : tensorSheaf (Spec (regularListQuotientRing s))
    (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)

/-- On every open, original class one followed by canonical contraction and the
same normal insertion is the original pulled coefficient section. -/
theorem regularListCanonicalModelTopHomologyIso_insert_class
    (U : (Spec (regularListQuotientRing s)).Opens) :
    (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
        (closedImmersionRegularListNormalFrameIso α s hs) Δ).hom.val.app (op U)
      ((regularListCanonicalModelTopHomologyIso s hs e α J Δ).hom.val.app (op U)
        (regularListModelTopClass s hs J e (1 : A) U)) =
      closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s) U := by
  let Z := Spec (regularListQuotientRing s)
  let C := closedImmersionRegularListNormalLineBundle α s hs
  let eC := closedImmersionRegularListNormalFrameIso α s hs
  let eD := closedImmersionRegularListNormalDualFrameIso α s hs
  let F := closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e
  let N := closedImmersionRegularListInverseNormalLineIso α s hs e
  let ell := closedImmersionRegularListNormalDualSection α s hs U
  let c := closedImmersionRegularListNormalSection α s hs U
  let p := closedImmersionRegularListCoefficientSection s e (1 : regularListQuotientRing s) U
  let ξ := regularListModelTopClass s hs J e (1 : A) U
  have hF := regularListModelTopClass_unitFrame s hs J e (1 : A) U
  rw [map_one] at hF
  have hN : N.hom.val.app (op U) (F.hom.val.app (op U) ξ) =
      moduleTensorSection Z (dualLineBundle Z C).val
        ((pullback (Spec.map (regularListQuotientMap s))).obj L) U ell p :=
    (congrArg (N.hom.val.app (op U)) hF).trans
      (closedImmersionRegularListInverseNormalLineIso_section α s hs e 1 U)
  have hI := normalDeterminantContractionIso_insert_section C eC eD Δ U ell c p
    (closedImmersionRegularListNormalFrameIso_normalSection α s hs U)
    (closedImmersionRegularListNormalDualSection_dualEvaluation α s hs U)
  change (normalDeterminantInsertionIso C eC Δ).hom.val.app (op U)
    ((normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U)
      (N.hom.val.app (op U) (F.hom.val.app (op U) ξ))) = p
  exact (congrArg (fun z => (normalDeterminantInsertionIso C eC Δ).hom.val.app (op U)
    ((normalDeterminantContractionIso C eC eD Δ).hom.val.app (op U) z)) hN).trans hI

/-- Inserting the same normal generator identifies the actual canonical model arrow
with the original model unit frame and the inverse original coefficient frame. -/
theorem regularListCanonicalModelTopHomologyIso_insert :
    (regularListCanonicalModelTopHomologyIso s hs e α J Δ).hom ≫
        (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
          (closedImmersionRegularListNormalFrameIso α s hs) Δ).hom =
      (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom ≫
        (closedImmersionRegularListCoefficientFrameIso s e).inv := by
  apply regularListModelTopClass_hom_ext_global s hs J e
  let E := closedImmersionRegularListCoefficientFrameIso s e
  have hc := closedImmersionRegularListCoefficientSection_eq s e
    (1 : regularListQuotientRing s) ⊤
  have hs₁ : closedImmersionRegularListCoefficientSection s e
      (1 : regularListQuotientRing s) ⊤ = E.inv.val.app (op ⊤) (1 : Γ(Spec
        (regularListQuotientRing s), ⊤)) :=
    hc.trans (congrArg (E.inv.val.app (op ⊤)) (tilde_toOpen_self_one (R :=
      regularListQuotientRing s) ⊤))
  exact (regularListCanonicalModelTopHomologyIso_insert_class s hs e α J Δ ⊤).trans
    (hs₁.trans (congrArg (E.inv.val.app (op ⊤))
      (regularListModelTopClass_one s hs J e ⊤)).symm)

end AlgebraicGeometry.Scheme.Modules
