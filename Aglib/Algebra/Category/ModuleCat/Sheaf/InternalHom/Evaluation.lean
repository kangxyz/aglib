/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.PresheafTensor
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Objects

/-!
# Actual evaluation on a commutative ringed site

Evaluation is right-oriented uncurrying of the identity on the actual Hom presheaf,
followed by native module sheafification. Its order is `Hom(M,N) ⊗ M`, and its value
on original pure-section generators is evaluation at the identity slice object.

The actual input ring and module carriers have the common universe `max uC vC r`.
No smaller ring presentation is silently lifted, and no monoidal structure on
module sheaves or tensor stability is assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite MonoidalCategory
open SheafOfModulesOfCommRing (tensorProduct tensorUnitMap)

universe uC vC r

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
  (M N : SheafOfModulesOfCommRing R)

/-- The actual presheaf evaluation, with the Hom factor first. -/
def evaluationPresheaf :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj)
      (sheaf R M N).val M.val ⟶ N.val :=
  PresheafSource.uncurryRight.{uC, vC, r} R M.val (sheaf R M N).val N (𝟙 _)

/-- Presheaf evaluation retains the original identity-slice value. -/
theorem evaluationPresheaf_app_tmul (U : Cᵒᵖ)
    (s : (sheaf R M N).val.obj U) (m : M.val.obj U) :
    (evaluationPresheaf.{uC, vC, r} R M N).app U (s ⊗ₜ m) =
      s.val.app (op (Over.mk (𝟙 U.unop))) m :=
  PresheafSource.uncurryRight_app_tmul.{uC, vC, r} R M.val (sheaf R M N).val N (𝟙 _) U s m

variable [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

/-- Evaluation on the actual sheafified tensor, using the original sheafification equivalence. -/
def evaluationSheaf : tensorProduct R (sheaf R M N) M ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj)
      (sheaf R M N).val M.val) (F := N)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).symm
      (evaluationPresheaf.{uC, vC, r} R M N)

/-- Evaluation on original pure-section generators is the original Hom value. -/
theorem evaluationSheaf_tmul (U : Cᵒᵖ)
    (s : (sheaf R M N).val.obj U) (m : M.val.obj U) :
    (evaluationSheaf.{uC, vC, r} R M N).val.app U
        ((tensorUnitMap R (sheaf R M N) M).app U (s ⊗ₜ m)) =
      s.val.app (op (Over.mk (𝟙 U.unop))) m := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj)
      (sheaf R M N).val M.val) (F := N)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).apply_symm_apply
      (evaluationPresheaf.{uC, vC, r} R M N)
  exact (congrArg (fun f :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj)
      (sheaf R M N).val M.val ⟶ N.val => f.app U (s ⊗ₜ[R.obj.obj U] m)) h).trans
    (evaluationPresheaf_app_tmul.{uC, vC, r} R M N U s m)

/-- The whole sheaf evaluation is obtained from its actual presheaf map by the native adjunction. -/
theorem evaluationSheaf_eq_sheafificationHomEquiv :
    evaluationSheaf.{uC, vC, r} R M N =
      (PresheafOfModules.sheafificationHomEquiv
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj)
          (sheaf R M N).val M.val) (F := N)
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).symm
          (evaluationPresheaf.{uC, vC, r} R M N) := rfl

end SheafOfModules.InternalHom
