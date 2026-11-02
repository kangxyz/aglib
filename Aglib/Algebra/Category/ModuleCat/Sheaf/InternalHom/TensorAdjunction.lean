/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Evaluation
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Functor
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorSections

/-!
# The actual tensor–Hom adjunction on a commutative ringed site

The native module-sheafification adjunction and actual presheaf-source currying
construct the tensor–Hom equivalence. Its right adjoint is the constructed Hom
functor, and its counit is the same actual evaluation map.

The ring and module carriers are `max uC vC r`. The actual binary tensor and its
unit maps are used throughout; no descended monoidal structure or tensor-stability
assumption is needed for this adjunction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite MonoidalCategory
open SheafOfModulesOfCommRing
  (tensorProduct tensorMap tensorUnitMap toPresheaf associatedSheaf)

universe uC vC r

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  (M N P : SheafOfModulesOfCommRing R)

/-- The actual tensor–Hom equivalence, through native module sheafification. -/
def tensorHomEquiv :
    (tensorProduct R M N ⟶ P) ≃ (M ⟶ sheaf R N P) :=
  (PresheafOfModules.sheafificationHomEquiv
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val) (F := P)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).trans
      ((PresheafSource.tensorHomEquivRight.{uC, vC, r} R N.val M.val P).trans
        (show (M.val ⟶ (sheaf R N P).val) ≃ (M ⟶ sheaf R N P) from
          ((SheafOfModules.fullyFaithfulForget
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).homEquiv
              (X := M) (Y := sheaf R N P)).symm))

/-- Currying a morphism from the actual sheaf tensor. -/
abbrev curry (h : tensorProduct R M N ⟶ P) : M ⟶ sheaf R N P :=
  tensorHomEquiv.{uC, vC, r} R M N P h

/-- The actual Hom section produced by currying a section of the left factor. -/
abbrev currySection (h : tensorProduct R M N ⟶ P) (U : Cᵒᵖ) (m : M.val.obj U) :
    (sheaf R N P).val.obj U :=
  (curry.{uC, vC, r} R M N P h).val.app U m

/-- Currying retains the original restriction and sheafification-unit formula. -/
theorem currySection_app (h : tensorProduct R M N ⟶ P) (U : Cᵒᵖ)
    (m : M.val.obj U) (V : (Over U.unop)ᵒᵖ) (n : N.val.obj (op V.unop.left)) :
    (currySection.{uC, vC, r} R M N P h U m).val.app V n =
      h.val.app (op V.unop.left)
        ((tensorUnitMap R M N).app (op V.unop.left)
          (M.val.map V.unop.hom.op m ⊗ₜ[R.obj.obj (op V.unop.left)] n)) := rfl

/-- The actual presheaf arrow underlying uncurrying. -/
abbrev uncurryPresheaf (h : M ⟶ sheaf R N P) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val ⟶ P.val :=
  PresheafSource.uncurryRight.{uC, vC, r} R N.val M.val P h.val

/-- Uncurrying uses the original module-sheafification Hom equivalence. -/
def uncurry (h : M ⟶ sheaf R N P) : tensorProduct R M N ⟶ P :=
  (PresheafOfModules.sheafificationHomEquiv
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val) (F := P)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).symm
      (uncurryPresheaf.{uC, vC, r} R M N P h)

/-- The selected uncurrying map is the inverse of the same actual equivalence. -/
theorem uncurry_eq_tensorHomEquiv_symm (h : M ⟶ sheaf R N P) :
    uncurry.{uC, vC, r} R M N P h = (tensorHomEquiv.{uC, vC, r} R M N P).symm h := rfl

omit [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}] in
/-- The original presheaf uncurrying formula on pure tensors. -/
theorem uncurryPresheaf_app_tmul (h : M ⟶ sheaf R N P) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (uncurryPresheaf.{uC, vC, r} R M N P h).app U (m ⊗ₜ[R.obj.obj U] n) =
      (h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n :=
  PresheafSource.uncurryRight_app_tmul.{uC, vC, r} R N.val M.val P h.val U m n

/-- Uncurrying retains the original values on the sheafification-unit generators. -/
theorem uncurry_tmul (h : M ⟶ sheaf R N P) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (uncurry.{uC, vC, r} R M N P h).val.app U
        ((tensorUnitMap R M N).app U (m ⊗ₜ[R.obj.obj U] n)) =
      (h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n := by
  have hh := (PresheafOfModules.sheafificationHomEquiv
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val) (F := P)
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).apply_symm_apply
      (uncurryPresheaf.{uC, vC, r} R M N P h)
  exact (congrArg (fun f :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val ⟶ P.val =>
      f.app U (m ⊗ₜ[R.obj.obj U] n)) hh).trans
        (uncurryPresheaf_app_tmul.{uC, vC, r} R M N P h U m n)

theorem uncurry_curry (h : tensorProduct R M N ⟶ P) :
    uncurry.{uC, vC, r} R M N P (curry.{uC, vC, r} R M N P h) = h :=
  (tensorHomEquiv.{uC, vC, r} R M N P).symm_apply_apply h

theorem curry_uncurry (h : M ⟶ sheaf R N P) :
    curry.{uC, vC, r} R M N P (uncurry.{uC, vC, r} R M N P h) = h :=
  (tensorHomEquiv.{uC, vC, r} R M N P).apply_symm_apply h

/-- Uncurrying commutes with precomposition by the original left-factor morphism. -/
theorem uncurry_comp {M' : SheafOfModulesOfCommRing R}
    (f : M' ⟶ M) (h : M ⟶ sheaf R N P) :
    uncurry.{uC, vC, r} R M' N P (f ≫ h) = tensorMap R f (𝟙 N) ≫ uncurry.{uC, vC, r} R M N P h := by
  apply SheafOfModulesOfCommRing.tensor_hom_ext R
  intro U m n
  exact (uncurry_tmul.{uC, vC, r} R M' N P (f ≫ h) U m n).trans
    (((congrArg (fun z : (tensorProduct R M N).val.obj U =>
      (uncurry.{uC, vC, r} R M N P h).val.app U z)
        (SheafOfModulesOfCommRing.tensor_map_tensorSection R f (𝟙 N) U m n)).trans
      (uncurry_tmul.{uC, vC, r} R M N P h U (f.val.app U m) n)).symm)

/-- Uncurrying commutes with the actual target coefficient map. -/
theorem uncurry_map {P' : SheafOfModulesOfCommRing R}
    (h : M ⟶ sheaf R N P) (b : P ⟶ P') :
    uncurry.{uC, vC, r} R M N P' (h ≫ map R (𝟙 N) b) =
      uncurry.{uC, vC, r} R M N P h ≫ b := by
  apply SheafOfModulesOfCommRing.tensor_hom_ext R
  intro U m n
  exact (uncurry_tmul.{uC, vC, r} R M N P' (h ≫ map R (𝟙 N) b) U m n).trans
    ((map_apply R (𝟙 N) b U.unop (h.val.app U m) (op (Over.mk (𝟙 U.unop))) n).trans
      (congrArg (fun p : P.val.obj U => b.val.app U p)
        (uncurry_tmul.{uC, vC, r} R M N P h U m n)).symm)

/-- The original binary tensor as a functor in its left factor. -/
def tensorRightFunctor : SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing R :=
  toPresheaf R ⋙ tensorRight ((toPresheaf R).obj N) ⋙ associatedSheaf R

/-- The right-tensor functor retains the original tensor object. -/
theorem tensorRightFunctor_obj :
    (tensorRightFunctor.{uC, vC, r} R N).obj M = tensorProduct R M N := rfl

/-- The right-tensor functor retains the original two-factor tensor map. -/
theorem tensorRightFunctor_map {M' : SheafOfModulesOfCommRing R} (f : M ⟶ M') :
    (tensorRightFunctor.{uC, vC, r} R N).map f = tensorMap R f (𝟙 N) := rfl

/-- The actual Hom sheaf and its actual target coefficient maps form a functor. -/
def homFunctor : SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing R where
  obj P := sheaf R N P
  map b := map R (𝟙 N) b
  map_id _ := SheafOfModules.InternalHom.map_id R
  map_comp b c := by
    simpa only [Category.id_comp] using
      (SheafOfModules.InternalHom.map_comp R (𝟙 N) b (𝟙 N) c).symm

/-- The actual tensor–Hom adjunction, without assuming a descended monoidal structure. -/
def tensorHomAdjunction : tensorRightFunctor.{uC, vC, r} R N ⊣ homFunctor.{uC, vC, r} R N :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun M P => tensorHomEquiv.{uC, vC, r} R M N P
    homEquiv_naturality_left_symm := fun {M'} {M} {P} f g =>
      uncurry_comp.{uC, vC, r} R M N P (M' := M') f g
    homEquiv_naturality_right := by
      intro M P P' f g
      change tensorProduct R M N ⟶ P at f
      apply (tensorHomEquiv.{uC, vC, r} R M N P').symm.injective
      change uncurry.{uC, vC, r} R M N P' (curry.{uC, vC, r} R M N P' (f ≫ g)) =
        uncurry.{uC, vC, r} R M N P' (curry.{uC, vC, r} R M N P f ≫ map R (𝟙 N) g)
      rw [uncurry_curry.{uC, vC, r}, uncurry_map.{uC, vC, r},
        uncurry_curry.{uC, vC, r}] }

/-- The adjunction retains the same actual tensor–Hom equivalence. -/
theorem tensorHomAdjunction_homEquiv :
    (tensorHomAdjunction.{uC, vC, r} R N).homEquiv M P =
      tensorHomEquiv.{uC, vC, r} R M N P :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) M) P

/-- The whole unit is actual currying of the identity on the original tensor. -/
theorem tensorHomAdjunction_unit_app :
    (tensorHomAdjunction.{uC, vC, r} R N).unit.app M =
      curry.{uC, vC, r} R M N (tensorProduct R M N) (𝟙 _) := rfl

/-- The whole counit is the original actual evaluation. -/
theorem tensorHomAdjunction_counit_app :
    (tensorHomAdjunction.{uC, vC, r} R N).counit.app P = evaluationSheaf.{uC, vC, r} R N P := rfl

/-- Actual uncurrying is tensoring the original Hom morphism followed by actual evaluation. -/
theorem uncurry_eq_tensorMap_evaluation (h : M ⟶ sheaf R N P) :
    uncurry.{uC, vC, r} R M N P h = tensorMap R h (𝟙 N) ≫ evaluationSheaf.{uC, vC, r} R N P := by
  calc
    uncurry.{uC, vC, r} R M N P h =
        ((tensorHomAdjunction.{uC, vC, r} R N).homEquiv M P).symm h := by
      rw [tensorHomAdjunction_homEquiv.{uC, vC, r}]
      rfl
    _ = (tensorRightFunctor.{uC, vC, r} R N).map h ≫
        (tensorHomAdjunction.{uC, vC, r} R N).counit.app P :=
      (tensorHomAdjunction.{uC, vC, r} R N).homEquiv_counit M P h
    _ = tensorMap R h (𝟙 N) ≫ evaluationSheaf.{uC, vC, r} R N P := rfl

end SheafOfModules.InternalHom
