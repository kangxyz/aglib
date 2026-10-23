/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedCocycles

/-!
# Cocycle normalization of the native represented Ext comparison

All classes and maps below belong to the original native injective resolution.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.Sheaf.ModuleCoefficients

/-- The identity forgetful functor on additive commutative groups. -/
local instance derivedExtNormalizationHasForget₂ :
    HasForget₂ AddCommGrpCat.{v} AddCommGrpCat.{v} where
  forget₂ := 𝟭 _

local instance : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).Additive :=
  inferInstanceAs (Functor.Additive (𝟭 AddCommGrpCat.{v}))

local instance : (forget₂ AddCommGrpCat.{v} AddCommGrpCat.{v}).PreservesHomology :=
  inferInstanceAs (Functor.PreservesHomology (𝟭 AddCommGrpCat.{v}))

/-- Extension by zero sends the original cocycle class to its original supported component. -/
lemma extendHomologyIso_cyclesMk (K : CochainComplex AddCommGrpCat.{v} ℕ)
    (n : ℕ) (x : (K.extend ComplexShape.embeddingUpNat).X (n : ℤ))
    (hx : (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) (n + 1) x = 0) :
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom
      ((K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ)
        ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)) =
      K.homologyπ n (K.cyclesMk
        ((K.extendXIso ComplexShape.embeddingUpNat (i' := (n : ℤ)) rfl).hom x)
        (n + 1) (by simp) (by
          change K.d n (n + 1) ((K.extendXIso ComplexShape.embeddingUpNat
            (i := n) rfl).hom x) = 0
          apply (AddCommGrpCat.mono_iff_injective
            (K.extendXIso ComplexShape.embeddingUpNat (i := n + 1)
              (i' := (n : ℤ) + 1) (by simp)).inv).mp inferInstance
          have h := ConcreteCategory.congr_hom
            (K.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n + 1)
              (i' := (n : ℤ)) (j' := (n : ℤ) + 1) rfl (by simp)) x
          change (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) (n + 1) x =
            (K.extendXIso ComplexShape.embeddingUpNat (i := n + 1)
              (i' := (n : ℤ) + 1) (by simp)).inv
                (K.d n (n + 1) ((K.extendXIso ComplexShape.embeddingUpNat
                  (i := n) rfl).hom x)) at h
          simpa only [map_zero] using h.symm.trans hx)) := by
  have h := ConcreteCategory.congr_hom
    (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat (j := n) rfl)
    ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)
  change (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom
    ((K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ)
      ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)) =
    K.homologyπ n ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).hom
      ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)) at h
  rw [h]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have he := ConcreteCategory.congr_hom
    (K.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat (j := n) rfl)
    ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)
  change K.iCycles n
      ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).hom
        ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)) =
    (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
      ((K.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ)
        ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx)) at he
  have hi : (K.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ)
      ((K.extend ComplexShape.embeddingUpNat).cyclesMk x (n + 1) (by simp) hx) = x :=
    (K.extend ComplexShape.embeddingUpNat).i_cyclesMk _ _ _ _
  rw [hi] at he
  exact he.trans (K.i_cyclesMk _ _ _ _).symm

section Represented

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] {X Y : C} (n : ℕ)

/-- The represented Ext comparison retains the original injective-resolution cocycle. -/
lemma extRightDerivedRepresentedAddEquiv_extMk
    (f : X ⟶ (injectiveResolution Y).cocomplex.X n)
    (hf : f ≫ (injectiveResolution Y).cocomplex.d n (n + 1) = 0) :
    extRightDerivedRepresentedAddEquiv X Y n
      ((injectiveResolution Y).extMk f (n + 1) rfl hf) =
      ((injectiveResolution Y).isoRightDerivedObj
        (preadditiveCoyoneda.obj (op X)) n).inv
        ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj
          (injectiveResolution Y).cocomplex).homologyπ n
          ((((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj
            (injectiveResolution Y).cocomplex).cyclesMk f (n + 1) (by simp) hf)) := by
  let I := injectiveResolution Y
  let G := preadditiveCoyoneda.obj (op X)
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hf' : f ≫ I.cocomplex.d n (n + 1) = 0 := hf
  let z : Cocycle ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex (n : ℤ) :=
    Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)
      (n + 1) (by lia)
      (by
        simp only [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by simp),
          Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc, hf', zero_comp])
  have hz := homologyAddEquiv_cyclesMk
    ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex (n : ℤ) z
  have hz' : (HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex (n : ℤ)).symm
      (CohomologyClass.mk z) =
      (HomComplex ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex).homologyπ
        (n : ℤ) ((HomComplex ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex).cyclesMk
          z.val (n + 1) (by simp) z.property) :=
    (AddEquiv.symm_apply_eq _).mpr hz.symm
  simp only [extRightDerivedRepresentedAddEquiv, AddEquiv.trans_apply,
    InjectiveResolution.extAddEquivCohomologyClass_apply,
    InjectiveResolution.extEquivCohomologyClass_extMk]
  change (I.isoRightDerivedObj G n).inv
    ((K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom
      (HomologicalComplex.homologyMap (I.cocomplex.mapExtendIso G
        ComplexShape.embeddingUpNat).hom (n : ℤ)
        (HomologicalComplex.homologyMap (singleHomComplexIso X I.cochainComplex).hom
          (n : ℤ) ((HomComplex.homologyAddEquiv
            ((CochainComplex.singleFunctor C 0).obj X) I.cochainComplex (n : ℤ)).symm
              (CohomologyClass.mk z))))) = _
  erw [hz', homologyMap_cyclesMk, homologyMap_cyclesMk, extendHomologyIso_cyclesMk]
  congr 3
  change (K.extendXIso ComplexShape.embeddingUpNat (i' := (n : ℤ)) rfl).hom
    ((I.cocomplex.mapExtendIso G ComplexShape.embeddingUpNat).hom.f (n : ℤ)
      ((Cochain.fromSingleEquiv (zero_add (n : ℤ))) z.val)) = f
  change (K.extendXIso ComplexShape.embeddingUpNat (i' := (n : ℤ)) rfl).hom
    ((I.cocomplex.mapExtendIso G ComplexShape.embeddingUpNat).hom.f (n : ℤ)
      ((Cochain.fromSingleEquiv (zero_add (n : ℤ)))
        (Cochain.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)))) = f
  rw [Cochain.fromSingleEquiv_fromSingleMk]
  have he := congrArg
    (fun q : G.obj (I.cochainComplex.X (n : ℤ)) ⟶ G.obj (I.cocomplex.X n) =>
      q (show G.obj (I.cochainComplex.X (n : ℤ)) from
        f ≫ (I.cochainComplexXIso n n rfl).inv))
    (I.cocomplex.mapExtendIso_hom_f_extendXIso G ComplexShape.embeddingUpNat
      (i := n) (j := (n : ℤ)) rfl)
  change (K.extendXIso ComplexShape.embeddingUpNat (i' := (n : ℤ)) rfl).hom
      ((I.cocomplex.mapExtendIso G ComplexShape.embeddingUpNat).hom.f (n : ℤ)
        (f ≫ (I.cochainComplexXIso n n rfl).inv)) =
    (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫
    (I.cochainComplexXIso n n rfl).hom at he
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he

end Represented

end CategoryTheory.Sheaf.ModuleCoefficients
