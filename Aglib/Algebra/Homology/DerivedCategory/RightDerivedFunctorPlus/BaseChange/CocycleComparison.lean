/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived

/-! # Native cocycle comparison through a derived natural transformation -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

universe u v w

namespace HomologicalComplex

/-- The native cycle projection of an explicit cocycle of abelian groups. -/
def addCommGrpCycleClass (K : CochainComplex AddCommGrpCat.{v} ℤ)
    (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n ((K.sc n).abCyclesIso.inv ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [CochainComplex.next ℤ n]
    exact hx⟩)

theorem addCommGrpCycleClass_map
    {K L : CochainComplex AddCommGrpCat.{v} ℤ} (φ : K ⟶ L)
    (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    homologyMap φ n (addCommGrpCycleClass K n x hx) =
      addCommGrpCycleClass L n (φ.f n x) (by
        rw [← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply, hx]
        exact map_zero _) := by
  let z := (K.sc n).abCyclesIso.inv ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [CochainComplex.next ℤ n]
    exact hx⟩
  have hz : K.iCycles n z = x :=
    (K.sc n).abCyclesIso_inv_apply_iCycles _
  have hc : cyclesMap φ n z =
      (L.sc n).abCyclesIso.inv ⟨φ.f n x, by
        change L.d n ((ComplexShape.up ℤ).next n) (φ.f n x) = 0
        rw [CochainComplex.next ℤ n, ← ConcreteCategory.comp_apply,
          φ.comm, ConcreteCategory.comp_apply, hx]
        exact map_zero _⟩ := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hz]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  change homologyMap φ n (K.homologyπ n z) = _
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply, hc]
  rfl

end HomologicalComplex

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] (X : C) {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
  (α : preadditiveCoyoneda.obj (Opposite.op X) ⟶ G)
  {Y : C} (I : InjectiveResolution Y) (n : ℕ)

/-- The original Ext representative, followed by the actual derived natural
transformation, is its native mapped cycle class on the same resolution. -/
theorem extRightDerivedAddEquiv_cocycle_natTrans
    (f : X ⟶ I.cochainComplex.X (n : ℤ))
    (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    (I.isoRightDerivedObjCochain G n).hom
      ((α.rightDerived n).app Y (I.extRightDerivedAddEquiv X n
        (I.extEquivCohomologyClass.symm
          (.mk (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf))))) =
    let H := (G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    addCommGrpCycleClass H (n : ℤ) (α.app _ f) (by
      have he := ConcreteCategory.congr_hom
        (α.naturality (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))) f
      change α.app _ (f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) =
        G.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) (α.app _ f) at he
      rw [hf, map_zero] at he
      exact he.symm) := by
  let P := preadditiveCoyoneda.obj (Opposite.op X)
  let H := (P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let E := (NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex
  let b := I.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf))
  have hNT := InjectiveResolution.isoRightDerivedObjCochain_hom_natTrans α I n
  have hExt := I.extRightDerivedAddEquiv_cocycle X n f hf
  change (I.isoRightDerivedObjCochain G n).hom
    ((α.rightDerived n).app Y (I.extRightDerivedAddEquiv X n b)) = _
  rw [← ConcreteCategory.comp_apply, hNT, ConcreteCategory.comp_apply, hExt]
  have hfH : H.d (n : ℤ) ((n : ℤ) + 1) f = 0 := hf
  change homologyMap E (n : ℤ)
    ((I.isoRightDerivedObjCochain P n).hom
      ((I.isoRightDerivedObjCochain P n).inv
        (addCommGrpCycleClass H (n : ℤ) f hfH))) = _
  have hc : (I.isoRightDerivedObjCochain P n).hom
      ((I.isoRightDerivedObjCochain P n).inv (addCommGrpCycleClass H (n : ℤ) f hfH)) =
        addCommGrpCycleClass H (n : ℤ) f hfH :=
    ConcreteCategory.congr_hom (I.isoRightDerivedObjCochain P n).inv_hom_id _
  rw [hc, addCommGrpCycleClass_map]
  rfl

end CategoryTheory.InjectiveResolution
