/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorRow
public import Aglib.CategoryTheory.Abelian.Ext1.Representability
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! Signed Ext action of a degree-one self-extension of the tensor unit. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v e

namespace CategoryTheory.Abelian.Ext

variable {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasExt.{e} D]

local notation "𝒪" => 𝟙_ D

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (M : D) [PreservesFiniteLimits (tensorRight M)] [PreservesFiniteColimits (tensorRight M)]

/-- The degree-one self-extension of the unit tensored with a coefficient sheaf,
transported through the original left unitor. -/
def tensorRightUnitExt (x : Ext.{e} 𝒪 𝒪 1) : Ext.{e} M M 1 :=
  ((Ext.mk₀ (λ_ M).inv).comp (x.mapExactFunctor (tensorRight M)) (zero_add 1)).comp
    (Ext.mk₀ (λ_ M).hom) (add_zero 1)

/-- The degree-one self-extension of the original tensor unit acts on Ext
through tensoring the coefficient, with the Koszul sign. -/
theorem comp_tensorRightUnitExt
    (hT : ∀ (E : Ext1.Extension 𝒪 𝒪) (N : D),
      (E.toShortComplex.map (tensorRight N)).ShortExact)
    (x : Ext.{e} 𝒪 𝒪 1) {q : ℕ} (c : Ext.{e} 𝒪 M q) :
    x.comp c rfl =
      ((-1 : ℤ) ^ q) • c.comp (tensorRightUnitExt M x) (Nat.add_comm q 1) := by
  obtain ⟨E, rfl⟩ := Ext1.exists_extension x
  let i : 𝟭 D ⟶ tensorLeft E.middle := (leftUnitorNatIso D).inv ≫ (curriedTensor D).map E.i
  let j : tensorLeft E.middle ⟶ 𝟭 D := (curriedTensor D).map E.p ≫ (leftUnitorNatIso D).hom
  have hij (N : D) : i.app N ≫ j.app N = 0 := by
    change ((λ_ N).inv ≫ (E.i ▷ N)) ≫ ((E.p ▷ N) ≫ (λ_ N).hom) = 0
    rw [Category.assoc, ← comp_whiskerRight_assoc, E.zero,
      MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, Limits.comp_zero]
  let row (N : D) := ShortComplex.mk (i.app N) (j.app N) (hij N)
  have hraw (N : D) : (E.toShortComplex.map (tensorRight N)).ShortExact :=
    hT E N
  let compare (N : D) : E.toShortComplex.map (tensorRight N) ≅ row N :=
    ShortComplex.isoMk (λ_ N) (Iso.refl _) (λ_ N)
      (by
        change (λ_ N).hom ≫ ((λ_ N).inv ≫ (E.i ▷ N)) = (E.i ▷ N) ≫ 𝟙 _
        simp)
      (by
        change 𝟙 _ ≫ ((E.p ▷ N) ≫ (λ_ N).hom) = (E.p ▷ N) ≫ (λ_ N).hom
        simp)
  have hrow (N : D) : (row N).ShortExact :=
    ShortComplex.shortExact_of_iso (compare N) (hraw N)
  let unitMap : row 𝒪 ⟶ E.toShortComplex := ShortComplex.homMk
    (𝟙 _) (ρ_ E.middle).hom (𝟙 _)
      (by
        change 𝟙 _ ≫ E.i = ((λ_ 𝒪).inv ≫ (E.i ▷ 𝒪)) ≫ (ρ_ E.middle).hom
        rw [Category.id_comp, Category.assoc, rightUnitor_naturality, ← unitors_equal]
        simp)
      (by
        change (ρ_ E.middle).hom ≫ E.p = ((E.p ▷ 𝒪) ≫ (λ_ 𝒪).hom) ≫ 𝟙 _
        rw [Category.comp_id, unitors_equal, rightUnitor_naturality])
  have hunit : (hrow 𝒪).extClass = E.extClass := by
    simpa only [unitMap, ShortComplex.homMk_τ₁, ShortComplex.homMk_τ₃,
      Ext.comp_mk₀_id, Ext.mk₀_id_comp, Ext1.Extension.extClass] using
      (hrow 𝒪).extClass_naturality E.shortExact unitMap
  have hcoeff : (hrow M).extClass = tensorRightUnitExt M E.extClass := by
    have h := (hraw M).extClass_naturality (hrow M) (compare M).hom
    change (hraw M).extClass.comp (Ext.mk₀ (λ_ M).hom) (add_zero 1) =
      (Ext.mk₀ (λ_ M).hom).comp (hrow M).extClass (zero_add 1) at h
    unfold tensorRightUnitExt
    have hm : E.extClass.mapExactFunctor (tensorRight M) = (hraw M).extClass :=
      Ext.mapExactFunctor_extClass (tensorRight M) E.shortExact
    rw [hm, Ext.comp_assoc_of_third_deg_zero, h,
      Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]
  have h := Functor.exactFunctorRow_extClass_left (𝟭 D) (tensorLeft E.middle) (𝟭 D)
    i j hij hrow c
  simpa only [Ext.id_mapExactFunctor, hunit, hcoeff] using h

/-- Tensor a degree-one self-extension at an object identified with the unit,
using the original unit comparison at the tensor coefficient. -/
def tensorRightIsoUnitExt {U : D} (a : U ≅ 𝒪) (x : Ext.{e} U U 1) : Ext.{e} M M 1 :=
  let aM := (tensorRight M).mapIso a ≪≫ λ_ M
  ((Ext.mk₀ aM.inv).comp (x.mapExactFunctor (tensorRight M)) (zero_add 1)).comp
    (Ext.mk₀ aM.hom) (add_zero 1)

/-- Transport of the signed unit-extension identity through a given unit isomorphism. -/
theorem comp_tensorRightIsoUnitExt
    (hT : ∀ (E : Ext1.Extension 𝒪 𝒪) (N : D),
      (E.toShortComplex.map (tensorRight N)).ShortExact)
    {U : D} (a : U ≅ 𝒪) (x : Ext.{e} U U 1) {q : ℕ} (c : Ext.{e} U M q) :
    x.comp c rfl =
      ((-1 : ℤ) ^ q) • c.comp (tensorRightIsoUnitExt M a x) (Nat.add_comm q 1) := by
  let x' := ((Ext.mk₀ a.inv).comp x (zero_add 1)).comp (Ext.mk₀ a.hom) (add_zero 1)
  let c' := (Ext.mk₀ a.inv).comp c (zero_add q)
  have h := comp_tensorRightUnitExt M hT x' c'
  have hx : tensorRightUnitExt M x' = tensorRightIsoUnitExt M a x := by
    simp only [tensorRightUnitExt, tensorRightIsoUnitExt, x', Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀_assoc]
  have hxc : x'.comp c' rfl =
      (Ext.mk₀ a.inv).comp (x.comp c rfl) (zero_add (1 + q)) := by
    dsimp only [x', c']
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc,
      a.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_assoc _ _ _ (zero_add 1) rfl (by omega)]
  let pre := (Ext.mk₀ a.inv).precomp M (zero_add (1 + q))
  have pre_injective : Function.Injective pre := by
    intro α β eq
    change (Ext.mk₀ a.inv).comp α (zero_add (1 + q)) =
      (Ext.mk₀ a.inv).comp β (zero_add (1 + q)) at eq
    have eq' := congrArg (fun z : Ext.{e} 𝒪 M (1 + q) =>
      (Ext.mk₀ a.hom).comp z (zero_add (1 + q))) eq
    simpa only [Ext.mk₀_comp_mk₀_assoc, a.hom_inv_id, Ext.mk₀_id_comp] using eq'
  apply pre_injective
  rw [map_zsmul]
  change (Ext.mk₀ a.inv).comp (x.comp c rfl) (zero_add (1 + q)) =
    ((-1 : ℤ) ^ q) • (Ext.mk₀ a.inv).comp
      (c.comp (tensorRightIsoUnitExt M a x) (Nat.add_comm q 1)) (zero_add (1 + q))
  rw [← hxc, ← hx,
    ← Ext.comp_assoc _ _ _ (zero_add q) (Nat.add_comm q 1) (by omega)]
  exact h

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Abelian.Ext

variable {D : Type u} [Category.{v} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasExt.{e} D]

end CategoryTheory.Abelian.Ext
