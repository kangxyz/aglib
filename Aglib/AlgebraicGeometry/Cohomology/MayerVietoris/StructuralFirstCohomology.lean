/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Structural first cohomology on a two-affine-open cover

The original structure-sheaf `coherentH1` of a field scheme is linearly
equivalent to overlap sections modulo the sum of the ranges of the two
literal restriction maps. Only the two covering opens must be affine; their
intersection need not be affine, and the scheme need not be separated.

All section actions are `Module.compHom` along the original `constantSection`.
The proof uses the native structural Mayer–Vietoris sequence and the actual
affine-open vanishing of `Sheaf.H'`, with comparison back to `Sheaf.H`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian CategoryTheory.ComposableArrows
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] (X : FScheme k)

/-- The original structural field action on sections of an actual open. -/
abbrev structuralSectionModule (U : X.left.Opens) : Module k Γ(X.left, U) :=
  Module.compHom _ (Scheme.constantSection X U)

attribute [local instance] structuralSectionModule

/-- The literal restriction of structure-sheaf sections, with its structural scalars. -/
def structuralRestrictionLinearMap {U V : X.left.Opens} (h : U ≤ V) :
    Γ(X.left, V) →ₗ[k] Γ(X.left, U) where
  __ := (X.left.presheaf.map (homOfLE h).op).hom.toAddMonoidHom
  map_smul' a x := by
    change X.left.presheaf.map (homOfLE h).op (Scheme.constantSection X V a * x) =
      Scheme.constantSection X U a * X.left.presheaf.map (homOfLE h).op x
    rw [map_mul, Scheme.map_constantSection]

/-- Native open cohomology with the original structural scalar action. -/
abbrev structuralOpenCohomology (n : ℕ) (U : X.left.Opens) : ModuleCat.{u + 1} k :=
  (moduleHPrimePresheaf X.left (Scheme.constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) n).obj (op U)

/-- Native degree-zero open cohomology is the actual section module. -/
def structuralOpenH0LinearEquiv (U : X.left.Opens) :
    structuralOpenCohomology X 0 U ≃ₗ[k] Γ(X.left, U) := by
  let build (A : AddCommGrpCat.{u + 1}) (B : AddCommGrpCat.{u})
      (mA : Module k A) (mB : Module k B) (e : A ≃+ B)
      (h : letI := mA; letI := mB; ∀ (a : k) (x : A), e (a • x) = a • e x) :
      letI := mA; letI := mB; A ≃ₗ[k] B := by
    letI := mA
    letI := mB
    exact { __ := e, map_smul' := h }
  refine build (AddCommGrpCat.of (structuralOpenCohomology X 0 U))
    (AddCommGrpCat.of Γ(X.left, U)) inferInstance (structuralSectionModule X U)
    (Ext.addEquiv₀.trans (additiveOpenHomAddEquiv X.left U
      (moduleAddSheaf X.left (SheafOfModules.unit X.left.ringCatSheaf)))) ?_
  dsimp only
  intro a x
  let φ := moduleScalarOfGlobal X.left (SheafOfModules.unit X.left.ringCatSheaf)
    (Scheme.constants X a)
  have he : Ext.addEquiv₀ (x.comp (Ext.mk₀ φ) (Nat.add_zero 0)) =
      Ext.addEquiv₀ x ≫ φ := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  change additiveOpenHomEquiv X.left U
      (moduleAddSheaf X.left (SheafOfModules.unit X.left.ringCatSheaf))
      (Ext.addEquiv₀ (x.comp (Ext.mk₀ φ) (Nat.add_zero 0))) =
    Scheme.constantSection X U a *
      (show Γ(X.left, U) from additiveOpenHomEquiv X.left U
        (moduleAddSheaf X.left (SheafOfModules.unit X.left.ringCatSheaf)) (Ext.addEquiv₀ x))
  erw [he, additiveOpenHomEquiv_naturality_coefficient]
  rfl

/-- The degree-zero comparison preserves the literal restrictions on actual opens. -/
theorem structuralOpenH0LinearEquiv_restriction {U V : X.left.Opens} (h : U ≤ V)
    (x : structuralOpenCohomology X 0 V) :
    structuralOpenH0LinearEquiv X U
        ((moduleHPrimePresheaf X.left (Scheme.constants X)
          (SheafOfModules.unit X.left.ringCatSheaf) 0).map (homOfLE h).op x) =
      structuralRestrictionLinearMap X h (structuralOpenH0LinearEquiv X V x) := by
  let A := moduleAddSheaf X.left (SheafOfModules.unit X.left.ringCatSheaf)
  let f := (additiveOpenFreeFunctor X.left).map (homOfLE h)
  have he : Ext.addEquiv₀ ((Ext.mk₀ f).comp x (Nat.zero_add 0)) =
      f ≫ Ext.addEquiv₀ x := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  change additiveOpenHomEquiv X.left U A
      (Ext.addEquiv₀ ((Ext.mk₀ f).comp x (Nat.zero_add 0))) =
    A.obj.map (homOfLE h).op (additiveOpenHomEquiv X.left V A (Ext.addEquiv₀ x))
  rw [he, additiveOpenHomEquiv_naturality]

/-- Whole-space native open cohomology is the original structural cohomology. -/
def structuralOpenTopLinearEquiv (n : ℕ) :
    structuralOpenCohomology X n ⊤ ≃ₗ[k] Scheme.structureCohomology k X n :=
  (moduleHPrimeTopLinearEquivOfHom X.left (Scheme.constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) n).trans
      (structureModuleCohomologyEquiv X n)

/-- The original signed Mayer–Vietoris difference is the signed literal section restriction. -/
theorem structuralMayerVietorisFromBiprod_apply (U V : X.left.Opens)
    (x : (structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V :
      ModuleCat.{u + 1} k)) :
    structuralOpenH0LinearEquiv X (U ⊓ V)
        (moduleMayerVietorisFromBiprod X.left (Scheme.constants X)
          (SheafOfModules.unit X.left.ringCatSheaf) U V 0 x) =
      structuralRestrictionLinearMap X inf_le_left
          (structuralOpenH0LinearEquiv X U
            ((biprod.fst : structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V ⟶
              structuralOpenCohomology X 0 U) x)) -
        structuralRestrictionLinearMap X inf_le_right
          (structuralOpenH0LinearEquiv X V
            ((biprod.snd : structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V ⟶
              structuralOpenCohomology X 0 V) x)) := by
  simp only [moduleMayerVietorisFromBiprod, biprod.desc_eq]
  change structuralOpenH0LinearEquiv X (U ⊓ V)
      ((moduleHPrimePresheaf X.left (Scheme.constants X)
          (SheafOfModules.unit X.left.ringCatSheaf) 0).map
          (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
          ((biprod.fst : structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V ⟶
            structuralOpenCohomology X 0 U) x) +
        -((moduleHPrimePresheaf X.left (Scheme.constants X)
          (SheafOfModules.unit X.left.ringCatSheaf) 0).map
          (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
          ((biprod.snd : structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V ⟶
            structuralOpenCohomology X 0 V) x))) = _
  rw [map_add, map_neg, structuralOpenH0LinearEquiv_restriction,
    structuralOpenH0LinearEquiv_restriction]
  exact (sub_eq_add_neg _ _).symm

/-- The range of the native difference becomes the sum of the two literal restriction ranges. -/
theorem structuralMayerVietoris_range (U V : X.left.Opens) :
    (LinearMap.range (moduleMayerVietorisFromBiprod X.left (Scheme.constants X)
        (SheafOfModules.unit X.left.ringCatSheaf) U V 0).hom).map
        (structuralOpenH0LinearEquiv X (U ⊓ V)).toLinearMap =
      LinearMap.range (structuralRestrictionLinearMap X (show U ⊓ V ≤ U from inf_le_left)) ⊔
        LinearMap.range (structuralRestrictionLinearMap X (show U ⊓ V ≤ V from inf_le_right)) := by
  let f := moduleMayerVietorisFromBiprod X.left (Scheme.constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) U V 0
  have hzero {A B : ModuleCat.{u + 1} k} (x : A) : (0 : A ⟶ B) x = 0 := rfl
  apply le_antisymm
  · rintro _ ⟨y, ⟨z, rfl⟩, rfl⟩
    erw [structuralMayerVietorisFromBiprod_apply]
    exact sub_mem
      (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  · refine sup_le ?_ ?_
    · rintro _ ⟨s, rfl⟩
      let z := (biprod.inl : structuralOpenCohomology X 0 U ⟶
        structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V)
          ((structuralOpenH0LinearEquiv X U).symm s)
      refine ⟨f z, ⟨z, rfl⟩, ?_⟩
      dsimp only [f, z]
      erw [structuralMayerVietorisFromBiprod_apply]
      simp only [← ConcreteCategory.comp_apply, biprod.inl_fst, biprod.inl_snd,
        ModuleCat.id_apply, hzero, map_zero, LinearEquiv.apply_symm_apply,
        sub_zero]
    · rintro _ ⟨s, rfl⟩
      let z := (biprod.inr : structuralOpenCohomology X 0 V ⟶
        structuralOpenCohomology X 0 U ⊞ structuralOpenCohomology X 0 V)
          (-((structuralOpenH0LinearEquiv X V).symm s))
      refine ⟨f z, ⟨z, rfl⟩, ?_⟩
      dsimp only [f, z]
      erw [structuralMayerVietorisFromBiprod_apply]
      simp only [← ConcreteCategory.comp_apply, biprod.inr_fst, biprod.inr_snd,
        ModuleCat.id_apply, hzero, map_zero, map_neg,
        LinearEquiv.apply_symm_apply, neg_zero, zero_sub, neg_neg]

/-- Affine vanishing makes the original first connecting map surjective. -/
theorem structuralMayerVietorisDelta_epi (U V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Epi (moduleMayerVietorisDelta X.left (Scheme.constants X)
      (SheafOfModules.unit X.left.ringCatSheaf) U V 0) := by
  let M : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf
  let := Scheme.Modules.unit_isLocallyFree X.left
  let : M.IsQuasicoherent := inferInstance
  let : Subsingleton ((moduleHPrimePresheaf X.left (Scheme.constants X) M 1).obj (op U)) :=
    subsingleton_sheafHPrime_of_isAffineOpen M U hU 0
  let : Subsingleton ((moduleHPrimePresheaf X.left (Scheme.constants X) M 1).obj (op V)) :=
    subsingleton_sheafHPrime_of_isAffineOpen M V hV 0
  have hS := moduleMayerVietorisSequence_exact X.left (Scheme.constants X) M U V 0
  apply (hS.exact 2).epi_f_iff.mpr
  change moduleMayerVietorisToBiprod X.left (Scheme.constants X) M U V 1 = 0
  apply biprod.hom_ext
  · simp only [moduleMayerVietorisToBiprod, biprod.lift_fst, zero_comp]
    ext x
    exact Subsingleton.elim _ _
  · simp only [moduleMayerVietorisToBiprod, biprod.lift_snd, zero_comp]
    ext x
    exact Subsingleton.elim _ _

/-- An exact pair with epimorphic second map gives the ordinary linear cokernel. -/
def structuralCokernelLinearEquiv {A B C : ModuleCat.{u + 1} k}
    (f : A ⟶ B) (g : B ⟶ C) (hz : f ≫ g = 0)
    (he : (ShortComplex.mk f g hz).Exact) (hg : Epi g) :
    C ≃ₗ[k] B ⧸ LinearMap.range f.hom := by
  let := hg
  exact (he.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv

/-- Original first open cohomology is the quotient by the original native difference. -/
def structuralOpenH1EquivNativeQuotient (U V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    structuralOpenCohomology X 1 (U ⊔ V) ≃ₗ[k]
      structuralOpenCohomology X 0 (U ⊓ V) ⧸
        LinearMap.range (moduleMayerVietorisFromBiprod X.left (Scheme.constants X)
          (SheafOfModules.unit X.left.ringCatSheaf) U V 0).hom := by
  let M : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf
  let P₀ := moduleHPrimePresheaf X.left (Scheme.constants X) M 0
  let P₁ := moduleHPrimePresheaf X.left (Scheme.constants X) M 1
  let f : P₀.obj (op U) ⊞ P₀.obj (op V) ⟶ P₀.obj (op (U ⊓ V)) :=
    moduleMayerVietorisFromBiprod X.left (Scheme.constants X) M U V 0
  let g : P₀.obj (op (U ⊓ V)) ⟶ P₁.obj (op (U ⊔ V)) :=
    moduleMayerVietorisDelta X.left (Scheme.constants X) M U V 0
  let hS := moduleMayerVietorisSequence_exact X.left (Scheme.constants X) M U V 0
  have hz : f ≫ g = 0 := hS.toIsComplex.zero 1
  have he : (ShortComplex.mk f g hz).Exact := hS.exact 1
  exact structuralCokernelLinearEquiv f g hz he (structuralMayerVietorisDelta_epi X U V hU hV)

/-- The actual structural `coherentH1` is the quotient of overlap sections by
the sum of the ranges of the two literal restrictions on a two-affine-open cover. -/
def structuralH1EquivTwoAffineQuotient (U V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Scheme.coherentH1 k X ≃ₗ[k]
      Γ(X.left, U ⊓ V) ⧸
        (LinearMap.range (structuralRestrictionLinearMap X (show U ⊓ V ≤ U from inf_le_left)) ⊔
          LinearMap.range
            (structuralRestrictionLinearMap X (show U ⊓ V ≤ V from inf_le_right))) := by
  let P := moduleHPrimePresheaf X.left (Scheme.constants X)
    (SheafOfModules.unit X.left.ringCatSheaf) 1
  let e : structuralOpenCohomology X 1 (U ⊔ V) ≃ₗ[k] Scheme.coherentH1 k X :=
    (P.mapIso (eqToIso hUV.symm).op).toLinearEquiv.trans (structuralOpenTopLinearEquiv X 1)
  exact e.symm.trans ((structuralOpenH1EquivNativeQuotient X U V hU hV).trans
    (Submodule.Quotient.equiv _ _ (structuralOpenH0LinearEquiv X (U ⊓ V))
      (structuralMayerVietoris_range X U V)))

end AlgebraicGeometry.Scheme.Cohomology
