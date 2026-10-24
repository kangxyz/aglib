/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext1.Representability
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Original open-restriction kernels and actual extensions

An original structure-module H1 class killed by the actual structural
restriction map has a short exact representative with the original
endpoints and an actual retraction on the original open over-site.
The native Ext/H1 comparison, its restriction equation and the canonical
unit isomorphism retain the original cohomology map.

The current consumer is the punctured complementary graph in the
normal-surface H1 restriction theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace

namespace CategoryTheory.ShortComplex.ShortExact

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The canonical class of an actual short exact complex vanishes exactly
when that same complex has a splitting. -/
public theorem extClass_eq_zero_iff_splitting {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ Nonempty S.Splitting := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS
      (Ext.mk₀ (𝟙 S.X₃)) (show 0 + 1 = 1 from rfl) (by simp only [hz, Ext.comp_zero])
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective x
    have hsg : s ≫ S.g = 𝟙 S.X₃ :=
      (Ext.mk₀_bijective S.X₃ S.X₃).injective (by
        simpa only [Ext.mk₀_comp_mk₀] using hx)
    exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact s hsg hS.mono_f⟩
  · rintro ⟨s⟩
    have h := congrArg (fun z : Ext.{w} S.X₂ S.X₁ 1 =>
      (Ext.mk₀ s.s).comp z (Nat.zero_add 1)) hS.comp_extClass
    simpa only [Ext.mk₀_comp_mk₀_assoc, s.s_g, Ext.mk₀_id_comp, Ext.comp_zero] using h

end CategoryTheory.ShortComplex.ShortExact

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) (U : X.Opens)

local notation "Oₓ" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)
local notation "Oᵤ" =>
  (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules)

/-- Vanishing under the original structural H1 restriction constructs a
short exact representative and the precise original over-site retraction
needed by the complementary-section graph construction. -/
public theorem exists_extension_retraction_of_structureRestriction_eq_zero
    (c : Sheaf.H.{u + 1} (moduleAddSheaf X Oₓ) 1)
    (hc : moduleCohomologyMapAlong U.ι (Scheme.Hom.structureModuleMap U.ι) 1 c = 0) :
    ∃ E : Ext1.Extension Oₓ Oₓ,
      moduleExtCohomologyMap X Oₓ 1 E.extClass = c ∧
      ∃ rU : E.middle.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U,
        (SheafOfModules.overFunctor X.ringCatSheaf U).map E.i ≫ rU = 𝟙 _ := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OU : U.toScheme.Modules := SheafOfModules.unit U.toScheme.ringCatSheaf
  let M : U.toScheme.Modules := (Scheme.Modules.restrictFunctor U.ι).obj OX
  let : (Scheme.Modules.restrictFunctor U.ι).Additive := ⟨by intros; rfl⟩
  let : (Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let : (Scheme.Modules.restrictFunctor U.ι).IsRightAdjoint :=
    Scheme.Modules.restrictFunctor_isRightAdjoint U.ι
  let : (Scheme.Modules.restrictFunctor U.ι).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction U.ι).isLeftAdjoint
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := inferInstance
  let : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι) := inferInstance
  let e : M ≅ OU :=
    Scheme.Modules.restrictUnitIso U.ι
  let unit := (Scheme.Modules.restrictAdjunction U.ι).unit.app OX
  have hunit : unit ≫ (Scheme.Modules.pushforward U.ι).map e.hom =
      Scheme.Hom.structureModuleMap U.ι := by
    have h := (Scheme.Modules.restrictAdjunction U.ι).homEquiv_unit OX OU
      (Scheme.Modules.restrictUnitIso U.ι).hom
    exact h.symm.trans (Scheme.Modules.restrictUnitIso_hom_adjoint U.ι)
  have hRzero : moduleCohomologyMapAlong U.ι unit 1 c = 0 := by
    apply (bijective_sheafH_map_of_iso e 1).injective
    rw [map_zero]
    have h := moduleCohomologyMapAlong_postcomp U.ι unit e.hom 1 c
    rw [hunit] at h
    exact h.symm.trans hc
  let xi : Ext.{u + 1} (C := X.Modules) OX OX 1 :=
    (moduleExtCohomologyAddEquiv X OX 1).symm c
  have hxi : moduleExtCohomologyMap X OX 1 xi = c :=
    (moduleExtCohomologyAddEquiv X OX 1).apply_symm_apply c
  let restrictedXi : Ext.{u + 1} (C := U.toScheme.Modules) M M 1 :=
    Ext.mapExactFunctor (C := X.Modules) (D := U.toScheme.Modules)
      (Scheme.Modules.restrictFunctor U.ι) xi
  let zeta : Ext.{u + 1} (C := U.toScheme.Modules) OU M 1 :=
    (Ext.mk₀ (C := U.toScheme.Modules) e.inv : Ext.{u + 1} (C := U.toScheme.Modules) OU
      M 0).comp (C := U.toScheme.Modules)
        restrictedXi (Nat.zero_add 1)
  let comparison : Ext.{u + 1} (C := U.toScheme.Modules) OU M 1 →+
      Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme M) 1 :=
    moduleExtCohomologyMap U.toScheme M 1
  have hzeta : zeta = 0 := by
    apply (moduleExtCohomologyMap_bijective U.toScheme M 1).injective
    have h := moduleExtCohomologyMap_restrict U.ι OX 1 xi
    have hzero : moduleCohomologyMapAlong U.ι unit 1
        (moduleExtCohomologyMap X OX 1 xi) = 0 :=
      (congrArg (moduleCohomologyMapAlong U.ι unit 1) hxi).trans hRzero
    have hmap : comparison zeta = 0 :=
      h.symm.trans hzero
    exact hmap.trans comparison.map_zero.symm
  have hmapxi : restrictedXi = 0 := by
    have h := congrArg (fun z : Ext.{u + 1} (C := U.toScheme.Modules) OU M 1 =>
      (Ext.mk₀ (C := U.toScheme.Modules) e.hom : Ext.{u + 1} (C := U.toScheme.Modules)
        M OU 0).comp (C := U.toScheme.Modules)
          z (Nat.zero_add 1)) hzeta
    simpa only [zeta, Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
      Ext.mk₀_id_comp, Ext.comp_zero] using h
  obtain ⟨E, hE⟩ := Ext1.exists_extension xi
  have hEc : moduleExtCohomologyMap X OX 1 E.extClass = c := by
    rw [hE]
    exact hxi
  have hRclass :
      (E.shortExact.map_of_exact (Scheme.Modules.restrictFunctor U.ι)).extClass = 0 := by
    rw [← Ext.mapExactFunctor_extClass (C := X.Modules) (D := U.toScheme.Modules)
      (Scheme.Modules.restrictFunctor U.ι) E.shortExact]
    change Ext.mapExactFunctor (C := X.Modules) (D := U.toScheme.Modules)
      (Scheme.Modules.restrictFunctor U.ι) E.extClass = 0
    rw [hE]
    exact hmapxi
  obtain ⟨sU⟩ :=
    (ShortComplex.ShortExact.extClass_eq_zero_iff_splitting
      (E.shortExact.map_of_exact (Scheme.Modules.restrictFunctor U.ι))).mp hRclass
  let eta := Scheme.Modules.overFunctorEquiv U
  let rU : E.middle.over U ⟶ OX.over U :=
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimage
      (eta.hom.app E.middle ≫ sU.r ≫ eta.inv.app OX)
  have hrU : (Scheme.Modules.overEquiv U).functor.map rU =
      eta.hom.app E.middle ≫ sU.r ≫ eta.inv.app OX :=
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage _
  have hnat : (Scheme.Modules.overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map E.i) ≫
      eta.hom.app E.middle = eta.hom.app OX ≫ (Scheme.Modules.restrictFunctor U.ι).map E.i :=
    eta.hom.naturality E.i
  have hsplit : (Scheme.Modules.restrictFunctor U.ι).map E.i ≫ sU.r =
      𝟙 M := sU.f_r
  refine ⟨E, hEc, rU, ?_⟩
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hrU]
  calc
    (Scheme.Modules.overEquiv U).functor.map
        ((SheafOfModules.overFunctor X.ringCatSheaf U).map E.i) ≫
        (eta.hom.app E.middle ≫ sU.r ≫ eta.inv.app OX) =
      ((Scheme.Modules.overEquiv U).functor.map
        ((SheafOfModules.overFunctor X.ringCatSheaf U).map E.i) ≫
        eta.hom.app E.middle) ≫ sU.r ≫ eta.inv.app OX := by
          simp only [Category.assoc]
    _ = (eta.hom.app OX ≫ (Scheme.Modules.restrictFunctor U.ι).map E.i) ≫
        sU.r ≫ eta.inv.app OX := by rw [hnat]
    _ = eta.hom.app OX ≫ ((Scheme.Modules.restrictFunctor U.ι).map E.i ≫ sU.r) ≫
        eta.inv.app OX := by
      simp only [Category.assoc]
    _ = eta.hom.app OX ≫ eta.inv.app OX := by rw [hsplit, Category.id_comp]
    _ = 𝟙 _ := eta.hom_inv_id_app OX

end AlgebraicGeometry.Scheme.Cohomology
