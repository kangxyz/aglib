/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.CoverEffacement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.GaloisOverlapH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.GaloisPrimitives
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.LowDegree
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.UniqueAugmentation
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives

/-! # Original degree-two multiplicative cohomology of algebraic function fields

Individual original classes are effaced by actual finite Galois covers. The
original free Čech augmentation, Artinian overlap Picard vanishing, and actual
Amitsur primitives then apply the two-kernel Ext criterion. No Brauer comparison
or field cohomological-dimension hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

variable (K E : Type u) [Field K] [IsAlgClosed K] [Field E]
  [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

include K

attribute [local instance] hasSheafifyLarge

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original degree-two étale cohomology of `Gm` vanishes over every
algebraic extension of an algebraically closed rational function field. -/
theorem gmH2_eq_zero_of_algebraic_ratFunc
    (α : Sheaf.H.{w} (gm (Spec (.of E))) 2) : α = 0 := by
  let J := Scheme.smallEtaleTopology (Spec (.of E))
  let : EnoughInjectives (AbelianSheaf.{u, u + 1} (Spec (.of E))) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge.{u + 1, u} J
  obtain ⟨L, hL⟩ := exists_finiteGalois_ext_eq_zero E (gm (Spec (.of E))) 1 α
  let e := constantIntegerFreeTerminalIso.{u + 1, u, u + 1} J
    (StrictlyLocal.terminalIsTerminal E)
  let β : Ext.{w} (freeAbelianSheaf.{u + 1} J (StrictlyLocal.terminalObject E))
      (gm (Spec (.of E))) 2 := (Ext.mk₀ e.inv).comp α (Nat.zero_add 2)
  let f := Presheaf.Cech.familyMap (galoisCoverFamily E L)
  let π := Presheaf.Cech.sheafAugmentation f J
  let : QuasiIso π := Presheaf.Cech.sheafAugmentation_quasiIso_of_sizes f J
  let U := (∏ᶜ fun _ : Fin 2 => galoisCoverOver E L).left
  let : HasExt.{u + 2} (Sheaf (J.over U) AddCommGrpCat.{u + 1}) :=
    HasExt.standard _
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} U.left) := hasExtStandard U.left
  let g := (StrictlyLocal.terminalIsTerminal E).from
    ((Scheme.FiniteEtale.toEtale _).obj
      (Scheme.FiniteEtale.FieldGalois.Arbitrary.finiteFieldCover E L))
  have hL' : (Ext.mk₀ ((freeAbelianSheafFunctor.{u + 1} J).map g ≫ e.inv)).comp
      α (Nat.zero_add 2) = 0 := hL
  have hπ : (Ext.mk₀ (π.f 0)).comp β (Nat.zero_add 2) = 0 := by
    change (Ext.mk₀ ((Presheaf.Cech.sheafAugmentation
      (Presheaf.Cech.familyMap (fun _ : PUnit.{u + 2} => Over.mk g)) J).f 0)).comp
        β (Nat.zero_add 2) = 0
    rw [Presheaf.Cech.sheafAugmentation_zero_uniqueFamily]
    simpa only [β, Ext.mk₀_comp_mk₀_assoc, Category.assoc, Ext.comp_zero] using
      congrArg (fun γ => (Ext.mk₀ (Presheaf.Cech.uniqueAugmentationSource
        PUnit.{u + 2} g J)).comp γ (Nat.zero_add 2)) hL'
  have hβ : β = 0 :=
    Sheaf.BasisAcyclicity.ext_two_eq_zero_of_augmentation_primitives π
      (galoisCech_ext_one_eq_zero.{u, w, u + 2, u + 2} E L)
      (galoisCech_exists_primitive E L K) β hπ
  have h := congrArg (fun γ => (Ext.mk₀ e.hom).comp γ (Nat.zero_add 2)) hβ
  simpa only [β, Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
    Ext.mk₀_id_comp, Ext.comp_zero] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
