/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.CommonFractionalIdeal
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles
public import Aglib.AlgebraicGeometry.Cohomology.Support.Skyscraper
public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StalkScalars
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Euler
public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Actual common-quotient degree and conditional proper product formula

The principal degree is computed from the original quotient sheaves and their
structural field actions. Proper H1(O) finiteness remains an explicit input;
no unconditional producer for the original family #6 is claimed here.
Authoring basis 3397a339, unchanged Lean 4.34.1 / Mathlib d13 / Quillen 0.7.
The scalar bridge is used at its accepted and committed SHA 4a6343d3.
-/

open _root_.AlgebraicGeometry.Scheme (structureCohomology)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (finiteClosedSupportModuleCohomology_positive moduleAdditiveStalk moduleCohomology
    structureModuleCohomologyEquiv)
open AlgebraicGeometry.Scheme.Cohomology.QuotientEuler
  (moduleEulerQuotient_dim quotientSequence quotientSequence_shortExact)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal
open AlgebraicGeometry.Scheme.Modules
  (stalkBaseModule stalkBaseTower stalkBaseModule_germ_smul stalkBase_finite)
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve
open Picard.Degree Picard.Degree.CommonFractionalIdeal
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.CommonQuotientDegree
universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
def leftStalkDimension (f : X.functionFieldˣ) (x : X) : ℕ :=
  letI := stalkBaseModule X p (leftQuotient X f) x
  Module.finrank k ((leftQuotient X f).presheaf.stalk x)
def rightStalkDimension (f : X.functionFieldˣ) (x : X) : ℕ :=
  letI := stalkBaseModule X p (rightQuotient X f) x
  Module.finrank k ((rightQuotient X f).presheaf.stalk x)

theorem degree_principal_eq_sum (hdim : topologicalKrullDim X = 1) (f : X.functionFieldˣ)
    (S : Finset X) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hleft : ∀ x, x ∉ S → Subsingleton ((leftQuotient X f).presheaf.stalk x))
    (hright : ∀ x, x ∉ S → Subsingleton ((rightQuotient X f).presheaf.stalk x)) :
    degDiv X p (Divisors.principal X (Additive.ofMul f)) =
      ∑ x ∈ S, ((leftStalkDimension X p f x : ℤ) - (rightStalkDimension X p f x : ℤ)) := by
  classical
  let z := Divisors.principal X (Additive.ofMul f)
  let j : S → Scheme.ClosedPoint X := fun x => ⟨x.val, hclosed x.val x.property⟩
  let T : Finset (Scheme.ClosedPoint X) := Finset.univ.image j
  have hinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : Scheme.ClosedPoint X => x.val) h
  have hsub : z.support ⊆ T := by
    intro x hx
    have hv : x.val ∈ S := by
      by_contra h
      let := hleft x.val h
      let := hright x.val h
      have ho : X.ord (f : X.functionField) x.val = 0 := by
        rw [order_eq_quotient_stalk_length X x.val
          (ProductFormula.closedPoint_coheight_one X hdim x.val x.property) f]
        simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, sub_self]
      exact (Finsupp.mem_support_iff.mp hx) ho
    exact Finset.mem_image.mpr ⟨⟨x.val,hv⟩, Finset.mem_univ _, by apply Subtype.ext; rfl⟩
  have hlocal (x : S) : z (j x) * weight X p (j x) =
      (leftStalkDimension X p f x.val : ℤ) - (rightStalkDimension X p f x.val : ℤ) :=
    weighted_order_eq_quotient_stalk_finrank X p f x.val (j x).property
      (ProductFormula.closedPoint_coheight_one X hdim x.val (j x).property)
  calc
    degDiv X p z = ∑ x ∈ z.support, z x * weight X p x := degDiv_apply X p z
    _ = ∑ x ∈ T, z x * weight X p x := by
      apply Finset.sum_subset hsub
      intro x _ hx
      have hz : z x = 0 := by simpa only [Finsupp.mem_support_iff, not_ne_iff] using hx
      rw [hz, zero_mul]
    _ = ∑ x : S, z (j x) * weight X p (j x) :=
      Finset.sum_image (fun a _ b _ hab => hinj hab)
    _ = ∑ x : S, ((leftStalkDimension X p f x.val : ℤ) - (rightStalkDimension X p f x.val : ℤ)) :=
      Finset.sum_congr rfl (fun x _ => hlocal x)
    _ = _ := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach S (fun x =>
          (leftStalkDimension X p f x : ℤ) - (rightStalkDimension X p f x : ℤ)))

/-- The actual additive-stalk action agrees with the native structural action. -/
def additiveStalkNativeEquiv (Y : FScheme k) (M : Y.left.Modules) (x : Y.left) :
    letI := stalkBaseModule Y.left Y.hom M x
    Scheme.Cohomology.moduleAdditiveStalk Y M x ≃ₗ[k] M.presheaf.stalk x :=
  (Scheme.Cohomology.nativeModuleStalkLinearEquiv Y M x).symm


/-- Finite closed support of the actual native stalks kills positive cohomology. -/
theorem moduleCohomology_positive_of_native_stalk_support (Y : FScheme k)
    (M : Y.left.Modules) (S : Finset Y.left)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set Y.left))
    (hzero : ∀ x, x ∉ S → Subsingleton (M.presheaf.stalk x)) (n : ℕ) :
    Subsingleton (moduleCohomology k Y M (n + 1)) := by
  classical
  let e := S.equivFin
  let p : Fin S.card → Y.left := fun i => (e.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hc (i : Fin S.card) : IsClosed ({p i} : Set Y.left) :=
    hclosed (e.symm i).val (e.symm i).property
  have hM (x : Y.left) (hx : x ∉ Set.range p) :
      IsZero (moduleAdditiveStalk Y M x) := by
    have hxS : x ∉ S := fun hxS => hx ⟨e ⟨x,hxS⟩, by simp [p]⟩
    let : Subsingleton (moduleAdditiveStalk Y M x) := hzero x hxS
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact finiteClosedSupportModuleCohomology_positive Y M p hp hc hM n


variable (Y : FScheme k) [hIntegralY : IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left]
variable [LocallyOfFiniteType Y.hom]
theorem leftH0_finite_of_support (hdim : topologicalKrullDim Y.left = 1) (f : Y.left.functionFieldˣ)
    (S : Finset Y.left) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set Y.left))
    (hzero : ∀ x, x ∉ S → Subsingleton ((leftQuotient Y.left f).presheaf.stalk x)) :
    Module.Finite k (Scheme.Cohomology.moduleCohomology k Y (leftQuotient Y.left f) 0) := by
  classical
  let e := S.equivFin
  let p : Fin S.card → Y.left := fun i => (e.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hc (x : Fin S.card) : IsClosed ({p x} : Set Y.left) := hclosed (e.symm x).val (e.symm
    x).property
  have hM (x : Y.left) (hx : x ∉ Set.range p) :
      IsZero (Scheme.Cohomology.moduleAdditiveStalk Y (leftQuotient Y.left f) x) := by
    have hxS : x ∉ S := fun hxS => hx ⟨e ⟨x,hxS⟩, by simp [p]⟩
    let : Subsingleton (Scheme.Cohomology.moduleAdditiveStalk Y (leftQuotient Y.left f) x) :=
      hzero x hxS
    apply AddCommGrpCat.isZero_of_subsingleton
  let (x : Fin S.card) : FiniteDimensional k (Scheme.Cohomology.moduleAdditiveStalk Y
    (leftQuotient Y.left f) (p x)) := by
    let := stalkBaseModule Y.left Y.hom (leftQuotient Y.left f) (p x)
    have hlocal := quotient_stalks_finiteLength Y.left (p x)
      (ProductFormula.closedPoint_coheight_one Y.left hdim (p x) (hc x)) f
    let : Module.Finite k ((leftQuotient Y.left f).presheaf.stalk (p x)) :=
      stalkBase_finite Y.left Y.hom (leftQuotient Y.left f) (p x) (hc x) hlocal.1
    exact (additiveStalkNativeEquiv Y (leftQuotient Y.left f) (p x)).symm.finiteDimensional
  exact Scheme.Cohomology.finiteClosedSupportModuleH0_finite Y (leftQuotient Y.left f) p hp hc hM

theorem leftH0_finrank_of_support (hdim : topologicalKrullDim Y.left = 1) (f :
  Y.left.functionFieldˣ)
    (S : Finset Y.left) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set Y.left))
    (hzero : ∀ x, x ∉ S → Subsingleton ((leftQuotient Y.left f).presheaf.stalk x)) :
    Module.finrank k (Scheme.Cohomology.moduleCohomology k Y (leftQuotient Y.left f) 0) =
      ∑ x ∈ S, leftStalkDimension Y.left Y.hom f x := by
  classical
  let e := S.equivFin
  let p : Fin S.card → Y.left := fun i => (e.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hc (x : Fin S.card) : IsClosed ({p x} : Set Y.left) := hclosed (e.symm x).val (e.symm
    x).property
  have hM (x : Y.left) (hx : x ∉ Set.range p) :
      IsZero (Scheme.Cohomology.moduleAdditiveStalk Y (leftQuotient Y.left f) x) := by
    have hxS : x ∉ S := fun hxS => hx ⟨e ⟨x,hxS⟩, by simp [p]⟩
    let : Subsingleton (Scheme.Cohomology.moduleAdditiveStalk Y (leftQuotient Y.left f) x) :=
      hzero x hxS
    apply AddCommGrpCat.isZero_of_subsingleton
  let (x : Fin S.card) : FiniteDimensional k (Scheme.Cohomology.moduleAdditiveStalk Y
    (leftQuotient Y.left f) (p x)) := by
    let := stalkBaseModule Y.left Y.hom (leftQuotient Y.left f) (p x)
    have hlocal := quotient_stalks_finiteLength Y.left (p x)
      (ProductFormula.closedPoint_coheight_one Y.left hdim (p x) (hc x)) f
    let : Module.Finite k ((leftQuotient Y.left f).presheaf.stalk (p x)) :=
      stalkBase_finite Y.left Y.hom (leftQuotient Y.left f) (p x) (hc x) hlocal.1
    exact (additiveStalkNativeEquiv Y (leftQuotient Y.left f) (p x)).symm.finiteDimensional
  rw [Scheme.Cohomology.finiteClosedSupportModuleH0_finrank Y (leftQuotient Y.left f) p hp hc hM]
  calc
    ∑ x : Fin S.card, Module.finrank k (Scheme.Cohomology.moduleAdditiveStalk Y (leftQuotient
      Y.left f) (p x)) =
        ∑ x : Fin S.card, leftStalkDimension Y.left Y.hom f (p x) := by
      apply Finset.sum_congr rfl
      intro x _
      let := stalkBaseModule Y.left Y.hom (leftQuotient Y.left f) (p x)
      exact (additiveStalkNativeEquiv Y (leftQuotient Y.left f) (p x)).finrank_eq
    _ = ∑ x : S, leftStalkDimension Y.left Y.hom f x.val := by
      exact e.symm.sum_comp (fun x : S => leftStalkDimension Y.left Y.hom f x.val)
    _ = _ := by simpa only [Finset.attach_eq_univ] using Finset.sum_attach S (leftStalkDimension
      Y.left Y.hom f)
theorem rightH0_finite_of_support (hdim : topologicalKrullDim Y.left = 1) (f :
  Y.left.functionFieldˣ)
    (S : Finset Y.left) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set Y.left))
    (hzero : ∀ x, x ∉ S → Subsingleton ((rightQuotient Y.left f).presheaf.stalk x)) :
    Module.Finite k (Scheme.Cohomology.moduleCohomology k Y (rightQuotient Y.left f) 0) := by
  classical
  let e := S.equivFin
  let p : Fin S.card → Y.left := fun i => (e.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hc (x : Fin S.card) : IsClosed ({p x} : Set Y.left) := hclosed (e.symm x).val (e.symm
    x).property
  have hM (x : Y.left) (hx : x ∉ Set.range p) :
      IsZero (Scheme.Cohomology.moduleAdditiveStalk Y (rightQuotient Y.left f) x) := by
    have hxS : x ∉ S := fun hxS => hx ⟨e ⟨x,hxS⟩, by simp [p]⟩
    let : Subsingleton (Scheme.Cohomology.moduleAdditiveStalk Y (rightQuotient Y.left f) x) :=
      hzero x hxS
    apply AddCommGrpCat.isZero_of_subsingleton
  let (x : Fin S.card) : FiniteDimensional k (Scheme.Cohomology.moduleAdditiveStalk Y
    (rightQuotient Y.left f) (p x)) := by
    let := stalkBaseModule Y.left Y.hom (rightQuotient Y.left f) (p x)
    have hlocal := quotient_stalks_finiteLength Y.left (p x)
      (ProductFormula.closedPoint_coheight_one Y.left hdim (p x) (hc x)) f
    let : Module.Finite k ((rightQuotient Y.left f).presheaf.stalk (p x)) :=
      stalkBase_finite Y.left Y.hom (rightQuotient Y.left f) (p x) (hc x) hlocal.2
    exact (additiveStalkNativeEquiv Y (rightQuotient Y.left f) (p x)).symm.finiteDimensional
  exact Scheme.Cohomology.finiteClosedSupportModuleH0_finite Y (rightQuotient Y.left f) p hp hc hM

theorem rightH0_finrank_of_support (hdim : topologicalKrullDim Y.left = 1) (f :
  Y.left.functionFieldˣ)
    (S : Finset Y.left) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set Y.left))
    (hzero : ∀ x, x ∉ S → Subsingleton ((rightQuotient Y.left f).presheaf.stalk x)) :
    Module.finrank k (Scheme.Cohomology.moduleCohomology k Y (rightQuotient Y.left f) 0) =
      ∑ x ∈ S, rightStalkDimension Y.left Y.hom f x := by
  classical
  let e := S.equivFin
  let p : Fin S.card → Y.left := fun i => (e.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hc (x : Fin S.card) : IsClosed ({p x} : Set Y.left) := hclosed (e.symm x).val (e.symm
    x).property
  have hM (x : Y.left) (hx : x ∉ Set.range p) :
      IsZero (Scheme.Cohomology.moduleAdditiveStalk Y (rightQuotient Y.left f) x) := by
    have hxS : x ∉ S := fun hxS => hx ⟨e ⟨x,hxS⟩, by simp [p]⟩
    let : Subsingleton (Scheme.Cohomology.moduleAdditiveStalk Y (rightQuotient Y.left f) x) :=
      hzero x hxS
    apply AddCommGrpCat.isZero_of_subsingleton
  let (x : Fin S.card) : FiniteDimensional k (Scheme.Cohomology.moduleAdditiveStalk Y
    (rightQuotient Y.left f) (p x)) := by
    let := stalkBaseModule Y.left Y.hom (rightQuotient Y.left f) (p x)
    have hlocal := quotient_stalks_finiteLength Y.left (p x)
      (ProductFormula.closedPoint_coheight_one Y.left hdim (p x) (hc x)) f
    let : Module.Finite k ((rightQuotient Y.left f).presheaf.stalk (p x)) :=
      stalkBase_finite Y.left Y.hom (rightQuotient Y.left f) (p x) (hc x) hlocal.2
    exact (additiveStalkNativeEquiv Y (rightQuotient Y.left f) (p x)).symm.finiteDimensional
  rw [Scheme.Cohomology.finiteClosedSupportModuleH0_finrank Y (rightQuotient Y.left f) p hp hc hM]
  calc
    ∑ x : Fin S.card, Module.finrank k (Scheme.Cohomology.moduleAdditiveStalk Y (rightQuotient
      Y.left f) (p x)) =
        ∑ x : Fin S.card, rightStalkDimension Y.left Y.hom f (p x) := by
      apply Finset.sum_congr rfl
      intro x _
      let := stalkBaseModule Y.left Y.hom (rightQuotient Y.left f) (p x)
      exact (additiveStalkNativeEquiv Y (rightQuotient Y.left f) (p x)).finrank_eq
    _ = ∑ x : S, rightStalkDimension Y.left Y.hom f x.val := by
      exact e.symm.sum_comp (fun x : S => rightStalkDimension Y.left Y.hom f x.val)
    _ = _ := by simpa only [Finset.attach_eq_univ] using Finset.sum_attach S (rightStalkDimension
      Y.left Y.hom f)
theorem principal_degree_eq_H0_difference (hdim : topologicalKrullDim Y.left = 1)
    (f : Y.left.functionFieldˣ) :
    degDiv Y.left Y.hom (Divisors.principal Y.left (Additive.ofMul f)) =
      (Module.finrank k (Scheme.Cohomology.moduleCohomology k Y (leftQuotient Y.left f) 0) : ℤ) -
        (Module.finrank k (Scheme.Cohomology.moduleCohomology k Y (rightQuotient Y.left f) 0) : ℤ)
          := by
  classical
  obtain ⟨S,hclosed,hleft,hright⟩ := exists_finite_closed_quotient_stalk_support Y.left hdim f
  rw [leftH0_finrank_of_support Y hdim f S hclosed hleft,
    rightH0_finrank_of_support Y hdim f S hclosed hright, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  exact degree_principal_eq_sum Y.left Y.hom hdim f S hclosed hleft hright


theorem leftH0_finite (hdim : topologicalKrullDim Y.left = 1) (f : Y.left.functionFieldˣ) :
    Module.Finite k (moduleCohomology k Y (leftQuotient Y.left f) 0) := by
  obtain ⟨S,hclosed,hleft,_⟩ := exists_finite_closed_quotient_stalk_support Y.left hdim f
  exact leftH0_finite_of_support Y hdim f S hclosed hleft

theorem rightH0_finite (hdim : topologicalKrullDim Y.left = 1) (f : Y.left.functionFieldˣ) :
    Module.Finite k (moduleCohomology k Y (rightQuotient Y.left f) 0) := by
  obtain ⟨S,hclosed,_,hright⟩ := exists_finite_closed_quotient_stalk_support Y.left hdim f
  exact rightH0_finite_of_support Y hdim f S hclosed hright

omit [LocallyOfFiniteType Y.hom] in
theorem leftCohomology_positive (hdim : topologicalKrullDim Y.left = 1)
    (f : Y.left.functionFieldˣ) (n : ℕ) :
    Subsingleton (moduleCohomology k Y (leftQuotient Y.left f) (n + 1)) := by
  obtain ⟨S,hclosed,hleft,_⟩ := exists_finite_closed_quotient_stalk_support Y.left hdim f
  exact moduleCohomology_positive_of_native_stalk_support Y (leftQuotient Y.left f) S hclosed
    hleft n

omit [LocallyOfFiniteType Y.hom] in
theorem rightCohomology_positive (hdim : topologicalKrullDim Y.left = 1)
    (f : Y.left.functionFieldˣ) (n : ℕ) :
    Subsingleton (moduleCohomology k Y (rightQuotient Y.left f) (n + 1)) := by
  obtain ⟨S,hclosed,_,hright⟩ := exists_finite_closed_quotient_stalk_support Y.left hdim f
  exact moduleCohomology_positive_of_native_stalk_support Y (rightQuotient Y.left f) S hclosed
    hright n

omit hIntegralY [AlgebraicGeometry.IsNoetherian Y.left] [LocallyOfFiniteType Y.hom] in
theorem regularH0_finite [IsIntegral Y.left] [IsProper Y.hom] :
    Module.Finite k (moduleCohomology k Y (regularModule Y.left) 0) := by
  let := Scheme.Cohomology.properStructureCohomologyFinite _ Y 0 inferInstance
  exact (structureModuleCohomologyEquiv Y 0).symm.finiteDimensional

/- The original principal product formula follows from the explicit actual H1(O)
finiteness input; no regularity, DVR or geometric-integrality condition is added. -/
omit [LocallyOfFiniteType Y.hom] in
theorem principalProductFormula_of_structureH1_finite [IsProper Y.hom]
    (hdim : topologicalKrullDim Y.left = 1)
    (hH1 : Module.Finite k (structureCohomology k Y 1)) :
    PrincipalProductFormula Y.left Y.hom := by
  let := hH1
  have hO1 : Module.Finite k (moduleCohomology k Y (regularModule Y.left) 1) :=
    (structureModuleCohomologyEquiv Y 1).symm.finiteDimensional
  intro f
  have hl := @moduleEulerQuotient_dim.{u} k inferInstance Y
    (quotientSequence Y (leftInclusion Y.left f))
    (quotientSequence_shortExact Y (leftInclusion Y.left f))
    (regularH0_finite Y) (leftH0_finite Y hdim f) hO1
    (leftCohomology_positive Y hdim f 0)
  have hr := @moduleEulerQuotient_dim.{u} k inferInstance Y
    (quotientSequence Y (rightInclusion Y.left f))
    (quotientSequence_shortExact Y (rightInclusion Y.left f))
    (regularH0_finite Y) (rightH0_finite Y hdim f) hO1
    (rightCohomology_positive Y hdim f 0)
  change (Module.finrank k (moduleCohomology k Y (leftQuotient Y.left f) 0) : ℤ) =
    (Module.finrank k (moduleCohomology k Y (regularModule Y.left) 0) : ℤ) -
    (Module.finrank k (moduleCohomology k Y (commonIdeal Y.left f) 0) : ℤ) +
    (Module.finrank k (moduleCohomology k Y (commonIdeal Y.left f) 1) : ℤ) -
    (Module.finrank k (moduleCohomology k Y (regularModule Y.left) 1) : ℤ) at hl
  change (Module.finrank k (moduleCohomology k Y (rightQuotient Y.left f) 0) : ℤ) =
    (Module.finrank k (moduleCohomology k Y (regularModule Y.left) 0) : ℤ) -
    (Module.finrank k (moduleCohomology k Y (commonIdeal Y.left f) 0) : ℤ) +
    (Module.finrank k (moduleCohomology k Y (commonIdeal Y.left f) 1) : ℤ) -
    (Module.finrank k (moduleCohomology k Y (regularModule Y.left) 1) : ℤ) at hr
  rw [principal_degree_eq_H0_difference Y hdim f]
  exact sub_eq_zero.mpr (hl.trans hr.symm)


end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.CommonQuotientDegree
