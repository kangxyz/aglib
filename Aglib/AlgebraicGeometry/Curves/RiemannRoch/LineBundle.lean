/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StalkScalars
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ExactSequences
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Euler
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles
public import Aglib.AlgebraicGeometry.Cohomology.Support.Skyscraper
public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Curves.Picard.LocalTrivialization
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.CommonFractionalIdeal
public import Aglib.AlgebraicGeometry.Curves.Genus
public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
# Actual divisor modifications and Riemann–Roch

This file constructs the actual inclusions O(A) -> O(B), their categorical
cokernels, and finite closed support. On actual stalks, explicit principal
generators identify the inclusion with multiplication by a nonzero stalk
element of order B(x)-A(x). The quotient is the actual R/(a); its full length
and the original residue-field degree give its dimension over the structural
base field. The field-action comparison is the equality proved in CurveEuler.

The actual cohomology exact sequence then propagates finiteness before Euler
arithmetic. Two modifications from min(D,0), together with the existing divisor
classification, identify the actual Euler expression with the existing divisor
and Picard degree. The actual constants bijection identifies H0(O) with the
field, and H1(O) retains the original coherent genus.

The conditional reduction has only actual coherentH1 finiteness as an added
input. The final theorem supplies it from native proper structure-sheaf
cohomology finiteness at degree one and proves the unchanged LineBundleRiemannRoch
family in Curves/RiemannRoch.lean:49–59. No dimension-vanishing family is used.

Mathematical comparison: Stacks Tags 0AYY (effective divisor modification),
02M0 (residue-weighted local length), and 0B5B (Riemann–Roch). Degree is the
existing divisor/Picard degree, rather than an Euler-characteristic definition.
The local quotient calculation retains all multiplicities and residue weights.

Authoring basis: project `3397a339b6a52fbba586dae127aa729d873b771d`,
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and
Quillen `83629578a3d70787d41ec631f5234af8758716af`.
-/

open _root_.AlgebraicGeometry.Scheme (coherentH1 constants)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (finiteClosedSupportModuleCohomology_positive finiteClosedSupportModuleH0_finite
    finiteClosedSupportModuleH0_finrank moduleAdditiveStalk moduleAdditiveStalkModule
    moduleAdditiveStalkModule_eq moduleCohomology moduleCohomologyIso
    moduleCohomology_finite_middle moduleEuler_of_shortExact moduleH0Equiv moduleH0H1_finite_iff
    structureModuleCohomologyEquiv)
open AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)



@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules.RationalFunctions (rationalValue rationalValueEquiv)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

theorem fractionalPresheaf_mono {A B : Divisor X} (h : A ≤ B) :
    fractionalPresheaf X A ≤ fractionalPresheaf X B := by
  intro U s hs
  by_cases hU : Nonempty U.unop
  · let := hU
    simp only [fractionalPresheaf, dite_eq_left hU, Submodule.mem_comap] at hs ⊢
    rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr (fun x hx => (hs x hx).trans (add_le_add le_rfl (h x)))
  · simp only [fractionalPresheaf, dite_eq_right hU, Submodule.mem_top]

/-- The inclusion of divisor sheaves induced by the coefficientwise inequality A ≤ B. -/
def divisorInclusion {A B : Divisor X} (h : A ≤ B) :
    divisorSheaf X A ⟶ divisorSheaf X B :=
  ⟨PresheafOfModules.Submodule.homOfLE (fractionalPresheaf_mono X h)⟩

instance divisorInclusion_mono {A B : Divisor X} (h : A ≤ B) :
    Mono (divisorInclusion X h) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  exact inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE
    (fractionalPresheaf_mono X h)))

/-- The cokernel sheaf of the inclusion from the divisor sheaf of A to that of B. -/
def divisorQuotient {A B : Divisor X} (h : A ≤ B) : X.Modules :=
  cokernel (divisorInclusion X h)

/-- The canonical divisor-sheaf inclusion followed by its cokernel projection. -/
def divisorQuotientSequence {A B : Divisor X} (h : A ≤ B) : ShortComplex X.Modules :=
  ShortComplex.mk (divisorInclusion X h) (cokernel.π (divisorInclusion X h))
    (cokernel.condition _)

theorem divisorQuotientSequence_shortExact {A B : Divisor X} (h : A ≤ B) :
    (divisorQuotientSequence X h).ShortExact := by
  dsimp only [divisorQuotientSequence]
  exact { exact := ShortComplex.exact_cokernel (divisorInclusion X h)
          mono_f := divisorInclusion_mono X h
          epi_g := inferInstanceAs (Epi (cokernel.π (divisorInclusion X h))) }

theorem fractionalPresheaf_obj_eq_of_eq_on_open {A B : Divisor X} (U : X.Opens)
    (h : ∀ y : ClosedPoint X, y.val ∈ U → A y = B y) :
    (fractionalPresheaf X A).obj (op U) = (fractionalPresheaf X B).obj (op U) := by
  by_cases hU : Nonempty U
  · let := hU
    ext s
    simp only [fractionalPresheaf, dite_eq_left hU, Submodule.mem_comap]
    constructor
    · rintro (hs | hs)
      · exact Or.inl hs
      · right
        intro y hy
        simpa only [h y hy] using hs y hy
    · rintro (hs | hs)
      · exact Or.inl hs
      · right
        intro y hy
        simpa only [h y hy] using hs y hy
  · simp only [fractionalPresheaf, dite_eq_right hU]

theorem divisorInclusion_app_surjective {A B : Divisor X} (hAB : A ≤ B)
    (U : X.Opens) (h : ∀ y : ClosedPoint X, y.val ∈ U → A y = B y) :
    Function.Surjective ((divisorInclusion X hAB).val.app (op U)) := by
  intro s
  have he := fractionalPresheaf_obj_eq_of_eq_on_open X U h
  let t : (divisorSheaf X A).val.obj (op U) :=
    ⟨s.val, he.symm ▸ s.property⟩
  exact ⟨t, rfl⟩

theorem divisorInclusion_stalk_surjective {A B : Divisor X} (hAB : A ≤ B)
    (x : X) (h : ∀ y : ClosedPoint X, y.val = x → A y = B y) :
    Function.Surjective (Scheme.Modules.moduleStalkMap x (divisorInclusion X hAB)) := by
  obtain ⟨U, hxU, hU⟩ := exists_open_divisor_zero X (B - A) x
    (fun y hy => sub_eq_zero.mpr (h y hy).symm)
  intro m
  obtain ⟨V, hVU, hxV, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat)
    (divisorSheaf X B).val.presheaf m hxU
  obtain ⟨t, ht⟩ := divisorInclusion_app_surjective X hAB V (fun y hy => by
    have hzero := hU y (hVU hy)
    exact (sub_eq_zero.mp hzero).symm) s
  refine ⟨TopCat.Presheaf.germ (X := X.toTopCat) (divisorSheaf X A).val.presheaf V x hxV t, ?_⟩
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (Scheme.Modules.Hom.mapPresheaf (X := X) (divisorInclusion X hAB)))
      (TopCat.Presheaf.germ (X := X.toTopCat) (divisorSheaf X A).val.presheaf V x hxV t) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact congrArg (TopCat.Presheaf.germ (X := X.toTopCat) (divisorSheaf X B).val.presheaf V x hxV) ht

theorem divisorQuotient_stalk_subsingleton {A B : Divisor X} (hAB : A ≤ B)
    (x : X) (h : ∀ y : ClosedPoint X, y.val = x → A y = B y) :
    Subsingleton ((divisorQuotient X hAB).presheaf.stalk x) := by
  let F := Scheme.Modules.moduleStalk X x
  let : Epi (F.map (divisorInclusion X hAB)) :=
    (ModuleCat.epi_iff_surjective _).mpr (divisorInclusion_stalk_surjective X hAB x h)
  exact ModuleCat.subsingleton_of_isZero
    ((isZero_cokernel_of_epi (F.map (divisorInclusion X hAB))).of_iso
      (PreservesCokernel.iso F (divisorInclusion X hAB)))

theorem divisorQuotient_finite_closed_support {A B : Divisor X} (hAB : A ≤ B) :
    ∃ S : Finset X, (∀ x ∈ S, IsClosed ({x} : Set X)) ∧
      ∀ x, x ∉ S → Subsingleton ((divisorQuotient X hAB).presheaf.stalk x) := by
  classical
  let S : Finset X := (B - A).support.image Subtype.val
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro x hx
    apply divisorQuotient_stalk_subsingleton X hAB x
    intro y hy
    by_contra hne
    apply hx
    exact Finset.mem_image.mpr ⟨y, Finsupp.mem_support_iff.mpr (sub_ne_zero.mpr (fun he => hne
      he.symm)), hy⟩
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- The actual divisor stalk embedded in the actual function field. -/
def divisorStalkValue (D : Divisor X) (x : X) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) (Scheme.Modules.presheaf (X
      := X) (divisorSheaf X D)) x) →ₗ[X.presheaf.stalk x] X.functionField :=
  (AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal.rationalStalkEquiv X
    x).toLinearMap.comp
    (Scheme.Modules.moduleStalkMap x (fractionalSubsheaf X D).ι)

theorem divisorStalkValue_germ (D : Divisor X) (x : X) (U : X.Opens)
    (hx : x ∈ U) [Nonempty U] (s : (divisorSheaf X D).val.obj (op U)) :
    divisorStalkValue X D x
      (TopCat.Presheaf.germ (X := X.toTopCat) (Scheme.Modules.presheaf (X := X) (divisorSheaf X
        D)) U x hx s) =
      rationalValue X U s.val := by
  change
    AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal.rationalStalkValue X
    x
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf (X := X) (fractionalSubsheaf X D).ι))
        (TopCat.Presheaf.germ (X := X.toTopCat) (Scheme.Modules.presheaf (X := X) (divisorSheaf X
          D)) U x hx s)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact
    AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal.rationalStalkValue_germ
    X x U hx s.val

theorem divisorStalkValue_injective (D : Divisor X) (x : X) :
    Function.Injective (divisorStalkValue X D x) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (X := X.toTopCat) (Scheme.Modules.presheaf (X := X) (divisorSheaf X D)) m
  let : Nonempty (show X.Opens from U) := ⟨⟨x, hx⟩⟩
  have hs : s = 0 := by
    apply Subtype.ext
    apply (rationalValueEquiv X U).injective
    change rationalValue X U s.val = rationalValue X U 0
    rw [map_zero]
    exact (divisorStalkValue_germ X D x U hx s).symm.trans hm
  rw [hs, map_zero]

/-- The germ at x of the section corresponding to 1 under the local trivialization determined
by g. -/
def divisorStalkGenerator (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (x : X) (U : X.Opens) (hx : x ∈ U) (g : X.functionFieldˣ)
    (hg : ∀ y : ClosedPoint X, y.val ∈ U → X.ord (g : X.functionField) y.val + D y = 0) :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat) (Scheme.Modules.presheaf (X
      := X) (divisorSheaf X D)) x) :=
  TopCat.Presheaf.germ (X := X.toTopCat) (Scheme.Modules.presheaf (X := X) (divisorSheaf X D)) U x
    hx
    (sectionTrivialization X hdim D U g hg 1)

theorem divisorStalkGenerator_value (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (x : X) (U : X.Opens) (hx : x ∈ U) (g : X.functionFieldˣ)
    (hg : ∀ y : ClosedPoint X, y.val ∈ U → X.ord (g : X.functionField) y.val + D y = 0) :
    divisorStalkValue X D x (divisorStalkGenerator X hdim D x U hx g hg) = g := by
  let : Nonempty (show X.Opens from U) := ⟨⟨x, hx⟩⟩
  rw [divisorStalkGenerator, divisorStalkValue_germ, sectionTrivialization_value,
    map_one, mul_one]

/-- The actual divisor stalk is free of rank one, with the specified rational generator. -/
def divisorStalkTrivialization (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (x : X) (U : X.Opens) (hx : x ∈ U) (g : X.functionFieldˣ)
    (hg : ∀ y : ClosedPoint X, y.val ∈ U → X.ord (g : X.functionField) y.val + D y = 0) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X
      := X.toTopCat) (Scheme.Modules.presheaf (X := X) (divisorSheaf X D)) x) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _
    (divisorStalkGenerator X hdim D x U hx g hg)) (by
    constructor
    · intro a b hab
      have hv := congrArg (divisorStalkValue X D x) hab
      simp only [LinearMap.toSpanSingleton_apply, _root_.map_smul,
        divisorStalkGenerator_value] at hv
      exact (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
        (mul_right_cancel₀ g.ne_zero hv)
    · intro m
      obtain ⟨V, hVU, hxV, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
        (X := X.toTopCat) (Scheme.Modules.presheaf (X := X) (divisorSheaf X D)) m hx
      let : Nonempty (show X.Opens from V) := ⟨⟨x, hxV⟩⟩
      let hgV := fun y hy => hg y (hVU hy)
      let e := sectionTrivialization X hdim D V g hgV
      refine ⟨X.presheaf.germ V x hxV (e.symm s), ?_⟩
      apply divisorStalkValue_injective X D x
      erw [LinearMap.toSpanSingleton_apply, _root_.map_smul, divisorStalkGenerator_value,
        divisorStalkValue_germ]
      change algebraMap (X.presheaf.stalk x) X.functionField
          (X.presheaf.germ V x hxV (e.symm s)) * (g : X.functionField) = _
      rw [Scheme.algebraMap_germ_eq_germToFunctionField, mul_comm,
        ← sectionTrivialization_value X hdim D V g hgV]
      exact congrArg (fun t : (divisorSheaf X D).val.obj (op V) => rationalValue X V t.val)
        (e.apply_symm_apply s))
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

theorem divisorStalkTrivialization_value (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (x : X) (U : X.Opens) (hx : x ∈ U) (g : X.functionFieldˣ)
    (hg : ∀ y : ClosedPoint X, y.val ∈ U → X.ord (g : X.functionField) y.val + D y = 0)
    (r : X.presheaf.stalk x) :
    divisorStalkValue X D x (divisorStalkTrivialization X hdim D x U hx g hg r) =
      algebraMap (X.presheaf.stalk x) X.functionField r * (g : X.functionField) := by
  change divisorStalkValue X D x (r • divisorStalkGenerator X hdim D x U hx g hg) = _
  rw [_root_.map_smul, divisorStalkGenerator_value]
  rfl

theorem divisorInclusion_stalk_value {A B : Divisor X} (hAB : A ≤ B) (x : X)
    (m : (Scheme.Modules.presheaf (X := X) (divisorSheaf X A)).stalk x) :
    divisorStalkValue X B x (Scheme.Modules.moduleStalkMap x (divisorInclusion X hAB) m) =
      divisorStalkValue X A x m := by
  obtain ⟨U, hx, s, rfl⟩ :=
    (Scheme.Modules.presheaf (X := X) (divisorSheaf X A)).exists_germ_eq m
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  change divisorStalkValue X B x
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf (X := X) (divisorInclusion X hAB)))
      ((Scheme.Modules.presheaf (X := X) (divisorSheaf X A)).germ U x hx s)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [divisorStalkValue_germ, divisorStalkValue_germ]
  rfl

variable (hdim : topologicalKrullDim X ≤ 1) {A B : Divisor X} (hAB : A ≤ B)
variable (x : X) (U V : X.Opens) (hxU : x ∈ U) (hxV : x ∈ V)
variable (gA gB : X.functionFieldˣ)
variable (hgA : ∀ y : ClosedPoint X, y.val ∈ U → X.ord (gA : X.functionField) y.val + A y = 0)
variable (hgB : ∀ y : ClosedPoint X, y.val ∈ V → X.ord (gB : X.functionField) y.val + B y = 0)

/-- The actual stalk element describing an inclusion in the two specified generators. -/
def divisorInclusionMultiplier : X.presheaf.stalk x :=
  (divisorStalkTrivialization X hdim B x V hxV gB hgB).symm
    (Scheme.Modules.moduleStalkMap x (divisorInclusion X hAB)
      (divisorStalkTrivialization X hdim A x U hxU gA hgA 1))

theorem divisorInclusionMultiplier_value :
    algebraMap (X.presheaf.stalk x) X.functionField
        (divisorInclusionMultiplier X hdim hAB x U V hxU hxV gA gB hgA hgB) *
      (gB : X.functionField) = (gA : X.functionField) := by
  rw [← divisorStalkTrivialization_value X hdim B x V hxV gB hgB]
  simp only [divisorInclusionMultiplier, LinearEquiv.apply_symm_apply,
    divisorInclusion_stalk_value, divisorStalkTrivialization_value, map_one, one_mul]

theorem divisorInclusionMultiplier_ne_zero :
    divisorInclusionMultiplier X hdim hAB x U V hxU hxV gA gB hgA hgB ≠ 0 := by
  intro hz
  have h := divisorInclusionMultiplier_value X hdim hAB x U V hxU hxV gA gB hgA hgB
  rw [hz, map_zero, zero_mul] at h
  exact gA.ne_zero h.symm

/-- The inclusion multiplier has order B(x)-A(x), fixing the positive-divisor sign. -/
theorem divisorInclusionMultiplier_order (y : ClosedPoint X) (hy : y.val = x) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField
        (divisorInclusionMultiplier X hdim hAB x U V hxU hxV gA gB hgA hgB)) x = B y - A y := by
  have ha := divisorInclusionMultiplier_ne_zero X hdim hAB x U V hxU hxV gA gB hgA hgB
  have ha' : algebraMap (X.presheaf.stalk x) X.functionField
      (divisorInclusionMultiplier X hdim hAB x U V hxU hxV gA gB hgA hgB) ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne ha
  have he := congrArg (fun z : X.functionField => X.ord z x)
    (divisorInclusionMultiplier_value X hdim hAB x U V hxU hxV gA gB hgA hgB)
  rw [Scheme.ord_mul ha' gB.ne_zero] at he
  have hA := hgA y (hy.symm ▸ hxU)
  have hB := hgB y (hy.symm ▸ hxV)
  rw [hy] at hA hB
  omega

/-- The actual cokernel stalk is the principal quotient by the inclusion multiplier. -/
def divisorQuotientStalkIso :
    (Scheme.Modules.moduleStalk X x).obj (divisorQuotient X hAB) ≅
      ModuleCat.of (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span
          {divisorInclusionMultiplier X hdim hAB x U V hxU hxV gA gB hgA hgB}) := by
  let R := X.presheaf.stalk x
  let F := Scheme.Modules.moduleStalk X x
  let eA := divisorStalkTrivialization X hdim A x U hxU gA hgA
  let eB := divisorStalkTrivialization X hdim B x V hxV gB hgB
  let a := divisorInclusionMultiplier X hdim hAB x U V hxU hxV gA gB hgA hgB
  let f := Scheme.Modules.moduleStalkMap x (divisorInclusion X hAB)
  let g := ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)
  have he : eB.symm.toLinearMap.comp (f.comp eA.toLinearMap) =
      LinearMap.toSpanSingleton R R a := by
    apply LinearMap.ext_ring
    exact (LinearMap.toSpanSingleton_apply_one R R a).symm
  have h : F.map (divisorInclusion X hAB) ≫ eB.symm.toModuleIso.hom =
      eA.symm.toModuleIso.hom ≫ g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change eB.symm (f m) = (LinearMap.toSpanSingleton R R a) (eA.symm m)
    have hm := LinearMap.congr_fun he (eA.symm m)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using! hm
  exact (PreservesCokernel.iso F (divisorInclusion X hAB)) ≪≫
    (cokernel.mapIso (F.map (divisorInclusion X hAB)) g
      eA.symm.toModuleIso eB.symm.toModuleIso h) ≪≫
      (ModuleCat.cokernelIsoRangeQuotient g) ≪≫
        (Submodule.quotEquivOfEq _ _ (LinearMap.range_toSpanSingleton a)).toModuleIso

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
open Degree.FiniteSupportLengths
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- An actual principal quotient description with its exact divisor coefficient difference. -/
theorem divisorQuotient_stalk_principal (hdim : topologicalKrullDim X ≤ 1)
    {A B : Divisor X} (hAB : A ≤ B) (y : ClosedPoint X) :
    ∃ a : X.presheaf.stalk y.val, a ≠ 0 ∧
      Nonempty ((divisorQuotient X hAB).presheaf.stalk y.val ≃ₗ[X.presheaf.stalk y.val]
        X.presheaf.stalk y.val ⧸ Ideal.span {a}) ∧
      (stalkColength X y.val a : ℤ) = B y - A y := by
  obtain ⟨U, hxU, gA, hgA⟩ := exists_local_principal_function X A y.val
  obtain ⟨V, hxV, gB, hgB⟩ := exists_local_principal_function X B y.val
  let a := divisorInclusionMultiplier X hdim hAB y.val U V hxU hxV gA gB hgA hgB
  have ha : a ≠ 0 :=
    divisorInclusionMultiplier_ne_zero X hdim hAB y.val U V hxU hxV gA gB hgA hgB
  refine ⟨a, ha,
    ⟨(divisorQuotientStalkIso X hdim hAB y.val U V hxU hxV gA gB hgA hgB).toLinearEquiv⟩, ?_⟩
  rw [← Degree.ProductFormula.order_stalk_element X y.val
    (coheight_eq_one_of_dvr X y.val) a ha]
  exact divisorInclusionMultiplier_order X hdim hAB y.val U V hxU hxV gA gB hgA hgB y rfl

/-- Finite length of the actual quotient stalk, proved before taking numerical lengths. -/
theorem divisorQuotient_stalk_finiteLength (hdim : topologicalKrullDim X ≤ 1)
    {A B : Divisor X} (hAB : A ≤ B) (y : ClosedPoint X) :
    IsFiniteLength (X.presheaf.stalk y.val) ((divisorQuotient X hAB).presheaf.stalk y.val) := by
  obtain ⟨a, ha, ⟨e⟩, _⟩ := divisorQuotient_stalk_principal X hdim hAB y
  let : Ring.KrullDimLE 1 (X.presheaf.stalk y.val) :=
    krullDimLE_of_coheight_le (coheight_eq_one_of_dvr X y.val).le
  exact (isFiniteLength_quotient_span_singleton (X.presheaf.stalk y.val)
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha)).of_injective (f := e.toLinearMap) e.injective

/-- The full stalk length counts the divisor multiplicity. -/
theorem divisorQuotient_stalk_length (hdim : topologicalKrullDim X ≤ 1)
    {A B : Divisor X} (hAB : A ≤ B) (y : ClosedPoint X) :
    ((Module.length (X.presheaf.stalk y.val)
      ((divisorQuotient X hAB).presheaf.stalk y.val)).toNat : ℤ) = B y - A y := by
  obtain ⟨a, _, ⟨e⟩, h⟩ := divisorQuotient_stalk_principal X hdim hAB y
  rw [e.length_eq]
  exact h

section OverField
open AlgebraicGeometry.Scheme.OverField.Curve
variable {K : Type u} [Field K] (Y : FScheme K)
variable [IsIntegral Y.left] [IsNoetherian Y.left] [LocallyOfFiniteType Y.hom]
variable [∀ x : ClosedPoint Y.left, IsDiscreteValuationRing (Y.left.presheaf.stalk x.val)]

/-- The actual quotient stalk is finite over the original structural field. -/
theorem divisorQuotient_stalk_finite (hdim : topologicalKrullDim Y.left ≤ 1)
    {A B : Divisor Y.left} (hAB : A ≤ B) (y : ClosedPoint Y.left) :
    Module.Finite K (moduleAdditiveStalk Y (divisorQuotient Y.left hAB) y.val) := by
  change @Module.Finite K ((divisorQuotient Y.left hAB).presheaf.stalk y.val) _ _
    (moduleAdditiveStalkModule Y (divisorQuotient Y.left hAB) y.val)
  rw [moduleAdditiveStalkModule_eq]
  exact Scheme.Modules.stalkBase_finite Y.left Y.hom
    (divisorQuotient Y.left hAB) y.val y.property
    (divisorQuotient_stalk_finiteLength Y.left hdim hAB y)

/-- The actual field dimension is multiplicity times the original residue weight. -/
theorem divisorQuotient_stalk_finrank (hdim : topologicalKrullDim Y.left ≤ 1)
    {A B : Divisor Y.left} (hAB : A ≤ B) (y : ClosedPoint Y.left) :
    (Module.finrank K (moduleAdditiveStalk Y (divisorQuotient Y.left hAB) y.val) : ℤ) =
      (B y - A y) * Degree.weight Y.left Y.hom y := by
  change (@Module.finrank K ((divisorQuotient Y.left hAB).presheaf.stalk y.val) _ _
    (moduleAdditiveStalkModule Y (divisorQuotient Y.left hAB) y.val) : ℤ) = _
  rw [moduleAdditiveStalkModule_eq]
  have h := Degree.CommonFractionalIdeal.stalkBase_finrank Y.left Y.hom
    (divisorQuotient Y.left hAB) y.val y.property
    (divisorQuotient_stalk_finiteLength Y.left hdim hAB y)
  rw [divisorQuotient_stalk_length Y.left hdim hAB y] at h
  exact h
end OverField
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable {K : Type u} [Field K] (X : FScheme K)
variable [IsIntegral X.left] [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
variable [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

/-- Enumerate the closed points in the finite support of D using its canonical Fin
equivalence. -/
def divisorSupportPoint (D : Divisor X.left) : Fin D.support.card → ClosedPoint X.left :=
  fun i => (D.support.equivFin.symm i).val

omit [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)] in
-- Retain the noetherian, finite-type and DVR-curve conditions of the divisor quotient cohomology
-- interface; injectivity of this finite support enumeration is combinatorial.
@[nolint unusedArguments]
theorem divisorSupportPoint_injective [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (D : Divisor X.left) :
    Function.Injective (fun i => (divisorSupportPoint X D i).val) := by
  intro i j hij
  apply D.support.equivFin.symm.injective
  exact Subtype.ext (Subtype.ext hij)

omit [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)] in
-- Retain the noetherian, finite-type and DVR-curve conditions of the divisor quotient cohomology
-- interface; the range statement itself only uses the finite support equivalence.
@[nolint unusedArguments]
theorem divisorSupportPoint_range [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (D : Divisor X.left) (y : ClosedPoint X.left)
    (hy : y ∈ D.support) : y.val ∈ Set.range (fun i => (divisorSupportPoint X D i).val) := by
  refine ⟨D.support.equivFin ⟨y, hy⟩, ?_⟩
  simp only [divisorSupportPoint, Equiv.symm_apply_apply]

theorem divisorQuotient_support_isZero {A B : Divisor X.left} (hAB : A ≤ B)
    (x : X.left) (hx : x ∉ Set.range (fun i => (divisorSupportPoint X (B - A) i).val)) :
    IsZero (moduleAdditiveStalk X (divisorQuotient X.left hAB) x) := by
  let : Subsingleton (moduleAdditiveStalk X (divisorQuotient X.left hAB) x) :=
    divisorQuotient_stalk_subsingleton X.left hAB x (by
      intro y hy
      by_contra hne
      apply hx
      rw [← hy]
      exact divisorSupportPoint_range X (B - A) y
        (Finsupp.mem_support_iff.mpr (sub_ne_zero.mpr (fun he => hne he.symm))))
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Finite actual H0 of the actual divisor-modification quotient. -/
theorem divisorQuotientH0_finite (hdim : topologicalKrullDim X.left ≤ 1)
    {A B : Divisor X.left} (hAB : A ≤ B) :
    Module.Finite K (moduleCohomology K X (divisorQuotient X.left hAB) 0) := by
  let (i : Fin (B - A).support.card) :=
    divisorQuotient_stalk_finite X hdim hAB (divisorSupportPoint X (B - A) i)
  exact finiteClosedSupportModuleH0_finite X (divisorQuotient X.left hAB)
    (fun i => (divisorSupportPoint X (B - A) i).val)
    (divisorSupportPoint_injective X (B - A))
    (fun i => (divisorSupportPoint X (B - A) i).property)
    (divisorQuotient_support_isZero X hAB)

/-- All positive actual cohomology of the actual finite-support quotient vanishes. -/
theorem divisorQuotientCohomology_positive {A B : Divisor X.left} (hAB : A ≤ B) (n : ℕ) :
    Subsingleton (moduleCohomology K X (divisorQuotient X.left hAB) (n + 1)) :=
  finiteClosedSupportModuleCohomology_positive X (divisorQuotient X.left hAB)
    (fun i => (divisorSupportPoint X (B - A) i).val)
    (divisorSupportPoint_injective X (B - A))
    (fun i => (divisorSupportPoint X (B - A) i).property)
    (divisorQuotient_support_isZero X hAB) n

/-- The actual quotient H0 dimension equals the existing degree of B-A. -/
theorem divisorQuotientH0_finrank (hdim : topologicalKrullDim X.left ≤ 1)
    {A B : Divisor X.left} (hAB : A ≤ B) :
    (Module.finrank K (moduleCohomology K X (divisorQuotient X.left hAB) 0) : ℤ) =
      Degree.degDiv X.left X.hom (B - A) := by
  let (i : Fin (B - A).support.card) :=
    divisorQuotient_stalk_finite X hdim hAB (divisorSupportPoint X (B - A) i)
  rw [finiteClosedSupportModuleH0_finrank X (divisorQuotient X.left hAB)
    (fun i => (divisorSupportPoint X (B - A) i).val)
    (divisorSupportPoint_injective X (B - A))
    (fun i => (divisorSupportPoint X (B - A) i).property)
    (divisorQuotient_support_isZero X hAB), Nat.cast_sum]
  simp_rw [divisorQuotient_stalk_finrank X hdim hAB]
  rw [Degree.degDiv_apply, ← Finset.sum_coe_sort (B - A).support
    (fun y => (B - A) y * Degree.weight X.left X.hom y)]
  exact Fintype.sum_equiv (B - A).support.equivFin.symm
    (fun i => (B (divisorSupportPoint X (B - A) i) - A (divisorSupportPoint X (B - A) i)) *
      Degree.weight X.left X.hom (divisorSupportPoint X (B - A) i))
    (fun y : (B - A).support => (B y.val - A y.val) * Degree.weight X.left X.hom y.val)
    (fun i => rfl)

/-- Actual H0/H1 finiteness transfers in both directions across a divisor modification. -/
theorem divisorCohomology_finite_iff (hdim : topologicalKrullDim X.left ≤ 1)
    {A B : Divisor X.left} (hAB : A ≤ B) :
    (Module.Finite K (moduleCohomology K X (divisorSheaf X.left A) 0) ∧
      Module.Finite K (moduleCohomology K X (divisorSheaf X.left A) 1)) ↔
    (Module.Finite K (moduleCohomology K X (divisorSheaf X.left B) 0) ∧
      Module.Finite K (moduleCohomology K X (divisorSheaf X.left B) 1)) := by
  let : Module.Finite K (moduleCohomology K X (divisorQuotientSequence X.left hAB).X₃ 0) :=
    divisorQuotientH0_finite X hdim hAB
  let : Subsingleton (moduleCohomology K X (divisorQuotientSequence X.left hAB).X₃ 1) :=
    divisorQuotientCohomology_positive X hAB 0
  exact moduleH0H1_finite_iff X (divisorQuotientSequence X.left hAB)
    (divisorQuotientSequence_shortExact X.left hAB)

/-- An ordered divisor modification changes the actual Euler expression by deg(B-A). -/
theorem divisorEuler_of_le (hdim : topologicalKrullDim X.left ≤ 1)
    {A B : Divisor X.left} (hAB : A ≤ B)
    [Module.Finite K (moduleCohomology K X (divisorSheaf X.left A) 0)]
    [Module.Finite K (moduleCohomology K X (divisorSheaf X.left A) 1)] :
    (Module.finrank K (moduleCohomology K X (divisorSheaf X.left B) 0) : ℤ) -
      Module.finrank K (moduleCohomology K X (divisorSheaf X.left B) 1) =
    (Module.finrank K (moduleCohomology K X (divisorSheaf X.left A) 0) : ℤ) -
      Module.finrank K (moduleCohomology K X (divisorSheaf X.left A) 1) +
        Degree.degDiv X.left X.hom (B - A) := by
  let : Module.Finite K (moduleCohomology K X (divisorQuotientSequence X.left hAB).X₃ 0) :=
    divisorQuotientH0_finite X hdim hAB
  let : Subsingleton (moduleCohomology K X (divisorQuotientSequence X.left hAB).X₃ 1) :=
    divisorQuotientCohomology_positive X hAB 0
  let : Module.Finite K (moduleCohomology K X (divisorQuotientSequence X.left hAB).X₁ 0) :=
    inferInstanceAs (Module.Finite K (moduleCohomology K X (divisorSheaf X.left A) 0))
  let : Module.Finite K (moduleCohomology K X (divisorQuotientSequence X.left hAB).X₁ 1) :=
    inferInstanceAs (Module.Finite K (moduleCohomology K X (divisorSheaf X.left A) 1))
  let := moduleCohomology_finite_middle X (divisorQuotientSequence X.left hAB)
    (divisorQuotientSequence_shortExact X.left hAB) 0
  let := moduleCohomology_finite_middle X (divisorQuotientSequence X.left hAB)
    (divisorQuotientSequence_shortExact X.left hAB) 1
  rw [← divisorQuotientH0_finrank X hdim hAB]
  exact moduleEuler_of_shortExact X (divisorQuotientSequence X.left hAB)
    (divisorQuotientSequence_shortExact X.left hAB)
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable {K : Type u} [Field K] (X : FScheme K)
variable [IsIntegral X.left] [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
variable [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

/-- The structure-module isomorphism with the zero-divisor sheaf, induced by the rational unit
1. -/
def zeroDivisorIso (hdim : topologicalKrullDim X.left ≤ 1) :
    (show X.left.Modules from SheafOfModules.unit X.left.ringCatSheaf) ≅ divisorSheaf X.left 0 :=
  globalTrivialization X.left hdim 0 1 (by
    intro y
    have ho : X.left.ord (1 : X.left.functionField) y.val = 0 :=
      (localOrder X.left y).map_zero
    simpa only [Units.val_one, Finsupp.zero_apply, add_zero] using ho)

/-- Identify zeroth structure-module cohomology with K using the supplied bijectivity of the
constants map. -/
def structureModuleH0ConstantsEquiv (hc : Function.Bijective (constants X)) :
    moduleCohomology K X (SheafOfModules.unit X.left.ringCatSheaf) 0 ≃ₗ[K] K := by
  let f : K →ₗ[K] (SheafOfModules.unit X.left.ringCatSheaf).val.obj (op ⊤) :=
    { toFun := constants X
      map_add' := (constants X).map_add
      map_smul' := by
        intro a b
        change constants X (a * b) = constants X a * constants X b
        exact (constants X).map_mul a b }
  exact (moduleH0Equiv X (SheafOfModules.unit X.left.ringCatSheaf)).trans
    (LinearEquiv.ofBijective f hc).symm

omit [LocallyOfFiniteType X.hom] in
-- Retain finite type of the curve structure morphism in the cohomological divisor interface; this
-- transport of finiteness uses the supplied H1 finiteness and constants bijection.
@[nolint unusedArguments]
theorem zeroDivisorCohomology_finite [LocallyOfFiniteType X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hc : Function.Bijective (constants X)) [Module.Finite K (coherentH1 K X)] :
    Module.Finite K (moduleCohomology K X (divisorSheaf X.left 0) 0) ∧
      Module.Finite K (moduleCohomology K X (divisorSheaf X.left 0) 1) := by
  let e0 := (moduleCohomologyIso X (zeroDivisorIso X hdim).symm 0).trans
    (structureModuleH0ConstantsEquiv X hc)
  let e1 := (moduleCohomologyIso X (zeroDivisorIso X hdim).symm 1).trans
    (structureModuleCohomologyEquiv X 1)
  exact ⟨e0.symm.finiteDimensional, e1.symm.finiteDimensional⟩

omit [LocallyOfFiniteType X.hom] in
-- Retain finite type and H1 finiteness in the Riemann–Roch cohomology interface; the displayed
-- finrank identity only transports dimensions across the constructed isomorphisms.
@[nolint unusedArguments]
theorem zeroDivisorEuler [LocallyOfFiniteType X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (hc : Function.Bijective (constants X)) [Module.Finite K (coherentH1 K X)] :
    (Module.finrank K (moduleCohomology K X (divisorSheaf X.left 0) 0) : ℤ) -
      Module.finrank K (moduleCohomology K X (divisorSheaf X.left 0) 1) =
      1 - (coherentGenus K X : ℤ) := by
  let e0 := (moduleCohomologyIso X (zeroDivisorIso X hdim).symm 0).trans
    (structureModuleH0ConstantsEquiv X hc)
  let e1 := (moduleCohomologyIso X (zeroDivisorIso X hdim).symm 1).trans
    (structureModuleCohomologyEquiv X 1)
  rw [e0.finrank_eq, e1.finrank_eq, Module.finrank_self]
  rfl

theorem divisorCohomology_finite (hdim : topologicalKrullDim X.left ≤ 1) (D : Divisor X.left)
    [Module.Finite K (moduleCohomology K X (divisorSheaf X.left 0) 0)]
    [Module.Finite K (moduleCohomology K X (divisorSheaf X.left 0) 1)] :
    Module.Finite K (moduleCohomology K X (divisorSheaf X.left D) 0) ∧
      Module.Finite K (moduleCohomology K X (divisorSheaf X.left D) 1) := by
  let T : Divisor X.left := D.mapRange (fun n => min n 0) (min_self 0)
  have hT0 : T ≤ 0 := fun y => min_le_right (D y) 0
  have hTD : T ≤ D := fun y => min_le_left (D y) 0
  exact (divisorCohomology_finite_iff X hdim hTD).mp
    ((divisorCohomology_finite_iff X hdim hT0).mpr ⟨inferInstance, inferInstance⟩)

/-- Two actual modifications identify the Euler difference with the existing divisor degree. -/
theorem divisorEuler (hdim : topologicalKrullDim X.left ≤ 1) (D : Divisor X.left)
    [Module.Finite K (moduleCohomology K X (divisorSheaf X.left 0) 0)]
    [Module.Finite K (moduleCohomology K X (divisorSheaf X.left 0) 1)] :
    (Module.finrank K (moduleCohomology K X (divisorSheaf X.left D) 0) : ℤ) -
      Module.finrank K (moduleCohomology K X (divisorSheaf X.left D) 1) =
      Degree.degDiv X.left X.hom D +
        ((Module.finrank K (moduleCohomology K X (divisorSheaf X.left 0) 0) : ℤ) -
          Module.finrank K (moduleCohomology K X (divisorSheaf X.left 0) 1)) := by
  let T : Divisor X.left := D.mapRange (fun n => min n 0) (min_self 0)
  have hT0 : T ≤ 0 := fun y => min_le_right (D y) 0
  have hTD : T ≤ D := fun y => min_le_left (D y) 0
  obtain ⟨ht0, ht1⟩ := (divisorCohomology_finite_iff X hdim hT0).mpr
    ⟨inferInstance, inferInstance⟩
  let := ht0
  let := ht1
  have hz := divisorEuler_of_le X hdim hT0
  have hd := divisorEuler_of_le X hdim hTD
  rw [map_sub, map_zero] at hz
  rw [map_sub] at hd
  omega

/-- Actual line-bundle H0/H1 finiteness follows from actual H1(O) finiteness and constants. -/
theorem lineBundleCohomology_finite_of_finiteH1 (hdim : topologicalKrullDim X.left ≤ 1)
    (L : LineBundle X.left) (hc : Function.Bijective (constants X))
    [Module.Finite K (coherentH1 K X)] :
    Module.Finite K (moduleCohomology K X L.val 0) ∧
      Module.Finite K (moduleCohomology K X L.val 1) := by
  obtain ⟨hz0, hz1⟩ := zeroDivisorCohomology_finite X hdim hc
  let := hz0
  let := hz1
  obtain ⟨D, ⟨e⟩⟩ := DivisorInverse.exists_divisor_iso X.left L.val L.property hdim
  obtain ⟨hd0, hd1⟩ := divisorCohomology_finite X hdim D
  let := hd0
  let := hd1
  exact ⟨(moduleCohomologyIso X e 0).symm.finiteDimensional,
    (moduleCohomologyIso X e 1).symm.finiteDimensional⟩

/-- Riemann–Roch for the existing actual degree, conditional on actual H1(O) finiteness. -/
theorem lineBundleRiemannRoch_of_finiteH1 (hdim : topologicalKrullDim X.left ≤ 1)
    (hprod : Degree.PrincipalProductFormula X.left X.hom) (L : LineBundle X.left)
    (hc : Function.Bijective (constants X)) [Module.Finite K (coherentH1 K X)] :
    (Module.finrank K (moduleCohomology K X L.val 0) : ℤ) -
      Module.finrank K (moduleCohomology K X L.val 1) =
      Degree.lineBundleDegree X.left X.hom hdim hprod L + 1 - (coherentGenus K X : ℤ) := by
  obtain ⟨hz0, hz1⟩ := zeroDivisorCohomology_finite X hdim hc
  let := hz0
  let := hz1
  obtain ⟨D, ⟨e⟩⟩ := DivisorInverse.exists_divisor_iso X.left L.val L.property hdim
  have hdeg : Degree.lineBundleDegree X.left X.hom hdim hprod L =
      Degree.degDiv X.left X.hom D :=
    (Degree.lineBundleDegree_iso X.left X.hom hdim hprod
      (L := L) (N := divisorLineBundle X.left hdim D) e).trans
      (Degree.lineBundleDegree_divisor X.left X.hom hdim hprod D)
  rw [(moduleCohomologyIso X e 0).finrank_eq,
    (moduleCohomologyIso X e 1).finrank_eq, divisorEuler X hdim D,
    zeroDivisorEuler X hdim hc, hdeg]
  omega
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
/-- Conditional reduction of the exact original family at
`Curves/RiemannRoch.lean:49–59`, project revision
`3397a339b6a52fbba586dae127aa729d873b771d`. All original hypotheses and the
literal original conclusion are retained. The only added hypothesis is
finiteness of the actual coherentH1. -/
theorem lineBundleRiemannRoch_of_actualH1_finite
    (K : Type u) [Field K] (X : FScheme K) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom) (L : Invertible.LineBundle X.left)
    (hproper : IsProper X.hom) (hc : Function.Bijective (constants X))
    (hfinite : Module.Finite K (coherentH1 K X)) :
    (Module.finrank K (moduleCohomology K X L.val 0) : ℤ) -
      Module.finrank K (moduleCohomology K X L.val 1) =
      Picard.Degree.lineBundleDegree X.left X.hom hdim hprod L + 1 -
        (coherentGenus K X : ℤ) := by
  let := hproper
  let := hfinite
  exact Picard.DivisorClass.lineBundleRiemannRoch_of_finiteH1 X hdim hprod L hc
end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
attribute [local instance] specializationOrder in
theorem dimension_eq_one_of_closedDVR
    {K : Type u} [Field K] (X : FScheme K) [IsIntegral X.left]
    [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1) : topologicalKrullDim X.left = 1 := by
  apply le_antisymm hdim
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints (X := X.left)
    (Z := Set.univ) Set.univ_nonempty isClosed_univ.isLocallyClosed
  let x : ClosedPoint X.left := ⟨z, hz⟩
  calc
    (1 : WithBot ℕ∞) = (Order.coheight x.val : WithBot ℕ∞) := by
      rw [coheight_eq_one_of_dvr X.left x.val]
      rfl
    _ ≤ Order.krullDim X.left := Order.coheight_le_krullDim x.val
    _ = topologicalKrullDim X.left :=
      (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X.left))).symm
end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
/-- The unchanged original `LineBundleRiemannRoch.{u}` family at
`Curves/RiemannRoch.lean:49–59`, project revision
`3397a339b6a52fbba586dae127aa729d873b771d`, with no additional hypotheses.
Native proper structure-sheaf cohomology finiteness supplies actual H1(O)
finiteness. All original closed-DVR and dimension hypotheses remain in the family. -/
theorem lineBundleRiemannRoch : LineBundleRiemannRoch.{u} := by
  intro K hK X hInt hNoeth hDVR hdim hprod L hproper hc
  let := hproper
  exact lineBundleRiemannRoch_of_actualH1_finite K X hdim hprod L hproper hc
    (Scheme.Cohomology.properStructureCohomologyFinite
      K X 1 hproper)
end AlgebraicGeometry.Scheme.OverField.Curve
