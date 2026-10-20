/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Length.PrincipalIntersection
public import Aglib.AlgebraicGeometry.Modules.RationalFunctions
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# Common fractional ideals on singular integral curves

Components for the unchanged proper-curve product formula: actual generic
rational sections, the common pullback of the two regular modules, and the
local projection-quotient dictionary. No closed-stalk DVR condition is used.
Proper H1 finiteness and the Euler argument are separate remaining obligations.

Authoring basis `28e33dafb3b1e78e9749a27f20bf4c6e0bc5b26b`, Lean4.34.1,
Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 and coherent Quillen0.7
83629578a3d70787d41ec631f5234af8758716af. The latter supplies the actual
module-valued stalk and global-unit maps used here.
-/

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Modules.RationalFunctions.CommonFractionalIdeal` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ed6a548bfad729141aedf19a9dc7dd9b4f0d1fc8243a516fb59cf2683eec7bd0`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal
universe u
variable (X : Scheme.{u}) [hIntegralX : IsIntegral X]

/-- The native rational-function module sheaf on the given integral scheme. -/
abbrev rationalFunctions := AlgebraicGeometry.Scheme.Modules.RationalFunctions.rationalFunctions X
/-- The unit module sheaf of regular functions on the given scheme. -/
abbrev regularModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

theorem generic_preimage_eq_top (U : X.Opens) [hU : Nonempty U] :
    ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U = ⊤ := by
  apply le_antisymm le_top
  intro z _
  let : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of X.functionField)))
  have hz : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  change (X.fromSpecStalk (genericPoint X)) z ∈ U
  rw [hz, Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- Identify sections over the generic preimage of a nonempty open with the function field
through the canonical spectrum comparison. -/
def rationalSectionIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) ≅ X.functionField :=
  (eqToIso (by rw [generic_preimage_eq_top X U])) ≪≫ Scheme.ΓSpecIso X.functionField

theorem generic_app_rationalSectionIso (U : X.Opens) [hU : Nonempty U] :
    ((X.fromSpecStalk (genericPoint X))).app U ≫ (rationalSectionIso X U).hom =
      X.germToFunctionField U := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  change (X.fromSpecStalk (genericPoint X)).app U ≫ _ = _
  rw [Scheme.fromSpecStalk_app hx]
  simp only [rationalSectionIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  have hr : (Spec X.functionField).presheaf.map
      (homOfLE (show ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
        eqToHom (show Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) =
          Γ(Spec X.functionField, ⊤) by rw [generic_preimage_eq_top X U]) = 𝟙 _ := by
    have aux (V : (Spec X.functionField).Opens) (hV : V = ⊤) :
        (Spec X.functionField).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
          eqToHom (show Γ(Spec X.functionField, V) = Γ(Spec X.functionField, ⊤) by rw [hV]) = 𝟙
              _ := by
      subst V
      simp
    exact aux _ (generic_preimage_eq_top X U)
  rw [← Category.assoc _ (eqToHom _), hr]
  simp

/-- Evaluate rational-function sections on a nonempty open as a linear map to the function field. -/
def rationalValue (U : X.Opens) [Nonempty U] :
    (rationalFunctions X).val.obj (op U) →ₗ[Γ(X, U)] X.functionField where
  toFun := (rationalSectionIso X U).hom
  map_add' := (rationalSectionIso X U).hom.hom.map_add
  map_smul' a f := by
    change Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) at f
    change (rationalSectionIso X U).hom ((((X.fromSpecStalk (genericPoint X))).app U a) * f) =
      X.germToFunctionField U a * (rationalSectionIso X U).hom f
    rw [map_mul]
    congr 1
    exact congrArg (fun e : Γ(X, U) ⟶ X.functionField => e a)
      (generic_app_rationalSectionIso X U)

/-- Identify rational-function sections on a nonempty open with their values in the function
field. -/
def rationalValueEquiv (U : X.Opens) [Nonempty U] :
    (rationalFunctions X).val.obj (op U) ≃ₗ[Γ(X, U)] X.functionField :=
  LinearEquiv.ofBijective (rationalValue X U)
    (ConcreteCategory.bijective_of_isIso (rationalSectionIso X U).hom)

theorem rationalSectionIso_naturality {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    (Spec X.functionField).presheaf.map ((Opens.map ((X.fromSpecStalk (genericPoint
        X))).base).map i).op ≫
      (rationalSectionIso X U).hom = (rationalSectionIso X V).hom := by
  have aux (A B : (Spec X.functionField).Opens) (hA : A = ⊤) (hB : B = ⊤) (j : A ⟶ B) :
      (Spec X.functionField).presheaf.map j.op ≫
        eqToHom (show Γ(Spec X.functionField, A) = Γ(Spec X.functionField, ⊤) by rw [hA]) =
        eqToHom (show Γ(Spec X.functionField, B) = Γ(Spec X.functionField, ⊤) by rw [hB]) := by
    subst A; subst B
    have hj : j = 𝟙 ⊤ := Subsingleton.elim _ _
    rw [hj]
    simp
  simp only [rationalSectionIso, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, aux _ _ (generic_preimage_eq_top X U) (generic_preimage_eq_top X V)]

theorem rationalValue_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : (rationalFunctions X).val.obj (op V)) :
    rationalValue X U ((rationalFunctions X).val.map i.op s) = rationalValue X V s :=
  congrArg (fun e => (e : Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ V) ⟶
    X.functionField) s) (rationalSectionIso_naturality X i)

/-- The structure-module map including regular functions into rational functions along the
actual generic-point morphism. -/
def regularMap : regularModule X ⟶ rationalFunctions X :=
  AlgebraicGeometry.Scheme.Hom.structureModuleMap ((X.fromSpecStalk (genericPoint X)))

instance regularMap_mono : Mono (regularMap X) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have hUb : U.unop = ⊥ := by
      ext x
      constructor
      · intro hx; exact hU.false (⟨x, hx⟩ : U.unop)
      · intro hx; exact False.elim hx
    have hs : Subsingleton Γ(X, U.unop) := by rw [hUb]; infer_instance
    intro a b _
    change Γ(X, U.unop) at a b
    exact @Subsingleton.elim Γ(X, U.unop) hs a b
  · let : Nonempty U.unop := hU
    intro a b hab
    apply X.germToFunctionField_injective U.unop
    have he (s : Γ(X, U.unop)) :
        (rationalSectionIso X U.unop).hom (((X.fromSpecStalk (genericPoint X))).app U.unop s) =
          X.germToFunctionField U.unop s :=
      ConcreteCategory.congr_hom (generic_app_rationalSectionIso X U.unop) s
    change ((X.fromSpecStalk (genericPoint X))).app U.unop a =
      ((X.fromSpecStalk (genericPoint X))).app U.unop b at hab
    exact (he a).symm.trans ((congrArg (rationalSectionIso X U.unop).hom hab).trans (he b))

/-- Multiplication by the specified function-field unit as an automorphism of the
rational-function module. -/
def rationalMultiplier (f : X.functionFieldˣ) : rationalFunctions X ≅ rationalFunctions X :=
  (Scheme.Modules.pushforward ((X.fromSpecStalk (genericPoint X)))).mapIso
    (Scheme.Modules.globalScalarIso (X := Spec X.functionField)
      (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)
      (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom f))

/-- Include regular functions into rational functions and then multiply by the specified unit. -/
def scaledRegularMap (f : X.functionFieldˣ) : regularModule X ⟶ rationalFunctions X :=
  regularMap X ≫ (rationalMultiplier X f).hom
instance scaledRegularMap_mono (f : X.functionFieldˣ) : Mono (scaledRegularMap X f) := by
  dsimp [scaledRegularMap]
  infer_instance

/-- The actual common fractional ideal, with both its regular-module projections. -/
def commonIdeal (f : X.functionFieldˣ) : X.Modules := CategoryTheory.Limits.pullback
    (regularMap X) (scaledRegularMap X f)
/-- The first projection from the common fractional ideal to the unscaled regular module. -/
def leftInclusion (f : X.functionFieldˣ) : commonIdeal X f ⟶ regularModule X :=
    CategoryTheory.Limits.pullback.fst _ _
/-- The second projection from the common fractional ideal to the regular module whose
rational inclusion is scaled by the specified unit. -/
def rightInclusion (f : X.functionFieldˣ) : commonIdeal X f ⟶ regularModule X :=
    CategoryTheory.Limits.pullback.snd _ _
instance leftInclusion_mono (f : X.functionFieldˣ) : Mono (leftInclusion X f) := by
  dsimp [leftInclusion]; infer_instance
instance rightInclusion_mono (f : X.functionFieldˣ) : Mono (rightInclusion X f) := by
  dsimp [rightInclusion]; infer_instance

/-- The cokernel of the first projection from the common fractional ideal. -/
def leftQuotient (f : X.functionFieldˣ) : X.Modules := cokernel (leftInclusion X f)
/-- The cokernel of the second projection from the common fractional ideal. -/
def rightQuotient (f : X.functionFieldˣ) : X.Modules := cokernel (rightInclusion X f)

theorem rationalSectionIso_restrict_top (U : X.Opens) [Nonempty U] (a : X.functionField) :
    (rationalSectionIso X U).hom
      ((Spec X.functionField).presheaf.map (homOfLE (show
        ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
          ((Scheme.ΓSpecIso X.functionField).inv a)) = a := by
  have aux (V : (Spec X.functionField).Opens) (hV : V = ⊤) :
      ((eqToIso (show Γ(Spec X.functionField, V) = Γ(Spec X.functionField, ⊤) by rw [hV])) ≪≫
        Scheme.ΓSpecIso X.functionField).hom
          ((Spec X.functionField).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
            ((Scheme.ΓSpecIso X.functionField).inv a)) = a := by
    subst V
    simp
  exact aux _ (generic_preimage_eq_top X U)

theorem rationalMultiplier_value (f : X.functionFieldˣ) (U : X.Opens) [Nonempty U]
    (s : (rationalFunctions X).val.obj (op U)) :
    rationalValue X U ((rationalMultiplier X f).hom.app U s) =
      (f : X.functionField) * rationalValue X U s := by
  change (rationalSectionIso X U).hom
    (((Spec X.functionField).presheaf.map (homOfLE (show
      ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso X.functionField).inv (f : X.functionField))) *
          (show Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) from s)) = _
  rw [map_mul, rationalSectionIso_restrict_top]
  rfl

theorem regularMap_value (U : X.Opens) [Nonempty U] (s : Γ(X, U)) :
    rationalValue X U ((regularMap X).app U s) = X.germToFunctionField U s :=
  ConcreteCategory.congr_hom (generic_app_rationalSectionIso X U) s

theorem scaledRegularMap_value (f : X.functionFieldˣ) (U : X.Opens) [Nonempty U]
    (s : Γ(X, U)) : rationalValue X U ((scaledRegularMap X f).app U s) =
      (f : X.functionField) * X.germToFunctionField U s := by
  change rationalValue X U ((rationalMultiplier X f).hom.app U ((regularMap X).app U s)) = _
  rw [rationalMultiplier_value, regularMap_value]

theorem commonIdeal_sections_relation (f : X.functionFieldˣ) (U : X.Opens) [Nonempty U]
    (s : (commonIdeal X f).val.obj (op U)) :
    X.germToFunctionField U ((leftInclusion X f).app U s) =
      (f : X.functionField) * X.germToFunctionField U ((rightInclusion X f).app U s) := by
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have hcone : leftInclusion X f ≫ regularMap X = rightInclusion X f ≫ scaledRegularMap X f :=
    CategoryTheory.Limits.pullback.condition
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun φ => ev.map φ) hcone) s
  have h := congrArg (rationalValue X U) hc
  change rationalValue X U ((regularMap X).app U ((leftInclusion X f).app U s)) =
    rationalValue X U ((scaledRegularMap X f).app U ((rightInclusion X f).app U s)) at h
  rwa [regularMap_value, scaledRegularMap_value] at h

open Ideal
namespace LocalRelation
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]

/-- The linear relation sending a pair to its first coordinate minus the specified scalar
times its second coordinate in the given field algebra. -/
def relationMap (f : K) : (R × R) →ₗ[R] K where
  toFun := fun z => algebraMap R K z.1 - f * algebraMap R K z.2
  map_add' := by intro u v; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
  map_smul' := by
    intro r z
    change algebraMap R K (r • z.1) - f * algebraMap R K (r • z.2) =
      r • (algebraMap R K z.1 - f * algebraMap R K z.2)
    simp only [smul_eq_mul, Algebra.smul_def]
    rw [map_mul, map_mul]
    ring

/-- The submodule of pairs satisfying the specified fractional relation. -/
def commonModule (f : K) : Submodule R (R × R) := (relationMap R K f).ker

/-- The first-coordinate linear map on the common-relation submodule. -/
def leftProjection (f : K) : commonModule R K f →ₗ[R] R :=
  (LinearMap.fst R R R).comp (commonModule R K f).subtype

/-- The second-coordinate linear map on the common-relation submodule. -/
def rightProjection (f : K) : commonModule R K f →ₗ[R] R :=
  (LinearMap.snd R R R).comp (commonModule R K f).subtype

variable [hDomainR : IsDomain R] [IsFractionRing R K]
omit hDomainR in
-- Retain the domain guard of the original fraction-field relation interface.
@[nolint unusedArguments]
theorem mem_commonModule_iff [IsDomain R] (a b : R) (hb : b ≠ 0) (z : R × R) :
    z ∈ commonModule R K (algebraMap R K a / algebraMap R K b) ↔ b * z.1 = a * z.2 := by
  have hbK : algebraMap R K b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hb
  change algebraMap R K z.1 - (algebraMap R K a / algebraMap R K b) *
    algebraMap R K z.2 = 0 ↔ _
  rw [sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul,
    (IsFractionRing.injective R K).eq_iff]
  simp only [mul_comm z.1 b]

/-- Multiply by the denominator and reduce modulo the intersection of the two principal ideals. -/
def principalImageMap (a b : R) : R →ₗ[R] (R ⧸ (Ideal.span {a} ⊓ Ideal.span {b})) :=
  (Submodule.mkQ (Ideal.span {a} ⊓ Ideal.span {b} : Ideal R)).comp (LinearMap.mulLeft R b)

theorem principalImageMap_ker (a b : R) (hb : b ≠ 0) :
    (principalImageMap R a b).ker =
      (leftProjection R K (algebraMap R K a / algebraMap R K b)).range := by
  ext x
  constructor
  · intro hx
    have hm : b * x ∈ Ideal.span {a} ⊓ Ideal.span {b} := by
      simpa only [principalImageMap, LinearMap.mem_ker, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hm.1
    refine ⟨⟨(x, v), (mem_commonModule_iff R K a b hb (x,v)).mpr ?_⟩, rfl⟩
    exact hv
  · rintro ⟨z, rfl⟩
    simp only [principalImageMap, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change b * z.val.1 ∈ Ideal.span {a} ⊓ Ideal.span {b}
    have hz := (mem_commonModule_iff R K a b hb z.val).mp z.property
    constructor
    · rw [hz]
      exact Ideal.mem_span_singleton.mpr ⟨z.val.2, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨z.val.1, rfl⟩

omit hDomainR in
-- Retain the original domain context of the left fractional-ideal quotient formula.
@[nolint unusedArguments]
theorem principalImageMap_range [IsDomain R] (a b : R) :
    (principalImageMap R a b).range =
      quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b}) (Ideal.span {b}) := by
  have hm : (LinearMap.mulLeft R b).range = (Ideal.span {b} : Ideal R) := by
    ext x
    constructor
    · rintro ⟨r, hr⟩
      exact Ideal.mem_span_singleton.mpr ⟨r, hr.symm⟩
    · intro hx
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨r, hr.symm⟩
  rw [principalImageMap, LinearMap.range_comp, hm]
  rfl

/-- Identify the quotient by the first common-relation projection with the quotient-ideal
image of the denominator ideal modulo the intersection. -/
def leftQuotientEquiv (a b : R) (hb : b ≠ 0) :
    (R ⧸ (leftProjection R K (algebraMap R K a / algebraMap R K b)).range) ≃ₗ[R]
      quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b}) (Ideal.span {b}) :=
  (Submodule.quotEquivOfEq _ _ (principalImageMap_ker R K a b hb).symm).trans
    ((principalImageMap R a b).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (principalImageMap_range R a b)))
/-- Multiply by the numerator and reduce modulo the intersection of the two principal ideals. -/
def rightPrincipalImageMap (a b : R) : R →ₗ[R] (R ⧸ (Ideal.span {a} ⊓ Ideal.span {b})) :=
  (Submodule.mkQ (Ideal.span {a} ⊓ Ideal.span {b} : Ideal R)).comp (LinearMap.mulLeft R a)

theorem rightPrincipalImageMap_ker (a b : R) (hb : b ≠ 0) :
    (rightPrincipalImageMap R a b).ker =
      (rightProjection R K (algebraMap R K a / algebraMap R K b)).range := by
  ext x
  constructor
  · intro hx
    have hm : a * x ∈ Ideal.span {a} ⊓ Ideal.span {b} := by
      simpa only [rightPrincipalImageMap, LinearMap.mem_ker, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hm.2
    refine ⟨⟨(v, x), (mem_commonModule_iff R K a b hb (v,x)).mpr hv.symm⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    simp only [rightPrincipalImageMap, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change a * z.val.2 ∈ Ideal.span {a} ⊓ Ideal.span {b}
    have hz := (mem_commonModule_iff R K a b hb z.val).mp z.property
    constructor
    · exact Ideal.mem_span_singleton.mpr ⟨z.val.2, rfl⟩
    · rw [← hz]
      exact Ideal.mem_span_singleton.mpr ⟨z.val.1, rfl⟩

omit hDomainR in
-- Retain the original domain context of the right fractional-ideal quotient formula.
@[nolint unusedArguments]
theorem rightPrincipalImageMap_range [IsDomain R] (a b : R) :
    (rightPrincipalImageMap R a b).range =
      quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b}) (Ideal.span {a}) := by
  have hm : (LinearMap.mulLeft R a).range = (Ideal.span {a} : Ideal R) := by
    ext x
    constructor
    · rintro ⟨r, hr⟩
      exact Ideal.mem_span_singleton.mpr ⟨r, hr.symm⟩
    · intro hx
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨r, hr.symm⟩
  rw [rightPrincipalImageMap, LinearMap.range_comp, hm]
  rfl

/-- Identify the quotient by the second common-relation projection with the quotient-ideal
image of the numerator ideal modulo the intersection. -/
def rightQuotientEquiv (a b : R) (hb : b ≠ 0) :
    (R ⧸ (rightProjection R K (algebraMap R K a / algebraMap R K b)).range) ≃ₗ[R]
      quotientIdealImage R (Ideal.span {a} ⊓ Ideal.span {b}) (Ideal.span {a}) :=
  (Submodule.quotEquivOfEq _ _ (rightPrincipalImageMap_ker R K a b hb).symm).trans
    ((rightPrincipalImageMap R a b).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (rightPrincipalImageMap_range R a b)))
end LocalRelation

/-- The cocone of compatible rational values on neighbourhoods, with vertex the function field. -/
def rationalStalkCocone (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (rationalFunctions X).presheaf) where
  pt := AddCommGrpCat.of X.functionField
  ι := {
    app := fun U => by
      letI : Nonempty U.unop.val := ⟨⟨x, U.unop.property⟩⟩
      exact AddCommGrpCat.ofHom (rationalValue X U.unop.val).toAddMonoidHom
    naturality := by
      intro U V f
      let : Nonempty U.unop.val := ⟨⟨x, U.unop.property⟩⟩
      let : Nonempty V.unop.val := ⟨⟨x, V.unop.property⟩⟩
      ext s
      exact rationalValue_restrict X (U := V.unop.val) (V := U.unop.val)
        ((OpenNhds.inclusion x).map f.unop) s }

/-- The additive value map from the rational-function stalk to the function field. -/
def rationalStalkValue (x : X) :
    (rationalFunctions X).presheaf.stalk x →+ X.functionField :=
  (colimit.desc _ (rationalStalkCocone X x)).hom

theorem rationalStalkValue_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    [Nonempty U] (s : (rationalFunctions X).val.obj (op U)) :
    rationalStalkValue X x ((rationalFunctions X).presheaf.germ U x hx s) = rationalValue X U s
        := by
  change (colimit.ι _ (op ⟨U, hx⟩) ≫ colimit.desc _ (rationalStalkCocone X x)) s = _
  rw [colimit.ι_desc]
  rfl

/-- The rational stalk-value map as a linear map over the actual local ring. -/
def rationalStalkLinear (x : X) :
    (rationalFunctions X).presheaf.stalk x →ₗ[X.presheaf.stalk x] X.functionField where
  __ := rationalStalkValue X x
  map_smul' r m := by
    obtain ⟨U, hx, a, s, rfl, rfl⟩ :=
      Scheme.Modules.exists_germ_smul_representatives X x
          (rationalFunctions X) r m
    let : Nonempty U := ⟨⟨x, hx⟩⟩
    erw [← PresheafOfModules.germ_smul (rationalFunctions X).val x U hx]
    change rationalStalkValue X x ((rationalFunctions X).presheaf.germ U x hx (a • s)) =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx a) *
        rationalStalkValue X x ((rationalFunctions X).presheaf.germ U x hx s)
    rw [rationalStalkValue_germ, rationalStalkValue_germ,
        Scheme.algebraMap_germ_eq_germToFunctionField]
    exact (rationalValue X U).map_smul a s

/-- Identify the rational-function stalk with the function field as modules over the local ring. -/
def rationalStalkEquiv (x : X) :
    (rationalFunctions X).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.functionField :=
  LinearEquiv.ofBijective (rationalStalkLinear X x) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro m hm
      obtain ⟨U, hx, s, rfl⟩ := (rationalFunctions X).presheaf.exists_germ_eq m
      let : Nonempty U := ⟨⟨x, hx⟩⟩
      have hs : s = 0 := (rationalValueEquiv X U).injective (by
        change rationalValue X U s = rationalValue X U 0
        rw [map_zero]
        exact (rationalStalkValue_germ X x U hx s).symm.trans hm)
      rw [hs, map_zero]
    · intro a
      let : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
      refine ⟨(rationalFunctions X).presheaf.germ ⊤ x trivial ((rationalValueEquiv X ⊤).symm a), ?_⟩
      change rationalStalkValue X x _ = a
      rw [rationalStalkValue_germ]
      exact (rationalValueEquiv X ⊤).apply_symm_apply a)
/-- The cocone of actual regular-section germ maps to the local ring. -/
def regularStalkCocone (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (regularModule X).presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι := {
    app := fun U => AddCommGrpCat.ofHom
      (X.presheaf.germ U.unop.val x U.unop.property).hom.toAddMonoidHom
    naturality := by
      intro U V f
      ext s
      exact X.presheaf.germ_res_apply ((OpenNhds.inclusion x).map f.unop) x V.unop.property s }

/-- The additive map from the unit-module stalk to the ring stalk induced by actual germs. -/
def regularStalkValue (x : X) :
    (regularModule X).presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (regularStalkCocone X x)).hom

omit hIntegralX in
-- Retain integrality in the original common fractional-ideal stalk interface.
@[nolint unusedArguments]
theorem regularStalkValue_germ [IsIntegral X] (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : (regularModule X).val.obj (op U)) :
    regularStalkValue X x ((regularModule X).presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (show Γ(X,U) from s) := by
  change (colimit.ι _ (op ⟨U, hx⟩) ≫ colimit.desc _ (regularStalkCocone X x)) s = _
  rw [colimit.ι_desc]
  rfl

/-- The regular stalk-value map as a linear map over the actual local ring. -/
def regularStalkLinear (x : X) :
    (regularModule X).presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x where
  __ := regularStalkValue X x
  map_smul' r m := by
    obtain ⟨U, hx, a, s, rfl, rfl⟩ :=
      Scheme.Modules.exists_germ_smul_representatives X x
          (regularModule X) r m
    erw [← PresheafOfModules.germ_smul (regularModule X).val x U hx]
    change regularStalkValue X x ((regularModule X).presheaf.germ U x hx (a • s)) =
      X.presheaf.germ U x hx a * regularStalkValue X x ((regularModule X).presheaf.germ U x hx s)
    rw [regularStalkValue_germ, regularStalkValue_germ]
    exact (X.presheaf.germ U x hx).hom.map_mul a s

/-- Identify the unit-module stalk with the ring stalk through the actual germ maps. -/
def regularStalkEquiv (x : X) :
    (regularModule X).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  LinearEquiv.ofBijective (regularStalkLinear X x) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro m hm
      obtain ⟨U, hx, s, rfl⟩ := (regularModule X).presheaf.exists_germ_eq m
      have hz : X.presheaf.germ U x hx (show Γ(X,U) from s) = 0 :=
        (regularStalkValue_germ X x U hx s).symm.trans hm
      have hs : s = 0 := (germ_injective_of_isIntegral X x hx)
        (hz.trans (X.presheaf.germ U x hx).hom.map_zero.symm)
      rw [hs, map_zero]
    · intro a
      obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
      exact ⟨(regularModule X).presheaf.germ U x hx s, regularStalkValue_germ X x U hx s⟩)

theorem rationalStalkMap_regularMap (x : X) (m : (regularModule X).presheaf.stalk x) :
    rationalStalkEquiv X x (Scheme.Modules.moduleStalkMap x
        (regularMap X) m) =
      algebraMap (X.presheaf.stalk x) X.functionField (regularStalkEquiv X x m) := by
  obtain ⟨U, hx, s, rfl⟩ := (regularModule X).presheaf.exists_germ_eq m
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  change rationalStalkValue X x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (regularMap X).mapPresheaf ((regularModule X).presheaf.germ U x hx s)) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (regularStalkValue X x ((regularModule X).presheaf.germ U x hx s))
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, rationalStalkValue_germ, regularStalkValue_germ]
  change rationalValue X U ((regularMap X).app U (show Γ(X,U) from s)) =
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx (show Γ(X,U) from s))
  rw [regularMap_value, Scheme.algebraMap_germ_eq_germToFunctionField]

theorem rationalStalkMap_scaledRegularMap (f : X.functionFieldˣ) (x : X)
    (m : (regularModule X).presheaf.stalk x) :
    rationalStalkEquiv X x (Scheme.Modules.moduleStalkMap x
        (scaledRegularMap X f) m) =
      (f : X.functionField) *
        algebraMap (X.presheaf.stalk x) X.functionField (regularStalkEquiv X x m) := by
  obtain ⟨U, hx, s, rfl⟩ := (regularModule X).presheaf.exists_germ_eq m
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  change rationalStalkValue X x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (scaledRegularMap X f).mapPresheaf ((regularModule X).presheaf.germ U x hx s)) =
      (f : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField
        (regularStalkValue X x ((regularModule X).presheaf.germ U x hx s))
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, rationalStalkValue_germ, regularStalkValue_germ]
  change rationalValue X U ((scaledRegularMap X f).app U (show Γ(X,U) from s)) =
    (f : X.functionField) *
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx (show Γ(X,U) from s))
  rw [scaledRegularMap_value, Scheme.algebraMap_germ_eq_germToFunctionField]
/-- Extract the two regular stalk coordinates of a common fractional-ideal germ. -/
def pairStalkMap (f : X.functionFieldˣ) (x : X) :
    (commonIdeal X f).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      ((X.presheaf.stalk x) × (X.presheaf.stalk x)) :=
  ((regularStalkEquiv X x).toLinearMap.comp
    (Scheme.Modules.moduleStalkMap x (leftInclusion X f))).prod
      ((regularStalkEquiv X x).toLinearMap.comp
        (Scheme.Modules.moduleStalkMap x (rightInclusion X f)))

theorem pairStalkMap_relation (f : X.functionFieldˣ) (x : X)
    (m : (commonIdeal X f).presheaf.stalk x) :
    pairStalkMap X f x m ∈
        LocalRelation.commonModule (X.presheaf.stalk x) X.functionField f := by
  let F := Scheme.Modules.moduleStalk X x
  have hc : F.map (leftInclusion X f) ≫ F.map (regularMap X) =
      F.map (rightInclusion X f) ≫ F.map (scaledRegularMap X f) := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (show leftInclusion X f ≫ regularMap X =
      rightInclusion X f ≫ scaledRegularMap X f from CategoryTheory.Limits.pullback.condition)
  have h := congrArg (rationalStalkEquiv X x) (ConcreteCategory.congr_hom hc m)
  change rationalStalkEquiv X x (Scheme.Modules.moduleStalkMap x
      (regularMap X)
    (Scheme.Modules.moduleStalkMap x (leftInclusion X f) m)) =
      rationalStalkEquiv X x (Scheme.Modules.moduleStalkMap x
          (scaledRegularMap X f)
        (Scheme.Modules.moduleStalkMap x (rightInclusion X f) m)) at h
  rw [rationalStalkMap_regularMap, rationalStalkMap_scaledRegularMap] at h
  exact sub_eq_zero.mpr h

/-- View the pair of stalk coordinates as an element of the local common-relation submodule. -/
def commonStalkLinear (f : X.functionFieldˣ) (x : X) :
    (commonIdeal X f).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      LocalRelation.commonModule (X.presheaf.stalk x) X.functionField f :=
  (pairStalkMap X f x).codRestrict _ (pairStalkMap_relation X f x)

theorem commonStalkLinear_injective (f : X.functionFieldˣ) (x : X) :
    Function.Injective (commonStalkLinear X f x) := by
  have hinj : Function.Injective (Scheme.Modules.moduleStalkMap x
      (leftInclusion X f)) :=
    (ModuleCat.mono_iff_injective ((Scheme.Modules.moduleStalk X x).map
      (leftInclusion X f))).mp inferInstance
  intro m n h
  apply hinj
  apply (regularStalkEquiv X x).injective
  exact congrArg (fun z => z.val.1) h

theorem commonStalkLinear_surjective (f : X.functionFieldˣ) (x : X) :
    Function.Surjective (commonStalkLinear X f x) := by
  let F := Scheme.Modules.moduleStalk X x
  let e := PreservesPullback.iso F (regularMap X) (scaledRegularMap X f)
  intro z
  let u := (regularStalkEquiv X x).symm z.val.1
  let v := (regularStalkEquiv X x).symm z.val.2
  have hz : algebraMap (X.presheaf.stalk x) X.functionField z.val.1 =
      (f : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField z.val.2 :=
    sub_eq_zero.mp z.property
  have hc : Scheme.Modules.moduleStalkMap x (regularMap X) u =
      Scheme.Modules.moduleStalkMap x (scaledRegularMap X f) v := by
    apply (rationalStalkEquiv X x).injective
    rw [rationalStalkMap_regularMap, rationalStalkMap_scaledRegularMap]
    simpa only [u, v, LinearEquiv.apply_symm_apply] using hz
  let h₁ : ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶ F.obj (regularModule X) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton (X.presheaf.stalk x) _ u)
  let h₂ : ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) ⟶ F.obj (regularModule X) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton (X.presheaf.stalk x) _ v)
  have hcone : h₁ ≫ F.map (regularMap X) = h₂ ≫ F.map (scaledRegularMap X f) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Scheme.Modules.moduleStalkMap x (regularMap X) (r • u) =
      Scheme.Modules.moduleStalkMap x (scaledRegularMap X f) (r • v)
    rw [(Scheme.Modules.moduleStalkMap x (regularMap X)).map_smul,
      (Scheme.Modules.moduleStalkMap x (scaledRegularMap X f)).map_smul, hc]
  let l := CategoryTheory.Limits.pullback.lift h₁ h₂ hcone
  let m : (commonIdeal X f).presheaf.stalk x := (l ≫ e.inv) (1 : X.presheaf.stalk x)
  have hleft : Scheme.Modules.moduleStalkMap x (leftInclusion X f) m =
      u := by
    change (l ≫ e.inv ≫ F.map (CategoryTheory.Limits.pullback.fst (regularMap X)
        (scaledRegularMap X f))) (1 :
        X.presheaf.stalk x) = u
    rw [PreservesPullback.iso_inv_fst, CategoryTheory.Limits.pullback.lift_fst]
    exact one_smul _ _
  have hright : Scheme.Modules.moduleStalkMap x (rightInclusion X f) m
      = v := by
    change (l ≫ e.inv ≫ F.map (CategoryTheory.Limits.pullback.snd (regularMap X)
        (scaledRegularMap X f))) (1 :
        X.presheaf.stalk x) = v
    rw [PreservesPullback.iso_inv_snd, CategoryTheory.Limits.pullback.lift_snd]
    exact one_smul _ _
  refine ⟨m, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change regularStalkEquiv X x (Scheme.Modules.moduleStalkMap x
      (leftInclusion X f) m) = z.val.1
    rw [hleft]
    exact (regularStalkEquiv X x).apply_symm_apply z.val.1
  · change regularStalkEquiv X x (Scheme.Modules.moduleStalkMap x
      (rightInclusion X f) m) = z.val.2
    rw [hright]
    exact (regularStalkEquiv X x).apply_symm_apply z.val.2

/-- Identify the actual common fractional-ideal stalk with the local module of related pairs. -/
def commonStalkEquiv (f : X.functionFieldˣ) (x : X) :
    (commonIdeal X f).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      LocalRelation.commonModule (X.presheaf.stalk x) X.functionField f :=
  LinearEquiv.ofBijective (commonStalkLinear X f x)
    ⟨commonStalkLinear_injective X f x, commonStalkLinear_surjective X f x⟩
/-- Identify the first quotient stalk with the quotient of the local ring by the first
local projection range. -/
def leftQuotientStalkIso (f : X.functionFieldˣ) (x : X) :
    (Scheme.Modules.moduleStalk X x).obj (leftQuotient X f) ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸
            (LocalRelation.leftProjection (X.presheaf.stalk x) X.functionField f).range) := by
  let F := Scheme.Modules.moduleStalk X x
  let e₁ := (commonStalkEquiv X f x).toModuleIso
  let e₂ := (regularStalkEquiv X x).toModuleIso
  let g := ModuleCat.ofHom
      (LocalRelation.leftProjection (X.presheaf.stalk x) X.functionField (f : X.functionField))
  have h : F.map (leftInclusion X f) ≫ e₂.hom = e₁.hom ≫ g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  exact (PreservesCokernel.iso F (leftInclusion X f)) ≪≫
    (cokernel.mapIso (F.map (leftInclusion X f)) g e₁ e₂ h) ≪≫ ModuleCat.cokernelIsoRangeQuotient g

/-- Identify the second quotient stalk with the quotient of the local ring by the second
local projection range. -/
def rightQuotientStalkIso (f : X.functionFieldˣ) (x : X) :
    (Scheme.Modules.moduleStalk X x).obj (rightQuotient X f) ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸
            (LocalRelation.rightProjection (X.presheaf.stalk x) X.functionField f).range) := by
  let F := Scheme.Modules.moduleStalk X x
  let e₁ := (commonStalkEquiv X f x).toModuleIso
  let e₂ := (regularStalkEquiv X x).toModuleIso
  let g := ModuleCat.ofHom
      (LocalRelation.rightProjection (X.presheaf.stalk x) X.functionField (f : X.functionField))
  have h : F.map (rightInclusion X f) ≫ e₂.hom = e₁.hom ≫ g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  exact (PreservesCokernel.iso F (rightInclusion X f)) ≪≫
    (cokernel.mapIso (F.map (rightInclusion X f)) g e₁ e₂ h) ≪≫ ModuleCat.cokernelIsoRangeQuotient g

/-- Express the first quotient stalk as the quotient-ideal image of the denominator ideal
for the specified fractional presentation. -/
def leftQuotientStalkImageEquiv (f : X.functionFieldˣ) (x : X)
    (a b : X.presheaf.stalk x) (hb : b ≠ 0)
    (hf : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b) :
    (leftQuotient X f).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Ideal.quotientIdealImage (X.presheaf.stalk x) (Ideal.span {a} ⊓ Ideal.span {b})
          (Ideal.span {b}) :=
  (leftQuotientStalkIso X f x).toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (congrArg (fun z =>
      (LocalRelation.leftProjection (X.presheaf.stalk x) X.functionField z).range) hf)).trans
        (LocalRelation.leftQuotientEquiv (X.presheaf.stalk x) X.functionField a b hb))

/-- Express the second quotient stalk as the quotient-ideal image of the numerator ideal
for the specified fractional presentation. -/
def rightQuotientStalkImageEquiv (f : X.functionFieldˣ) (x : X)
    (a b : X.presheaf.stalk x) (hb : b ≠ 0)
    (hf : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b) :
    (rightQuotient X f).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Ideal.quotientIdealImage (X.presheaf.stalk x) (Ideal.span {a} ⊓ Ideal.span {b})
          (Ideal.span {a}) :=
  (rightQuotientStalkIso X f x).toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (congrArg (fun z =>
      (LocalRelation.rightProjection (X.presheaf.stalk x) X.functionField z).range) hf)).trans
        (LocalRelation.rightQuotientEquiv (X.presheaf.stalk x) X.functionField a b hb))
theorem leftQuotient_stalk_subsingleton_of_unit (f : X.functionFieldˣ) (x : X)
    (r : (X.presheaf.stalk x)ˣ)
    (hf : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField r) :
    Subsingleton ((leftQuotient X f).presheaf.stalk x) := by
  have hrepr : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField r /
      algebraMap (X.presheaf.stalk x) X.functionField 1 := by simpa only [map_one, div_one] using hf
  let e := leftQuotientStalkImageEquiv X f x r 1 one_ne_zero hrepr
  have hj : (Ideal.span {(r : X.presheaf.stalk x)} ⊓ Ideal.span {(1 : X.presheaf.stalk x)}) = ⊤
      := by
    rw [Ideal.span_singleton_eq_top.mpr r.isUnit, Ideal.span_singleton_one]
    simp
  let : Subsingleton (X.presheaf.stalk x ⧸
      (Ideal.span {(r : X.presheaf.stalk x)} ⊓ Ideal.span {(1 : X.presheaf.stalk x)})) := by
    rw [hj]
    infer_instance
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

theorem rightQuotient_stalk_subsingleton_of_unit (f : X.functionFieldˣ) (x : X)
    (r : (X.presheaf.stalk x)ˣ)
    (hf : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField r) :
    Subsingleton ((rightQuotient X f).presheaf.stalk x) := by
  have hrepr : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField r /
      algebraMap (X.presheaf.stalk x) X.functionField 1 := by simpa only [map_one, div_one] using hf
  let e := rightQuotientStalkImageEquiv X f x r 1 one_ne_zero hrepr
  have hj : (Ideal.span {(r : X.presheaf.stalk x)} ⊓ Ideal.span {(1 : X.presheaf.stalk x)}) = ⊤
      := by
    rw [Ideal.span_singleton_eq_top.mpr r.isUnit, Ideal.span_singleton_one]
    simp
  let : Subsingleton (X.presheaf.stalk x ⧸
      (Ideal.span {(r : X.presheaf.stalk x)} ⊓ Ideal.span {(1 : X.presheaf.stalk x)})) := by
    rw [hj]
    infer_instance
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

theorem quotient_stalks_subsingleton_on_unit_open (f : X.functionFieldˣ) (U : X.Opens)
    [Nonempty U] (s : Γ(X, U)ˣ) (hs : X.germToFunctionField U s = (f : X.functionField))
    (x : X) (hx : x ∈ U) :
    Subsingleton ((leftQuotient X f).presheaf.stalk x) ∧
      Subsingleton ((rightQuotient X f).presheaf.stalk x) := by
  let r : (X.presheaf.stalk x)ˣ := Units.map (X.presheaf.germ U x hx).hom.toMonoidHom s
  have hf : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField r := by
    change (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ U x hx (s : Γ(X, U)))
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, hs]
  exact ⟨leftQuotient_stalk_subsingleton_of_unit X f x r hf,
    rightQuotient_stalk_subsingleton_of_unit X f x r hf⟩

end AlgebraicGeometry.Scheme.Modules.RationalFunctions.CommonFractionalIdeal
