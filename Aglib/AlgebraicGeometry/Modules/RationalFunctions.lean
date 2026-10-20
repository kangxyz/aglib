/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Basic
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.RationalFunctions` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`a68700635e59758cd351ca02411e172728cbd91793bdf7b1eb58f9c151ce93c2`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules.RationalFunctions
universe u
variable (X : Scheme.{u}) [IsIntegral X] [hNoeth : IsNoetherian X]

/-- The actual sheaf of rational functions, as generic-point direct image. -/
def rationalFunctions : X.Modules :=
  (Scheme.Modules.pushforward ((X.fromSpecStalk (genericPoint X)))).obj
    (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)

omit hNoeth in
-- Retain the original Noetherian integral-scheme interface for rational sections.
@[nolint unusedArguments]
theorem generic_preimage_eq_top [IsNoetherian X] (U : X.Opens) [hU : Nonempty U] :
    ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U = ⊤ := by
  apply le_antisymm le_top
  intro z _
  let : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of X.functionField)))
  have hz : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  change (X.fromSpecStalk (genericPoint X)) z ∈ U
  rw [hz, AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- Rational sections on any nonempty open are the actual function field. -/
def rationalSectionIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U) ≅ X.functionField :=
  (eqToIso (by rw [generic_preimage_eq_top X U])) ≪≫ Scheme.ΓSpecIso X.functionField

omit hNoeth in
-- Retain the original Noetherian and nonempty-open guards of the rational-section formula.
@[nolint unusedArguments]
theorem rationalFunctions_obj [IsNoetherian X] (U : X.Opens) [Nonempty U] :
    (rationalFunctions X).val.obj (op U) =
      (ModuleCat.restrictScalars (((X.fromSpecStalk (genericPoint X))).app U).hom).obj
        (ModuleCat.of Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)
          Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U)) := rfl

omit hNoeth in
theorem generic_app_rationalSectionIso [IsNoetherian X] (U : X.Opens) [hU : Nonempty U] :
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

/-- The linear value map from rational-function sections on a nonempty open to the
function field, with the actual section scalar action. -/
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

omit hNoeth in
theorem rationalSectionIso_naturality [IsNoetherian X] {U V : X.Opens} [Nonempty U] [Nonempty V]
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

omit hNoeth in
theorem rationalValue_restrict [IsNoetherian X] {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : (rationalFunctions X).val.obj (op V)) :
    rationalValue X U ((rationalFunctions X).val.map i.op s) = rationalValue X V s :=
  congrArg (fun e => (e : Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ V) ⟶
    X.functionField) s) (rationalSectionIso_naturality X i)




/-- Identify rational-function sections on a nonempty open with the function field by
their actual value map. -/
def rationalValueEquiv (U : X.Opens) [Nonempty U] :
    (rationalFunctions X).val.obj (op U) ≃ₗ[Γ(X, U)] X.functionField :=
  LinearEquiv.ofBijective (rationalValue X U)
    (ConcreteCategory.bijective_of_isIso (rationalSectionIso X U).hom)

end AlgebraicGeometry.Scheme.Modules.RationalFunctions
