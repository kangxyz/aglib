/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistExt.Linear

/-!
# Twist Ext with arbitrary base-module coefficients

The original opposite-twist tensor adjunction identifies native Ext into
`O(b) ⊗ π*tilde(J)` with the unchanged additive-sheaf cohomology of
`O(-a+b) ⊗ π*tilde(J)`. The comparison retains its four original forward factors,
the structural R-action, and native coefficient morphisms. The sharp positive-twist
vanishing gives positive Ext effacement for every sufficiently negative source twist.

The ring and base module are arbitrary. No flatness, finiteness, projectivity,
injectivity or Noetherianity assumption is imposed on the base coefficients.
-/

public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The actual opposite-twist tensor adjunction retains arbitrary native coefficients. -/
@[expose]
def twistingTensorCoefficientsExtCohomologyAddEquiv (a b : ℤ)
    (J : ModuleCat.{u} R) (q : ℕ) :
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheafTensorCoefficients R ι b J) q ≃+
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheafTensorCoefficients R ι (-a + b) J)) q := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let T := twistingTensorEquivalence R ι a
  let P : X.Modules := (Scheme.Modules.pullback (toSpec R ι)).obj
    (tilde (R := CommRingCat.of R) J)
  let N : X.Modules := twistingSheafTensorCoefficients R ι b J
  let : T.functor.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
  let : T.inverse.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
  let e₁ : Ext.{u + 1} (C := X.Modules) (twistingSheaf R ι a) N q ≃+
      Ext.{u + 1} (C := X.Modules) (T.functor.obj O) N q :=
    (((extFunctor (C := X.Modules) q).mapIso
      (twistingTensorUnitIso R ι a).op).app N).addCommGroupIsoToAddEquiv
  let e₂ : Ext.{u + 1} (C := X.Modules) (T.functor.obj O) N q ≃+
      Ext.{u + 1} (C := X.Modules) O (T.inverse.obj N) q := T.toAdjunction.extEquiv
  let e₃ : Ext.{u + 1} (C := X.Modules) O (T.inverse.obj N) q ≃+
      Ext.{u + 1} (C := X.Modules) O (twistingSheafTensorCoefficients R ι (-a + b) J) q :=
    ((extFunctorObj O q).mapIso
      ((twistingTensorCompIso R ι (-a) b).app P)).addCommGroupIsoToAddEquiv
  exact e₁.trans (e₂.trans (e₃.trans
    (moduleExtCohomologyAddEquiv X (twistingSheafTensorCoefficients R ι (-a + b) J) q)))

/-- Positive Ext vanishes in the sharp positive-difference range for every base module. -/
theorem twistingTensorCoefficientsExt_subsingleton_of_neg_le_difference
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (a b : ℤ) (J : ModuleCat.{u} R) (q : ℕ)
    (hd : -(n : ℤ) ≤ -a + b) (hq : q ≠ 0) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheafTensorCoefficients R ι b J) q) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := twistingTensorCohomology_subsingleton_of_neg_le_degree R ι n e (-a + b) hd J q hq
  exact (twistingTensorCoefficientsExtCohomologyAddEquiv R ι a b J q).injective.subsingleton

/-- Sufficiently negative twists efface positive Ext into the coefficient residue twist. -/
theorem negativeTwistExt_dualizingCoefficients_subsingleton [Fintype ι]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : ℕ) (hN : Fintype.card ι ≤ N)
    (J : ModuleCat.{u} R) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι (-(N : ℤ)))
      (twistingSheafTensorCoefficients R ι (-(Fintype.card ι : ℤ)) J) q) :=
  twistingTensorCoefficientsExt_subsingleton_of_neg_le_difference R ι n e _ _ J q (by
    have hN' : (Fintype.card ι : ℤ) ≤ N := by exact_mod_cast hN
    omega) hq


private def twistingExtCohomologyLinearEquivWithIso
    (α : R →+* Γ(ProjectiveSpace R ι, ⊤)) (a : ℤ)
    (N D : (ProjectiveSpace R ι).Modules)
    (β : (twistingTensorEquivalence R ι a).inverse.obj N ≅ D) (q : ℕ) :
    let X : Scheme.{u} := ProjectiveSpace R ι
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCohomologyModuleOfHom X α D q
    Ext.{u + 1} (C := X.Modules) (twistingSheaf R ι a) N q ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X D) q := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  letI := moduleCategoryLinearOfHom X α
  letI := moduleCohomologyModuleOfHom X α D q
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let T := twistingTensorEquivalence R ι a
  letI : T.functor.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
  letI : T.inverse.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
  letI : Functor.Linear R T.inverse := inferInstanceAs
    (Functor.Linear R (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))))
  let E₁ : Ext.{u + 1} (C := X.Modules) (twistingSheaf R ι a) N q ≃ₗ[R]
      Ext.{u + 1} (C := X.Modules) (T.functor.obj O) N q := {
    __ := (((extFunctor (C := X.Modules) q).mapIso
      (twistingTensorUnitIso R ι a).op).app N).addCommGroupIsoToAddEquiv
    map_smul' := by
      intro r x
      change (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp (r • x) (Nat.zero_add q) =
        r • (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp x (Nat.zero_add q)
      exact Ext.comp_smul _ _ _ _ }
  let E₂ : Ext.{u + 1} (C := X.Modules) (T.functor.obj O) N q ≃ₗ[R]
      Ext.{u + 1} (C := X.Modules) O (T.inverse.obj N) q :=
    T.toAdjunction.extLinearEquiv R
  let E₃ : Ext.{u + 1} (C := X.Modules) O (T.inverse.obj N) q ≃ₗ[R]
      Ext.{u + 1} (C := X.Modules) O D q := {
    __ := ((extFunctorObj O q).mapIso β).addCommGroupIsoToAddEquiv
    map_smul' := by
      intro r x
      change (r • x).comp (Ext.mk₀ β.hom) (Nat.add_zero q) =
        r • x.comp (Ext.mk₀ β.hom) (Nat.add_zero q)
      exact Ext.smul_comp _ _ _ _ }
  exact E₁.trans (E₂.trans (E₃.trans
    (moduleExtCohomologyLinearEquivOfCategory X α D q)))

/-- The original additive comparison is linear for the actual structural R-action.
Its data is reduced publicly by the literal additive-map theorem below. -/
def twistingTensorCoefficientsExtCohomologyLinearEquiv (a b : ℤ)
    (J : ModuleCat.{u} R) (q : ℕ) :
    let X : Scheme.{u} := ProjectiveSpace R ι
    let α : R →+* Γ(X, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let N : X.Modules := twistingSheafTensorCoefficients R ι b J
    let D : X.Modules := twistingSheafTensorCoefficients R ι (-a + b) J
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCohomologyModuleOfHom X α D q
    Ext.{u + 1} (C := X.Modules) (twistingSheaf R ι a) N q ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X D) q :=
  twistingExtCohomologyLinearEquivWithIso R ι
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    a (twistingSheafTensorCoefficients R ι b J)
    (twistingSheafTensorCoefficients R ι (-a + b) J)
    ((twistingTensorCompIso R ι (-a) b).app
      ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde J))) q

@[expose] public section

/-- The linear refinement has literally the original four-factor additive map. -/
theorem twistingTensorCoefficientsExtCohomologyLinearEquiv_toAddEquiv (a b : ℤ)
    (J : ModuleCat.{u} R) (q : ℕ) :
    let X := ProjectiveSpace R ι
    let α : R →+* Γ(X, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom X α
    letI := moduleCohomologyModuleOfHom X α
      (twistingSheafTensorCoefficients R ι (-a + b) J) q
    (twistingTensorCoefficientsExtCohomologyLinearEquiv R ι a b J q).toAddEquiv =
      twistingTensorCoefficientsExtCohomologyAddEquiv R ι a b J q := by
  apply AddEquiv.ext
  intro x
  rfl


/-- The forward map is the original unit precomposition, adjunction, multiplication,
and module Ext/cohomology comparison, in that order. -/
theorem twistingTensorCoefficientsExtCohomologyAddEquiv_apply (a b : ℤ)
    (J : ModuleCat.{u} R) (q : ℕ)
    (x : Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheafTensorCoefficients R ι b J) q) :
    let X := ProjectiveSpace R ι
    let T := twistingTensorEquivalence R ι a
    letI : T.functor.Additive := inferInstanceAs
      (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
    letI : T.inverse.Additive := inferInstanceAs
      (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
    twistingTensorCoefficientsExtCohomologyAddEquiv R ι a b J q x =
      moduleExtCohomologyMap X (twistingSheafTensorCoefficients R ι (-a + b) J) q
        ((T.toAdjunction.extEquiv
          ((Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp x (Nat.zero_add q))).comp
            (Ext.mk₀ ((twistingTensorCompIso R ι (-a) b).hom.app
              ((Scheme.Modules.pullback (toSpec R ι)).obj
                (tilde (R := CommRingCat.of R) J)))) (Nat.add_zero q)) := rfl

private theorem twistingTensorCompIso_coefficients_naturality (a b : ℤ)
    {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    ((twistingTensorCompIso R ι (-a) b).app
      ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde J))).inv ≫
      (twistingTensorEquivalence R ι a).inverse.map
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) ≫
      ((twistingTensorCompIso R ι (-a) b).app
        ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde J'))).hom =
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-a + b))).map
      ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)) := by
  let h := (Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)
  have hn := (twistingTensorCompIso R ι (-a) b).hom.naturality h
  change (twistingTensorEquivalence R ι a).inverse.map
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).map h) ≫
      ((twistingTensorCompIso R ι (-a) b).app
        ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde J'))).hom =
    ((twistingTensorCompIso R ι (-a) b).app
      ((Scheme.Modules.pullback (toSpec R ι)).obj (tilde J))).hom ≫ _ at hn
  rw [hn, Iso.inv_hom_id_assoc]

/-- Every native base-coefficient morphism induces the original cohomology map. -/
theorem twistingTensorCoefficientsExtCohomologyAddEquiv_naturality_coefficients
    (a b : ℤ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') (q : ℕ)
    (x : Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheafTensorCoefficients R ι b J) q) :
    twistingTensorCoefficientsExtCohomologyAddEquiv R ι a b J' q
      (x.comp (Ext.mk₀
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)))) (Nat.add_zero q)) =
    Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-a + b))).map
        ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)))) q
      (twistingTensorCoefficientsExtCohomologyAddEquiv R ι a b J q x) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let T := twistingTensorEquivalence R ι a
  let : T.functor.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
  let : T.inverse.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
  let P : X.Modules := (Scheme.Modules.pullback (toSpec R ι)).obj (tilde J)
  let P' : X.Modules := (Scheme.Modules.pullback (toSpec R ι)).obj (tilde J')
  let ψ := (moduleTensorLeftFunctor X (twistingSheaf R ι b)).map
    ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))
  let β := (twistingTensorCompIso R ι (-a) b).app P
  let β' := (twistingTensorCompIso R ι (-a) b).app P'
  let δ := β.inv ≫ T.inverse.map ψ ≫ β'.hom
  have hδ : δ =
      (moduleTensorLeftFunctor X (twistingSheaf R ι (-a + b))).map
        ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)) :=
    twistingTensorCompIso_coefficients_naturality R ι a b f
  conv_rhs => rw [← hδ]
  let y := (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp x (Nat.zero_add q)
  change moduleExtCohomologyMap X (twistingSheafTensorCoefficients R ι (-a + b) J') q
      ((T.toAdjunction.extEquiv
        ((Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp
          (x.comp (Ext.mk₀ ψ) (Nat.add_zero q)) (Nat.zero_add q))).comp
            (Ext.mk₀ β'.hom) (Nat.add_zero q)) =
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map δ) q
      (moduleExtCohomologyMap X (twistingSheafTensorCoefficients R ι (-a + b) J) q
        ((T.toAdjunction.extEquiv y).comp (Ext.mk₀ β.hom) (Nat.add_zero q)))
  rw [← moduleExtCohomologyMap_naturality]
  apply congrArg (moduleExtCohomologyMap X (twistingSheafTensorCoefficients R ι (-a + b) J') q)
  have hp : (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp
      (x.comp (Ext.mk₀ ψ) (Nat.add_zero q)) (Nat.zero_add q) =
      y.comp (Ext.mk₀ ψ) (Nat.add_zero q) :=
    (Ext.comp_assoc_of_third_deg_zero _ _ _ (Nat.zero_add q)).symm
  rw [hp, T.toAdjunction.extEquiv_naturality_right₀]
  dsimp only [δ]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_assoc]

/-- The same native coefficient naturality uses the original structural linear map. -/
theorem twistingTensorCoefficientsExtCohomologyLinearEquiv_naturality_coefficients
    (a b : ℤ) {J J' : ModuleCat.{u} R} (f : J ⟶ J') (q : ℕ)
    (x : Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheafTensorCoefficients R ι b J) q) :
    twistingTensorCoefficientsExtCohomologyLinearEquiv R ι a b J' q
      (x.comp (Ext.mk₀
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f)))) (Nat.add_zero q)) =
    moduleCohomologyMapOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-a + b))).map
        ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) q
      (twistingTensorCoefficientsExtCohomologyLinearEquiv R ι a b J q x) :=
  twistingTensorCoefficientsExtCohomologyAddEquiv_naturality_coefficients R ι a b f q x

end

end AlgebraicGeometry.Scheme.Cohomology
