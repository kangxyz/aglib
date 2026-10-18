/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal

/-!
# Genuine ideal transport is original open restriction

The native restriction identity and composition isomorphisms preserve
arrows on the original chart. Equality of the quotient ideal therefore
presents its original chart arrow by actual spectral restriction, with
its original restriction-congruence and composition maps retained.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem restrictionLeftIdentityIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules) :
    (restrictFunctorCongr (Category.id_comp j).symm).hom.app M ≫
        (restrictFunctorComp (𝟙 U) j).hom.app M =
      restrictFunctorId.inv.app (M.restrict j) := by
  apply Scheme.Modules.hom_ext
  intro V
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_hom_app_app, restrictFunctorId_inv_app_app]
  change M.presheaf.map _ ≫ M.presheaf.map _ = M.presheaf.map _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

private theorem restrictionLeftIdentity_naturality {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules}
    (f : M.restrict j ⟶ N.restrict j) (g : U ⟶ U) [IsOpenImmersion g]
    (hg : g = 𝟙 U) (h : j = g ≫ j) :
    (restrictFunctorCongr h).hom.app M ≫ (restrictFunctorComp g j).hom.app M ≫
        (restrictFunctor g).map f =
      f ≫ (restrictFunctorCongr h).hom.app N ≫ (restrictFunctorComp g j).hom.app N := by
  subst g
  have hM := restrictionLeftIdentityIso j M
  have hN := restrictionLeftIdentityIso j N
  have hfg := restrictFunctorId.inv.naturality f
  have hTotal : ((restrictFunctorCongr h).hom.app M ≫
      (restrictFunctorComp (𝟙 U) j).hom.app M) ≫ (restrictFunctor (𝟙 U)).map f =
      f ≫ ((restrictFunctorCongr h).hom.app N ≫
        (restrictFunctorComp (𝟙 U) j).hom.app N) :=
    (congrArg (fun k => k ≫ (restrictFunctor (𝟙 U)).map f) hM).trans
      (hfg.symm.trans (congrArg (fun k => f ≫ k) hN.symm))
  simpa only [Category.assoc] using hTotal

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance chartIdealRestrictionStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) (J : InjectiveResolution (relativeCanonicalModule p n))
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- Genuine ideal transport of the original chart arrow is its original spectral restriction. -/
theorem canonicalCommonModelChartHomologyIsoAtIdeal_restrict (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    let Q := C.quotientChart
    let g := Spec.map (Ideal.quotEquivOfEq hI).toCommRingCatIso.hom
    let h := canonicalChartSourceAtIdeal_spec C I hI
    let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)
    let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
    (restrictFunctorCongr h).hom.app M ≫ (restrictFunctorComp g Q.jX).hom.app M ≫
        (restrictFunctor g).map (canonicalCommonModelChartHomologyIso i p n d J C).hom =
      (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J C I hI).hom ≫
        (restrictFunctorCongr h).hom.app N ≫ (restrictFunctorComp g Q.jX).hom.app N := by
  subst I
  intro Q g h M N
  have hg : g = 𝟙 (Spec Q.B) := by
    apply (cancel_mono Q.jX).mp
    exact h.symm.trans (Category.id_comp Q.jX).symm
  exact restrictionLeftIdentity_naturality Q.jX
    (canonicalCommonModelChartHomologyIso i p n d J C).hom g hg h

end AlgebraicGeometry.Scheme.Modules
