/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SupportedStalkFinite
public import Aglib.CategoryTheory.Pi.FiniteSupport

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.SupportedFamilies` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`74db4f9d0c12e922bb9f4b532efd5cd0b69d0f954a0e0b577ad1100d3b24e675`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pi AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
attribute [local instance] canonicalQuotientAbelian
open AlgebraicGeometry.Scheme.Modules.Coherent.Support

open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]

/-- The full category of coherent sheaves supported at the closed point of the specified
codimension-one local spectrum. -/
abbrev localSupportedCategories (x : CodimensionOnePoint X) := (localSupport X x).FullSubcategory

instance instAbelianLocalSupportedCategories : ∀ x, Abelian (localSupportedCategories X x) :=
  fun x => inferInstanceAs (Abelian (localSupport X x).FullSubcategory)

/-- The exact functor taking a coherent sheaf in the support stratum to all its supported
codimension-one stalks. -/
def allSupportedStalks : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohOne X))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (∀ x : CodimensionOnePoint X,
        localSupportedCategories X x)) where
  toFunctor := Functor.pi' (fun x => (supportedStalk X x).toFunctor)
  additive := {map_add := by intros; funext x; exact (supportedStalk X x).toFunctor.map_add}
  map_conflation S h := shortExact_pi_of _ _ (fun x => (supportedStalk X x).map_conflation S h)

/-- The exact functor assembling supported codimension-one stalks as a finitely supported family. -/
def supportedStalkFamily : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohOne X))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (FiniteCategoryFamily
        (localSupportedCategories X))) where
  toFunctor := (finiteObjectSupport (localSupportedCategories X)).lift
    (allSupportedStalks X).toFunctor (supportedStalk_finite X)
  additive := {map_add := by intros; apply ObjectProperty.hom_ext; exact (allSupportedStalks
      X).toFunctor.map_add}
  map_conflation S h := by
    let P := finiteObjectSupport (localSupportedCategories X)
    have he := (allSupportedStalks X).map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful P.ι _ he.exact
            mono_f := P.ι.mono_of_mono_map he.mono_f
            epi_g := P.ι.epi_of_epi_map he.epi_g }

/-- The family kernel is precisely the ACTUAL second support class. -/
theorem supportedStalkFamily_kernel (N : CohOne X) :
    (supportedStalkFamily X).toFunctor.kernel N ↔ secondSupport X N := by
  constructor
  · intro h x
    have hx := (finiteCategoryEvaluation (localSupportedCategories X) x).toFunctor.map_isZero h
    exact (localSupport X x).ι.map_isZero hx
  · intro h
    apply IsZero.of_full_of_faithful_of_isZero
      (finiteObjectSupport (localSupportedCategories X)).ι _
    apply (isZero_family_iff (localSupportedCategories X) _).mpr
    intro x
    exact IsZero.of_full_of_faithful_of_isZero (localSupport X x).ι _ (h x)

theorem quotientSupportedStalkFamily_finite (N : (secondSupport X).isoModSerre.Localization) :
    finiteObjectSupport (localSupportedCategories X) (fun x => (quotientSupportedStalk X x).obj
        N) := by
  obtain ⟨N, rfl⟩ := (Localization.Construction.objEquiv (secondSupport X).isoModSerre).surjective N
  exact supportedStalk_finite X N

instance quotientSupportedStalkPi_additive :
    (Functor.pi' (fun x : CodimensionOnePoint X => quotientSupportedStalk X x)).Additive where
  map_add := by
    intros
    funext x
    exact (quotientSupportedStalk X x).map_add

/-- The specified family of actual quotient stalks with proved finite support. -/
def quotientSupportedStalkFamily : _root_.CategoryTheory.ExactCategory.ExactFunctor
    ((_root_.CategoryTheory.ExactCategory.abelianExactStructure
      (secondSupport X).isoModSerre.Localization))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (FiniteCategoryFamily
        (localSupportedCategories X))) where
  toFunctor := (finiteObjectSupport (localSupportedCategories X)).lift
    (Functor.pi' (fun x => quotientSupportedStalk X x)) (quotientSupportedStalkFamily_finite X)
  additive := {
    map_add := by
      intros
      apply ObjectProperty.hom_ext
      funext x
      exact (quotientSupportedStalk X x).map_add }
  map_conflation S h := by
    let P := finiteObjectSupport (localSupportedCategories X)
    have he := shortExact_pi_of (localSupportedCategories X)
      (S.map (Functor.pi' (fun x => quotientSupportedStalk X x)))
      (fun x => (quotientSupportedStalkExact X x).map_conflation S h)
    exact { exact := Functor.reflects_exact_of_faithful P.ι _ he.exact
            mono_f := P.ι.mono_of_mono_map he.mono_f
            epi_g := P.ι.epi_of_epi_map he.epi_g }

theorem quotientSupportedStalkFamily_fac :
    (secondSupport X).isoModSerre.Q ⋙ (quotientSupportedStalkFamily X).toFunctor =
      (supportedStalkFamily X).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro N N' f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext
  funext x
  change (quotientSupportedStalk X x).map ((secondSupport X).isoModSerre.Q.map f) =
    (supportedStalk X x).toFunctor.map f
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    CategoryTheory.Functor.congr_hom (quotientSupportedStalk_fac X x) f

/-- The evaluation of the constructed family is the original quotient stalk. -/
theorem quotientSupportedStalkFamily_evaluation (x : CodimensionOnePoint X) :
    (quotientSupportedStalkFamily X).toFunctor ⋙
      (finiteCategoryEvaluation (localSupportedCategories X) x).toFunctor =
      (quotientSupportedStalkExact X x).toFunctor := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
