/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkStrata
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Quotient
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.CategoryTheory.ExactCategory.Basic

/-!
# Faithful exact stalk descent through support quotients

Source-only extraction from `R5Lab.KTheory.Quillen.CoherentStratumQuotient` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.StratumQuotient` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1727398aa6bb34dc2e917bcc4515cd7ad0a198349017640ad9aa34436b933e75`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
open ModuleCat.FiniteLengthFamilies CategoryTheory.Pi
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable (X : Scheme.{u}) [IsNoetherian X] (p : ℕ)

instance stratumStalks_preservesFiniteLimits : PreservesFiniteLimits (stratumStalks X
    p).toFunctor := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S h
  have he := (stratumStalks X p).map_conflation S h
  exact ⟨he.exact, he.mono_f⟩

instance stratumStalks_preservesFiniteColimits : PreservesFiniteColimits (stratumStalks X
    p).toFunctor := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S h
  have he := (stratumStalks X p).map_conflation S h
  exact ⟨he.exact, he.epi_g⟩

/-- The objects of the height-at-least-`p` category whose height-`p` stalks all vanish. -/
abbrev nextSupport : ObjectProperty (CohAtLeast X p) := (stratumStalks X p).toFunctor.kernel
instance nextSupport_serre : (nextSupport X p).IsSerreClass :=
  CategoryTheory.ObjectProperty.exactKernelSerre (stratumStalks X p)

/-- The Serre class used below is exactly the actual next stalk-support condition. -/
theorem nextSupport_eq : nextSupport X p =
    fun M : CohAtLeast X p => coherentAtLeast X (p + 1) M.obj := by
  funext M
  exact propext (stratumStalks_kernel_next X p M)

/-- The Serre quotient of height-at-least-`p` objects by those with vanishing height-`p` stalks. -/
abbrev StratumQuotient := (nextSupport X p).isoModSerre.Localization
instance stratumQuotientAbelian : Abelian (StratumQuotient X p) :=
  ObjectProperty.SerreClassLocalization.abelian (nextSupport X p).isoModSerre.Q (nextSupport X p)

lemma stalkDenominator_iff {M N : CohAtLeast X p} (f : M ⟶ N) :
    (nextSupport X p).isoModSerre f ↔ IsIso ((stratumStalks X p).toFunctor.map f) := by
  change (stratumStalks X p).toFunctor.kernel.isoModSerre f ↔ _
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  rfl

lemma stalks_inverts : (nextSupport X p).isoModSerre.IsInvertedBy (stratumStalks X p).toFunctor
    := by
  intro M N f hf
  exact (stalkDenominator_iff X p f).mp hf

/-- The actual stalk map descends to the actual Serre quotient. No quotient equivalence
or essential-surjectivity premise is present. -/
/- Exact faithful descent reaches finite-support modules; no quotient equivalence,
   fullness, or essential-surjectivity claim is made. -/
def quotientStalks : StratumQuotient X p ⥤ FiniteSupportFamily (localRings X p) :=
  Localization.Construction.lift (stratumStalks X p).toFunctor (stalks_inverts X p)

theorem quotientStalks_fac :
    (nextSupport X p).isoModSerre.Q ⋙ quotientStalks X p = (stratumStalks X p).toFunctor :=
  Localization.Construction.fac _ _

@[simp] theorem quotientStalks_map_Q {M N : CohAtLeast X p} (f : M ⟶ N) :
    (quotientStalks X p).map ((nextSupport X p).isoModSerre.Q.map f) =
      (stratumStalks X p).toFunctor.map f := by
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom (quotientStalks_fac X p) f

/-- A stalk-zero morphism has its actual kernel inclusion as a valid denominator. -/
theorem stalk_kernel_denominator {M N : CohAtLeast X p} (f : M ⟶ N)
    (hf : (stratumStalks X p).toFunctor.map f = 0) :
    (nextSupport X p).isoModSerre (kernel.ι f) := by
  rw [stalkDenominator_iff]
  exact KernelFork.IsLimit.isIso_ι _
    (KernelFork.mapIsLimit _ (kernelIsKernel f) (stratumStalks X p).toFunctor) hf

/-- Faithfulness on all quotient morphisms follows by genuine kernel fractions. -/
instance quotientStalks_faithful : (quotientStalks X p).Faithful := by
  let Q := (nextSupport X p).isoModSerre.Q
  apply Functor.faithful_of_comp_of_hasLeftCalculusOfFractions Q
    (nextSupport X p).isoModSerre (quotientStalks X p)
  intro M N f g h
  simp only [Q, quotientStalks_map_Q] at h
  have hs : (nextSupport X p).isoModSerre (kernel.ι (f - g)) :=
    stalk_kernel_denominator X p (f - g) (by simp [h])
  have : IsIso (Q.map (kernel.ι (f - g))) :=
    Localization.inverts Q (nextSupport X p).isoModSerre _ hs
  apply (cancel_epi (Q.map (kernel.ι (f - g)))).mp
  have he : kernel.ι (f - g) ≫ f = kernel.ι (f - g) ≫ g := by
    simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f - g)
  simpa only [← Q.map_comp] using congrArg Q.map he

instance quotientStalks_additive : (quotientStalks X p).Additive := by
  apply (Localization.functor_additive_iff (nextSupport X p).isoModSerre.Q
    (nextSupport X p).isoModSerre _).mpr
  rw [quotientStalks_fac]
  infer_instance

instance quotientStalks_preservesFiniteLimits : PreservesFiniteLimits (quotientStalks X p) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    (nextSupport X p).isoModSerre.Q (nextSupport X p) _).mp
  rw [quotientStalks_fac]
  infer_instance

instance quotientStalks_preservesFiniteColimits : PreservesFiniteColimits (quotientStalks X p) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    (nextSupport X p).isoModSerre.Q (nextSupport X p) _).mp
  rw [quotientStalks_fac]
  infer_instance

/-- The exact functor from the support-stratum quotient to its finite-support stalk families. -/
def quotientStalksExact : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (StratumQuotient X p))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (FiniteSupportFamily (localRings
        X p))) where
  toFunctor := quotientStalks X p
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
