/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Denominators
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor

/-!
# The coherent support quotient and restriction

Restriction descends from Mathlib's constructed support-Serre quotient. The descended functor is
faithful, additive and exact, with literal factorization and image-support equations.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Quotient.lean`.
SHA-256: `9fd97aad52a1914a00545bd3d86192a0b3db4b1b8cc155073b72c2cbfabf5725`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual categorical quotient by coherent sheaves supported off the open. -/
abbrev CoherentSupportQuotient := (finiteTypeSheavesSupportedAway j).isoModSerre.Localization

/-- The actual supported Serre quotient carries Mathlib's abelian structure. -/
instance instAbelianCoherentSupportQuotient : Abelian (CoherentSupportQuotient j) :=
  ObjectProperty.SerreClassLocalization.abelian
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q (finiteTypeSheavesSupportedAway j)

/-- Restriction descends to the actual constructed coherent Serre quotient. -/
def quotientCoherentRestriction : CoherentSupportQuotient j ⥤ FiniteTypeSheaves U :=
  Localization.Construction.lift (finiteTypeSheavesRestriction j)
    (finiteTypeSheavesRestriction_inverts_support j)

/-- The descended functor factors actual geometric restriction strictly. -/
theorem quotientCoherentRestriction_fac :
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q ⋙ quotientCoherentRestriction j =
      finiteTypeSheavesRestriction j :=
  Localization.Construction.fac _ _

/-- The associated natural isomorphism explicitly identifies the quotient
factorization with actual coherent restriction. -/
def quotientCoherentRestrictionFactorsIso :
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q ⋙ quotientCoherentRestriction j ≅
      finiteTypeSheavesRestriction j := eqToIso (quotientCoherentRestriction_fac j)

/-- The quotient comparison sends an original quotient arrow to its actual restricted arrow. -/
@[simp] theorem quotientCoherentRestriction_map_Q {M N : FiniteTypeSheaves X} (f : M ⟶ N) :
    (quotientCoherentRestriction j).map ((finiteTypeSheavesSupportedAway j).isoModSerre.Q.map f) =
      (finiteTypeSheavesRestriction j).map f := by
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom (quotientCoherentRestriction_fac j) f

/-- The induced functor is faithful on every quotient morphism, by the
actual coherent kernel denominators and the Serre fraction calculus. -/
instance quotientCoherentRestriction_faithful : (quotientCoherentRestriction j).Faithful := by
  let Q := (finiteTypeSheavesSupportedAway j).isoModSerre.Q
  apply Functor.faithful_of_comp_of_hasLeftCalculusOfFractions Q
    (finiteTypeSheavesSupportedAway j).isoModSerre (quotientCoherentRestriction j)
  intro M N f g h
  simp only [Q, quotientCoherentRestriction_map_Q] at h
  obtain ⟨M', s, _, hs, hfg⟩ := (finiteTypeSheavesRestriction_map_eq_iff_denominator j f g).mp h
  have : IsIso (Q.map s) :=
    Localization.inverts Q (finiteTypeSheavesSupportedAway j).isoModSerre s hs
  apply (cancel_epi (Q.map s)).mp
  simpa only [← Q.map_comp] using congrArg Q.map hfg

/-- The actual descended restriction functor is additive. -/
instance quotientCoherentRestriction_additive : (quotientCoherentRestriction j).Additive := by
  apply (Localization.functor_additive_iff (finiteTypeSheavesSupportedAway j).isoModSerre.Q
    (finiteTypeSheavesSupportedAway j).isoModSerre _).mpr
  rw [quotientCoherentRestriction_fac]
  infer_instance

/-- The actual descended restriction functor preserves finite limits. -/
instance quotientCoherentRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (quotientCoherentRestriction j) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q (finiteTypeSheavesSupportedAway j) _).mp
  rw [quotientCoherentRestriction_fac]
  infer_instance

/-- The actual descended restriction functor preserves finite colimits. -/
instance quotientCoherentRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (quotientCoherentRestriction j) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q (finiteTypeSheavesSupportedAway j) _).mp
  rw [quotientCoherentRestriction_fac]
  infer_instance

/-- Exactness of the genuine quotient-induced geometric functor. -/
def quotientCoherentRestrictionExact :
    ExactFunctor (abelianExactStructure (CoherentSupportQuotient j)) (coherentExactStructure U)
      where
  toFunctor := quotientCoherentRestriction j
  map_conflation _ h := h.map_of_exact _

/-- Two original coherent maps represent the same quotient map precisely
when their actual restrictions agree. -/
theorem coherent_quotient_map_eq_iff {M N : FiniteTypeSheaves X} (f g : M ⟶ N) :
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q.map f =
      (finiteTypeSheavesSupportedAway j).isoModSerre.Q.map g ↔
        (finiteTypeSheavesRestriction j).map f = (finiteTypeSheavesRestriction j).map g := by
  rw [← quotientCoherentRestriction_map_Q j f, ← quotientCoherentRestriction_map_Q j g]
  exact ⟨congrArg _, fun h => (quotientCoherentRestriction j).map_injective h⟩

/-- A coherent map vanishes on the open exactly when its actual coherent
image is supported in the complement. -/
theorem finiteTypeSheavesRestriction_map_eq_zero_iff_image_supported {M N : FiniteTypeSheaves X} (f
  : M ⟶ N) :
    (finiteTypeSheavesRestriction j).map f = 0 ↔
      finiteTypeSheavesSupportedAway j (Abelian.image f) := by
  rw [← (finiteTypeSheavesRestriction j).map_zero M N, ← coherent_quotient_map_eq_iff j f 0]
  rw [Functor.map_zero]
  exact ObjectProperty.SerreClassLocalization.map_eq_zero_iff
    (finiteTypeSheavesSupportedAway j).isoModSerre.Q (finiteTypeSheavesSupportedAway j) f

/-- The vanishing criterion is the ordinary stalk-support condition on the
image sheaf, rather than an abstract replacement for support. -/
theorem finiteTypeSheavesRestriction_map_eq_zero_iff_image_support_subset
    {M N : FiniteTypeSheaves X} (f : M ⟶ N) :
    (finiteTypeSheavesRestriction j).map f = 0 ↔
      AlgebraicGeometry.Scheme.Modules.support (Abelian.image f).obj ⊆ (Set.range j)ᶜ := by
  rw [finiteTypeSheavesRestriction_map_eq_zero_iff_image_supported,
    finiteTypeSheavesSupportedAway_iff_support_subset]

end AlgebraicGeometry.Scheme.Modules.Coherent
