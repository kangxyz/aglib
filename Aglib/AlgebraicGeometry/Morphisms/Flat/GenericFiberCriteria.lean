/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericSection
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Flat descent over Dedekind bases and actual generic-fibre criteria

Flatness descends through injective ring maps over a Dedekind domain and through
pointwise flat source charts. For a flat locally finitely presented scheme over
a domain, the actual generic projection is dominant and generic integrality
implies integrality when the source is reduced. Reduced generic fibre implies
reduced source under flatness alone. All generic fibres use the supplied actual
fraction-field map; no DVR regularity or purity conclusion is asserted.
-/

@[expose] public section




open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section DVRFlatSourceDescent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Flat

/-- Over a Dedekind domain, flatness descends along an injective ring homomorphism. -/
lemma ringHom_flat_of_injective_comp {R A B : Type*}
    [CommRing R] [IsDedekindDomain R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hg : Function.Injective g)
    (hcomp : (g.comp f).Flat) : f.Flat := by
  algebraize [f, g, g.comp f]
  letI : Module.IsTorsionFree R A :=
    Function.Injective.moduleIsTorsionFree (R := R) g hg (by
      intro r a
      simp only [Algebra.smul_def, map_mul]
      rfl)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The actual stalk map of a flat scheme morphism is injective. -/
lemma flat_stalkMap_injective {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g] (y : Y) :
    Function.Injective (g.stalkMap y).hom := by
  algebraize [(g.stalkMap y).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g y) (g.toLRSHom.prop y)
  exact ‹RingHom.FaithfullyFlat _›.injective

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Flatness of a composite with a flat chart gives flatness at every point in that chart. -/
lemma stalkMap_flat_of_flat_chart {Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g] [Flat (g ≫ f)] (y : Y) : (f.stalkMap (g y)).hom.Flat := by
  let A := (Spec (.of R)).presheaf.stalk (f (g y))
  letI : (f (g y)).asIdeal.IsPrime := (f (g y)).isPrime
  letI : Algebra R A := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).presheaf.stalk (f (g y))))
  letI : IsLocalization.AtPrime A (f (g y)).asIdeal := inferInstanceAs
    (IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk (f (g y)))
      (f (g y)).asIdeal)
  letI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A
    (f (g y)).asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsDedekindDomain A :=
    IsLocalization.AtPrime.isDedekindDomain R (f (g y)).asIdeal A
  apply ringHom_flat_of_injective_comp (f.stalkMap (g y)).hom (g.stalkMap y).hom
    (flat_stalkMap_injective g y)
  have h := Flat.stalkMap (g ≫ f) y
  simpa only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] using h

/-- An actual pointwise family of flat charts with flat structural composites proves flatness.
No reducedness, integrality, dominance, or quasi-compactness of the source is assumed. -/
lemma flat_of_pointwise_flat_cover
    (hcover : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (y : Y),
      g y = x ∧ Flat g ∧ Flat (g ≫ f)) : Flat f := by
  apply Flat.of_stalkMap
  intro x
  obtain ⟨Y, g, y, rfl, hg, hgf⟩ := hcover x
  let := hg
  let := hgf
  exact stalkMap_flat_of_flat_chart f g y

/-- Flatness descends from an actual flat surjective source morphism over a Dedekind base. -/
lemma flat_of_flat_surjective {Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g] [Surjective g] [Flat (g ≫ f)] : Flat f := by
  apply flat_of_pointwise_flat_cover f
  intro x
  obtain ⟨y, hy⟩ := g.surjective x
  exact ⟨Y, g, y, hy, inferInstance, inferInstance⟩

end AlgebraicGeometry.Flat

end
end DVRFlatSourceDescent

section FlatGenericDensity


noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber

lemma pullback_fst_dominant {X Y T : Scheme.{u}} (f : X ⟶ Y) (j : T ⟶ Y)
    [IsDominant j] (hf : IsOpenMap f) : IsDominant (pullback.fst f j) := by
  constructor
  change Dense (Set.range (pullback.fst f j))
  rw [Scheme.Pullback.range_fst]
  exact j.denseRange.preimage hf

lemma integral_of_dense_integral_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsDominant f] [IsReduced Y] : IsIntegral Y := by
  have hi : IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
  let : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr (by
    change IsIrreducible (Set.univ : Set Y)
    rw [← f.denseRange.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

variable (R F : Type u) [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

lemma fraction_base_dominant : IsDominant (baseMap R F) := by
  constructor
  change Dense (Set.range (baseMap R F))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec (Spec (.of R)))]
  apply closure_mono
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨IsLocalRing.closedPoint F,
    baseMap_closedPoint_eq_genericPoint R F⟩

variable {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
  [Flat π] [LocallyOfFinitePresentation π]

lemma generic_projection_dominant : IsDominant
    (pullback.fst π (baseMap R F)) := by
  let := fraction_base_dominant R F
  exact pullback_fst_dominant π _ π.isOpenMap

lemma integral_of_reduced_integral_generic [IsReduced X]
    [IsIntegral (pullback π (baseMap R F))] :
    IsIntegral X := by
  let := generic_projection_dominant R F π
  exact integral_of_dense_integral_source (pullback.fst π
    (baseMap R F))

end AlgebraicGeometry.Scheme.LocalRing.GenericFiber

end
end FlatGenericDensity

section FlatGenericReducedness


/-! Reducedness descends from the actual generic fibre of a flat scheme over
a domain. Scheme-theoretic dominance is obtained by the native flat base-change
instance, and its actual injective section maps give the descent. -/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.LocalRing.GenericFiber
variable (R F : Type u) [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f]

lemma generic_projection_schemeTheoreticallyDominant : IsSchemeTheoreticallyDominant
    (pullback.fst f (baseMap R F)) := by
  let := fraction_base_dominant R F
  let := IsSchemeTheoreticallyDominant.of_isDominant
    (baseMap R F)
  infer_instance

lemma reduced_of_reduced_generic
    [IsReduced (pullback f (baseMap R F))] : IsReduced X := by
  let := generic_projection_schemeTheoreticallyDominant R F f
  exact IsSchemeTheoreticallyDominant.isReduced
    (pullback.fst f (baseMap R F))

end AlgebraicGeometry.Scheme.LocalRing.GenericFiber

end
end FlatGenericReducedness

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Flat/GenericFiberCriteria.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 9a0e23f628aed3061cb8dd507abb1309ed484627b326b5791a07e18a836bf190. -/
