/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.RingTheory.IntegralClosure.ChangeBaseMap
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The original separable two-field normalization square

The two bases are already normal Noetherian domains. Trace-dual finiteness
supplies their literal integral closures in the two finite separable fields.
The existing change-base map retains the specified common-field embedding.
The square is commutative, not asserted to be cartesian. Lying over concerns
prime ideals, not a lift of an arbitrarily prescribed residue-field point.
This does not construct an initial normal arithmetic model.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.SeparableBaseSquare

universe u

section OneBase

variable (R k F : Type u) [CommRing R] [IsDomain R]
  [Field k] [Field F] [Algebra R k] [IsFractionRing R k]
  [Algebra k F] [Algebra R F] [IsScalarTower R k F]

include k in
omit [IsDomain R] in
/-- The original fraction-field tower makes the closure structural map injective. -/
theorem closure_algebraMap_injective :
    Function.Injective (algebraMap R (integralClosure R F)) := by
  have hi : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R k F]
    exact (algebraMap k F).injective.comp (IsFractionRing.injective R k)
  intro x y h
  apply hi
  exact congrArg (fun z : integralClosure R F => (z : F)) h

include k in
omit [IsDomain R] in
/-- A specified prime has an actual prime above it in the literal closure. -/
theorem exists_closure_prime (q : PrimeSpectrum R) :
    ∃ q' : PrimeSpectrum (integralClosure R F),
      PrimeSpectrum.comap (algebraMap R (integralClosure R F)) q' = q := by
  let : FaithfulSMul R (integralClosure R F) :=
    (faithfulSMul_iff_algebraMap_injective R (integralClosure R F)).mpr
      (closure_algebraMap_injective R k F)
  exact Algebra.IsIntegral.comap_surjective R (integralClosure R F) q

variable [IsNoetherianRing R] [IsIntegrallyClosed R]
  [FiniteDimensional k F] [Algebra.IsSeparable k F]

include k in
/-- The normal model, its exact fraction field, and the actual finite map use
one literal integral closure; no normalization realization is chosen again. -/
theorem normal_finite_model :
    Module.Finite R (integralClosure R F) ∧
      IsNoetherianRing (integralClosure R F) ∧
      IsIntegrallyClosed (integralClosure R F) ∧
      IsFractionRing (integralClosure R F) F ∧
      IsFinite (Spec.algebraMap R (integralClosure R F)) := by
  have hfin : Module.Finite R (integralClosure R F) :=
    IsIntegralClosure.finite R k F _
  exact ⟨hfin, IsIntegralClosure.isNoetherianRing R k F _,
    integralClosure.isIntegrallyClosedOfFiniteExtension k,
    integralClosure.isFractionRing_of_finite_extension k F,
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)⟩

end OneBase

section TwoBases

variable (A B k K F E : Type u) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Field k] [Field K] [Field F] [Field E]
  [Algebra A B] [Algebra A k] [IsFractionRing A k]
  [Algebra B K] [IsFractionRing B K] [Algebra k K] [Algebra A K]
  [IsScalarTower A k K] [IsScalarTower A B K]
  [Algebra k F] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  [Algebra A F] [Algebra A E] [Algebra B E]
  [IsScalarTower A k F] [IsScalarTower A k E]
  [IsScalarTower B K E] [IsScalarTower A B E]

include k K in
omit [IsDomain A] [IsDomain B] [IsFractionRing B K] in
/-- Compatibility with the original fraction fields forces injectivity of the
original base map; it is not silently assumed for an arbitrary base change. -/
theorem base_injective : Function.Injective (algebraMap A B) := by
  have hi : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A k K]
    exact (algebraMap k K).injective.comp (IsFractionRing.injective A k)
  intro x y h
  apply hi
  simpa only [IsScalarTower.algebraMap_apply A B K] using
    congrArg (algebraMap B K) h

variable (a : F →ₐ[k] E)

/-- The existing closure constructor, with the original common-field map. -/
abbrev closureMap : integralClosure A F →ₐ[A] integralClosure B E :=
  integralClosure.changeBaseMap A B F E (a.restrictScalars A)

omit [IsDomain A] [IsDomain B] [IsFractionRing A k] in
/-- The exact generic element is retained, not transported through a new field. -/
@[simp] theorem closureMap_coe (x : integralClosure A F) :
    (closureMap A B k F E a x : E) = a (x : F) := rfl

omit [IsDomain A] [IsDomain B] [IsFractionRing A k] in
/-- The two finite vertical maps commute with the original base map. -/
@[reassoc] theorem spec_square :
    Spec.map (CommRingCat.ofHom (closureMap A B k F E a).toRingHom) ≫
        Spec.algebraMap A (integralClosure A F) =
      Spec.algebraMap B (integralClosure B E) ≫ Spec.algebraMap A B := by
  rw [Spec.map_algHom_algebraMap]
  simp only [Spec.algebraMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (IsScalarTower.algebraMap_eq A B (integralClosure B E)))

omit [IsDomain A] [IsDomain B] [IsFractionRing A k] in
/-- The generic triangle is the actual embedding supplied by two-field
refinement, on the literal ambient fields and literal closure inclusions. -/
@[reassoc] theorem generic_square :
    Spec.algebraMap (integralClosure B E) E ≫
        Spec.map (CommRingCat.ofHom (closureMap A B k F E a).toRingHom) =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        Spec.algebraMap (integralClosure A F) F := by
  simp only [Spec.algebraMap, ← Spec.map_comp]
  rfl

include K in
omit [IsDomain A] [IsDomain B] [IsFractionRing A k]
  [Algebra k K] [Algebra A K] [IsScalarTower A k K]
  [IsScalarTower A B K] [IsScalarTower k K E] in
/-- A coefficient prime lifts to its normalization. Its image on the other
normalization has exactly the original base prime as contraction. This is not
a choice of a rational lift over a prescribed geometric field. -/
theorem exists_coefficient_prime (q : PrimeSpectrum B) :
    ∃ q' : PrimeSpectrum (integralClosure B E),
      PrimeSpectrum.comap (algebraMap B (integralClosure B E)) q' = q ∧
      PrimeSpectrum.comap (algebraMap A (integralClosure A F))
          (PrimeSpectrum.comap (closureMap A B k F E a).toRingHom q') =
        PrimeSpectrum.comap (algebraMap A B) q := by
  obtain ⟨q', hq⟩ := exists_closure_prime B K E q
  refine ⟨q', hq, ?_⟩
  have hmap : (closureMap A B k F E a).toRingHom.comp
      (algebraMap A (integralClosure A F)) = algebraMap A (integralClosure B E) :=
    (closureMap A B k F E a).comp_algebraMap
  calc
    _ = PrimeSpectrum.comap (algebraMap A (integralClosure B E)) q' :=
      congrArg (fun f : A →+* integralClosure B E => PrimeSpectrum.comap f q') hmap
    _ = PrimeSpectrum.comap (algebraMap A B) q := by
      rw [IsScalarTower.algebraMap_eq A B (integralClosure B E),
        PrimeSpectrum.comap_comp_apply, hq]

end TwoBases

end AlgebraicGeometry.Scheme.SeparableBaseSquare
