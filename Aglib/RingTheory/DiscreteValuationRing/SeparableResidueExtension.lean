/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.EssentiallyEtale
public import Aglib.RingTheory.Localization.ResiduePoint
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Smooth.Flat

/-! # An actual essentially étale local lift of a finite separable residue extension

A monic lift of the primitive element's minimal polynomial, with its derivative
inverted, gives the standard étale algebra. Localization at the actual residue
point gives the required DVR and the prescribed residue-field equivalence.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace SeparableResidueExtension

variable (R E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field E] [Algebra (ResidueField R) E] [Module.Finite (ResidueField R) E]
  [Algebra.IsSeparable (ResidueField R) E]

/-- The base DVR acts on the specified residue extension through its residue map. -/
local instance residueExtensionBaseAlgebra : Algebra R E :=
  ((algebraMap (ResidueField R) E).comp (residue R)).toAlgebra

local instance : IsScalarTower R (ResidueField R) E :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A primitive element in the specified residue extension. -/
def primitive : E := (Field.exists_primitive_element (ResidueField R) E).choose

/-- The chosen element generates the actual specified field extension. -/
theorem primitive_spec : IntermediateField.adjoin (ResidueField R) {primitive R E} = ⊤ :=
  (Field.exists_primitive_element (ResidueField R) E).choose_spec

theorem exists_monic_lift : ∃ F : R[X],
    F.map (residue R) = minpoly (ResidueField R) (primitive R E) ∧ F.Monic := by
  have hi : IsIntegral (ResidueField R) (primitive R E) :=
    Algebra.IsSeparable.isIntegral _ _
  obtain ⟨F, hF, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := residue R) (p := minpoly (ResidueField R) (primitive R E))
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) _)
    (minpoly.monic hi)
  exact ⟨F, hF, hmonic⟩

/-- A genuine monic polynomial over the original DVR lifting the minimal polynomial. -/
def polynomial : R[X] := (exists_monic_lift R E).choose

theorem polynomial_map :
    (polynomial R E).map (residue R) = minpoly (ResidueField R) (primitive R E) :=
  (exists_monic_lift R E).choose_spec.1

theorem polynomial_monic : (polynomial R E).Monic :=
  (exists_monic_lift R E).choose_spec.2

/-- The standard étale derivative localization is constructed literally. -/
def pair : StandardEtalePair R where
  f := polynomial R E
  monic_f := polynomial_monic R E
  g := (polynomial R E).derivative
  cond := ⟨1, 0, 1, by simp⟩

/-- The finite-presentation étale algebra before selecting the local residue point. -/
abbrev EtaleAlgebra := (pair R E).Ring

theorem aeval_residue_map (F : R[X]) :
    aeval (primitive R E) (F.map (residue R)) = aeval (primitive R E) F := by
  simp only [aeval_def, eval₂_map]
  rfl

/-- The original primitive element is a simple root of the actual lifted polynomial. -/
theorem pair_hasMap : (pair R E).HasMap (primitive R E) := by
  constructor
  · change aeval (primitive R E) (polynomial R E) = 0
    rw [← aeval_residue_map, polynomial_map]
    exact minpoly.aeval _ _
  · apply isUnit_iff_ne_zero.mpr
    change aeval (primitive R E) (polynomial R E).derivative ≠ 0
    rw [← aeval_residue_map, ← derivative_map, polynomial_map]
    exact (Algebra.IsSeparable.isSeparable (ResidueField R)
      (primitive R E)).aeval_derivative_ne_zero (minpoly.aeval _ _)

/-- The chosen point in the specified residue field. -/
def point : EtaleAlgebra R E →ₐ[R] E :=
  (pair R E).lift (primitive R E) (pair_hasMap R E)

@[simp] theorem point_X : point R E (pair R E).X = primitive R E :=
  StandardEtalePair.lift_X _ _ _

/-- Primitive generation makes the actual standard-étale point surjective. -/
theorem point_surjective : Function.Surjective (point R E) := by
  intro x
  have hadjoin : Algebra.adjoin (ResidueField R) {primitive R E} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic (primitive R E)) (primitive_spec R E)
  obtain ⟨G, hG⟩ := Algebra.adjoin_mem_exists_aeval (ResidueField R) (primitive R E)
    (show x ∈ Algebra.adjoin (ResidueField R) {primitive R E} by rw [hadjoin]; trivial)
  obtain ⟨F, rfl⟩ := Polynomial.map_surjective (residue R) residue_surjective G
  refine ⟨aeval (pair R E).X F, ?_⟩
  rw [← aeval_algHom_apply, point_X, ← aeval_residue_map]
  exact hG

/-- The native local ring selected by this actual point. -/
abbrev Ring := Localization.ResiduePoint.Ring (point R E).toRingHom

/-- The original residue point on the actual local ring. -/
def localPoint : Ring R E →ₐ[R] E where
  toRingHom := Localization.ResiduePoint.point (point R E).toRingHom
  commutes' r := by
    change Localization.ResiduePoint.point (point R E).toRingHom
      (algebraMap R (Ring R E) r) = _
    rw [IsScalarTower.algebraMap_apply R (EtaleAlgebra R E) (Ring R E),
      Localization.ResiduePoint.point_algebraMap]
    exact (point R E).commutes r

instance localPoint_isLocalHom : IsLocalHom (localPoint R E).toRingHom :=
  Localization.ResiduePoint.point_isLocalHom _

/-- The original DVR maps locally into the selected local ring. -/
instance algebraMap_isLocalHom : IsLocalHom (algebraMap R (Ring R E)) := by
  refine ⟨fun r hr => ?_⟩
  apply (residue_ne_zero_iff_isUnit r).mp
  intro hz
  have hzero : localPoint R E (algebraMap R (Ring R E) r) = 0 := by
    rw [AlgHom.commutes]
    change algebraMap (ResidueField R) E (residue R r) = 0
    rw [hz, map_zero]
  exact (hr.map (localPoint R E)).ne_zero hzero

instance formallyEtale : Algebra.FormallyEtale R (Ring R E) := inferInstance

instance essFiniteType : Algebra.EssFiniteType R (Ring R E) :=
  Algebra.EssFiniteType.comp R (EtaleAlgebra R E) (Ring R E)

instance flat : Module.Flat R (Ring R E) := inferInstance

/-- The local domain is obtained from the actual essentially étale local map. -/
instance isDomain : IsDomain (Ring R E) :=
  Algebra.FormallyUnramified.isDomain_of_flat_local_dvr R (Ring R E)

/-- The actual selected local ring is a DVR. -/
instance isDiscreteValuationRing : IsDiscreteValuationRing (Ring R E) :=
  Algebra.FormallyUnramified.isDiscreteValuationRing_of_flat_local_dvr R (Ring R E)

/-- Every original uniformizer remains a uniformizer. -/
theorem irreducible_algebraMap {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (Ring R E) π) :=
  Algebra.FormallyUnramified.irreducible_algebraMap_of_flat_local_dvr R (Ring R E) hπ

/-- The actual residue field is exactly the prescribed extension. -/
def residueEquiv : ResidueField (Ring R E) ≃+* E :=
  Localization.ResiduePoint.residueEquiv (point R E).toRingHom (point_surjective R E)

@[simp] theorem residueEquiv_residue (x : Ring R E) :
    residueEquiv R E (residue (Ring R E) x) = localPoint R E x := rfl

/-- The residue equivalence preserves the original residue-field coefficients. -/
def residueAlgEquiv : ResidueField (Ring R E) ≃ₐ[ResidueField R] E where
  __ := residueEquiv R E
  commutes' r := by
    change residueEquiv R E (algebraMap (ResidueField R) (ResidueField (Ring R E)) r) =
      algebraMap (ResidueField R) E r
    obtain ⟨r, rfl⟩ := residue_surjective r
    rw [ResidueField.algebraMap_residue, residueEquiv_residue, AlgHom.commutes]
    rfl

end SeparableResidueExtension
