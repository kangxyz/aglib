/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Basic for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `Basic.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ab7b93ceded9a3d61b221289e570e9b6c13419aa59dc114fdc1eaab46fc7d7d8`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R]

/-- The actual affine rank-two Laurent torus. -/
def torusScheme (R : Type u) [CommRing R] : Scheme := Spec (.of (Laurent R))

/-- The structure map of the split two-dimensional torus to the coefficient spectrum. -/
def torusStructure (R : Type u) [CommRing R] : torusScheme R ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Laurent R)))

/-- The integral closed subscheme Spec(Laurent R / p) for a literal label p. -/
def pointScheme (p : FiniteDominantPrime R) : Scheme := Spec (.of (Laurent R ⧸ p.val))

/-- The closed immersion of the prime quotient labeled by `p` into the torus. -/
def pointImmersion (p : FiniteDominantPrime R) : pointScheme p ⟶ torusScheme R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.val))

/-- Its structural map is the actual finite algebra map from the base. -/
def pointStructure (p : FiniteDominantPrime R) : pointScheme p ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Laurent R ⧸ p.val)))

/-- The scheme defined by a finite dominant prime label is integral. -/
instance pointScheme_isIntegral (p : FiniteDominantPrime R) : IsIntegral (pointScheme p) := by
  dsimp [pointScheme]
  infer_instance

/-- The prime-quotient map into the torus is a closed immersion. -/
instance pointImmersion_isClosedImmersion (p : FiniteDominantPrime R) :
    IsClosedImmersion (pointImmersion p) := by
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The scheme defined by a finite dominant prime label is finite over the base. -/
instance pointStructure_isFinite (p : FiniteDominantPrime R) : IsFinite (pointStructure p) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The ambient torus embedding and the base projection commute literally. -/
theorem pointImmersion_structure (p : FiniteDominantPrime R) :
    pointImmersion p ≫ torusStructure R = pointStructure p := by
  rw [pointImmersion, torusStructure, ← Spec.map_comp]
  rfl

/-- Dominance of the prime label is exactly injectivity of the structural map
on coordinate rings. -/
theorem point_algebraMap_injective (p : FiniteDominantPrime R) :
    Function.Injective (algebraMap R (Laurent R ⧸ p.val)) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  ext r
  change Ideal.Quotient.mk p.val (algebraMap R (Laurent R) r) = 0 ↔ r = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change r ∈ p.val.under R ↔ r = 0
  rw [MonoidAlgebra.FiniteDominantPrime.under_eq_bot]
  rfl

/-- Finite dominance gives actual surjectivity over the base by lying over. -/
instance pointStructure_surjective (p : FiniteDominantPrime R) : Surjective (pointStructure p) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap R (Laurent R ⧸ p.val)))
  exact (algebraMap_isIntegral_iff.mpr inferInstance).comap_surjective
    (point_algebraMap_injective p)

/-- The scheme defined by a finite dominant prime label is dominant over the base. -/
instance pointStructure_isDominant (p : FiniteDominantPrime R) : IsDominant (pointStructure p) :=
  inferInstance

end AlgebraicGeometry.Torus.FiniteCorrespondence
