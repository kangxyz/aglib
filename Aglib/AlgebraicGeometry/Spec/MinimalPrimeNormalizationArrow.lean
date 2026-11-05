/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.MinimalPrimeNormalizationArrow
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # The finite two-axis family of an arbitrary Nagata arrow

The native coproduct contains every original minimal-prime coefficient
normalization and its actual kernel-normalized source. The source map is
finite, the coefficient map is finite and surjective, and the map between
the two coproducts retains the original ring-map square componentwise.
The square is only commuting; no Cartesian normalization or surjectivity
onto the square's pullback is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.MinimalPrimeNormalizationArrow

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The original finite source map on one literal component. -/
def sourceComponentMap (p : minimalPrimes B) :
    Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (RingHom.MinimalPrimeNormalization.sourceMap f p))

/-- The original coefficient normalization map, including its quotient map. -/
def coefficientComponentMap (p : minimalPrimes B) :
    Spec (.of (Algebra.minimalPrimeNormalization B p)) ⟶ Spec (.of B) :=
  Spec.algebraMap B (Algebra.minimalPrimeNormalization B p)

/-- The original injective normal-ring arrow, on spectra. -/
def normalComponentMap (p : minimalPrimes B) :
    Spec (.of (Algebra.minimalPrimeNormalization B p)) ⟶
      Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p)) :=
  Spec.map (CommRingCat.ofHom (RingHom.MinimalPrimeNormalization.componentMap f p))

@[reassoc]
theorem component_square (p : minimalPrimes B) :
    normalComponentMap f p ≫ sourceComponentMap f p =
      coefficientComponentMap p ≫ Spec.map (CommRingCat.ofHom f) := by
  change Spec.map (CommRingCat.ofHom (RingHom.MinimalPrimeNormalization.componentMap f p)) ≫
      Spec.map (CommRingCat.ofHom (RingHom.MinimalPrimeNormalization.sourceMap f p)) =
    Spec.map (CommRingCat.ofHom
      (algebraMap B (Algebra.minimalPrimeNormalization B p))) ≫
        Spec.map (CommRingCat.ofHom f)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.MinimalPrimeNormalization.componentMap_sourceMap f p)

/-- Every original kernel-normalized source is retained in the finite source family. -/
def sourceCover :
    (∐ fun p : minimalPrimes B =>
      Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p))) ⟶ Spec (.of A) :=
  Sigma.desc (sourceComponentMap f)

/-- The whole native coefficient cover, indexed by all original minimal primes. -/
def coefficientCover :
    (∐ fun p : minimalPrimes B => Spec (.of (Algebra.minimalPrimeNormalization B p))) ⟶
      Spec (.of B) :=
  Sigma.desc coefficientComponentMap

/-- The original normal arrows assembled without reindexing the components. -/
def normalMap :
    (∐ fun p : minimalPrimes B => Spec (.of (Algebra.minimalPrimeNormalization B p))) ⟶
      (∐ fun p : minimalPrimes B =>
        Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p))) :=
  Sigma.desc fun p => normalComponentMap f p ≫
    Sigma.ι (fun p : minimalPrimes B =>
      Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p))) p

@[reassoc (attr := simp)]
theorem sourceCover_component (p : minimalPrimes B) :
    Sigma.ι (fun p : minimalPrimes B =>
      Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p))) p ≫ sourceCover f =
        sourceComponentMap f p :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem coefficientCover_component (p : minimalPrimes B) :
    Sigma.ι (fun p : minimalPrimes B => Spec (.of (Algebra.minimalPrimeNormalization B p))) p ≫
      coefficientCover (B := B) = coefficientComponentMap p :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem normalMap_component (p : minimalPrimes B) :
    Sigma.ι (fun p : minimalPrimes B => Spec (.of (Algebra.minimalPrimeNormalization B p))) p ≫
      normalMap f = normalComponentMap f p ≫
        Sigma.ι (fun p : minimalPrimes B =>
          Spec (.of (RingHom.MinimalPrimeNormalization.sourceComponent f p))) p :=
  Sigma.ι_comp_desc _ _

/-- The whole family keeps the original arrow exactly. -/
@[reassoc]
theorem normalMap_square :
    normalMap f ≫ sourceCover f =
      coefficientCover (B := B) ≫ Spec.map (CommRingCat.ofHom f) := by
  apply Sigma.hom_ext
  intro p
  simp only [normalMap_component_assoc, sourceCover_component,
    coefficientCover_component_assoc]
  exact component_square f p

/-- Source Nagata and coefficient Noetherianity prove the actual finite
source coproduct map, without an assumed finite normalization. -/
theorem sourceCover_isFinite (hA : IsNagataRing.{u, 0} A)
    (hB : IsNagataRing.{u, 0} B) : IsFinite (sourceCover f) := by
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := B)).fintype
  let : ∀ p : minimalPrimes B, IsFinite (sourceComponentMap f p) := fun p =>
    (IsFinite.SpecMap_iff _).mpr (RingHom.MinimalPrimeNormalization.sourceMap_finite f hA p)
  exact AlgebraicGeometry.isFinite_sigmaDesc _ (sourceComponentMap f)

/-- The original coefficient Nagata hypothesis proves finiteness of its
whole native coefficient coproduct map. -/
theorem coefficientCover_isFinite (hB : IsNagataRing.{u, 0} B) :
    IsFinite (coefficientCover (B := B)) := by
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := B)).fintype
  let : ∀ p : minimalPrimes B, IsFinite (coefficientComponentMap p) := fun p =>
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr
      (Algebra.minimalPrimeNormalization_properties B hB p).1)
  exact AlgebraicGeometry.isFinite_sigmaDesc _ coefficientComponentMap

/-- The actual coefficient coproduct covers every original point, including
nilpotent and reducible coefficient rings. -/
theorem coefficientCover_surjective (hB : IsNagataRing.{u, 0} B) :
    Surjective (coefficientCover (B := B)) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  apply Set.eq_univ_iff_forall.mpr
  intro q
  obtain ⟨p, z, hz⟩ :=
    RingHom.MinimalPrimeNormalization.exists_coefficientComponent_prime_over hB q
  exact Set.mem_iUnion.mpr ⟨p, z, hz⟩

end AlgebraicGeometry.Scheme.MinimalPrimeNormalizationArrow
