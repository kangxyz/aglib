/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The original spectrum diagram of a split nilpotent quotient

A surjective original algebra quotient with nilpotent kernel defines an
actual surjective closed immersion. Its finite product target is finite
étale over the original coefficient ring, and the original algebra-map law
proves the structural triangle. The empty product is included; the product
projection itself is not asserted surjective.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.SplitThickening

universe u

/-- The original spectrum of a surjective map with nilpotent kernel is
surjective, without assuming the original source ring is reduced. -/
theorem specMap_surjective_of_ker_pow_eq_bot
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    (hq : Function.Surjective q) (n : ℕ) (hn : (RingHom.ker q) ^ n = ⊥) :
    Surjective (Spec.map (CommRingCat.ofHom q)) := by
  have hker : RingHom.ker q ≤ _root_.nilradical A := by
    intro x hx
    apply _root_.mem_nilradical.mpr
    refine ⟨n, ?_⟩
    have hpow := Ideal.pow_mem_pow hx n
    rw [hn] at hpow
    exact hpow
  have hhomeo := PrimeSpectrum.isHomeomorph_comap q (fun x => by
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    obtain ⟨y, hy⟩ := hq x
    exact ⟨y, hy.trans (pow_one x).symm⟩) hker
  exact ⟨hhomeo.surjective⟩

section Product

variable (C : Type u) [CommRing C] (J : Type u) [Finite J]

/-- The original finite product projection is finite, including an empty product. -/
theorem splitProduct_isFinite : IsFinite (Spec.algebraMap C (J → C)) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The original finite product projection is étale, including an empty product. -/
theorem splitProduct_etale : Etale (Spec.algebraMap C (J → C)) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

end Product

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
  {A : Type u} [CommRing A] [Algebra R A] {J : Type u}

/-- The quotient and product projection fit the original structural triangle. -/
theorem spec_splitQuotient_triangle (q : C ⊗[R] A →ₐ[C] (J → C)) :
    Spec.map (CommRingCat.ofHom q.toRingHom) ≫ Spec.algebraMap C (C ⊗[R] A) =
      Spec.algebraMap C (J → C) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext c j
  exact congrFun (q.commutes c) j

/-- The actual split quotient gives a surjective closed immersion followed by
the original finite étale product projection, with the original triangle. -/
theorem spec_splitQuotient [Finite J] (q : C ⊗[R] A →ₐ[C] (J → C))
    (hq : Function.Surjective q) (n : ℕ) (hn : (RingHom.ker q.toRingHom) ^ n = ⊥) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom q.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom q.toRingHom)) ∧
      IsFinite (Spec.algebraMap C (J → C)) ∧ Etale (Spec.algebraMap C (J → C)) ∧
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ Spec.algebraMap C (C ⊗[R] A) =
        Spec.algebraMap C (J → C) :=
  ⟨IsClosedImmersion.spec_of_surjective _ hq,
    specMap_surjective_of_ker_pow_eq_bot q.toRingHom hq n hn,
    splitProduct_isFinite C J, splitProduct_etale C J, spec_splitQuotient_triangle q⟩

end AlgebraicGeometry.Scheme.FiniteEtale.SplitThickening
