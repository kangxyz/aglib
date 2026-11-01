/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteDecomposition
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The original selected local factor over a Henselian base

The spectrum of the localization at a specified maximal ideal of a finite
algebra is an open-and-closed subscheme, with the original localization map.
Its closed point maps to the specified prime. No normalization, connected
generic-fibre, or Galois hypothesis is built into this construction.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Spec

universe u v

variable (R : Type v) [CommRing R] [HenselianLocalRing R]
  (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A]
  (q : Ideal A) [q.IsMaximal]

include R in
/-- The original selected-factor inclusion is an open immersion. -/
theorem isOpenImmersion_localizationAtPrime_of_finite_henselian :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.AtPrime q)))) := by
  obtain ⟨e, he, heq, hi⟩ := HenselianLocalRing.exists_idempotent_isolating_maximal R A q
  let E := IsLocalization.quotientEquivAtPrimeOfIsolatingIdempotent q e he heq hi
  have h : algebraMap A (Localization.AtPrime q) =
      E.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {1 - e})) := by
    ext a
    exact (E.commutes a).symm
  apply (isOpenImmersion_SpecMap_iff_of_surjective _
    (HenselianLocalRing.algebraMap_localizationAtPrime_surjective R A q)).mpr
  refine ⟨1 - e, he.one_sub, ?_⟩
  change RingHom.ker (algebraMap A (Localization.AtPrime q)) = Ideal.span {1 - e}
  rw [h]
  exact (RingHom.ker_comp_of_injective
    (Ideal.Quotient.mk (Ideal.span {1 - e}))
    (f := E.toRingHom) E.injective).trans Ideal.mk_ker

include R in
/-- The same original selected-factor inclusion is a closed immersion. -/
theorem isClosedImmersion_localizationAtPrime_of_finite_henselian :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.AtPrime q)))) :=
  IsClosedImmersion.spec_of_surjective _
    (HenselianLocalRing.algebraMap_localizationAtPrime_surjective R A q)

omit [q.IsMaximal] in
/-- The original localization map sends its closed point to the specified prime.
This point equation needs neither finiteness nor a Henselian base. -/
theorem map_localizationAtPrime_closedPoint [q.IsPrime] :
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime q)))
      (IsLocalRing.closedPoint (Localization.AtPrime q)) = ⟨q, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.under_maximalIdeal

end AlgebraicGeometry.Spec
