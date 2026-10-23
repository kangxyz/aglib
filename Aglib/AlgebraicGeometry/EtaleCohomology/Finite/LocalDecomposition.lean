/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteDecomposition
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Actual local components of a finite scheme over a Henselian ring

The coproduct of spectra of the maximal localizations maps isomorphically to
the original affine finite scheme. Every component map is the actual spectrum
map of its localization homomorphism, not an unspecified component isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u v

variable (A : Type v) [CommRing A]

/-- The family of actual maximal-localization spectra. -/
abbrev localComponents (p : MaximalSpectrum A) : Scheme :=
  Spec (.of (Localization.AtPrime p.asIdeal))

/-- The literal localization map on spectra. -/
def localComponentInclusion (p : MaximalSpectrum A) : localComponents A p ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal)))

/-- The map from all maximal-localization components, with the literal
localization maps as its coproduct restrictions. -/
def localDecompositionMap : (∐ localComponents A) ⟶ Spec (.of A) :=
  Sigma.desc (localComponentInclusion A)

@[reassoc (attr := simp)]
lemma ι_localDecompositionMap (p : MaximalSpectrum A) :
    Sigma.ι (localComponents A) p ≫ localDecompositionMap A =
      localComponentInclusion A p :=
  Sigma.ι_comp_desc _ _

/-- The actual decomposition map factors through the native spectrum/product
comparison and the canonical algebra-to-localizations map. -/
lemma localDecompositionMap_eq_sigmaSpec :
    localDecompositionMap A =
      sigmaSpec (fun p : MaximalSpectrum A => .of (Localization.AtPrime p.asIdeal)) ≫
        Spec.map (CommRingCat.ofHom (MaximalSpectrum.toPiLocalization A).toRingHom) := by
  apply Sigma.hom_ext
  intro p
  rw [ι_localDecompositionMap, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  rfl

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [Algebra R A] [Module.Finite R A]

include R in
/-- A finite algebra over a Henselian local base is the actual finite coproduct
of its maximal local spectra. -/
theorem localDecompositionMap_isIso : IsIso (localDecompositionMap A) := by
  let : Finite (MaximalSpectrum A) := Module.finiteAlgebra_maximalSpectrum_finite R A
  have : IsIso (CommRingCat.ofHom (MaximalSpectrum.toPiLocalization A).toRingHom) :=
    (HenselianLocalRing.finiteAlgebraLocalDecomposition R A).toRingEquiv.toCommRingCatIso.isIso_hom
  rw [localDecompositionMap_eq_sigmaSpec]
  infer_instance

/-- The decomposition isomorphism retains the canonical map from the actual
localization components as its forward map. -/
def localDecompositionIso : (∐ localComponents A) ≅ Spec (.of A) := by
  let := localDecompositionMap_isIso A R
  exact asIso (localDecompositionMap A)

@[simp]
lemma localDecompositionIso_hom : (localDecompositionIso A R).hom = localDecompositionMap A := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
