/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkBaseChange

/-!
# Etale neighborhoods from formally etale stalk maps

For a locally finitely presented scheme morphism, formal etaleness of its
actual local-ring map produces an open source neighborhood on which the
morphism is etale. The stalk-base-change criterion applies this result to
the actual canonical base-change maps.

Extraction source: `R5Lab.AlgebraicGeometry.LocalRing.EtaleLocus`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.LocalRing.Etale

universe u

/-- For a locally finitely presented morphism, formal etaleness of the actual
local ring map gives an actual source neighborhood on which the map is etale. -/
theorem exists_etale_neighborhood_of_stalkMap_formallyEtale
    {Z X : Scheme.{u}} (f : Z ⟶ X) [LocallyOfFinitePresentation f] (z : Z)
    (h : (f.stalkMap z).hom.FormallyEtale) :
    ∃ W : Z.Opens, z ∈ W ∧ Etale (W.ι ≫ f) := by
  obtain ⟨U, hU, hfz, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (f z))
  obtain ⟨V, hV, hz, hVU⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show z ∈ f ⁻¹ᵁ U from hfz)
  let A := Γ(X, U)
  let B := Γ(Z, V)
  let φ := f.appLE U V hVU
  let p := (hU.primeIdealOf ⟨f z, hVU hz⟩).asIdeal
  let q := (hV.primeIdealOf ⟨z, hz⟩).asIdeal
  haveI : p.IsPrime := (hU.primeIdealOf ⟨f z, hVU hz⟩).isPrime
  haveI : q.IsPrime := (hV.primeIdealOf ⟨z, hz⟩).isPrime
  have hpq : p = q.comap φ.hom :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hz).symm
  have hl : (Localization.localRingHom p q φ.hom hpq).FormallyEtale :=
    (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hz)).mp h
  letI : Algebra A B := φ.hom.toAlgebra
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q φ.hom hpq).toAlgebra
  haveI : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun a => (Localization.localRingHom_to_map p q φ.hom hpq a).symm
  haveI : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) := hl
  haveI : Algebra.FormallyEtale A (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  haveI : Algebra.IsEtaleAt A q :=
    Algebra.FormallyEtale.comp A (Localization.AtPrime p) (Localization.AtPrime q)
  haveI : Algebra.FinitePresentation A B := f.finitePresentation_appLE hU hV hVU
  obtain ⟨b, hb, hBb⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) q
  letI := hBb
  let ℓ : Spec (.of (Localization.Away b)) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫ hV.fromSpec
  haveI : IsOpenImmersion ℓ := by dsimp [ℓ]; infer_instance
  have hℓ : ℓ ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))) ≫ hU.fromSpec := by
    dsimp [ℓ]
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
  haveI : Etale (ℓ ≫ f) := by
    rw [hℓ]
    haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hBb)
    infer_instance
  have hzℓ : z ∈ ℓ.opensRange := by
    change z ∈ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫
      hV.fromSpec).opensRange
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway]
    exact ⟨hV.primeIdealOf ⟨z, hz⟩, hb, hV.fromSpec_primeIdealOf ⟨z, hz⟩⟩
  let e := IsOpenImmersion.isoOfRangeEq ℓ ℓ.opensRange.ι (by simp)
  refine ⟨ℓ.opensRange, hzℓ, ?_⟩
  apply (MorphismProperty.cancel_left_of_respectsIso @Etale e.hom (ℓ.opensRange.ι ≫ f)).mp
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  infer_instance

/-- Target-stalk base change detects an etale source neighborhood under the
original explicit local finite-presentation condition. -/
theorem exists_etale_neighborhood_of_etale_stalkBaseChange
    {Z X : Scheme.{u}} (f : Z ⟶ X) [LocallyOfFinitePresentation f] (z : Z)
    (h : Etale (Limits.pullback.snd f (X.fromSpecStalk (f z)))) :
    ∃ W : Z.Opens, z ∈ W ∧ Etale (W.ι ≫ f) :=
  exists_etale_neighborhood_of_stalkMap_formallyEtale f z
    (stalkMap_formallyEtale_of_etale_stalkBaseChange f z h)

end AlgebraicGeometry.Scheme.LocalRing.Etale
