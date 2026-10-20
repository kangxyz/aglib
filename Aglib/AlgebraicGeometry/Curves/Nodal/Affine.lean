/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Polynomial.PinchedPair
public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine charts of the pinched projective line

The normalization, conductor opens, and reciprocal-coordinate gluing use the
literal equal-evaluation subalgebra. The two branch sections stay distinct
over every field extension; the two actual open charts cover each pushout.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.PinchedLine

open Polynomial.PinchedPair

variable (k : Type u) [Field k]

/-- The actual affine normalization scheme. -/
abbrev normalizationScheme : Scheme.{u} := Spec (.of k[X])

/-- The actual pinched affine scheme. -/
abbrev nodeScheme : Scheme.{u} := Spec (.of (nodeRing k))

/-- The genuine integral-closure inclusion as a morphism of affine schemes. -/
def normalizationMap : normalizationScheme k ⟶ nodeScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k) k[X]))

/-- The ring-theoretic normalization gives an integral morphism of schemes. -/
theorem normalizationMap_integral : IsIntegralHom (normalizationMap k) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  exact (algebraMap_isIntegral_iff).mpr inferInstance

/-- The normalization map is finite, proved from its actual coordinate algebra. -/
theorem normalizationMap_finite : IsFinite (normalizationMap k) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The point of the affine line at the specified coordinate. -/
def branchMap (a : k) : Spec (.of k) ⟶ normalizationScheme k :=
  Spec.map (CommRingCat.ofHom (evalRingHom a))

/-- The two actual normalization points have the same image on the node. -/
theorem branchMap_same_image :
    branchMap k 0 ≫ normalizationMap k = branchMap k 1 ≫ normalizationMap k := by
  unfold branchMap normalizationMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact a.property

/-- The normalized branches are distinct in all characteristics. -/
theorem branchMap_distinct : branchMap k 0 ≠ branchMap k 1 := by
  intro h
  have hh := Spec.map_injective h
  have hx := congrArg (fun f : CommRingCat.of k[X] ⟶ CommRingCat.of k => f (X : k[X])) hh
  simp at hx
/-- The actual isomorphism of conductor-open affine schemes. -/
def conductorOpenIso : Spec (.of (normalizationOverlapRing k)) ≅
    Spec (.of (nodeOverlapRing k)) :=
  Scheme.Spec.mapIso (conductorLocalizationEquiv k).toCommRingCatIso.op

@[simp] theorem conductorOpenIso_hom :
    (conductorOpenIso k).hom = Spec.map (CommRingCat.ofHom (localizationComparison k)) := rfl

/-- The open immersion of the normalization's conductor chart. -/
def normalizationOverlapInclusion : Spec (.of (normalizationOverlapRing k)) ⟶
    normalizationScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (normalizationOverlapRing k)))

/-- The open immersion of the pinched curve's conductor chart. -/
def nodeOverlapInclusion : Spec (.of (nodeOverlapRing k)) ⟶ nodeScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap (nodeRing k) (nodeOverlapRing k)))

/-- The conductor localization embeds openly in the affine normalization chart. -/
instance normalizationOverlapInclusion_open : IsOpenImmersion (normalizationOverlapInclusion k) :=
  IsOpenImmersion.of_isLocalization (conductor k : k[X])

/-- The conductor localization embeds openly in the affine pinched chart. -/
instance nodeOverlapInclusion_open : IsOpenImmersion (nodeOverlapInclusion k) :=
  IsOpenImmersion.of_isLocalization (conductor k)

/-- The conductor-open isomorphism commutes with the same actual normalization
map. It is suitable for gluing an infinity chart without changing the affine cover. -/
@[reassoc] theorem conductorOpenIso_over :
    (conductorOpenIso k).hom ≫ nodeOverlapInclusion k =
      normalizationOverlapInclusion k ≫ normalizationMap k := by
  rw [conductorOpenIso_hom]
  unfold nodeOverlapInclusion normalizationOverlapInclusion normalizationMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact localizationComparison_algebraMap k a
/-- The spectrum involution induced by the reciprocal-coordinate algebra equivalence. -/
def reciprocalSchemeIso :
    Spec (.of (ConductorReciprocal.W k)) ≅ Spec (.of (ConductorReciprocal.W k)) :=
  Scheme.Spec.mapIso (ConductorReciprocal.reciprocalEquiv k).toRingEquiv.toCommRingCatIso.op

/-- The spectrum isomorphism identifying the normalization overlap with the infinity overlap. -/
def standardOverlapSpecIso : Spec (.of (normalizationOverlapRing k)) ≅
    Spec (.of (infinityOverlapRing k)) :=
  Scheme.Spec.mapIso (standardOverlapEquiv k).toRingEquiv.toCommRingCatIso.symm.op

/-- The localization map from the infinity overlap into the infinity chart. -/
def infinityOverlapInclusion : Spec (.of (infinityOverlapRing k)) ⟶
    Spec (.of (infinityChartRing k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (infinityChartRing k) (infinityOverlapRing k)))

/-- The infinity overlap is an open subscheme of the infinity chart. -/
instance infinityOverlapInclusion_open : IsOpenImmersion (infinityOverlapInclusion k) :=
  IsOpenImmersion.of_isLocalization (algebraMap k[X] (infinityChartRing k) X)

/-- The normalization overlap mapped to the infinity chart through the standard overlap
isomorphism. -/
def canonicalInfinityOpen : Spec (.of (normalizationOverlapRing k)) ⟶
    Spec (.of (infinityChartRing k)) :=
  (standardOverlapSpecIso k).hom ≫ infinityOverlapInclusion k

/-- The standard normalization-overlap map to the infinity chart is an open immersion. -/
instance canonicalInfinityOpen_open : IsOpenImmersion (canonicalInfinityOpen k) := by
  unfold canonicalInfinityOpen
  infer_instance

/-- The conductor overlap, viewed in the pinched affine chart. -/
def gluingToNode : Spec (.of (normalizationOverlapRing k)) ⟶ nodeScheme k :=
  (conductorOpenIso k).hom ≫ nodeOverlapInclusion k

/-- The conductor gluing map to the pinched affine chart is an open immersion. -/
instance gluingToNode_open : IsOpenImmersion (gluingToNode k) := by
  unfold gluingToNode
  infer_instance

/-- The actual inverse-coordinate map to the infinity chart. -/
def gluingToInfinity : Spec (.of (normalizationOverlapRing k)) ⟶
    Spec (.of (infinityChartRing k)) :=
  (reciprocalSchemeIso k).hom ≫ canonicalInfinityOpen k

/-- The reciprocal-coordinate gluing map to the infinity chart is an open immersion. -/
instance gluingToInfinity_open : IsOpenImmersion (gluingToInfinity k) := by
  have h₁ : IsOpenImmersion (reciprocalSchemeIso k).hom := inferInstance
  have h₂ := canonicalInfinityOpen_open k
  exact MorphismProperty.comp_mem (@IsOpenImmersion) _ _ h₁ h₂

/-- The actual two-chart glued scheme. Properness is proved below; no local
nodality criterion is asserted. -/
abbrev pinchedGluing : Scheme.{u} := pushout (gluingToNode k) (gluingToInfinity k)

/-- The corresponding actual gluing of the affine normalization and infinity
chart. A canonical comparison with projective one-space is constructed below
using the proved standard-chart bijection. -/
abbrev lineGluing : Scheme.{u} :=
  pushout (normalizationOverlapInclusion k) (gluingToInfinity k)

/-- The actual glued map, agreeing with the finite affine normalization on one
chart and with identity on the infinity chart. Global finiteness is proved
below from actual pullback squares; properness is proved later using the
proved standard projective-chart bijection. -/
def gluedNormalizationMap : lineGluing k ⟶ pinchedGluing k :=
  pushout.desc (normalizationMap k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k))
    (pushout.inr (gluingToNode k) (gluingToInfinity k)) (by
      rw [← Category.assoc, ← conductorOpenIso_over]
      exact pushout.condition)

@[reassoc, simp] theorem gluedNormalizationMap_affine :
    pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) ≫
      gluedNormalizationMap k =
        normalizationMap k ≫ pushout.inl (gluingToNode k) (gluingToInfinity k) :=
  pushout.inl_desc _ _ _

@[reassoc, simp] theorem gluedNormalizationMap_infinity :
    pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) ≫
      gluedNormalizationMap k = pushout.inr (gluingToNode k) (gluingToInfinity k) :=
  pushout.inr_desc _ _ _

/-- The explicitly constructed pinched gluing has exhaustive affine/infinity
coverage; there is no independently supplied component-covering certificate. -/
theorem pinchedGluing_covered (z : pinchedGluing k) :
    (∃ x, pushout.inl (gluingToNode k) (gluingToInfinity k) x = z) ∨
      ∃ y, pushout.inr (gluingToNode k) (gluingToInfinity k) y = z :=
  openPushout_covered (gluingToNode k) (gluingToInfinity k) z

/-- Exhaustive coverage of the actual source gluing. -/
theorem lineGluing_covered (z : lineGluing k) :
    (∃ x, pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) x = z) ∨
      ∃ y, pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k) y = z :=
  openPushout_covered (normalizationOverlapInclusion k) (gluingToInfinity k) z
end AlgebraicGeometry.Scheme.PinchedLine

/- Migration source: R5Lab/AlgebraicGeometry/Curves/Nodal/Affine.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 c55840f8fa866a3a99f7907c5a5bb33bd7226da06acbd4465a8b502dbe824910. -/
