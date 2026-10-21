/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenPullback
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.ChartFacts
public import Aglib.AlgebraicGeometry.Gluing.ProperModification

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.Recursion`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`7ed4dce45b5cab51403b47d600de71a2f5b90139b268263d4b1c635818c03ed2`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# The actual recursive resolution of a power node and its generic-fibre isomorphism.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre
universe u

section RecursiveNodeResolution


/-!
# Actual recursive resolution of UV = pi^n

For n=0 and n=1 use the literal regular node. For n=m + 2 take the actual
three-chart blowup, replace its middle node by the already constructed
resolution, and glue it to the unchanged union of its two regular outer
charts. The overlap is exactly D(U) union D(V). The canonical restricted
map is an isomorphism there, so the open pushout is an actual scheme and its
map to the blowup is proper by target locality. No resolution, regular-model,
component-count, or discriminant family occurs as a premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OpenPushout.Modification.OfRestriction
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)

instance resolution_overlap_isIso :
    IsIso (E.map ∣_ (middleChartMap B.atlas hπ ⁻¹ᵁ outerOpen B hπ)) := by
  rw [middle_preimage_outer]
  exact Scheme.Hom.isIso_restrict_sup E.map (uOpen π m) (vOpen π m)

/-- The literal replacement of the middle chart followed by the proper
three-chart blowdown. Every property is proved from the earlier resolution. -/
def step : Data π (m + 2) := by
  let i := middleChartMap B.atlas hπ
  let V := outerOpen B hπ
  let g := AlgebraicGeometry.Scheme.OpenPushout.Modification.OfRestriction.map E.map i V
  let : IsProper g := map_isProper E.map i V (middle_outer_cover B hπ)
  let : IsProper B.blowup.map := B.proper
  refine {
    Y := glued E.map i V
    map := g ≫ B.blowup.map
    proper := inferInstance
    regular := ?_
    isoU := ?_
    isoV := ?_ }
  · intro z
    rcases charts_cover E.map i V z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Scheme.RegularStalks.at_image (modifiedChart E.map i V) E.regular y
    · exact Scheme.RegularStalks.at_image (unchangedChart E.map i V) (outer_regular B hπ) y
  · let := blowup_u_isIso B
    let : IsIso (g ∣_ (B.blowup.map ⁻¹ᵁ uOpen π (m + 2))) :=
      Scheme.Hom.isIso_restrict_of_le g (blowup_preimage_u_le_outer B hπ)
    exact Scheme.Hom.isIso_restrict_comp g B.blowup.map (uOpen π (m + 2))
  · let := blowup_v_isIso B
    let : IsIso (g ∣_ (B.blowup.map ⁻¹ᵁ vOpen π (m + 2))) :=
      Scheme.Hom.isIso_restrict_of_le g (blowup_preimage_v_le_outer B hπ)
    exact Scheme.Hom.isIso_restrict_comp g B.blowup.map (vOpen π (m + 2))

/-- The open chart map from the exponent-reduced resolution source into the glued next-step source.
-/
def stepModifiedChart : E.Y ⟶ (step B hπ E).Y :=
  modifiedChart E.map (middleChartMap B.atlas hπ) (outerOpen B hπ)
/-- The open chart map from the unchanged outer open of the blowup into the glued next-step source.
-/
def stepUnchangedChart : (outerOpen B hπ).toScheme ⟶ (step B hπ E).Y :=
  unchangedChart E.map (middleChartMap B.atlas hπ) (outerOpen B hπ)

instance stepModifiedChart_isOpenImmersion : IsOpenImmersion (stepModifiedChart B hπ E) := by
  dsimp [stepModifiedChart]; infer_instance
instance stepUnchangedChart_isOpenImmersion : IsOpenImmersion (stepUnchangedChart B hπ E) := by
  dsimp [stepUnchangedChart]; infer_instance

@[reassoc] lemma stepModifiedChart_triangle :
    stepModifiedChart B hπ E ≫ (step B hπ E).map =
      E.map ≫ Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) := by
  change modifiedChart E.map (middleChartMap B.atlas hπ) (outerOpen B hπ) ≫
    map E.map (middleChartMap B.atlas hπ) (outerOpen B hπ) ≫ B.blowup.map = _
  rw [modifiedChart_triangle_assoc, middleChartMap_triangle]

@[reassoc] lemma stepUnchangedChart_triangle :
    stepUnchangedChart B hπ E ≫ (step B hπ E).map =
      (outerOpen B hπ).ι ≫ B.blowup.map := by
  simp only [stepUnchangedChart, step, ← Category.assoc, unchangedChart_triangle]

/-- The actual map to the same one-step blowup, before composition. -/
def stepToBlowup : (step B hπ E).Y ⟶ B.blowup.Y :=
  map E.map (middleChartMap B.atlas hπ) (outerOpen B hπ)

lemma stepModifiedChart_isPullback :
    IsPullback E.map (stepModifiedChart B hπ E) (middleChartMap B.atlas hπ)
      (stepToBlowup B hπ E) := modifiedChart_isPullback ..
lemma stepUnchangedChart_isPullback :
    IsPullback (𝟙 (outerOpen B hπ).toScheme) (stepUnchangedChart B hπ E)
      (outerOpen B hπ).ι (stepToBlowup B hπ E) := unchangedChart_isPullback ..
lemma stepToBlowup_comp : stepToBlowup B hπ E ≫ B.blowup.map = (step B hπ E).map := rfl


variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})

/-- A constructed actual proper regular resolution for every nonnegative
exponent. The only retained general premises are the three ordinary blowup
families already needed for the accepted one-step atlas. -/
def resolve : (n : ℕ) → Data π n
  | 0 => zero π
  | 1 => one π hπ
  | m + 2 => step (OneStepBlowup.ofFamilies π m hex hp ha) hπ (resolve m)

/-- Properness of the actual recursively constructed structural map. -/
theorem resolve_proper (n : ℕ) : IsProper (resolve π hπ hex hp ha n).map :=
  (resolve π hπ hex hp ha n).proper

/-- Regularity at every stalk of the actual recursively glued source scheme. -/
theorem resolve_regular (n : ℕ) : RegularStalks (resolve π hπ hex hp ha n).Y :=
  (resolve π hπ hex hp ha n).regular

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end RecursiveNodeResolution

section NodeResolutionGenericFibre


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution


variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {n : ℕ} (D : Data π n)
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The literal structure morphism to the original DVR. -/
def base : X π n ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (node π n)))
/-- The base morphism from the spectrum of `K` to the spectrum of `R` induced by the algebra
structure. -/
def genericBase : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The base change of the target power node from `R` to `K`. -/
def targetGenericFibre : Scheme.{u} := pullback (base (π := π) (n := n)) (genericBase (R := R) K)
/-- The base change of the modification source from `R` to `K`. -/
def sourceGenericFibre : Scheme.{u} :=
  pullback (D.map ≫ base) (genericBase (R := R) K)

/-- The morphism from the source generic fibre to the target generic fibre induced by `D.map`. -/
def genericFibreMap : sourceGenericFibre D K ⟶ targetGenericFibre (π := π) (n := n) K :=
  (pullbackRightPullbackFstIso base (genericBase K) D.map).inv ≫
    pullback.snd D.map (pullback.fst base (genericBase K))

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma generic_projection_range (hπ : π ≠ 0) :
    Set.range (pullback.fst (base (π := π) (n := n)) (genericBase (R := R) K)) ⊆
      (genericOpen π n : Set (X π n)) := by
  rintro _ ⟨z, rfl⟩
  change (pullback.fst base (genericBase K) ≫ base) z ∈ PrimeSpectrum.basicOpen π
  rw [pullback.condition]
  change algebraMap R K π ∉ (pullback.snd base (genericBase K) z).asIdeal
  exact (pullback.snd base (genericBase K) z).asIdeal.notMem_of_isUnit
    (isUnit_iff_ne_zero.mpr (by simpa only [map_zero] using (IsFractionRing.injective R K).ne hπ))

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma genericFibreMap_isIso (hπ : π ≠ 0) : IsIso (genericFibreMap D K) := by
  let := isIso_pullback_of_range_subset D.map (genericOpen π n)
    (pullback.fst base (genericBase K)) (generic_projection_range K hπ)
  dsimp [genericFibreMap]
  infer_instance

/-- The actual fibre product over the fraction field is preserved, with the
canonical morphism rather than merely an abstract generic-fibre equivalence. -/
def genericFibreIso (hπ : π ≠ 0) : sourceGenericFibre D K ≅ targetGenericFibre (π := π) (n := n) K
  := by
  let := genericFibreMap_isIso D K hπ
  exact asIso (genericFibreMap D K)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc] lemma genericFibreMap_fst :
    genericFibreMap D K ≫ pullback.fst base (genericBase K) =
      pullback.fst (D.map ≫ base) (genericBase K) ≫ D.map := by
  simp [genericFibreMap]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc] lemma genericFibreMap_snd :
    genericFibreMap D K ≫ pullback.snd base (genericBase K) =
      pullback.snd (D.map ≫ base) (genericBase K) := by
  simp [genericFibreMap]

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc] lemma genericFibreIso_hom_fst (hπ : π ≠ 0) :
    (genericFibreIso D K hπ).hom ≫ pullback.fst base (genericBase K) =
      pullback.fst (D.map ≫ base) (genericBase K) ≫ D.map := genericFibreMap_fst D K
omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc] lemma genericFibreIso_hom_snd (hπ : π ≠ 0) :
    (genericFibreIso D K hπ).hom ≫ pullback.snd base (genericBase K) =
      pullback.snd (D.map ≫ base) (genericBase K) := genericFibreMap_snd D K

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end NodeResolutionGenericFibre
