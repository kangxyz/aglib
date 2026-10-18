/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Grauert.Global
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BaseChangeLocus
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Affine
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality

/-!
# Original proper base change in affine coordinates of a general target

These lemmas apply the original scalar comparison to actual affine opens of
a locally Noetherian target. The coefficients are ordinary pullbacks of the
original coherent relatively flat module. Intrinsic ordinary point-fibre
dimension supplies the reduced Grauert criterion on every such chart.

The residue-coordinate equation retains the actual native residue-field
isomorphism. The basic-open criterion uses the original scalar comparison
and requires no reducedness. New target rings have no flatness or
Noetherianity hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The inverse actual residue-field isomorphism gives the native residue point
map in an affine open coordinate, as an equality of scheme morphisms. -/
@[reassoc]
theorem modulePointFiberAffineResidueFieldIso_inv_specMap
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j] (p : PrimeSpectrum R) :
    Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
        (modulePointFiberAffineResidueFieldIso j p).inv) ≫ j =
      Y.fromSpecResidueField (j p) := by
  apply (cancel_epi (Spec.map (modulePointFiberAffineResidueFieldIso j p).hom)).1
  simp only [← Spec.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [modulePointFiberAffineResidueFieldIso, Iso.trans_hom, asIso_hom,
    Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p]
  simp only [Category.assoc, ← Spec.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Intrinsic local constancy restricts to the unchanged ordinary affine fibre
dimension on every actual affine open of the original target. -/
theorem isLocallyConstant_moduleFiberCohomologyDimension_on_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (q : ℕ)
    (h : IsLocallyConstant (modulePointFiberCohomologyDimension f M q))
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j] :
    IsLocallyConstant (moduleFiberCohomologyDimension (pullback.snd f j)
      ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q) := by
  have hc := h.comp_continuous j.continuous
  have he : modulePointFiberCohomologyDimension f M q ∘ j =
      moduleFiberCohomologyDimension (pullback.snd f j)
        ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q := by
    funext p
    exact modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension f j p M q
  rw [he] at hc
  exact hc

/-- Over every affine open of a reduced locally Noetherian target, intrinsic
locally constant ordinary fibre dimension makes the original proper scalar
comparison invertible for every ring map. The new ring is arbitrary. -/
theorem moduleCohomologyBaseChangeMap_isIso_on_affine_of_isLocallyConstant_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (q : ℕ) (h : IsLocallyConstant (modulePointFiberCohomologyDimension f M q))
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap (pullback.snd f j) σ
      ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q) := by
  let : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := .of R)).mp inferInstance
  let : AlgebraicGeometry.IsReduced (Spec (.of R)) := isReduced_of_isOpenImmersion j
  let : _root_.IsReduced R := (affine_isReduced_iff (.of R)).mp inferInstance
  let a := pullback.fst f j
  let N := (Scheme.Modules.pullback a).obj M
  have hN : affineLocallyFiniteType (CategoryTheory.Limits.pullback f j) N :=
    (affineLocallyFiniteType _).prop_of_iso ((Scheme.Modules.restrictFunctorIsoPullback a).app M)
      (affineLocallyFiniteType_restrict a hM)
  exact moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant_of_proper
    (pullback.snd f j) N hN
    (Scheme.Modules.relativeFlat_pullback_of_isOpenImmersion f j hflat) q
    (isLocallyConstant_moduleFiberCohomologyDimension_on_affine f M q h j) σ

/-- On an actual affine target chart, surjectivity of the original residue
comparison gives one basic open where every further original scalar comparison
is invertible. The locally Noetherian target may be nonreduced. -/
theorem exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_on_affine_of_epi_residue_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (p : PrimeSpectrum R)
    (hres : Epi (moduleCohomologyBaseChangeMap (pullback.snd f j)
      (algebraMap R p.asIdeal.ResidueField)
      ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q)) :
    ∃ r ∉ p.asIdeal,
      ∀ (B : Type u) [CommRing B] (τ : Localization.Away r →+* B),
        IsIso (moduleCohomologyBaseChangeMap (pullback.snd f j)
          (τ.comp (algebraMap R (Localization.Away r)))
          ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q) := by
  let : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := .of R)).mp inferInstance
  let a := pullback.fst f j
  let N := (Scheme.Modules.pullback a).obj M
  have hN : affineLocallyFiniteType (CategoryTheory.Limits.pullback f j) N :=
    (affineLocallyFiniteType _).prop_of_iso ((Scheme.Modules.restrictFunctorIsoPullback a).app M)
      (affineLocallyFiniteType_restrict a hM)
  exact exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper
    (pullback.snd f j) N hN
    (Scheme.Modules.relativeFlat_pullback_of_isOpenImmersion f j hflat) q p hres

end AlgebraicGeometry.Scheme.Cohomology
