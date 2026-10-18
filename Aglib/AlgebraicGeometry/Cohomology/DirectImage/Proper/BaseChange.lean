/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.BaseChange.Neighbourhood
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.RingEquiv

/-!
# Canonical proper base change over locally Noetherian targets

The actual canonical sheaf comparison descends from the original scalar
maps on affine charts. Reducedness and intrinsic locally constant ordinary
fibre dimension give arbitrary base change. On a possibly nonreduced base,
surjectivity of the actual residue comparison on sections gives an open
neighbourhood on which every base change is invertible. Pointwise residue
surjectivity gives the global arbitrary-base-change criterion.

Only the original target is locally Noetherian. New target schemes need be
neither flat, Noetherian nor quasi-compact, and the coefficients on the fibres
are ordinary pullbacks. No comparison family is an endpoint hypothesis.

Development boundary: this source is authored against the frozen canonical
comparison and chart-criterion interfaces. Its native validation awaits the
closure of those providers; the endpoint declarations are not yet released.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual canonical comparison at a native residue point, on its original
global sections. Its target is the higher image of the ordinary coefficient
on the native point fibre, with the native residue-field action. -/
abbrev higherDirectImageResidueBaseChangeMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) (y : Y) :=
  (moduleSpecΓFunctor (R := Y.residueField y)).map
    (higherDirectImageBaseChangeMap (f.fiberι y) (f.fiberToSpecResidueField y) f
      (Y.fromSpecResidueField y) (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) q M)

/-- The actual residue comparison is epic exactly when the original scalar
comparison is epic in an affine open coordinate. The proof uses the actual
residue-field isomorphism and the original scalar-map transport. -/
theorem higherDirectImageResidueBaseChangeMap_epi_iff_on_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (p : PrimeSpectrum R) :
    Epi (higherDirectImageResidueBaseChangeMap f M q (j p)) ↔
      Epi (moduleCohomologyBaseChangeMap (Limits.pullback.snd f j)
        (algebraMap R p.asIdeal.ResidueField)
        ((pullback (Limits.pullback.fst f j)).obj M) q) := by
  let e := modulePointFiberAffineResidueFieldIso j p
  let σ := e.inv.hom.comp (algebraMap R p.asIdeal.ResidueField)
  let κ := e.commRingCatIsoToRingEquiv
  have hσ : Spec.map (CommRingCat.ofHom σ) ≫ j = Y.fromSpecResidueField (j p) :=
    modulePointFiberAffineResidueFieldIso_inv_specMap j p
  have hΓ := higherDirectImageBaseChangeMap_specTarget_sections_epi_iff_pullback
    (f.fiberι (j p)) (f.fiberToSpecResidueField (j p)) f
    (Y.fromSpecResidueField (j p))
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField (j p))) q M j σ hσ
  have he : κ.toRingHom.comp σ = algebraMap R p.asIdeal.ResidueField := by
    ext r
    exact Iso.inv_hom_id_apply e (algebraMap R p.asIdeal.ResidueField r)
  have hκ := moduleCohomologyBaseChangeMap_epi_iff_ringEquiv (Limits.pullback.snd f j)
    σ κ ((pullback (Limits.pullback.fst f j)).obj M) q
  rw [he] at hκ
  exact hΓ.trans hκ.symm

/-- On a reduced locally Noetherian target, locally constant intrinsic ordinary
fibre dimension makes the canonical proper comparison invertible after every
base change. The new target has no finiteness or flatness hypothesis. -/
theorem higherDirectImageBaseChangeMap_isIso_of_isLocallyConstant_of_proper
    {W X V Y : Scheme.{u}} [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (a : W ⟶ X) (b : W ⟶ V) (f : X ⟶ Y) (g : V ⟶ Y)
    (h : IsPullback a b f g) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M) (q : ℕ)
    (hdim : IsLocallyConstant (modulePointFiberCohomologyDimension f M q)) :
    letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
    IsIso (higherDirectImageBaseChangeMap a b f g h q M) := by
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  apply higherDirectImageBaseChangeMap_isIso_of_affineCharts_pullback a b f g h q M
    (fun C : Nonflat.AffineBaseChangeChart g => C) (Nonflat.affineBaseChangeCharts_cover g)
  intro C
  exact moduleCohomologyBaseChangeMap_isIso_on_affine_of_isLocallyConstant_of_proper
    f M hM hflat q hdim (R := C.sourceRing) C.source C.scalar.hom

/-- Surjectivity of the actual residue comparison gives a genuinely open neighbourhood
where the actual canonical proper comparison is invertible for every scheme
mapping into that neighbourhood. Reducedness of the base is not required. -/
theorem exists_open_higherDirectImageBaseChangeMap_isIso_of_epi_residue_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M) (q : ℕ) (y : Y)
    (hres : letI : M.IsQuasicoherent :=
        quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
      Epi (higherDirectImageResidueBaseChangeMap f M q y)) :
    letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
    ∃ U : Y.Opens, y ∈ U ∧
      ∀ (Z : Scheme.{u}) (g : Z ⟶ U.toScheme),
        IsIso (higherDirectImageBaseChangeMap
          (Limits.pullback.fst f (g ≫ U.ι)) (Limits.pullback.snd f (g ≫ U.ι))
          f (g ≫ U.ι) (IsPullback.of_hasPullback f (g ≫ U.ι)) q M) := by
  classical
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let A := Y.affineOpenCover
  let i := A.idx y
  let j := A.f i
  let : IsOpenImmersion j := A.map_prop i
  obtain ⟨p, hp⟩ := A.covers y
  have hp' : j p = y := hp
  have hresj : Epi (higherDirectImageResidueBaseChangeMap f M q (j p)) := by
    rw [hp']
    exact hres
  have hscalar := (higherDirectImageResidueBaseChangeMap_epi_iff_on_affine
    f M q (R := A.X i) j p).mp hresj
  obtain ⟨U, hyU, hU⟩ :=
    exists_open_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_on_affine
      f M hM hflat q (R := A.X i) j p hscalar
  refine ⟨U, ?_, ?_⟩
  · exact hp' ▸ hyU
  · intro Z g
    let B := Z.affineOpenCover
    choose σ hσ hβ using fun k : B.I₀ => hU (B.X k) (B.f k ≫ g)
    let C (k : B.I₀) : Nonflat.AffineBaseChangeChart (g ≫ U.ι) :=
      { sourceRing := A.X i
        targetRing := B.X k
        source := j
        target := B.f k
        scalar := CommRingCat.ofHom (σ k)
        source_open := A.map_prop i
        target_open := B.map_prop k
        comm := (hσ k).trans (Category.assoc (B.f k) g U.ι) }
    apply higherDirectImageBaseChangeMap_isIso_of_affineCharts_pullback
      (Limits.pullback.fst f (g ≫ U.ι)) (Limits.pullback.snd f (g ≫ U.ι))
      f (g ≫ U.ι) (IsPullback.of_hasPullback f (g ≫ U.ι)) q M C
      (fun z => ⟨B.idx z, B.covers z⟩)
    exact hβ

/-- One original scalar residue condition supplies an actual affine base-change
chart containing a specified new-target point, with an invertible original scalar map. -/
private theorem exists_affineBaseChangeChart_of_epi_residue
    {X Y Z : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (g : Z ⟶ Y) (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M)
    (q : ℕ) (z : Z) {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (hp : j p = g z)
    (hres : Epi (moduleCohomologyBaseChangeMap (Limits.pullback.snd f j)
      (algebraMap R p.asIdeal.ResidueField)
      ((pullback (Limits.pullback.fst f j)).obj M) q)) :
    ∃ C : Nonflat.AffineBaseChangeChart g, z ∈ Set.range C.target ∧
      IsIso (moduleCohomologyBaseChangeMap (Limits.pullback.snd f C.source) C.scalar.hom
        ((pullback (Limits.pullback.fst f C.source)).obj M) q) := by
  obtain ⟨U, hUp, hU⟩ :=
    exists_open_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_on_affine
      f M hM hflat q j p hres
  have hz : z ∈ g ⁻¹ᵁ U := by
    change g z ∈ U
    rw [← hp]
    exact hUp
  obtain ⟨B, t, ht, hzt, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset hz
  let : IsOpenImmersion t := ht
  have hrange : Set.range (t ≫ g) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hsub ⟨x, rfl⟩
  let l : Spec B ⟶ U.toScheme := IsOpenImmersion.lift U.ι (t ≫ g) hrange
  obtain ⟨σ, hσ, hiso⟩ := hU B l
  let C : Nonflat.AffineBaseChangeChart g :=
    { sourceRing := CommRingCat.of R
      targetRing := B
      source := j
      target := t
      scalar := CommRingCat.ofHom σ
      source_open := inferInstance
      target_open := ht
      comm := hσ.trans (IsOpenImmersion.lift_fac U.ι (t ≫ g) hrange) }
  exact ⟨C, hzt, hiso⟩

/-- If every actual residue comparison is surjective, the canonical proper
comparison is invertible after every base change. The locally Noetherian base
may be nonreduced and the new target may be empty or non-quasi-compact. -/
theorem higherDirectImageBaseChangeMap_isIso_of_epi_residue_of_proper
    {W X V Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (a : W ⟶ X) (b : W ⟶ V) (f : X ⟶ Y) (g : V ⟶ Y)
    (h : IsPullback a b f g) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M) (q : ℕ)
    (hres : letI : M.IsQuasicoherent :=
        quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
      ∀ y : Y, Epi (higherDirectImageResidueBaseChangeMap f M q y)) :
    letI : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
    IsIso (higherDirectImageBaseChangeMap a b f g h q M) := by
  classical
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  have hc (z : V) : ∃ C : Nonflat.AffineBaseChangeChart g, z ∈ Set.range C.target ∧
      IsIso (moduleCohomologyBaseChangeMap (Limits.pullback.snd f C.source) C.scalar.hom
        ((pullback (Limits.pullback.fst f C.source)).obj M) q) := by
    let A := Y.affineOpenCover
    let i := A.idx (g z)
    let j := A.f i
    let : IsOpenImmersion j := A.map_prop i
    obtain ⟨p, hp⟩ := A.covers (g z)
    have hscalar := (higherDirectImageResidueBaseChangeMap_epi_iff_on_affine
      f M q (R := A.X i) j p).mp (hres (j p))
    exact exists_affineBaseChangeChart_of_epi_residue f g M hM hflat q z
      (R := A.X i) j p hp hscalar
  choose C hC hβ using hc
  exact higherDirectImageBaseChangeMap_isIso_of_affineCharts_pullback a b f g h q M C
    (fun z => ⟨z, hC z⟩) hβ

end AlgebraicGeometry.Scheme.Modules
