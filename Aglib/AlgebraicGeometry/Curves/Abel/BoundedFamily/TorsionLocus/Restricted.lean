/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Immersion
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Grauert.Global

/-! # Actual q=0 Grauert on the reduced bounded power locus

The coefficient is the actual power bundle pulled back to the actual family
over its reduced closed nonvanishing locus. Native Cartesian fibre comparison
retains the original residue-field map and proves that this new family's
intrinsic H0 dimension is exactly one. On each actual affine chart, proper
Grauert therefore gives finite projective original H0 and an isomorphism for
the original scalar-extension cohomology map after every ring base change.

No vanishing of H1 or other positive cohomology is assumed. These are the
actual Grauert conclusions, not yet an evaluation or local-triviality theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

/-- The actual curve family over the native reduced closed power locus. -/
def powerLocusCurve (g n : ℕ) : Scheme.{u} :=
  pullback X.hom (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)

/-- Its original structure morphism to the actual reduced locus. -/
def powerLocusProjection (g n : ℕ) :
    powerLocusCurve X o ho g n ⟶ powerNonvanishingLocus X.hom o ho g n :=
  pullback.snd X.hom (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)

instance powerLocusProjection_isProper (g n : ℕ) :
    IsProper (powerLocusProjection X o ho g n) := by
  dsimp only [powerLocusProjection]
  infer_instance

instance powerLocusProjection_isFlat (g n : ℕ) :
    Flat (powerLocusProjection X o ho g n) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  dsimp only [powerLocusProjection]
  infer_instance

/-- The actual power coefficient on the actual restricted curve family. -/
def powerLocusLineBundle (g n : ℕ) : LineBundle (powerLocusCurve X o ho g n) :=
  pullbackLineBundle (Hom.familyMap X.hom (parameter X.hom g).hom
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)
    (powerNonvanishingι X.hom o ho g n) rfl) (powerLineBundle X.hom o ho g n)

/-- The restricted original coefficient remains coherent by actual finite
presentation of its line-bundle sheaf. -/
theorem powerLocusLineBundle_affineLocallyFiniteType (g n : ℕ) :
    affineLocallyFiniteType _ (powerLocusLineBundle X o ho g n).val := by
  let := lineBundle_isFinitePresentation _ (powerLocusLineBundle X o ho g n)
  exact affineLocallyFiniteType_of_finitePresentation _

/-- Flatness of the actual restricted curve projection gives relative
flatness of the actual restricted power coefficient. -/
theorem powerLocusLineBundle_relativeFlat (g n : ℕ) :
    Modules.relativeFlat (powerLocusProjection X o ho g n)
      (powerLocusLineBundle X o ho g n).val :=
  relativeFlat_of_flat _ (powerLocusLineBundle X o ho g n)

variable (hX : Properties X)

include hX

/-- The new family's actual point-fibre H0 dimension is one. The proof uses
its Cartesian fibre map and the closed immersion's original residue map. -/
theorem powerLocusLineBundle_pointFiberH0Dimension (g n : ℕ)
    (z : powerNonvanishingLocus X.hom o ho g n) :
    modulePointFiberCohomologyDimension (powerLocusProjection X o ho g n)
      (powerLocusLineBundle X o ho g n).val 0 z = 1 := by
  have h := Hom.familyMap_isPullback X.hom (parameter X.hom g).hom
    (powerNonvanishingι X.hom o ho g n ≫ (parameter X.hom g).hom)
    (powerNonvanishingι X.hom o ho g n) rfl
  have he := modulePointFiberCohomologyDimension_baseChange_of_surjectiveOnStalks
    h z (powerLineBundle X.hom o ho g n).val 0
  exact he.symm.trans (powerH0Dimension_eq_one_on_locus X hX o ho g n z)

/-- The actual intrinsic H0 dimension on the reduced closed base is constant. -/
theorem powerLocusLineBundle_pointFiberH0Dimension_isLocallyConstant (g n : ℕ) :
    IsLocallyConstant (modulePointFiberCohomologyDimension (powerLocusProjection X o ho g n)
      (powerLocusLineBundle X o ho g n).val 0) := by
  have he : modulePointFiberCohomologyDimension (powerLocusProjection X o ho g n)
      (powerLocusLineBundle X o ho g n).val 0 = fun _ => 1 := by
    funext z
    exact powerLocusLineBundle_pointFiberH0Dimension X o ho hX g n z
  rw [he]
  exact IsLocallyConstant.const 1

section AffineChart

variable {R : Type u} [CommRing R] (g n : ℕ)
  (j : Spec (.of R) ⟶ powerNonvanishingLocus X.hom o ho g n) [IsOpenImmersion j]

/-- On an actual affine chart, the original ordinary fibre-dimension function
is constantly one, by the native affine-coordinate comparison. -/
theorem powerLocusLineBundle_affineFiberH0Dimension (r : PrimeSpectrum R) :
    moduleFiberCohomologyDimension (pullback.snd (powerLocusProjection X o ho g n) j)
      ((Modules.pullback (pullback.fst (powerLocusProjection X o ho g n) j)).obj
        (powerLocusLineBundle X o ho g n).val) 0 r = 1 := by
  rw [← modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension
    (powerLocusProjection X o ho g n) j r (powerLocusLineBundle X o ho g n).val 0]
  exact powerLocusLineBundle_pointFiberH0Dimension X o ho hX g n (j r)

/-- Native Grauert gives finite projective original H0 on every actual affine
chart of the reduced closed parameter locus. -/
theorem powerLocusLineBundle_affineH0_finite_projective :
    let f := pullback.snd (powerLocusProjection X o ho g n) j
    let M := (Modules.pullback (pullback.fst (powerLocusProjection X o ho g n) j)).obj
      (powerLocusLineBundle X o ho g n).val
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom _ α M 0
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf _ M) 0) ∧
      Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf _ M) 0) := by
  let : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing R :=
    (isLocallyNoetherian_Spec (R := .of R)).mp inferInstance
  let : AlgebraicGeometry.IsReduced (Spec (.of R)) := isReduced_of_isOpenImmersion j
  let : _root_.IsReduced R := (affine_isReduced_iff (.of R)).mp inferInstance
  let f := pullback.snd (powerLocusProjection X o ho g n) j
  let L := pullbackLineBundle (pullback.fst (powerLocusProjection X o ho g n) j)
    (powerLocusLineBundle X o ho g n)
  let := lineBundle_isFinitePresentation _ L
  have hM := affineLocallyFiniteType_of_finitePresentation (show (pullback _ j).Modules from L.val)
  have hflat := relativeFlat_of_flat f L
  have hd : IsLocallyConstant (moduleFiberCohomologyDimension f L.val 0) := by
    have he : moduleFiberCohomologyDimension f L.val 0 = fun _ => 1 := by
      funext r
      exact powerLocusLineBundle_affineFiberH0Dimension X o ho hX g n j r
    rw [he]
    exact IsLocallyConstant.const 1
  exact moduleCohomology_finite_projective_of_isLocallyConstant_of_proper f L.val hM hflat 0 hd

/-- The literal original q=0 scalar base-change map is invertible on each
actual reduced Noetherian affine chart, for every new ring. -/
theorem powerLocusLineBundle_affineH0BaseChange_isIso
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap
      (pullback.snd (powerLocusProjection X o ho g n) j) σ
      ((Modules.pullback (pullback.fst (powerLocusProjection X o ho g n) j)).obj
        (powerLocusLineBundle X o ho g n).val) 0) := by
  let : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing R :=
    (isLocallyNoetherian_Spec (R := .of R)).mp inferInstance
  let : AlgebraicGeometry.IsReduced (Spec (.of R)) := isReduced_of_isOpenImmersion j
  let : _root_.IsReduced R := (affine_isReduced_iff (.of R)).mp inferInstance
  let f := pullback.snd (powerLocusProjection X o ho g n) j
  let L := pullbackLineBundle (pullback.fst (powerLocusProjection X o ho g n) j)
    (powerLocusLineBundle X o ho g n)
  let := lineBundle_isFinitePresentation _ L
  have hM := affineLocallyFiniteType_of_finitePresentation (show (pullback _ j).Modules from L.val)
  have hflat := relativeFlat_of_flat f L
  have hd : IsLocallyConstant (moduleFiberCohomologyDimension f L.val 0) := by
    have he : moduleFiberCohomologyDimension f L.val 0 = fun _ => 1 := by
      funext r
      exact powerLocusLineBundle_affineFiberH0Dimension X o ho hX g n j r
    rw [he]
    exact IsLocallyConstant.const 1
  exact moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant_of_proper f L.val hM hflat 0 hd σ

end AffineChart

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
