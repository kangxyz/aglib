/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Fibers
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Fibers.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism

/-!
# Canonical affine coordinates for original point-fibre cohomology

An affine open immersion identifies the actual residue field of its image
point with the prime's native residue field. The actual fibre pullbacks
and ordinary coefficient pullbacks are compared by the native residue-field
maps and pullback isomorphisms. The original geometric cohomology maps then
identify the general point-fibre dimension with the existing affine function.
No quasicoherence, properness, Noetherianity or flatness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Y) (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
  (p : PrimeSpectrum R)

/-- The canonical actual residue-field isomorphism in an affine open coordinate. -/
def modulePointFiberAffineResidueFieldIso : Y.residueField (j p) ≅
    CommRingCat.of p.asIdeal.ResidueField :=
  asIso (j.residueFieldMap p) ≪≫ Scheme.Spec.residueFieldIso (.of R) p

/-- The original affine residue-field fibre is canonically isomorphic to the native
point fibre of the original morphism over the image point. -/
def modulePointFiberAffineIso :
    pullback (pullback.snd f j)
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) ≅
      f.fiber (j p) := by
  let A := pullback f j
  let a := pullback.fst f j
  let b := pullback.snd f j
  let σ := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let e := Scheme.Spec.residueFieldIso (.of R) p
  let s : pullback b σ ⟶ b.fiber p :=
    pullback.map b σ b ((Spec (.of R)).fromSpecResidueField p)
      (𝟙 A) (Spec.map e.hom) (𝟙 _) (by dsimp [A, b]; simp) (by
        simp only [Category.comp_id]
        rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p]
        simp [σ, e, ← Spec.map_comp_assoc])
  let : IsIso s := inferInstance
  let t : b.fiber p ⟶ f.fiber (j p) :=
    pullback.map b ((Spec (.of R)).fromSpecResidueField p) f
      (Y.fromSpecResidueField (j p)) a (Spec.map (j.residueFieldMap p)) j
      pullback.condition.symm (by simp)
  have ht := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f j) p
  let : IsIso t := ht.isIso_fst_of_isIso
  exact asIso (s ≫ t)

/-- The fibre-coordinate isomorphism preserves the actual map to the original source. -/
@[reassoc]
theorem modulePointFiberAffineIso_hom_fiberι :
    (modulePointFiberAffineIso f j p).hom ≫ f.fiberι (j p) =
      pullback.fst (pullback.snd f j)
          (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) ≫
        pullback.fst f j := by
  simp [modulePointFiberAffineIso, Scheme.Hom.fiberι, Category.assoc]

/-- The fibre-coordinate isomorphism retains the canonical map on the actual
structural residue fields. -/
@[reassoc]
theorem modulePointFiberAffineIso_hom_toSpec :
    (modulePointFiberAffineIso f j p).hom ≫ f.fiberToSpecResidueField (j p) =
      pullback.snd (pullback.snd f j)
          (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) ≫
        Spec.map (modulePointFiberAffineResidueFieldIso j p).hom := by
  simp [modulePointFiberAffineIso, Scheme.Hom.fiberToSpecResidueField,
    modulePointFiberAffineResidueFieldIso, Spec.map_comp, Category.assoc]

/-- The ordinary pulled coefficient is identified through the same actual fibre
isomorphism, using only native pullback composition and equality comparisons. -/
def modulePointFiberAffineCoefficientIso (M : X.Modules) :
    (Scheme.Modules.pullback (modulePointFiberAffineIso f j p).hom).obj
        ((Scheme.Modules.pullback (f.fiberι (j p))).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd f j)
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj
          ((Scheme.Modules.pullback (pullback.fst f j)).obj M) :=
  (Scheme.Modules.pullbackComp (modulePointFiberAffineIso f j p).hom (f.fiberι (j p))).app M ≪≫
    (Scheme.Modules.pullbackCongr (modulePointFiberAffineIso_hom_fiberι f j p)).app M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd f j)
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))
          (pullback.fst f j)).app M).symm

/-- The original cohomology map through the actual fibre-coordinate isomorphism is
an isomorphism after restricting the old affine fibre's scalars along the canonical
actual residue-field isomorphism. -/
def modulePointFiberCohomologyAffineIso (M : X.Modules) (q : ℕ) :
    modulePointFiberCohomology f M q (j p) ≅
      let σ := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
      let P := pullback (pullback.snd f j) σ
      let N := (Scheme.Modules.pullback (pullback.fst (pullback.snd f j) σ)).obj
        ((Scheme.Modules.pullback (pullback.fst f j)).obj M)
      let β := (pullback.snd (pullback.snd f j) σ).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of p.asIdeal.ResidueField)).inv.hom
      letI := moduleCohomologyModuleOfHom P β N q
      (ModuleCat.restrictScalars (modulePointFiberAffineResidueFieldIso j p).hom.hom).obj
        (ModuleCat.of p.asIdeal.ResidueField (Sheaf.H.{u + 1} (moduleAddSheaf P N) q)) := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let P := pullback (pullback.snd f j) σ
  let b := pullback.snd (pullback.snd f j) σ
  let N := (Scheme.Modules.pullback (pullback.fst (pullback.snd f j) σ)).obj
    ((Scheme.Modules.pullback (pullback.fst f j)).obj M)
  let L := (Scheme.Modules.pullback (f.fiberι (j p))).obj M
  let α := (f.fiberToSpecResidueField (j p)).appTop.hom.comp
    (Scheme.ΓSpecIso (Y.residueField (j p))).inv.hom
  let β := b.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of p.asIdeal.ResidueField)).inv.hom
  let e := modulePointFiberAffineIso f j p
  let κ := (modulePointFiberAffineResidueFieldIso j p).hom.hom
  let C := modulePointFiberAffineCoefficientIso f j p M
  have h := moduleSectionsBaseChangeScalars e.hom b (f.fiberToSpecResidueField (j p)) κ
    (modulePointFiberAffineIso_hom_toSpec f j p)
  exact moduleCohomologyRestrictionIsoOfPullbackIso e.hom κ α β h L C q

/-- The intrinsic point-fibre dimension agrees in every affine open coordinate with
the unchanged original affine fibre-dimension function. No finiteness is assumed. -/
theorem modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension
    (M : X.Modules) (q : ℕ) :
    modulePointFiberCohomologyDimension f M q (j p) =
      moduleFiberCohomologyDimension (pullback.snd f j)
        ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q p := by
  let σ := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let P := pullback (pullback.snd f j) σ
  let N := (Scheme.Modules.pullback (pullback.fst (pullback.snd f j) σ)).obj
    ((Scheme.Modules.pullback (pullback.fst f j)).obj M)
  let β := (pullback.snd (pullback.snd f j) σ).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of p.asIdeal.ResidueField)).inv.hom
  let := moduleCohomologyModuleOfHom P β N q
  let κ := (modulePointFiberAffineResidueFieldIso j p).commRingCatIsoToRingEquiv
  let E : modulePointFiberCohomology f M q (j p) ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf P N) q :=
    (modulePointFiberCohomologyAffineIso f j p M q).toLinearEquiv.toAddEquiv
  have hs (a : Y.residueField (j p)) (x : modulePointFiberCohomology f M q (j p)) :
      E (a • x) = κ a • E x :=
    (modulePointFiberCohomologyAffineIso f j p M q).toLinearEquiv.map_smul a x
  have hr := lift_rank_eq_of_equiv_equiv κ E κ.bijective hs
  change Module.finrank (Y.residueField (j p)) (modulePointFiberCohomology f M q (j p)) =
    Module.finrank p.asIdeal.ResidueField (Sheaf.H.{u + 1} (moduleAddSheaf P N) q)
  simpa only [Module.finrank, Cardinal.toNat_lift] using congrArg Cardinal.toNat hr

/-- The honest intrinsic point-fibre Euler finsum is exactly the unchanged original
affine fibre Euler characteristic in every actual affine open coordinate. -/
theorem modulePointFiberEulerChar_eq_moduleFiberEulerChar (M : X.Modules) :
    modulePointFiberEulerChar f M (j p) =
      moduleFiberEulerChar (pullback.snd f j)
        ((Scheme.Modules.pullback (pullback.fst f j)).obj M) p := by
  unfold modulePointFiberEulerChar moduleFiberEulerChar
  apply finsum_congr
  intro q
  rw [modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension f j p M q]

end AlgebraicGeometry.Scheme.Cohomology
