/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Support
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.UnitLocus
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic density on native blowups

The complement of the exceptional locus is schematically dense without any
reducedness hypothesis. On a saturated chart its coordinate map is the literal
inclusion into the ambient localization. Kernel containment glues these
injections and also proves preservation of quasi-compact schematically dense
maps under the original blowup morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme.Blowup

/-- The actual inverse-image open of the complement of the centre. -/
def BlowupDatum.exceptionalComplement {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : BlowupDatum I) : B.Y.Opens := B.map ⁻¹ᵁ I.support.compl

/-- The open cover by the literal saturated charts of a native affine blowup atlas. -/
def saturatedAtlasCover {A : Type u} [CommRing A] {I : Ideal A}
    {B : BlowupDatum (affineCenter A I)} (H : AffineAtlas A I B) : B.Y.OpenCover where
  I₀ := I
  X a := Spec (.of (affineBlowupAlgebra A I a))
  f := H.chart
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨H.covers, H.openImmersion⟩

/-- The centre complement is schematically dense on every actual affine
blowup representative, using the original saturated atlas. -/
theorem BlowupDatum.exceptionalComplement_isSchemeTheoreticallyDominant_affine
    {A : Type u} [CommRing A] {I : Ideal A}
    (B : BlowupDatum (affineCenter A I)) :
    IsSchemeTheoreticallyDominant B.exceptionalComplement.ι := by
  let H := affineAtlas B
  let C := saturatedAtlasCover H
  let k (a : I) : Spec (.of (Localization.Away (a : A))) ⟶ C.X a :=
    Spec.map (CommRingCat.ofHom (affineBlowupAlgebra A I a).val.toRingHom)
  apply isSchemeTheoreticallyDominant_of_openCover_ranges B.exceptionalComplement.ι C
    (fun (a : I) => Spec (.of (Localization.Away (a : A)))) k
  · intro a
    change I at a
    exact isSchemeTheoreticallyDominant_specMap_of_injective _ Subtype.val_injective
  · intro a
    change I at a
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have ht : (k a ≫ C.f a) ≫ B.map = Coordinates.awayMap (a : A) := by
      rw [Category.assoc, show C.f a ≫ B.map = affineChartMap A I a from H.triangle a]
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      rfl
    change B.map ((k a ≫ C.f a) z) ∉ ((affineCenter A I).support : Set _)
    rw [support_affineCenter]
    change ((k a ≫ C.f a) ≫ B.map) z ∉ PrimeSpectrum.zeroLocus (I : Set A)
    rw [ht]
    intro hz
    have ha := hz a.property
    exact z.asIdeal.notMem_of_isUnit
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : A)) (a : A)) ha

private theorem exceptionalComplement_spectrum
    {A : Type u} [CommRing A] (I : (Spec (.of A)).IdealSheafData) (B : BlowupDatum I) :
    IsSchemeTheoreticallyDominant B.exceptionalComplement.ι := by
  obtain ⟨J, rfl⟩ : ∃ J : Ideal A, affineCenter A J = I :=
    ⟨spectrumIdeal I, affineCenter_spectrumIdeal I⟩
  exact B.exceptionalComplement_isSchemeTheoreticallyDominant_affine

/-- On an arbitrary, possibly nonreduced base, the complement of the exceptional
locus is schematically dense in every native universal blowup. -/
theorem BlowupDatum.exceptionalComplement_isSchemeTheoreticallyDominant
    {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I) :
    IsSchemeTheoreticallyDominant B.exceptionalComplement.ι := by
  let C := X.affineCover
  let D := C.pullback₁ B.map
  let B' (i : C.I₀) := flatPullbackDatum B (C.f i)
  let W (i : C.I₀) := (B' i).exceptionalComplement.toScheme
  let k (i : C.I₀) : W i ⟶ D.X i := (B' i).exceptionalComplement.ι
  apply isSchemeTheoreticallyDominant_of_openCover_ranges B.exceptionalComplement.ι D W k
  · intro i
    exact exceptionalComplement_spectrum _ (B' i)
  · intro i
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz := z.property
    change (pullback.snd B.map (C.f i)) z.val ∉ (I.comap (C.f i)).support at hz
    rw [Scheme.IdealSheafData.support_comap] at hz
    change (C.f i) ((pullback.snd B.map (C.f i)) z.val) ∉ I.support at hz
    change B.map ((pullback.fst B.map (C.f i)) z.val) ∉ I.support
    exact (congrArg (fun f => f z.val) (pullback.condition (f := B.map) (g := C.f i))).symm ▸ hz

/-- A quasi-compact schematically dominant map remains schematically dominant
after base change to any blowup. No reducedness, domain or Noetherian premise
is used; in particular this applies to quasi-compact dense open immersions. -/
theorem BlowupDatum.pullback_snd_isSchemeTheoreticallyDominant
    {X U : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)
    (j : U ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    IsSchemeTheoreticallyDominant (pullback.snd j B.map) := by
  let V : X.Opens := I.support.compl
  let E := B.exceptionalComplement
  let e : E.toScheme ⟶ X := E.ι ≫ B.map
  let : IsIso (B.map ∣_ V) := B.restrict_isIso_of_disjoint V
    (Set.disjoint_left.mpr fun _ hx hy => hx hy)
  have he : e = (B.map ∣_ V) ≫ V.ι := morphismRestrict_ι B.map V |>.symm
  let : Flat e := by rw [he]; infer_instance
  let : IsSchemeTheoreticallyDominant E.ι :=
    B.exceptionalComplement_isSchemeTheoreticallyDominant
  let q : pullback j e ⟶ pullback j B.map :=
    pullback.lift (pullback.fst j e) (pullback.snd j e ≫ E.ι)
      (by simpa [e, Category.assoc] using pullback.condition (f := j) (g := e))
  have hq : q ≫ pullback.snd j B.map = pullback.snd j e ≫ E.ι := pullback.lift_snd _ _ _
  let : IsSchemeTheoreticallyDominant (q ≫ pullback.snd j B.map) := by
    rw [hq]
    infer_instance
  exact IsSchemeTheoreticallyDominant.of_comp_right q _

/-- The same base-change statement in the blowup-first pullback convention. -/
theorem BlowupDatum.pullback_fst_isSchemeTheoreticallyDominant
    {X U : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)
    (j : U ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] :
    IsSchemeTheoreticallyDominant (pullback.fst B.map j) := by
  let := B.pullback_snd_isSchemeTheoreticallyDominant j
  have h : IsSchemeTheoreticallyDominant
      ((pullbackSymmetry j B.map).hom ≫ pullback.fst B.map j) := by
    rw [pullbackSymmetry_hom_comp_fst]
    infer_instance
  let := h
  exact IsSchemeTheoreticallyDominant.of_comp_right
    (pullbackSymmetry j B.map).hom (pullback.fst B.map j)

/-- The literal inverse-image open of a quasi-compact schematically dense open
is schematically dense after every native blowup. -/
theorem BlowupDatum.preimage_open_isSchemeTheoreticallyDominant
    {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)
    (U : X.Opens) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι] :
    IsSchemeTheoreticallyDominant (B.map ⁻¹ᵁ U).ι := by
  let := B.pullback_fst_isSchemeTheoreticallyDominant U.ι
  rw [← (isPullback_morphismRestrict B.map U).flip.isoPullback_hom_fst]
  infer_instance

end Scheme.Blowup
end AlgebraicGeometry
