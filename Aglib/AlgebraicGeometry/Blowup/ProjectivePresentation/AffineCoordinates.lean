/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation
public import Aglib.AlgebraicGeometry.Blowup.IdealFrames
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitEndomorphisms
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality

/-!
# Original affine coordinates of the tautological blowup quotient

On the original saturated chart with denominator `a`, the canonical
tautological quotient sends the original ideal element `b` to `b / a`
times the original denominator frame. The proof cancels the ideal
inclusion only after its pullback through that open chart.

Pulling the proved equality through any further affine morphism gives the
same ratio formula for the pulled invertible module. No monomorphism of
the further pulled ideal inclusion, flatness, or Cartier property of a
new image ideal is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineCoordinates

private theorem pullbackSection_comp_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (i : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    pullbackSection f s ≫ (Modules.pullback f).map i ≫ (pullbackUnitIso f).hom =
      pullbackUnitEnd f (s ≫ i) := by
  simp only [pullbackSection, pullbackUnitEnd, Functor.map_comp, Category.assoc]

private theorem pullbackSection_precomp_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules}
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    pullbackSection f (t ≫ s) = pullbackUnitEnd f t ≫ pullbackSection f s := by
  simp only [pullbackSection, pullbackUnitEnd, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

private theorem pullbackUnitEnd_affineMultiplication {S T : Type u}
    [CommRing S] [CommRing T] (φ : S →+* T) (s : S) :
    pullbackUnitEnd (Spec.map (CommRingCat.ofHom φ))
        (IdealFrames.affineMultiplication S s) =
      IdealFrames.affineMultiplication T (φ s) := by
  rw [pullbackUnitEnd, IdealFrames.affineMultiplication_pullback, Iso.inv_hom_id_assoc]

section Tautological

variable {X : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I)

/-- The original tautological quotient retains the actual ideal inclusion. -/
@[reassoc]
theorem tautologicalQuotient_inclusion :
    tautologicalQuotient B ≫ idealInclusion (I.comap B.map).subschemeι =
      (Modules.pullback B.map).map (idealInclusion I.subschemeι) ≫
        (pullbackUnitIso B.map).hom :=
  idealPullbackMap_inclusion I.subschemeι (I.comap B.map).subschemeι B.map
    (centreMap B) (centreMap_ι B)

/-- The actual tautological section associated to an original ideal-module section. -/
def tautologicalSection (s : SheafOfModules.unit X.ringCatSheaf ⟶
    idealModule I.subschemeι) :
    SheafOfModules.unit B.Y.ringCatSheaf ⟶ (tautologicalLine B).val :=
  pullbackSection B.map s ≫ tautologicalQuotient B

/-- The image of the actual quotient section is the original pulled scalar. -/
@[reassoc]
theorem tautologicalSection_inclusion
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ idealModule I.subschemeι) :
    tautologicalSection B s ≫ idealInclusion (I.comap B.map).subschemeι =
      pullbackUnitEnd B.map (s ≫ idealInclusion I.subschemeι) := by
  rw [tautologicalSection, Category.assoc, tautologicalQuotient_inclusion]
  exact pullbackSection_comp_unit B.map s (idealInclusion I.subschemeι)

end Tautological

section AffineIdeal

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Multiplication by an original ideal element, valued in the original quotient kernel. -/
def kernelSection (b : I) : A →ₗ[A] RingHom.ker (Ideal.Quotient.mk I) :=
  LinearMap.toSpanSingleton A _ ⟨(b : A), by
    change Ideal.Quotient.mk I (b : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr b.property⟩

/-- The actual ideal-module section of the original affine centre. -/
def idealSection (b : I) :
    SheafOfModules.unit (Spec (.of A)).ringCatSheaf ⟶
      idealModule (affineCenter A I).subschemeι := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (tildeSelf (R := CommRingCat.of A)).inv ≫
    tilde.map (ModuleCat.ofHom (kernelSection A I b)) ≫
      (affineIdealIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom ≫
        (IdealFrames.imageIdealIso q).hom

/-- The original affine ideal section has multiplication by `b` as its literal image. -/
@[reassoc]
theorem idealSection_inclusion (b : I) :
    idealSection A I b ≫ idealInclusion (affineCenter A I).subschemeι =
      IdealFrames.affineMultiplication A (b : A) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have he : ModuleCat.ofHom (kernelSection A I b) ≫
      ModuleCat.ofHom (RingHom.ker (Ideal.Quotient.mk I)).subtype =
        ModuleCat.ofHom (LinearMap.mulLeft A (b : A)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r * (b : A) = (b : A) * r
    exact mul_comm _ _
  have ht :
      (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom (kernelSection A I b)) ≫
        (tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (RingHom.ker (Ideal.Quotient.mk I)).subtype) =
      (tilde.functor (CommRingCat.of A)).map
        (ModuleCat.ofHom (LinearMap.mulLeft A (b : A))) :=
    ((tilde.functor (CommRingCat.of A)).map_comp _ _).symm.trans
      (congrArg (tilde.functor (CommRingCat.of A)).map he)
  change ((tildeSelf (R := CommRingCat.of A)).inv ≫
      tilde.map (ModuleCat.ofHom (kernelSection A I b)) ≫
        (affineIdealIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom ≫
          (IdealFrames.imageIdealIso q).hom) ≫ idealInclusion q.imageι = _
  simp only [Category.assoc]
  rw [IdealFrames.imageIdealIso_hom_inclusion, affineIdealIso_hom_inclusion]
  exact (Category.id_comp _).trans ht

end AffineIdeal

section BlowupChart

variable {A : Type u} [CommRing A] {I : Ideal A}
  (B : BlowupDatum (affineCenter A I))

/-- The original quotient section on its original saturated affine chart. -/
def chartSection (a b : I) :
    SheafOfModules.unit (Spec (.of (affineBlowupAlgebra A I a))).ringCatSheaf ⟶
      (Modules.pullback (IdealFrames.chartMap B a)).obj (tautologicalLine B).val :=
  pullbackSection (IdealFrames.chartMap B a)
    (tautologicalSection B (idealSection A I b))

/-- Before any further scalar change, the quotient section has its original scalar image. -/
@[reassoc]
theorem chartSection_inclusion (a b : I) :
    chartSection B a b ≫ (Modules.pullback (IdealFrames.chartMap B a)).map
        (idealInclusion (IdealFrames.centreι B)) ≫
        (pullbackUnitIso (IdealFrames.chartMap B a)).hom =
      IdealFrames.affineMultiplication (affineBlowupAlgebra A I a)
        (algebraMap A (affineBlowupAlgebra A I a) (b : A)) := by
  have hs : tautologicalSection B (idealSection A I b) ≫
      idealInclusion (IdealFrames.centreι B) =
        pullbackUnitEnd B.map (IdealFrames.affineMultiplication A (b : A)) :=
    (tautologicalSection_inclusion B (idealSection A I b)).trans
      (congrArg (pullbackUnitEnd B.map) (idealSection_inclusion A I b))
  have hc : IdealFrames.chartMap B a ≫ B.map = affineChartMap A I a :=
    (affineAtlas B).triangle a
  rw [chartSection, pullbackSection_comp_unit, hs, ← pullbackUnitEnd_comp, hc]
  exact pullbackUnitEnd_affineMultiplication
    (algebraMap A (affineBlowupAlgebra A I a)) (b : A)

/-- The original saturated ratio satisfies its literal denominator equation. -/
theorem ratio_mul_denominator (a b : I) :
    ratio A I a b * algebraMap A (affineBlowupAlgebra A I a) (a : A) =
      algebraMap A (affineBlowupAlgebra A I a) (b : A) := by
  apply Subtype.ext
  exact Localization.Away.fraction_mul_self (a : A) (b : A)

/-- The original canonical quotient sends `b` to `b / a` in the denominator frame.
The only cancelled ideal inclusion is pulled through the original open immersion. -/
theorem chartSection_eq_ratio (a b : I) :
    chartSection B a b =
      IdealFrames.affineMultiplication (affineBlowupAlgebra A I a) (ratio A I a b) ≫
        (IdealFrames.chartFrame B a).hom := by
  let : IsOpenImmersion (IdealFrames.chartMap B a) := (affineAtlas B).openImmersion a
  let : Mono ((Modules.pullback (IdealFrames.chartMap B a)).map
      (idealInclusion (IdealFrames.centreι B))) :=
    IdealFrames.idealInclusion_pullback_mono B (IdealFrames.chartMap B a)
  apply (cancel_mono ((Modules.pullback (IdealFrames.chartMap B a)).map
    (idealInclusion (IdealFrames.centreι B)))).mp
  apply (cancel_mono (pullbackUnitIso (IdealFrames.chartMap B a)).hom).mp
  simp only [Category.assoc]
  rw [chartSection_inclusion, IdealFrames.chartFrame_inclusion]
  change IdealFrames.affineMultiplication (affineBlowupAlgebra A I a)
      (algebraMap A (affineBlowupAlgebra A I a) (b : A)) =
    IdealFrames.affineMultiplication (affineBlowupAlgebra A I a) (ratio A I a b) ≫
      IdealFrames.affineMultiplication (affineBlowupAlgebra A I a)
        (algebraMap A (affineBlowupAlgebra A I a) (a : A))
  rw [IdealFrames.affineMultiplication_comp, ratio_mul_denominator]

/-- The same original quotient section pulled through an arbitrary further affine map. -/
def chartSectionAfterMap (a b : I) (T : Type u) [CommRing T]
    (φ : affineBlowupAlgebra A I a →+* T) :
    SheafOfModules.unit (Spec (.of T)).ringCatSheaf ⟶
      (Modules.pullback (Spec.map (CommRingCat.ofHom φ) ≫ IdealFrames.chartMap B a)).obj
        (tautologicalLine B).val :=
  pullbackSection (Spec.map (CommRingCat.ofHom φ)) (chartSection B a b) ≫
    (pullbackComp (Spec.map (CommRingCat.ofHom φ)) (IdealFrames.chartMap B a)).hom.app
      (tautologicalLine B).val

/-- Arbitrary further pullback retains the original ratio in the pulled frame.
No ideal inclusion after this scalar change is cancelled. -/
theorem chartSectionAfterMap_eq_ratio (a b : I) (T : Type u) [CommRing T]
    (φ : affineBlowupAlgebra A I a →+* T) :
    chartSectionAfterMap B a b T φ =
      IdealFrames.affineMultiplication T (φ (ratio A I a b)) ≫
        (IdealFrames.chartFrameAfterMap B a T φ).hom := by
  rw [chartSectionAfterMap, chartSection_eq_ratio, pullbackSection_precomp_unit,
    pullbackUnitEnd_affineMultiplication]
  simp only [IdealFrames.chartFrameAfterMap, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, pullbackSection, Category.assoc]
  rfl

end BlowupChart

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineCoordinates
