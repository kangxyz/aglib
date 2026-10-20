/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.CoordinateOverlap`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `fc75f6591c34c077c4e95f3ce15ed3a77b977054186de532848280f72eb78ddc`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Affine blowup overlap transport under ring isomorphisms

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section AlgebraicGeometry.Scheme.Blowup.Coordinates


/-!
Literal principal-open overlaps after changing affine chart coordinates.
All intersections are derived from the approved atlas overlap law. Neither
intersection coverage nor compatibility with the blowup is an extra premise.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup
namespace AlgebraicGeometry.Scheme.Blowup.Coordinates

variable {C D : Type u} [CommRing C] [CommRing D]

def specIso (e : C ≃+* D) : Spec (.of C) ≅ Spec (.of D) :=
  Scheme.Spec.mapIso e.symm.toCommRingCatIso.op

def awayMap (r : C) : Spec (.of (Localization.Away r)) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r)))

instance awayMap_isOpenImmersion (r : C) : IsOpenImmersion (awayMap r) := by
  dsimp [awayMap]; infer_instance

def awayEquiv (e : C ≃+* D) (r : C) (s : D) (h : e r = s) :
    Localization.Away r ≃+* Localization.Away s :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers r)
    (T := Submonoid.powers s) (Localization.Away r) (Localization.Away s) e (by simp [← h])

@[simp] lemma awayEquiv_base (e : C ≃+* D) (r : C) (s : D) (h : e r = s) (z : C) :
    awayEquiv e r s h (algebraMap C _ z) = algebraMap D _ (e z) := by
  simp [awayEquiv]

@[simp] lemma awayEquiv_symm_base (e : C ≃+* D) (r : C) (s : D)
    (h : e r = s) (z : D) :
    (awayEquiv e r s h).symm (algebraMap D _ z) = algebraMap C _ (e.symm z) := by
  apply (awayEquiv e r s h).injective
  simp

@[reassoc] lemma awaySpecIso_triangle (e : C ≃+* D) (r : C) (s : D) (h : e r = s) :
    (specIso (awayEquiv e r s h)).hom ≫ awayMap s =
      awayMap r ≫ (specIso e).hom := by
  change Spec.map (CommRingCat.ofHom (awayEquiv e r s h).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap D _)) =
      Spec.map (CommRingCat.ofHom (algebraMap C _)) ≫
        Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact awayEquiv_symm_base e r s h


variable {A : Type u} [CommRing A] {I : Ideal A}
variable {B : BlowupDatum (affineCenter A I)}
variable (H : AffineAtlas A I B) (a b : I)
variable (e : C ≃+* affineBlowupAlgebra A I a)
variable (f : D ≃+* affineBlowupAlgebra A I b)

/-- The chart map in the chosen concrete ring coordinates. -/
def chart : Spec (.of C) ⟶ B.Y := (specIso e).hom ≫ H.chart a

instance chart_isOpenImmersion : IsOpenImmersion (chart H a e) := by
  let := H.openImmersion a
  dsimp [chart]; infer_instance

/-- Exact principal-open intersection in the concrete chart, proved by
transport through the literal saturated localization. -/
lemma overlap_range (r : C) (hr : e r = ratio A I a b) :
    Set.range (awayMap r ≫ chart H a e) =
      Set.range (chart H a e) ∩ Set.range (chart H b f) := by
  rw [chart, ← Category.assoc, ← awaySpecIso_triangle e r _ hr, Category.assoc]
  change Set.range ((specIso (awayEquiv e r _ hr)).hom ≫
    affineOverlapMap A I a b ≫ H.chart a) = _
  rw [Scheme.Hom.Range.range_iso_comp, H.overlap]
  simp only [chart, Scheme.Hom.Range.range_iso_comp]

/-- Actual scheme transition between the two concrete localizations, over
the same blowup. The domain rings and inverted elements are literal. -/
def overlapIso (r : C) (s : D)
    (hr : e r = ratio A I a b) (hs : f s = ratio A I b a) :
    Spec (.of (Localization.Away r)) ≅ Spec (.of (Localization.Away s)) :=
  IsOpenImmersion.isoOfRangeEq
    (awayMap r ≫ chart H a e) (awayMap s ≫ chart H b f)
    (by rw [overlap_range H a b e f r hr, overlap_range H b a f e s hs, Set.inter_comm])

@[reassoc] lemma overlapIso_hom_triangle (r : C) (s : D)
    (hr : e r = ratio A I a b) (hs : f s = ratio A I b a) :
    (overlapIso H a b e f r s hr hs).hom ≫ awayMap s ≫ chart H b f =
      awayMap r ≫ chart H a e :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc] lemma overlapIso_inv_triangle (r : C) (s : D)
    (hr : e r = ratio A I a b) (hs : f s = ratio A I b a) :
    (overlapIso H a b e f r s hr hs).inv ≫ awayMap r ≫ chart H a e =
      awayMap s ≫ chart H b f :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

end AlgebraicGeometry.Scheme.Blowup.Coordinates

end
end AlgebraicGeometry.Scheme.Blowup.Coordinates
