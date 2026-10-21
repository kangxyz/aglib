/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.HomogeneousTranslation
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.SingularNormalization
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ExtensionPoints

/-!
# Homogeneous translations of the original projective Weierstrass cubic

The homogeneous quotient and Proj maps retain the exact original and translated cubics. The
affine, structural and infinity triangles identify the same native scale-one substitution.
Critical specialization requires the actual point and both gradient equations.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/OriginalCubicTranslation.lean`: source ranges [[34, 570]];
SHA-256 `e632ed2e94958560002dc6bb265bd07c35e94b00885c15cc7698e55178416e4a`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme.OverField

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
namespace WeierstrassCurve.Projective.Translation
open WeierstrassCurve WeierstrassCurve.Projective WeierstrassCurve.CriticalPoint
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equality in the literal homogeneous polynomial ring. -/
lemma shiftPolynomial_cubic (W : WeierstrassCurve k) (r t : k) :
    shiftPolynomial r t W.toProjective.polynomial =
      (translate W r t).toProjective.polynomial := by
  simp [WeierstrassCurve.Projective.polynomial, shiftCoordinates,
    WeierstrassCurve.Affine.evalEval_polynomial, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

lemma unshiftPolynomial_cubic (W : WeierstrassCurve k) (r t : k) :
    shiftPolynomial (-r) (-t) (translate W r t).toProjective.polynomial =
      W.toProjective.polynomial := by
  rw [← shiftPolynomial_cubic W r t, shiftPolynomial_inverse]

/-- Pullback on the literal homogeneous quotient under x ↦ x + r z and y ↦ y + t z. -/
def toTranslatedHomogeneous (W : WeierstrassCurve k) (r t : k) :
    homogeneousCoordinateRing W →+* homogeneousCoordinateRing (translate W r t) :=
  Ideal.quotientMap _ (shiftPolynomial r t) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change shiftPolynomial r t W.toProjective.polynomial ∈ cubicIdeal (translate W r t)
    rw [shiftPolynomial_cubic]
    exact Ideal.subset_span (Set.mem_singleton _))

/-- The inverse homogeneous-quotient pullback with parameters −r and −t. -/
def fromTranslatedHomogeneous (W : WeierstrassCurve k) (r t : k) :
    homogeneousCoordinateRing (translate W r t) →+* homogeneousCoordinateRing W :=
  Ideal.quotientMap _ (shiftPolynomial (-r) (-t)) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change shiftPolynomial (-r) (-t) (translate W r t).toProjective.polynomial ∈ cubicIdeal W
    rw [unshiftPolynomial_cubic]
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] lemma toTranslatedHomogeneous_mk (W : WeierstrassCurve k) (r t : k)
    (p : MvPolynomial (Fin 3) k) :
    toTranslatedHomogeneous W r t (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (shiftPolynomial r t p) := rfl

@[simp] lemma fromTranslatedHomogeneous_mk (W : WeierstrassCurve k) (r t : k)
    (p : MvPolynomial (Fin 3) k) :
    fromTranslatedHomogeneous W r t (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (shiftPolynomial (-r) (-t) p) := rfl

@[simp] lemma toTranslatedHomogeneous_constant (W : WeierstrassCurve k) (r t a : k) :
    toTranslatedHomogeneous W r t (algebraMap k _ a) = algebraMap k _ a := by
  change toTranslatedHomogeneous W r t (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _
  rw [toTranslatedHomogeneous_mk, shiftPolynomial_C]
  rfl

@[simp] lemma fromTranslatedHomogeneous_constant (W : WeierstrassCurve k) (r t a : k) :
    fromTranslatedHomogeneous W r t (algebraMap k _ a) = algebraMap k _ a := by
  change fromTranslatedHomogeneous W r t (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _
  rw [fromTranslatedHomogeneous_mk, shiftPolynomial_C]
  rfl

@[simp] lemma toTranslatedHomogeneous_z (W : WeierstrassCurve k) (r t : k) :
    toTranslatedHomogeneous W r t (WeierstrassCurve.Projective.coordinate W 2) =
      WeierstrassCurve.Projective.coordinate (translate W r t) 2 := by
  simp [WeierstrassCurve.Projective.coordinate, shiftCoordinates]

@[simp] lemma fromTranslatedHomogeneous_z (W : WeierstrassCurve k) (r t : k) :
    fromTranslatedHomogeneous W r t
      (WeierstrassCurve.Projective.coordinate (translate W r t) 2) =
      WeierstrassCurve.Projective.coordinate W 2 := by
  simp [WeierstrassCurve.Projective.coordinate, shiftCoordinates]

/-- The same homogeneous translation as a degree-preserving quotient-ring map. -/
def toTranslatedGraded (W : WeierstrassCurve k) (r t : k) :
    grading W →+*ᵍ grading (translate W r t) where
  __ := toTranslatedHomogeneous W r t
  map_mem := by
    intro n a ha
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    exact Submodule.mem_map.mpr ⟨shiftPolynomial r t p,
      shiftPolynomial_homogeneous r t hp, rfl⟩

/-- The inverse translation as a degree-preserving quotient-ring map. -/
def fromTranslatedGraded (W : WeierstrassCurve k) (r t : k) :
    grading (translate W r t) →+*ᵍ grading W where
  __ := fromTranslatedHomogeneous W r t
  map_mem := by
    intro n a ha
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    exact Submodule.mem_map.mpr ⟨shiftPolynomial (-r) (-t) p,
      shiftPolynomial_homogeneous (-r) (-t) hp, rfl⟩

lemma from_to_graded (W : WeierstrassCurve k) (r t : k) :
    (fromTranslatedGraded W r t).comp (toTranslatedGraded W r t) =
      GradedRingHom.id (grading W) := by
  apply GradedRingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk _ (shiftPolynomial (-r) (-t) (shiftPolynomial r t p)) = _
  rw [shiftPolynomial_inverse]
  rfl

lemma to_from_graded (W : WeierstrassCurve k) (r t : k) :
    (toTranslatedGraded W r t).comp (fromTranslatedGraded W r t) =
      GradedRingHom.id (grading (translate W r t)) := by
  apply GradedRingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk _ (shiftPolynomial r t (shiftPolynomial (-r) (-t) p)) = _
  rw [shiftPolynomial_inverse']
  rfl

end WeierstrassCurve.Projective.Translation
end

end


section

/-! Native Proj maps of the actual homogeneous quotient substitutions. -/
section
open CategoryTheory AlgebraicGeometry
universe u
namespace WeierstrassCurve.Projective.Translation
open WeierstrassCurve WeierstrassCurve.Projective WeierstrassCurve.CriticalPoint
variable {k : Type u} [Field k]

lemma graded_irrelevant_mem {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W) (a : homogeneousCoordinateRing V)
    (ha : a ∈ HomogeneousIdeal.irrelevant (grading V)) :
    f a ∈ HomogeneousIdeal.irrelevant (grading W) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha ⊢
  rw [← GradedRingHom.map_directSumDecompose, ha, map_zero]

lemma irrelevant_le_of_inverse {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W) (g : grading W →+*ᵍ grading V)
    (h : f.comp g = GradedRingHom.id (grading W)) :
    HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f := by
  intro a ha
  have hm := Ideal.mem_map_of_mem f (graded_irrelevant_mem g a ha)
  have he := DFunLike.congr_fun h a
  change f (g a) = a at he
  rwa [he] at hm

lemma toTranslated_irrelevant (W : WeierstrassCurve k) (r t : k) :
    HomogeneousIdeal.irrelevant (grading (translate W r t)) ≤
      (HomogeneousIdeal.irrelevant (grading W)).map (toTranslatedGraded W r t) :=
  irrelevant_le_of_inverse _ _ (to_from_graded W r t)

lemma fromTranslated_irrelevant (W : WeierstrassCurve k) (r t : k) :
    HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading (translate W r t))).map
        (fromTranslatedGraded W r t) :=
  irrelevant_le_of_inverse _ _ (from_to_graded W r t)

/-- The actual Proj morphism from the translated cubic to the original cubic. -/
def translatedProjectiveMap (W : WeierstrassCurve k) (r t : k) :
    scheme (translate W r t) ⟶ scheme W :=
  Proj.map (toTranslatedGraded W r t) (toTranslated_irrelevant W r t)

/-- The actual inverse Proj morphism on the same two cubic presentations. -/
def inverseTranslatedProjectiveMap (W : WeierstrassCurve k) (r t : k) :
    scheme W ⟶ scheme (translate W r t) :=
  Proj.map (fromTranslatedGraded W r t) (fromTranslated_irrelevant W r t)

lemma nativeProjMap_congr {V W : WeierstrassCurve k}
    (f g : grading V →+*ᵍ grading W)
    (hf : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f)
    (hg : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map g)
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- The actual homogeneous coordinate substitutions are inverse scheme maps. -/
def translatedProjectiveIso (W : WeierstrassCurve k) (r t : k) :
    scheme (translate W r t) ≅ scheme W where
  hom := translatedProjectiveMap W r t
  inv := inverseTranslatedProjectiveMap W r t
  hom_inv_id := by
    unfold translatedProjectiveMap inverseTranslatedProjectiveMap
    rw [← Proj.map_comp]
    exact (nativeProjMap_congr _ _ _ (by simp) (to_from_graded W r t)).trans Proj.map_id
  inv_hom_id := by
    unfold translatedProjectiveMap inverseTranslatedProjectiveMap
    rw [← Proj.map_comp]
    exact (nativeProjMap_congr _ _ _ (by simp) (from_to_graded W r t)).trans Proj.map_id

lemma native_away_constant {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W)
    (hc : ∀ a : k, f (algebraMap k _ a) = algebraMap k _ a)
    (r : homogeneousCoordinateRing V) (a : k) :
    HomogeneousLocalization.Away.map f r
      (HomogeneousLocalization.fromZeroRingHom (grading V)
        (Submonoid.powers r) (constToGradeZero V a)) =
    HomogeneousLocalization.fromZeroRingHom (grading W)
      (Submonoid.powers (f r)) (constToGradeZero W a) := by
  let P := Submonoid.powers r
  let Q := Submonoid.powers (f r)
  have hPQ : P ≤ Q.comap f := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  change HomogeneousLocalization.map f hPQ
      (HomogeneousLocalization.mk ⟨0, constToGradeZero V a, 1, one_mem P⟩) =
    HomogeneousLocalization.mk ⟨0, constToGradeZero W a, 1, one_mem Q⟩
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (f (algebraMap k _ a)) ⟨f 1, _⟩ =
    Localization.mk (algebraMap k _ a) ⟨1, _⟩
  simp only [map_one, hc]

/-- Check scalars on the transformed cover, not on a purportedly invariant Y-chart. -/
@[reassoc] lemma nativeProjMap_over {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W)
    (hf : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f)
    (hc : ∀ a : k, f (algebraMap k _ a) = algebraMap k _ a) :
    Proj.map f hf ≫ structureMap V = structureMap W := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change (i : ℕ+) × ↥(grading V (i : ℕ)) at s
  rcases s with ⟨⟨n, hn⟩, ⟨r, hr⟩⟩
  change r ∈ grading V n at hr
  change Proj.awayι (grading W) (f r) (f.map_mem hr) hn ≫
      Proj.map f hf ≫ structureMap V =
    Proj.awayι (grading W) (f r) (f.map_mem hr) hn ≫ structureMap W
  refine (Proj.awayι_comp_map_assoc f hf hn r hr (structureMap V)).trans ?_
  simp only [structureMap, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg (fun g : CommRingCat.of k ⟶
    CommRingCat.of (HomogeneousLocalization.Away (grading W) (f r)) => Spec.map g)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact native_away_constant f hc r a

@[reassoc] lemma translatedProjectiveMap_over (W : WeierstrassCurve k) (r t : k) :
    translatedProjectiveMap W r t ≫ structureMap W = structureMap (translate W r t) :=
  nativeProjMap_over _ _ (toTranslatedHomogeneous_constant W r t)

/-- The arbitrary translation is already defined over the original field. -/
def translatedProjectiveOverIso (W : WeierstrassCurve k) (r t : k) :
    Over.mk (structureMap (translate W r t)) ≅ Over.mk (structureMap W) :=
  Over.isoMk (translatedProjectiveIso W r t) (translatedProjectiveMap_over W r t)

end WeierstrassCurve.Projective.Translation
end

end


section

/-! Exact triangles for the existing affine translation and infinity section. -/
section
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
namespace WeierstrassCurve.Projective.Translation
open WeierstrassCurve WeierstrassCurve.Projective WeierstrassCurve.CriticalPoint
  WeierstrassCurve.CriticalCubic.SingularTranslation
variable {k : Type u} [Field k]

/-- Powers transport is proved with opaque graded-map endpoints. -/
lemma native_powers_le {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W)
    (x : homogeneousCoordinateRing V) (y : homogeneousCoordinateRing W)
    (h : f x = y) : Submonoid.powers x ≤ (Submonoid.powers y).comap f := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp only [map_pow, h]⟩

lemma nativeAwayMap_spec {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W)
    (hf : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f)
    (x : homogeneousCoordinateRing V) (hx : x ∈ grading V 1)
    (y : homogeneousCoordinateRing W) (hy : y ∈ grading W 1) (h : f x = y) :
    Proj.awayι (grading W) y hy (by decide) ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f
        (native_powers_le f x y h))) ≫ Proj.awayι (grading V) x hx (by decide) := by
  subst y
  exact Proj.awayι_comp_map f hf (by decide) x hx

lemma nativeAwayMap_mk {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W)
    (x : homogeneousCoordinateRing V) (hx : x ∈ grading V 1)
    (y : homogeneousCoordinateRing W) (hy : y ∈ grading W 1) (h : f x = y)
    (n : ℕ) (a : homogeneousCoordinateRing V) (ha : a ∈ grading V (n • 1)) :
    HomogeneousLocalization.map f (native_powers_le f x y h)
        (HomogeneousLocalization.Away.mk (grading V) hx n a ha) =
      HomogeneousLocalization.Away.mk (grading W) hy n (f a) (f.map_mem ha) := by
  subst y
  exact HomogeneousLocalization.Away.map_mk f x hx n a ha

lemma translated_z_powers (W : WeierstrassCurve k) (r t : k) :
    Submonoid.powers (WeierstrassCurve.Projective.coordinate W 2) ≤
      (Submonoid.powers (WeierstrassCurve.Projective.coordinate (translate W r t) 2)).comap
        (toTranslatedGraded W r t) :=
  native_powers_le (toTranslatedGraded W r t) _ _ (toTranslatedHomogeneous_z W r t)

/-- The induced degree-zero localization map on the unchanged z chart. -/
def translatedZChartMap (W : WeierstrassCurve k) (r t : k) :
    chartRing W 2 →+* chartRing (translate W r t) 2 :=
  HomogeneousLocalization.map (toTranslatedGraded W r t) (translated_z_powers W r t)

@[reassoc] lemma translatedZChartMap_spec (W : WeierstrassCurve k) (r t : k) :
    chart (translate W r t) 2 ≫ translatedProjectiveMap W r t =
      Spec.map (CommRingCat.ofHom (translatedZChartMap W r t)) ≫ chart W 2 :=
  nativeAwayMap_spec (toTranslatedGraded W r t) (toTranslated_irrelevant W r t)
    _ (coordinate_mem W 2) _ (coordinate_mem (translate W r t) 2)
    (toTranslatedHomogeneous_z W r t)

lemma translatedZChartMap_mk (W : WeierstrassCurve k) (r t : k) (n : ℕ)
    (a : homogeneousCoordinateRing W) (ha : a ∈ grading W (n • 1)) :
    translatedZChartMap W r t
        (HomogeneousLocalization.Away.mk (grading W) (coordinate_mem W 2) n a ha) =
      HomogeneousLocalization.Away.mk (grading (translate W r t))
        (coordinate_mem (translate W r t) 2) n (toTranslatedGraded W r t a)
        ((toTranslatedGraded W r t).map_mem ha) :=
  nativeAwayMap_mk (toTranslatedGraded W r t) _ (coordinate_mem W 2)
    _ (coordinate_mem (translate W r t) 2) (toTranslatedHomogeneous_z W r t) n a ha

lemma dehomogenize_translation (W : WeierstrassCurve k) (r t : k)
    (a : homogeneousCoordinateRing W) :
    dehomogenize (translate W r t) (toTranslatedHomogeneous W r t a) =
      WeierstrassCurve.affineTranslateHom W r t (dehomogenize W a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have he : (dehomogenize (translate W r t)).comp
      ((toTranslatedHomogeneous W r t).comp (Ideal.Quotient.mk _)) =
      (WeierstrassCurve.affineTranslateHom W r t).toRingHom.comp
        ((dehomogenize W).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change dehomogenize (translate W r t)
        (toTranslatedHomogeneous W r t (algebraMap k _ c)) =
        WeierstrassCurve.affineTranslateHom W r t (dehomogenize W (algebraMap k _ c))
      simp
    · intro i
      fin_cases i <;>
        simp [toTranslatedHomogeneous_mk, shiftCoordinates, dehomogenize]
  exact DFunLike.congr_fun he p

lemma translatedZChartMap_dehomogenize (W : WeierstrassCurve k) (r t : k) :
    (fromProjectiveChart (translate W r t)).comp (translatedZChartMap W r t) =
      (WeierstrassCurve.affineTranslateHom W r t).toRingHom.comp (fromProjectiveChart W) := by
  apply RingHom.ext
  intro a
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (coordinate_mem W 2) a
  simp only [RingHom.comp_apply, translatedZChartMap_mk, fromProjectiveChart_mk]
  exact dehomogenize_translation W r t b

/-- The homogeneous map restricts to the already permanent actual affine map. -/
@[reassoc] lemma translatedProjectiveIso_affine (W : WeierstrassCurve k) (r t : k) :
    affineChart (translate W r t) ≫ (translatedProjectiveIso W r t).hom =
      (translatedAffineIso W r t).hom ≫ affineChart W := by
  change (Spec.map (CommRingCat.ofHom (fromProjectiveChart (translate W r t))) ≫
      chart (translate W r t) 2) ≫ translatedProjectiveMap W r t = _
  rw [Category.assoc, translatedZChartMap_spec, ← Category.assoc, ← Spec.map_comp]
  rw [translatedAffineIso_hom, affineChart, ← Category.assoc, ← Spec.map_comp]
  congr 1
  exact congrArg (fun g : chartRing W 2 →+* affineRing (translate W r t) =>
    Spec.map (CommRingCat.ofHom g)) (translatedZChartMap_dehomogenize W r t)

lemma nativeProjMap_infinityPoint {V W : WeierstrassCurve k}
    (f : grading V →+*ᵍ grading W)
    (hf : HomogeneousIdeal.irrelevant (grading W) ≤
      (HomogeneousIdeal.irrelevant (grading V)).map f)
    (hz : f (WeierstrassCurve.Projective.coordinate V 2) = WeierstrassCurve.Projective.coordinate
      W 2) :
    Proj.map f hf (infinityPoint W) = infinityPoint V := by
  apply eq_infinityPoint_of_z_mem
  change f (WeierstrassCurve.Projective.coordinate V 2) ∈ (infinityPoint W).asHomogeneousIdeal
  rw [hz]
  exact infinityPoint_z_mem W

lemma translatedProjectiveMap_infinityPoint (W : WeierstrassCurve k) (r t : k) :
    translatedProjectiveMap W r t (infinityPoint (translate W r t)) = infinityPoint W :=
  nativeProjMap_infinityPoint (toTranslatedGraded W r t) (toTranslated_irrelevant W r t)
    (toTranslatedHomogeneous_z W r t)

/-- Actual section equality, using the original-field base triangle as well as support. -/
@[reassoc] lemma translatedProjectiveIso_infinity (W : WeierstrassCurve k) (r t : k) :
    infinitySection (translate W r t) ≫ (translatedProjectiveIso W r t).hom =
      infinitySection W := by
  let P : AlgebraicGeometry.Scheme.OverField.extensionPointSource (RingHom.id k) ⟶ curveOver W :=
    Over.homMk (infinitySection (translate W r t) ≫ translatedProjectiveMap W r t) (by
      change (infinitySection (translate W r t) ≫ translatedProjectiveMap W r t) ≫
        structureMap W = Spec.map (CommRingCat.ofHom (RingHom.id k))
      rw [Category.assoc, translatedProjectiveMap_over, infinitySection_structure]
      change 𝟙 (Spec (CommRingCat.of k)) = Spec.map (𝟙 (CommRingCat.of k))
      exact (Spec.map_id (CommRingCat.of k)).symm)
  have hp : P.left (IsLocalRing.closedPoint k) = infinityPoint W :=
    translatedProjectiveMap_infinityPoint W r t
  have h := congrArg (fun Q : AlgebraicGeometry.Scheme.OverField.extensionPointSource (RingHom.id
    k) ⟶ curveOver W => Q.left)
    (eq_originOverExtension_of_closedPoint W (RingHom.id k) P hp)
  change infinitySection (translate W r t) ≫ translatedProjectiveMap W r t =
    Spec.map (𝟙 (CommRingCat.of k)) ≫ infinitySection W at h
  rw [Spec.map_id, Category.id_comp] at h
  exact h

end WeierstrassCurve.Projective.Translation
end

end


section

/-! The original singular cubic becomes the literal critical cubic over k. -/
section
open CategoryTheory AlgebraicGeometry
universe u
namespace WeierstrassCurve.Projective.Translation
open WeierstrassCurve WeierstrassCurve.Projective WeierstrassCurve.CriticalPoint
  WeierstrassCurve.CriticalCubic.SingularTranslation
  WeierstrassCurve.CriticalCubic.SingularNormalization
variable {k : Type u} [Field k]

/-- Transport between the literal projective cubics along equality of their equations. -/
def projectiveEquationCastIso (V W : WeierstrassCurve k) (h : V = W) :
    scheme V ≅ scheme W := eqToIso (congrArg (fun U => scheme U) h)

@[reassoc] lemma projectiveEquationCastIso_over (V W : WeierstrassCurve k) (h : V = W) :
    (projectiveEquationCastIso V W h).hom ≫ structureMap W = structureMap V := by
  subst W
  simp [projectiveEquationCastIso]

/-- Equation-equality transport over the unchanged coefficient field. -/
def projectiveEquationCastOverIso (V W : WeierstrassCurve k) (h : V = W) :
    Over.mk (structureMap V) ≅ Over.mk (structureMap W) :=
  Over.isoMk (projectiveEquationCastIso V W h) (projectiveEquationCastIso_over V W h)

@[reassoc] lemma projectiveEquationCastIso_affine (V W : WeierstrassCurve k) (h : V = W) :
    affineChart V ≫ (projectiveEquationCastIso V W h).hom =
      (affineEquationCastIso V W h).hom ≫ affineChart W := by
  subst W
  simp [projectiveEquationCastIso, affineEquationCastIso]

@[reassoc] lemma projectiveEquationCastIso_infinity (V W : WeierstrassCurve k) (h : V = W) :
    infinitySection V ≫ (projectiveEquationCastIso V W h).hom = infinitySection W := by
  subst W
  simp [projectiveEquationCastIso]

@[reassoc] lemma inverseTranslatedProjectiveIso_affine (W : WeierstrassCurve k) (r t : k) :
    affineChart W ≫ (translatedProjectiveIso W r t).inv =
      (translatedAffineIso W r t).inv ≫ affineChart (translate W r t) := by
  apply (cancel_mono (translatedProjectiveIso W r t).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    translatedProjectiveIso_affine, Iso.inv_hom_id_assoc]

@[reassoc] lemma inverseTranslatedProjectiveIso_infinity (W : WeierstrassCurve k) (r t : k) :
    infinitySection W ≫ (translatedProjectiveIso W r t).inv =
      infinitySection (translate W r t) := by
  apply (cancel_mono (translatedProjectiveIso W r t).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    translatedProjectiveIso_infinity]

/-- Original-to-critical orientation; only the actual singular-point equations occur. -/
def originalToCriticalOverIso (W : WeierstrassCurve k) (r t : k)
    (he : W.toAffine.Equation r t)
    (hx : W.toAffine.polynomialX.evalEval r t = 0)
    (hy : W.toAffine.polynomialY.evalEval r t = 0) :
    Over.mk (structureMap W) ≅
      Over.mk (structureMap (CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r))) :=
  (translatedProjectiveOverIso W r t).symm.trans
    (projectiveEquationCastOverIso _ _ (translate_eq_critical W r t he hx hy))

@[reassoc] lemma originalToCriticalOverIso_over (W : WeierstrassCurve k) (r t : k)
    (he : W.toAffine.Equation r t)
    (hx : W.toAffine.polynomialX.evalEval r t = 0)
    (hy : W.toAffine.polynomialY.evalEval r t = 0) :
    (originalToCriticalOverIso W r t he hx hy).hom.left ≫
      structureMap (CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r)) = structureMap W :=
  (originalToCriticalOverIso W r t he hx hy).hom.w

/-- Actual chart triangle to the permanent inverse affine translation. -/
@[reassoc] lemma originalToCriticalOverIso_affine (W : WeierstrassCurve k) (r t : k)
    (he : W.toAffine.Equation r t)
    (hx : W.toAffine.polynomialX.evalEval r t = 0)
    (hy : W.toAffine.polynomialY.evalEval r t = 0) :
    affineChart W ≫ (originalToCriticalOverIso W r t he hx hy).hom.left =
      (translatedAffineIso W r t).inv ≫
        (affineEquationCastIso _ _ (translate_eq_critical W r t he hx hy)).hom ≫
          affineChart (CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r)) := by
  change affineChart W ≫ (translatedProjectiveIso W r t).inv ≫
    (projectiveEquationCastIso _ _ (translate_eq_critical W r t he hx hy)).hom = _
  rw [← Category.assoc, inverseTranslatedProjectiveIso_affine, Category.assoc,
    projectiveEquationCastIso_affine]

@[reassoc] lemma originalToCriticalOverIso_infinity (W : WeierstrassCurve k) (r t : k)
    (he : W.toAffine.Equation r t)
    (hx : W.toAffine.polynomialX.evalEval r t = 0)
    (hy : W.toAffine.polynomialY.evalEval r t = 0) :
    infinitySection W ≫ (originalToCriticalOverIso W r t he hx hy).hom.left =
      infinitySection (CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r)) := by
  change infinitySection W ≫ (translatedProjectiveIso W r t).inv ≫
    (projectiveEquationCastIso _ _ (translate_eq_critical W r t he hx hy)).hom = _
  rw [← Category.assoc, inverseTranslatedProjectiveIso_infinity,
    projectiveEquationCastIso_infinity]

/-- In the reverse direction this is exactly the permanent criticalChart, on the same maps. -/
@[reassoc] lemma originalToCriticalOverIso_inverse_affine
    (W : WeierstrassCurve k) (r t : k)
    (he : W.toAffine.Equation r t)
    (hx : W.toAffine.polynomialX.evalEval r t = 0)
    (hy : W.toAffine.polynomialY.evalEval r t = 0) :
    affineChart (CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r)) ≫
      (originalToCriticalOverIso W r t he hx hy).inv.left =
        criticalChart W r t he hx hy := by
  have hcast : (projectiveEquationCastIso _ _
      (translate_eq_critical W r t he hx hy)).inv =
      (projectiveEquationCastIso _ _ (translate_eq_critical W r t he hx hy).symm).hom := by
    simp [projectiveEquationCastIso]
  change affineChart _ ≫ (projectiveEquationCastIso _ _
    (translate_eq_critical W r t he hx hy)).inv ≫ (translatedProjectiveIso W r t).hom = _
  rw [hcast, ← Category.assoc, projectiveEquationCastIso_affine, Category.assoc,
    translatedProjectiveIso_affine]
  rfl

/-- The original actual singular section is sent to the literal critical origin. -/
@[reassoc] lemma originalToCriticalOverIso_origin (W : WeierstrassCurve k) (r t : k)
    (he : W.toAffine.Equation r t)
    (hx : W.toAffine.polynomialX.evalEval r t = 0)
    (hy : W.toAffine.polynomialY.evalEval r t = 0) :
    (affinePointOver W r t he).left ≫ affineChart W ≫
        (originalToCriticalOverIso W r t he hx hy).hom.left =
      CriticalCubic.originSection k W.a₁ (W.a₂ + 3 * r) ≫
        affineChart (CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r)) := by
  let C := CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r)
  let p : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (affineRing W)) :=
    (affinePointOver W r t he).left
  let f : scheme W ⟶ scheme C := (originalToCriticalOverIso W r t he hx hy).hom.left
  let g : scheme C ⟶ scheme W := (originalToCriticalOverIso W r t he hx hy).inv.left
  have hgf : g ≫ f = 𝟙 (scheme C) := by
    exact congrArg (fun z => z.left) (originalToCriticalOverIso W r t he hx hy).inv_hom_id
  have hchart : affineChart C ≫ g = criticalChart W r t he hx hy :=
    originalToCriticalOverIso_inverse_affine W r t he hx hy
  have hp : CriticalCubic.originSection k W.a₁ (W.a₂ + 3 * r) ≫
      criticalChart W r t he hx hy = p ≫ affineChart W :=
    criticalChart_origin W r t he hx hy
  change p ≫ affineChart W ≫ f =
    CriticalCubic.originSection k W.a₁ (W.a₂ + 3 * r) ≫ affineChart C
  rw [← Category.assoc, ← hp, ← hchart]
  simp only [Category.assoc, hgf, Category.comp_id]


end WeierstrassCurve.Projective.Translation
end

end
