/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Charts

/-!
# Coefficient naturality for the original generating-section map

Changing the coefficient ring commutes with the actual projective morphism
defined by the same original module and generating sections. The normalized
coefficients are unchanged; the base coefficient homomorphism is composed with
the given ring homomorphism. Native affine chart coefficient and ratio laws
then identify the original scheme morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type u} {X : Scheme.{u}}

namespace SectionFrames

/-- The original coefficient map on every source open composes with the
given ring homomorphism. -/
theorem baseCoefficient_coefficients (φ : R →+* S)
    (p : X ⟶ Spec (CommRingCat.of S)) (O : X.Opens) :
    baseCoefficient (p ≫ Spec.map (CommRingCat.ofHom φ)) O =
      (baseCoefficient p O).comp φ := by
  unfold baseCoefficient
  ext r
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  have hΓ := congrArg
    (fun f : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of S), ⊤) ↦ f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  exact congrArg (fun z ↦ sectionRestrict X le_top (p.appTop.hom z)) hΓ

variable {M : X.Modules} {s : I → M.sections} (F : SectionFrames M s)

/-- The original chart-ring map changes only its coefficient homomorphism;
all normalized original section ratios remain identical. -/
theorem chartRingHom_coefficients (φ : R →+* S)
    (p : X ⟶ Spec (CommRingCat.of S)) (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    F.chartRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) k hk =
      (F.chartRingHom p k hk).comp (coordinateRingMap φ I (F.coordinate k)) := by
  have hpoly :
      (F.chartRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) k hk).comp
          (polynomialToCoordinateRing R I (F.coordinate k)) =
        ((F.chartRingHom p k hk).comp (coordinateRingMap φ I (F.coordinate k))).comp
          (polynomialToCoordinateRing R I (F.coordinate k)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_C,
        chartRingHom_coefficient, coordinateRingMap_coefficient]
      exact RingHom.congr_fun (baseCoefficient_coefficients φ p O) r
    · intro j
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_X,
        chartRingHom_ratio, coordinateRingMap_ratio]
  have h := congrArg (fun g ↦ g.comp (coordinateRingToPolynomial R I (F.coordinate k))) hpoly
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h

/-- The actual local projective map commutes with the original projective
coefficient morphism. -/
theorem chartMap_coefficients (φ : R →+* S)
    (p : X ⟶ Spec (CommRingCat.of S)) (k : F.K) {O : X.Opens} (hk : O ≤ F.U k) :
    F.chartMap p k hk ≫ ProjectiveSpace.map φ I =
      F.chartMap (p ≫ Spec.map (CommRingCat.ofHom φ)) k hk := by
  have hc : CommRingCat.ofHom
      (F.chartRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) k hk) =
        CommRingCat.ofHom (coordinateRingMap φ I (F.coordinate k)) ≫
          CommRingCat.ofHom (F.chartRingHom p k hk) := by
    apply CommRingCat.hom_ext
    exact F.chartRingHom_coefficients φ p k hk
  unfold chartMap
  rw [hc, Spec.map_comp]
  simp only [Category.assoc]
  rw [coordinateRingMap_awayι]

/-- Coefficient naturality for the same actual supplied section frames. -/
@[reassoc]
theorem map_coefficients (φ : R →+* S) (p : X ⟶ Spec (CommRingCat.of S)) :
    F.map p ≫ ProjectiveSpace.map φ I =
      F.map (p ≫ Spec.map (CommRingCat.ofHom φ)) := by
  apply F.sourceOpenCover.hom_ext
  intro k
  change F.K at k
  change (F.U k).ι ≫ F.map p ≫ ProjectiveSpace.map φ I =
    (F.U k).ι ≫ F.map (p ≫ Spec.map (CommRingCat.ofHom φ))
  rw [F.ι_map_assoc, F.ι_map]
  exact F.chartMap_coefficients φ p k le_rfl

end SectionFrames

/-- Coefficient naturality retains the same original finite generating sections. -/
@[reassoc]
theorem mapOfGeneratingSections_coefficients (φ : R →+* S)
    (p : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules) (hM : IsLocallyRankOne X M)
    (σ : M.GeneratingSections) [σ.IsFiniteType] :
    mapOfGeneratingSections p M hM σ ≫ ProjectiveSpace.map φ σ.I =
      mapOfGeneratingSections (p ≫ Spec.map (CommRingCat.ofHom φ)) M hM σ :=
  (framesOfGeneratingSections M hM σ).map_coefficients φ p

/-- Coefficient naturality for the identical finite epimorphic section family
in the identical actual line module. -/
@[reassoc]
theorem mapOfFiniteFamily_coefficients (φ : R →+* S)
    (p : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules) (hM : IsLocallyRankOne X M)
    [Finite I] (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    [Epi (Sigma.desc s)] :
    mapOfFiniteFamily p M hM s ≫ ProjectiveSpace.map φ I =
      mapOfFiniteFamily (p ≫ Spec.map (CommRingCat.ofHom φ)) M hM s :=
  mapOfGeneratingSections_coefficients φ p M hM (generatingSectionsOfFamily s)

namespace LineSource

/-- The original line-source family has the same coefficient naturality,
with its canonical coefficient module and sections unchanged. -/
@[reassoc]
theorem mapOfFamily_coefficients (φ : R →+* S) (D J : X.Modules)
    (hD : IsLocallyRankOne X D) (p : X ⟶ Spec (CommRingCat.of S))
    (hJ : IsLocallyRankOne X J) [Finite I] (d : I → (D ⟶ J))
    [Epi (Sigma.desc d)] :
    mapOfFamily D J hD p hJ d ≫ ProjectiveSpace.map φ I =
      mapOfFamily D J hD (p ≫ Spec.map (CommRingCat.ofHom φ)) hJ d :=
  mapOfFiniteFamily_coefficients φ p (coefficientModule D J)
    (coefficientModule_locallyRankOne D J hD hJ)
    (fun i ↦ sectionOfHom D J hD (d i))

end LineSource

end AlgebraicGeometry.ProjectiveSpace.FromSections
