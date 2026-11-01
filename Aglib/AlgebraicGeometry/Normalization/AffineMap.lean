/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Normalization.Affine
public import Aglib.AlgebraicGeometry.Normalization.Relative
public import Aglib.RingTheory.IntegralClosure.ChangeBaseMap

/-! # Original affine-source normalization maps

The existing affine normalization and original source comparison identify the
literal integral closure with native normalization. An original ambient algebra
map then induces a map of those native normalizations with both structural
triangles. No ramified base-change isomorphism is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

section Source

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [QuasiCompact q] [QuasiSeparated q]
  (e : Spec (.of A) ≅ X) (he : e.hom ≫ q = Spec.algebraMap R A)

/-- The original affine-source comparison, using the native normalization once. -/
def integralClosureSourceIso : Spec (.of (integralClosure R A)) ≅ q.normalization :=
  specIntegralClosureNormalizationIso R A ≪≫
    normalizationSourceIso e (Spec.algebraMap R A) q he

@[reassoc (attr := simp)] theorem integralClosureSourceIso_hom_over :
    (integralClosureSourceIso R A q e he).hom ≫ q.fromNormalization =
      Spec.algebraMap R (integralClosure R A) := by
  simp only [integralClosureSourceIso, Iso.trans_hom, Category.assoc,
    normalizationSourceIso_hom_over, specIntegralClosureNormalizationIso_hom_over]

@[reassoc (attr := simp)] theorem integralClosureSourceIso_hom_generic :
    Spec.map (CommRingCat.ofHom (integralClosure R A).val.toRingHom) ≫
      (integralClosureSourceIso R A q e he).hom = e.hom ≫ q.toNormalization := by
  rw [integralClosureSourceIso, Iso.trans_hom, ← Category.assoc,
    specIntegralClosureNormalizationIso_hom_generic, normalizationSourceIso_hom_generic]

end Source

section Map

variable (R T L A : Type u) [CommRing R] [CommRing T] [CommRing L] [CommRing A]
  [Algebra R T] [Algebra R L] [Algebra R A] [Algebra T A] [IsScalarTower R T A]
  (i : L →ₐ[R] A)
  {X Y : Scheme.{u}} (q₀ : X ⟶ Spec (.of R)) (q₁ : Y ⟶ Spec (.of T))
  [QuasiCompact q₀] [QuasiSeparated q₀] [QuasiCompact q₁] [QuasiSeparated q₁]
  (e₀ : Spec (.of L) ≅ X) (e₁ : Spec (.of A) ≅ Y)
  (h₀ : e₀.hom ≫ q₀ = Spec.algebraMap R L)
  (h₁ : e₁.hom ≫ q₁ = Spec.algebraMap T A)

/-- Transport the actual integral-closure map to the original native normalizations. -/
def integralClosureNormalizationMap : q₁.normalization ⟶ q₀.normalization :=
  (integralClosureSourceIso T A q₁ e₁ h₁).inv ≫
    Spec.map (CommRingCat.ofHom (integralClosure.changeBaseMap R T L A i).toRingHom) ≫
      (integralClosureSourceIso R L q₀ e₀ h₀).hom

/-- The complete original affine chart square of the transported map. -/
@[reassoc (attr := simp)] theorem integralClosureNormalizationMap_chart :
    (integralClosureSourceIso T A q₁ e₁ h₁).hom ≫
        integralClosureNormalizationMap R T L A i q₀ q₁ e₀ e₁ h₀ h₁ =
      Spec.map (CommRingCat.ofHom (integralClosure.changeBaseMap R T L A i).toRingHom) ≫
        (integralClosureSourceIso R L q₀ e₀ h₀).hom := by
  simp only [integralClosureNormalizationMap, Iso.hom_inv_id_assoc]

/-- The transported map commutes with the original coefficient-base morphism. -/
@[reassoc] theorem integralClosureNormalizationMap_over :
    integralClosureNormalizationMap R T L A i q₀ q₁ e₀ e₁ h₀ h₁ ≫ q₀.fromNormalization =
      q₁.fromNormalization ≫ Spec.algebraMap R T := by
  rw [← cancel_epi (integralClosureSourceIso T A q₁ e₁ h₁).hom]
  simp only [integralClosureNormalizationMap_chart_assoc,
    integralClosureSourceIso_hom_over, integralClosureSourceIso_hom_over_assoc]
  rw [Spec.map_algHom_algebraMap]
  simp only [Spec.algebraMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (IsScalarTower.algebraMap_eq R T (integralClosure T A)))

/-- The transported map retains the original ambient-source triangle. -/
@[reassoc] theorem integralClosureNormalizationMap_generic :
    e₁.hom ≫ q₁.toNormalization ≫
        integralClosureNormalizationMap R T L A i q₀ q₁ e₀ e₁ h₀ h₁ =
      Spec.map (CommRingCat.ofHom i.toRingHom) ≫ e₀.hom ≫ q₀.toNormalization := by
  rw [← integralClosureSourceIso_hom_generic_assoc T A q₁ e₁ h₁,
    integralClosureNormalizationMap_chart]
  have h : Spec.map (CommRingCat.ofHom (integralClosure T A).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (integralClosure.changeBaseMap R T L A i).toRingHom) =
    Spec.map (CommRingCat.ofHom i.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (integralClosure R L).val.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, h, Category.assoc, integralClosureSourceIso_hom_generic]

end Map

end AlgebraicGeometry.Scheme.Hom
