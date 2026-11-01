/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Aglib.RingTheory.IntegralClosure.Equiv

/-! # The literal affine integral closure and relative normalization

The comparison uses the native global-sections chart of relative normalization
and the original `ΓSpecIso`. Both structural maps are retained. No normality,
domain, finiteness, or injectivity assumption is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u


variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap R A))

local instance : IsAffine (f).normalization :=
  isAffine_of_isAffineHom (f).fromNormalization

/-- The original global-section coordinates identify the two literal integral closures. -/
def affineIntegralClosureSectionsEquiv :
    letI := (f).appTop.hom.toAlgebra
    integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of A), ⊤) ≃+* integralClosure R A := by
  letI := (f).appTop.hom.toAlgebra
  exact RingEquiv.mapIntegralClosure
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv (by
      exact congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A))).symm)

/-- Global sections of the native affine normalization are the original integral closure. -/
def affineNormalizationSectionsIso :
    Γ((f).normalization, ⊤) ≅ CommRingCat.of (integralClosure R A) :=
  (f).normalizationObjIso (isAffineOpen_top _) ≪≫
    (affineIntegralClosureSectionsEquiv R A).toCommRingCatIso

set_option backward.isDefEq.respectTransparency false in
private lemma affineNormalizationSectionsIso_hom_val :
    (affineNormalizationSectionsIso R A).hom ≫
      CommRingCat.ofHom (integralClosure R A).val.toRingHom =
    (f).toNormalization.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom := by
  let := (f).appTop.hom.toAlgebra
  rw [affineNormalizationSectionsIso, Iso.trans_hom, Category.assoc]
  change ((f).normalizationObjIso (isAffineOpen_top _)).hom ≫
      (CommRingCat.ofHom (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of A), ⊤)).val.toRingHom ≫
        (Scheme.ΓSpecIso (.of A)).hom) = _
  rw [← Category.assoc]
  congr 1
  calc
    _ = (f).toNormalization.appLE ⊤ ⊤ (by simp) :=
      normalizationObjIso_hom_val (f) (isAffineOpen_top _)
    _ = (f).toNormalization.appTop := ((f).toNormalization.app_eq_appLE).symm

set_option backward.isDefEq.respectTransparency false in
private lemma affineNormalizationSectionsIso_hom_base :
    (f).fromNormalization.appTop ≫ (affineNormalizationSectionsIso R A).hom =
      (Scheme.ΓSpecIso (.of R)).hom ≫
        CommRingCat.ofHom (algebraMap R (integralClosure R A)) := by
  have h := fromNormalization_app (f) (isAffineOpen_top _)
  change (f).fromNormalization.appTop = _ at h
  rw [h, affineNormalizationSectionsIso, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext r
  exact congrArg (fun g : CommRingCat.of Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of A => g r)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A)))

/-- The spectrum of the literal integral closure is the native relative
normalization of the original affine morphism. -/
def specIntegralClosureNormalizationIso :
    Spec (.of (integralClosure R A)) ≅ (f).normalization :=
  Scheme.Spec.mapIso (affineNormalizationSectionsIso R A).op ≪≫
    (f).normalization.isoSpec.symm

@[reassoc (attr := simp)]
theorem specIntegralClosureNormalizationIso_hom_generic :
    Spec.map (CommRingCat.ofHom (integralClosure R A).val.toRingHom) ≫
      (specIntegralClosureNormalizationIso R A).hom = (f).toNormalization := by
  rw [← cancel_mono (f).normalization.isoSpec.hom]
  simp only [specIntegralClosureNormalizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map (CommRingCat.ofHom (integralClosure R A).val.toRingHom) ≫
      Spec.map (affineNormalizationSectionsIso R A).hom = _
  rw [← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact affineNormalizationSectionsIso_hom_val R A

@[reassoc (attr := simp)]
theorem specIntegralClosureNormalizationIso_hom_over :
    (specIntegralClosureNormalizationIso R A).hom ≫ (f).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A))) := by
  rw [← cancel_mono (Spec (.of R)).isoSpec.hom]
  rw [Category.assoc, ← Scheme.isoSpec_hom_naturality (f).fromNormalization]
  simp only [specIntegralClosureNormalizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  change Spec.map (affineNormalizationSectionsIso R A).hom ≫
      Spec.map (f).fromNormalization.appTop = _
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact affineNormalizationSectionsIso_hom_base R A

end AlgebraicGeometry.Scheme.Hom
