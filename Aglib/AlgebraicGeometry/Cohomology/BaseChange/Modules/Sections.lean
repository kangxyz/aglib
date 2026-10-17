/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.OpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Canonical module sections after arbitrary affine base change

The comparison is the scalar-adjunction transpose of the original geometric
pullback unit on every open. For quasicoherent coefficients it is invertible
on every affine open, for an arbitrary homomorphism of commutative rings.
No flatness, Noetherianity or finiteness assumption is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- The actual structural ring maps commute in a square over a map of spectra. -/
theorem moduleSectionsBaseChangeScalars (p : Y ⟶ X)
    (q : Y ⟶ Spec (CommRingCat.of B)) (f : X ⟶ Spec (CommRingCat.of A))
    (σ : A →+* B) (w : p ≫ f = q ≫ Spec.map (CommRingCat.ofHom σ)) :
    p.appTop.hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).comp σ := by
  have hw := congrArg (fun z : Y ⟶ Spec (CommRingCat.of A) => z.appTop) w
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hw
  have h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫ p.appTop =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ q.appTop := by
    rw [hw, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg CommRingCat.Hom.hom h

/-- A supplied affine fibre square gives the pushout of its actual structural ring maps.
Affineness of `Y` is retained as the affine-square family guard,
though this proof does not use it. -/
theorem moduleSectionsBaseChange_isPushout (p : Y ⟶ X)
    (q : Y ⟶ Spec (CommRingCat.of B)) (f : X ⟶ Spec (CommRingCat.of A))
    (σ : A →+* B) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    [IsAffine X] [_affineY : IsAffine Y] :
    IsPushout
      (CommRingCat.ofHom (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
      (CommRingCat.ofHom σ) p.appTop
      (CommRingCat.ofHom (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) := by
  refine (AlgebraicGeometry.isPushout_appTop_of_isPullback h).of_iso
    (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of B)) (Iso.refl _) ?_ ?_ ?_ ?_
  · change f.appTop ≫ 𝟙 _ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop
    simp
  · rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv]
    simp only [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp
  · change q.appTop ≫ 𝟙 _ = (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ q.appTop
    simp

/-- In a supplied fibre square over spectra, the original tensor comparison is
invertible on every affine open of the original scheme. -/
theorem moduleSectionsTensorComparison_isIso_app_of_isPullback
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((moduleSectionsTensorComparison p
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) σ
      (moduleSectionsBaseChangeScalars p q f σ h.w) M).app (op U)) := by
  let a := (p ⁻¹ᵁ U).ι
  let b := p ∣_ U
  let j := U.ι
  let hopen := (isPullback_morphismRestrict p U).flip
  let hlocal := (hopen.paste_horiz h.flip).flip
  let : IsAffine U.toScheme := hU
  let : IsAffine (p ⁻¹ᵁ U).toScheme := IsAffine.of_isPullback hlocal
  have hpush := moduleSectionsBaseChange_isPushout b (a ≫ q) (j ≫ f) σ hlocal
  have hpush' : IsPushout
      (CommRingCat.ofHom (j.appTop.hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)))
      (CommRingCat.ofHom σ) b.appTop
      (CommRingCat.ofHom (a.appTop.hom.comp
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom))) := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc] using hpush
  have H := moduleSectionsTensorComparison_isIso_app_of_isAffine a b p j hopen
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) σ
    (moduleSectionsBaseChangeScalars p q f σ h.w) hpush' M
  have hj : j.opensRange = U := Scheme.Opens.opensRange_ι U
  rw [hj] at H
  exact H

/-- The canonical section tensor transformation on the actual fibre product,
formed using the original module pullback unit and structural ring maps. -/
def moduleSectionsBaseChangeMap (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (M : X.Modules) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    moduleSectionsPresheaf X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) M ⋙
      ModuleCat.extendScalars σ ⟶
        (Opens.map p.base).op ⋙ moduleSectionsPresheaf
          (pullback f (Spec.map (CommRingCat.ofHom σ)))
          (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
          ((Scheme.Modules.pullback p).obj M) :=
  moduleSectionsTensorComparison _ _ _ σ
    (moduleSectionsBaseChangeScalars _ _ f σ pullback.condition) M

/-- On every original open, the canonical forward map sends a unit pure tensor
to the original geometric pullback unit on that open. -/
theorem moduleSectionsBaseChangeMap_one_tmul (f : X ⟶ Spec (CommRingCat.of A))
    (σ : A →+* B) (M : X.Modules) (U : X.Opens)
    (m : (moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) M).obj (op U)) :
    (moduleSectionsBaseChangeMap f σ M).app (op U) ((1 : B) ⊗ₜ[A,σ] m) =
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).unit.app M).app U) m :=
  moduleSectionsTensorComparison_one_tmul _ _ _ _ _ M U m

/-- Arbitrary affine base change commutes with the actual sections of a
quasicoherent module on every affine open. -/
theorem moduleSectionsBaseChangeMap_isIso_app (f : X ⟶ Spec (CommRingCat.of A))
    (σ : A →+* B) (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((moduleSectionsBaseChangeMap f σ M).app (op U)) :=
  moduleSectionsTensorComparison_isIso_app_of_isPullback _ _ f σ
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom σ))) M U hU

end AlgebraicGeometry.Scheme.Cohomology
