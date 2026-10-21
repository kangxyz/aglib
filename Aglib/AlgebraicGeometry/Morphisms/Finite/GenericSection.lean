/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Generic sections of a finite scheme over an integrally closed domain

The specified map from the fraction field descends uniquely through the
integrally closed base ring. Applied to the coordinate algebra of the same
finite scheme, this gives a section with both original triangles. The finite
scheme need not be integral or connected. The base is an arbitrary integrally
closed domain; no discrete-valuation or Noetherian condition is introduced.

Source: selected declarations at lines 25–130 of
`R5Lab.Aglib.AlgebraicGeometry.Morphisms.Finite.GenericSection`,
R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`388199370d9163a343577a020f2635e375d05156089337407204cc9698c1563e`.
All field, fraction-field, integral-algebra and actual generic-map premises
remain explicit.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace IsIntegrallyClosed

variable {R F A : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A]

omit [IsDomain R] in
/-- Every map from an integral R-algebra to Frac(R) factors uniquely through R. -/
-- Retain the original domain guard on the integral fraction-field retraction interface.
@[nolint unusedArguments]
theorem existsUnique_integral_retraction [IsDomain R] (f : R →+* A) (hf : f.IsIntegral)
    (g : A →+* F) (hg : g.comp f = algebraMap R F) :
    ∃! h : A →+* R, h.comp f = RingHom.id R ∧ (algebraMap R F).comp h = g := by
  let : Algebra R A := f.toAlgebra
  let g' : A →ₐ[R] F := { g with commutes' := fun r => RingHom.congr_fun hg r }
  have hint (a : A) : IsIntegral R (g a) := (show IsIntegral R a from hf a).map g'
  let h : A →+* R :=
    { toFun := fun a => IsIntegralClosure.mk' R (g a) (hint a)
      map_one' := by simp
      map_zero' := by simp
      map_add' := fun a b => by
        apply IsFractionRing.injective R F
        simp only [IsIntegralClosure.algebraMap_mk', map_add]
      map_mul' := fun a b => by
        apply IsFractionRing.injective R F
        simp only [IsIntegralClosure.algebraMap_mk', map_mul] }
  have hh (a : A) : algebraMap R F (h a) = g a :=
    IsIntegralClosure.algebraMap_mk' (R := R) R (g a) (hint a)
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · ext r
    apply IsFractionRing.injective R F
    simpa only [RingHom.comp_apply, RingHom.id_apply, hh] using RingHom.congr_fun hg r
  · ext a
    exact hh a
  · intro h' hh'
    ext a
    apply IsFractionRing.injective R F
    exact (RingHom.congr_fun hh'.2 a).trans (hh a).symm


end IsIntegrallyClosed

namespace AlgebraicGeometry.Scheme.Hom.FiniteSection

variable {R F : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Over an integrally closed affine base, every generic point of a finite
scheme extends uniquely to a section, by integral coordinate descent. -/
theorem existsUnique_section {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsFinite π]
    (g : Spec (.of F) ⟶ X)
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R F))) :
    ∃! h : Spec (.of R) ⟶ X, h ≫ π = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ h = g := by
  wlog hX : ∃ S : CommRingCat.{u}, X = Spec S generalizing X
  · have hAffine : IsAffine X := isAffine_of_isAffineHom π
    obtain ⟨h, hh, huniq⟩ := this (X.isoSpec.inv ≫ π) (g ≫ X.isoSpec.hom)
      (by simpa using hg) ⟨_, rfl⟩
    refine ⟨h ≫ X.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
    · simpa only [Category.assoc] using hh.1
    · rw [← Category.assoc, hh.2]
      simp
    · intro h' hh'
      have he : h' ≫ X.isoSpec.hom = h := huniq _ ⟨by simpa using hh'.1,
        by simp only [← Category.assoc, hh'.2]⟩
      simpa using congrArg (fun f => f ≫ X.isoSpec.inv) he
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective π
  obtain ⟨j, rfl⟩ := Spec.map_surjective g
  have hjf : f ≫ j = CommRingCat.ofHom (algebraMap R F) :=
    Spec.map_injective (by simpa using hg)
  have hint : f.hom.IsIntegral := (IsIntegralHom.SpecMap_iff (φ := f)).mp inferInstance
  obtain ⟨h, hh, huniq⟩ := IsIntegrallyClosed.existsUnique_integral_retraction f.hom hint j.hom
    (congrArg CommRingCat.Hom.hom hjf)
  refine ⟨Spec.map (CommRingCat.ofHom h), ⟨?_, ?_⟩, ?_⟩
  · have he : f ≫ CommRingCat.ofHom h = 𝟙 _ := by
      ext r
      exact RingHom.congr_fun hh.1 r
    simp only [← Spec.map_comp, he, Spec.map_id]
  · have he : CommRingCat.ofHom h ≫ CommRingCat.ofHom (algebraMap R F) = j := by
      ext a
      exact RingHom.congr_fun hh.2 a
    simp only [← Spec.map_comp, he]
  · intro h' hh'
    obtain ⟨k, rfl⟩ := Spec.map_surjective h'
    have hkf : f ≫ k = 𝟙 _ := Spec.map_injective (by simpa using hh'.1)
    have hkg : k ≫ CommRingCat.ofHom (algebraMap R F) = j :=
      Spec.map_injective (by simpa using hh'.2)
    have he : k.hom = h := huniq _ ⟨congrArg CommRingCat.Hom.hom hkf,
      congrArg CommRingCat.Hom.hom hkg⟩
    have : k = CommRingCat.ofHom h := by ext a; exact RingHom.congr_fun he a
    rw [this]


/-- The section constructed by descent of all integral coordinates. -/
def extendedSection {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsFinite π]
    (g : Spec (.of F) ⟶ X)
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R F))) :
    Spec (.of R) ⟶ X := (existsUnique_section π g hg).choose

@[simp, reassoc] theorem extendedSection_over {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [IsFinite π] (g : Spec (.of F) ⟶ X)
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R F))) :
    extendedSection π g hg ≫ π = 𝟙 _ := (existsUnique_section π g hg).choose_spec.1.1

@[simp, reassoc] theorem extendedSection_generic {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [IsFinite π] (g : Spec (.of F) ⟶ X)
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R F))) :
    Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ extendedSection π g hg = g :=
  (existsUnique_section π g hg).choose_spec.1.2

end AlgebraicGeometry.Scheme.Hom.FiniteSection
