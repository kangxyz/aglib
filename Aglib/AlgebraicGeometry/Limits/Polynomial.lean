/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants

/-!
# Polynomial base change and affine-open coordinates

Polynomial extension is a pushout for arbitrary coefficient-ring maps,
so the actual polynomial spectra form the displayed pullback square.
The field-algebra and affine-open chart isomorphisms keep their original
structural constants and both projection equations. No curve or
projective-line object is an input.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing declaration
namespaces, hypotheses, universes, objects, maps, and proofs are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.Polynomial` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`25a14a33f4667ac61dee058751132719a3fc6e678d065859bbbf7223f30bb721`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (constantSection)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
/- Component: PolynomialPullback; declaration bodies preserved. -/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace AlgebraicGeometry.Scheme.Pullback.Polynomial

universe u

/-- Polynomial extension commutes with arbitrary change of coefficient ring. -/
theorem polynomial_isPushout {R A : CommRingCat.{u}} (f : R ⟶ A) :
    IsPushout f (CommRingCat.ofHom (C : R →+* R[X]))
      (CommRingCat.ofHom (C : A →+* A[X]))
      (CommRingCat.ofHom (mapRingHom f.hom)) := by
  let w : CommSq f (CommRingCat.ofHom (C : R →+* R[X]))
      (CommRingCat.ofHom (C : A →+* A[X]))
      (CommRingCat.ofHom (mapRingHom f.hom)) := ⟨by ext r; simp⟩
  apply IsPushout.of_isColimit' w
  apply PushoutCocone.isColimitAux'
  intro s
  refine ⟨CommRingCat.ofHom (eval₂RingHom s.inl.hom (s.inr X)), ?_, ?_, ?_⟩
  · ext a
    change eval₂ s.inl.hom (s.inr X) (C a) = s.inl a
    exact eval₂_C ..
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      change eval₂ s.inl.hom (s.inr X) ((C r).map f.hom) = s.inr (C r)
      rw [map_C, eval₂_C]
      exact ConcreteCategory.congr_hom s.condition r
    · change eval₂ s.inl.hom (s.inr X) (X.map f.hom) = s.inr X
      rw [map_X, eval₂_X]
  · intro m hm₁ hm₂
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      change m (C a) = eval₂ s.inl.hom (s.inr X) (C a)
      rw [eval₂_C]
      exact ConcreteCategory.congr_hom hm₁ a
    · change m X = eval₂ s.inl.hom (s.inr X) X
      rw [eval₂_X]
      have h := ConcreteCategory.congr_hom hm₂ (X : R[X])
      change m (X.map f.hom) = s.inr X at h
      simpa only [map_X] using h

/-- The actual polynomial spectra square is a pullback of schemes. -/
theorem polynomial_isPullback {R A : CommRingCat.{u}} (f : R ⟶ A) :
    IsPullback (Spec.map (CommRingCat.ofHom (C : A →+* A[X])))
      (Spec.map (CommRingCat.ofHom (mapRingHom f.hom)))
      (Spec.map f) (Spec.map (CommRingCat.ofHom (C : R →+* R[X]))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomial_isPushout f)

/-- The polynomial base-change chart, with its actual scheme morphisms. -/
def polynomialPullbackIso {K : Type u} [Field K] (A : CommRingCat.{u}) [Algebra K A] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (C : K →+* K[X]))) ≅ Spec (.of A[X]) :=
  (polynomial_isPullback (CommRingCat.ofHom (algebraMap K A))).isoPullback.symm

@[reassoc (attr := simp)]
theorem polynomialPullbackIso_inv_fst {K : Type u} [Field K]
    (A : CommRingCat.{u}) [Algebra K A] :
    (polynomialPullbackIso (K := K) A).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (C : A →+* A[X])) :=
  (polynomial_isPullback (CommRingCat.ofHom (algebraMap K A))).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem polynomialPullbackIso_inv_snd {K : Type u} [Field K]
    (A : CommRingCat.{u}) [Algebra K A] :
    (polynomialPullbackIso (K := K) A).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap K A))) :=
  (polynomial_isPullback (CommRingCat.ofHom (algebraMap K A))).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.Pullback.Polynomial
end

/- Component: AffineOpenPolynomialPullback; declaration bodies preserved. -/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace AlgebraicGeometry.Scheme.Pullback.Polynomial
universe u
variable {K : Type u} [Field K]

/-- The affine-open chart identifies the structural morphism with actual constants. -/
theorem affineOpen_fromSpec_structure (X : FScheme K) (V : X.left.Opens)
    (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (constantSection X V)) := by
  rw [← cancel_mono (Spec (CommRingCat.of K)).toSpecΓ]
  rw [Category.assoc, Scheme.toSpecΓ_naturality, hV.fromSpec_toSpecΓ_assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  change X.hom.appTop ≫ X.left.presheaf.map (homOfLE le_top).op =
    (Scheme.ΓSpecIso (.of K)).hom ≫
      ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) ≫
        X.left.presheaf.map (homOfLE le_top).op
  simp

/-- Base change of the actual affine line over an arbitrary affine open. -/
theorem affineOpenPolynomial_isPullback (X : FScheme K) (V : X.left.Opens)
    (hV : IsAffineOpen V) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (C : Γ(X.left, V) →+* Γ(X.left, V)[X])) ≫
        hV.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (mapRingHom (constantSection X V))))
      (V.ι ≫ X.hom) (Spec.map (CommRingCat.ofHom (C : K →+* K[X]))) := by
  refine (polynomial_isPullback (CommRingCat.ofHom (constantSection X V))).of_iso
    (Iso.refl _) hV.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι_assoc] using (affineOpen_fromSpec_structure X V hV).symm
  · simp

/-- Actual polynomial base-change chart for any affine open of a field scheme. -/
def affineOpenPolynomialPullbackIso (X : FScheme K) (V : X.left.Opens)
    (hV : IsAffineOpen V) :
    pullback (V.ι ≫ X.hom) (Spec.map (CommRingCat.ofHom (C : K →+* K[X]))) ≅
      Spec (.of Γ(X.left, V)[X]) :=
  (affineOpenPolynomial_isPullback X V hV).isoPullback.symm

@[reassoc (attr := simp)]
theorem affineOpenPolynomialPullbackIso_inv_fst (X : FScheme K) (V : X.left.Opens)
    (hV : IsAffineOpen V) :
    (affineOpenPolynomialPullbackIso X V hV).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (C : Γ(X.left, V) →+* Γ(X.left, V)[X])) ≫
        hV.isoSpec.inv :=
  (affineOpenPolynomial_isPullback X V hV).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem affineOpenPolynomialPullbackIso_inv_snd (X : FScheme K) (V : X.left.Opens)
    (hV : IsAffineOpen V) :
    (affineOpenPolynomialPullbackIso X V hV).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (mapRingHom (constantSection X V))) :=
  (affineOpenPolynomial_isPullback X V hV).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.Pullback.Polynomial
end


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
universe u
namespace AlgebraicGeometry.Scheme.Pullback.Polynomial
variable {K : Type u} [Field K]
/-- Actual affine-open structural coordinates commute with the base map. -/
theorem affineOpen_fromSpec_over (X : FScheme K) (U : X.left.affineOpens) :
    U.2.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (constantSection X U.1)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
    (isAffineOpen_top _) U.2 (show U.1 ≤ X.hom ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm


end AlgebraicGeometry.Scheme.Pullback.Polynomial
