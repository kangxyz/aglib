/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.StandardEtaleDomainFactor

/-! # The actual standard etale algebra as a hypersurface open

Both maps use the original standard etale root and the actual quotient and
localization universal properties. The cofactor is inverted because the
original derivative is a unit, not because a new presentation is assumed.
-/

@[expose] public noncomputable section

open Polynomial

namespace StandardEtalePair

variable {R : Type*} [CommRing R] (P : StandardEtalePair R)

/-- The cofactor of a vanishing factor is a unit at the original root. -/
theorem isUnit_aeval_cofactor (p q : R[X]) (hf : P.f = p * q)
    (hp : aeval P.X p = 0) : IsUnit (aeval P.X q) := by
  have h := P.hasMap_X.isUnit_derivative_f
  rw [hf, derivative_mul, map_add, map_mul, map_mul, hp, zero_mul, add_zero] at h
  exact isUnit_of_mul_isUnit_right h

/-- The original factor root defines a map from the same standard etale
pair into its actual factor localization. -/
theorem hasMap_factorLocalization (p q : R[X]) (hf : P.f = p * q)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra (AdjoinRoot p) T]
    [IsScalarTower R (AdjoinRoot p) T]
    [IsLocalization.Away (AdjoinRoot.mk p (P.g * q)) T] :
    P.HasMap (algebraMap (AdjoinRoot p) T (AdjoinRoot.root p)) := by
  constructor
  · rw [hf, map_mul, aeval_algebraMap_apply, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self, map_zero, zero_mul]
  · have hu : IsUnit (aeval (algebraMap (AdjoinRoot p) T (.root p)) (P.g * q)) := by
      rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
      exact IsLocalization.Away.algebraMap_isUnit ..
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu

/-- The complete factor-localization equivalence over the original quotient,
with a variable localization carrier. -/
def equivLocalizationAdjoinRootFactor (p q : R[X]) (hf : P.f = p * q)
    (hp : aeval P.X p = 0) (T : Type*) [CommRing T] [Algebra R T]
    [Algebra (AdjoinRoot p) T] [IsScalarTower R (AdjoinRoot p) T]
    [IsLocalization.Away (AdjoinRoot.mk p (P.g * q)) T] : P.Ring ≃ₐ[R] T := by
  have hq := P.isUnit_aeval_cofactor p q hf hp
  have hunit : IsUnit (aeval P.X (P.g * q)) := by
    rw [map_mul]
    exact P.hasMap_X.2.mul hq
  let z : T := algebraMap (AdjoinRoot p) T (.root p)
  have hmap : P.HasMap z := P.hasMap_factorLocalization p q hf T
  have hpeval : p.eval₂ (Algebra.ofId R P.Ring) P.X = 0 := hp
  have hunit' : IsUnit ((AdjoinRoot.liftAlgHom p (Algebra.ofId R P.Ring) P.X hpeval)
      (AdjoinRoot.mk p (P.g * q))) := hunit
  let F : P.Ring →ₐ[R] T := P.lift z hmap
  let G : T →ₐ[R] P.Ring :=
    IsLocalization.Away.liftAlgHom (AdjoinRoot.mk p (P.g * q))
      (f := AdjoinRoot.liftAlgHom p (Algebra.ofId R P.Ring) P.X hpeval) hunit'
  have hF : F P.X = z := P.lift_X z hmap
  have hG : G z = P.X := by
    change IsLocalization.Away.lift (AdjoinRoot.mk p (P.g * q)) hunit'
      (algebraMap (AdjoinRoot p) T (.root p)) = P.X
    rw [IsLocalization.Away.lift_eq]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  refine .ofAlgHom F G ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (AdjoinRoot.mk p (P.g * q)))
    apply AdjoinRoot.algHom_ext
    change F (G z) = z
    rw [hG, hF]
  · apply P.hom_ext
    change G (F P.X) = P.X
    rw [hF, hG]

/-- The original standard etale algebra is the actual localization of its
factor hypersurface at the original product `g * q`. -/
def equivAwayAdjoinRootFactor (p q : R[X]) (hf : P.f = p * q)
    (hp : aeval P.X p = 0) :
    P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk p (P.g * q)) :=
  P.equivLocalizationAdjoinRootFactor p q hf hp _

@[simp]
theorem equivAwayAdjoinRootFactor_X (p q : R[X]) (hf : P.f = p * q)
    (hp : aeval P.X p = 0) :
    P.equivAwayAdjoinRootFactor p q hf hp P.X =
      algebraMap (AdjoinRoot p) _ (AdjoinRoot.root p) := by
  dsimp only [equivAwayAdjoinRootFactor, equivLocalizationAdjoinRootFactor,
    AlgEquiv.ofAlgHom]
  exact P.lift_X _ (P.hasMap_factorLocalization p q hf _)

end StandardEtalePair

namespace StandardEtalePresentation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The vanishing-factor equation is transported along the original
presentation, without choosing a replacement root. -/
theorem aeval_pair_X_eq_zero (P : StandardEtalePresentation R S)
    (p : R[X]) (hp : aeval P.x p = 0) : aeval P.X p = 0 := by
  apply P.equivRing.symm.injective
  rw [map_zero, ← aeval_algHom_apply, P.equivRing_symm_X]
  exact hp

/-- The actual receiving algebra, not a replacement model, is isomorphic to
the localization of its vanishing factor. -/
def equivAwayAdjoinRootFactor (P : StandardEtalePresentation R S)
    (p q : R[X]) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    S ≃ₐ[R] Localization.Away (AdjoinRoot.mk p (P.g * q)) :=
  P.equivRing.trans (P.P.equivAwayAdjoinRootFactor p q hf (P.aeval_pair_X_eq_zero p hp))

@[simp]
theorem equivAwayAdjoinRootFactor_x (P : StandardEtalePresentation R S)
    (p q : R[X]) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    P.equivAwayAdjoinRootFactor p q hf hp P.x =
      algebraMap (AdjoinRoot p) _ (AdjoinRoot.root p) := by
  simp [equivAwayAdjoinRootFactor]

end StandardEtalePresentation
