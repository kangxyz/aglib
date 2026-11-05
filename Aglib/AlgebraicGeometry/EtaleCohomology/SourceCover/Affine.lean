/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineCoefficientTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.StandardSmoothModuleVanishing
public import Aglib.AlgebraicGeometry.Limits.Polynomial

/-! # Full-test vanishing on the original arbitrary affine coefficient source

The accepted standard-smooth theorem already allows an arbitrary top-left
scheme and actual cartesian square. Only the coefficient-source scheme needs
its original affine isomorphism, handled by the existing genuine module
transport. No finite-type hypothesis on the coefficient-source arrow is added.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Positive higher-image vanishing on the original arbitrary affine source,
with genuine injectivity, original cartesian maps and natural degree retained. -/
theorem higherDirectImage_standardSmooth_affine_injective_positive_isZero
    {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    {U Y : Scheme.{u}} [IsAffine U]
    (f : U ⟶ Spec (.of A)) (a : Y ⟶ Spec (.of C)) (b : Y ⟶ U)
    (H : IsPullback a b (Spec.algebraMap A C) f)
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf U (ULift.{u + 1} (ZMod n))) [Injective I] :
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj I))) := by
  let B : Type u := Γ(U, ⊤)
  let e : U ≅ Spec (.of B) := U.isoSpec
  let φ : A →+* B := (Spec.preimage (e.inv ≫ f)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = e.inv ≫ f := Spec.map_preimage (e.inv ≫ f)
  have H' : IsPullback a (b ≫ e.hom) (Spec.algebraMap A C)
      (Spec.map (CommRingCat.ofHom φ)) := by
    rw [hφ]
    exact H.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact higherDirectImage_injective_isZero_of_coefficient_iso a b e
    (ULift.{u + 1} (ZMod n)) q
    (fun J _ => higherDirectImage_standardSmooth_injective_positive_isZero
      φ a (b ≫ e.hom) H' q hq n hn hunit J) I

/-- In particular the actual polynomial line square has full-test positive
vanishing for every original affine coefficient source, without a finite-type condition. -/
theorem higherDirectImage_polynomial_affine_injective_positive_isZero
    {A : Type u} [CommRing A] {U Y : Scheme.{u}} [IsAffine U]
    (f : U ⟶ Spec (.of A)) (a : Y ⟶ Spec (.of (Polynomial A))) (b : Y ⟶ U)
    (H : IsPullback a b (Spec.algebraMap A (Polynomial A)) f)
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf U (ULift.{u + 1} (ZMod n))) [Injective I] :
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj I))) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 A
      (MvPolynomial PUnit.{u + 1} A) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial A PUnit.{u + 1}
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 A (Polynomial A) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv A PUnit.{u + 1})
  exact higherDirectImage_standardSmooth_affine_injective_positive_isZero
    f a b H q hq n hn hunit I

end AlgebraicGeometry.Scheme.EtaleCohomology
