/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIsomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Fixed-degree higher-image vanishing with affine coefficients

Transport along the actual affine isomorphism uses the genuine module inverse
image and its original underlying comparison. The higher-image morphism and
coefficient on the original scheme remain unchanged. The arithmetic statement
reduces an arbitrary affine finite-type coefficient scheme to its section ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- The original pulled-back coefficient after a genuine module transport
along a scheme isomorphism. -/
def inverseImageModuleIsoCoefficient
    {X S T : Scheme.{u}} (b : X ⟶ S) (e : S ≅ T)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf S Λ) :
    (inverseImage (b ≫ e.hom)).obj
        ((SheafOfModules.toSheaf (constantRing T Λ)).obj
          ((moduleInverseImage e.inv Λ).obj I)) ≅
      (inverseImage b).obj ((SheafOfModules.toSheaf (constantRing S Λ)).obj I) := by
  let M := (SheafOfModules.toSheaf (constantRing S Λ)).obj I
  exact (inverseImage (b ≫ e.hom)).mapIso
      ((moduleInverseImageUnderlyingIso Λ e.inv).app I) ≪≫
    ((inverseImageComp e.inv (b ≫ e.hom)).app M).symm ≪≫
    eqToIso (congrArg (fun f => (inverseImage f).obj M) (by simp))

/-- Fixed-degree injective vanishing is invariant under an isomorphism of the
coefficient scheme, with the original higher-image arrow untouched. -/
theorem higherDirectImage_injective_isZero_of_coefficient_iso
    {X Y S T : Scheme.{u}} (a : Y ⟶ X) (b : Y ⟶ S) (e : S ≅ T)
    (Λ : Type (u + 1)) [Ring Λ] (q : ℕ)
    (hvan : ∀ (J : ModuleSheaf T Λ) [Injective J],
      IsZero ((higherDirectImage a q).obj ((inverseImage (b ≫ e.hom)).obj
        ((SheafOfModules.toSheaf (constantRing T Λ)).obj J))))
    (I : ModuleSheaf S Λ) [Injective I] :
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing S Λ)).obj I))) := by
  let : (moduleInverseImage e.inv Λ).IsEquivalence :=
    moduleInverseImage_isEquivalence_of_iso Λ e.symm
  let J := (moduleInverseImage e.inv Λ).obj I
  let : Injective J := (moduleInverseImage e.inv Λ).injective_obj I
  exact (hvan J).of_iso
    ((higherDirectImage a q).mapIso (inverseImageModuleIsoCoefficient b e Λ I)).symm

/-- A uniform arithmetic-spectra vanishing theorem in a fixed degree extends
to the original arbitrary affine finite-type coefficient scheme. -/
theorem higherDirectImage_injective_isZero_of_affine_coefficient
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    {X Y U : Scheme.{u}} [IsAffine U]
    (p : X ⟶ Spec (.of R)) (a : Y ⟶ X) (b : Y ⟶ U)
    (j : U ⟶ Spec (.of R)) [LocallyOfFiniteType j]
    (H : IsPullback a b p j) (Λ : Type (u + 1)) [Ring Λ] (q : ℕ)
    (hvan : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType ℤ S]
      (b' : Y ⟶ Spec (.of S)), IsPullback a b' p (Spec.algebraMap R S) →
      ∀ (J : ModuleSheaf (Spec (.of S)) Λ) [Injective J],
        IsZero ((higherDirectImage a q).obj ((inverseImage b').obj
          ((SheafOfModules.toSheaf (constantRing (Spec (.of S)) Λ)).obj J))))
    (I : ModuleSheaf U Λ) [Injective I] :
    IsZero ((higherDirectImage a q).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing U Λ)).obj I))) := by
  let S : Type u := Γ(U, ⊤)
  let e : U ≅ Spec (.of S) := U.isoSpec
  let φ : R →+* S := (Spec.preimage (e.inv ≫ j)).hom
  let : Algebra R S := φ.toAlgebra
  have hφ : φ.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  let : Algebra.FiniteType R S := RingHom.finiteType_algebraMap.mp hφ
  let : IsScalarTower ℤ R S := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : Algebra.FiniteType ℤ S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ R) (inferInstance : Algebra.FiniteType R S)
  have hβ : Spec.algebraMap R S = e.inv ≫ j := Spec.map_preimage (e.inv ≫ j)
  have H' : IsPullback a (b ≫ e.hom) p (Spec.algebraMap R S) := by
    rw [hβ]
    exact H.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact higherDirectImage_injective_isZero_of_coefficient_iso a b e Λ q
    (hvan S (b ≫ e.hom) H') I

end AlgebraicGeometry.Scheme.EtaleCohomology
