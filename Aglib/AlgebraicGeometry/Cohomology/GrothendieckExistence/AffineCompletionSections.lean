/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineEffectivity

/-!
# Original affine completion sections

The sections of the original coherent completion are the native completion
of the original affine module, over the completed ring. Every projection
and the original quotient unit are retained. The affine ring is not assumed
complete, and no ordinary localization of completion is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Build the completed equivalence and its coordinates at the abstract tower
level, before any geometric quotient objects are substituted. -/
def nativeCompletionSectionsComparison {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) (Q : ℕᵒᵖ ⥤ ModuleCat R)
    (hQ : AdicCompletion.IsCompatibleSystem I Q)
    (uMap : ∀ n, M →ₗ[R] Q.obj (op n))
    (hu : ∀ {m n} (h : m ≤ n), (AdicCompletion.towerTransition Q h).comp (uMap n) = uMap m)
    (hp : ∀ n, (I ^ n • ⊤ : Submodule R M) ≤ (uMap n).ker)
    (q : ∀ n, {e : (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R] Q.obj (op n) //
      ∀ x, e (Submodule.Quotient.mk x) = uMap n x})
    (hb : Function.Bijective (AdicCompletion.completionPresentation I Q hQ uMap hu hp)) :
    let := hQ.sectionsCompletionModule
    {e : AdicCompletion I M ≃ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule Q //
      ∀ x n, (e x).val (op n) = (q n).val (AdicCompletion.eval I M n x)} := by
  let := hQ.sectionsCompletionModule
  refine ⟨LinearEquiv.ofBijective
    (AdicCompletion.completionPresentation I Q hQ uMap hu hp) hb, ?_⟩
  intro x n
  change AdicCompletion.quotientToTower I Q uMap hp n (AdicCompletion.eval I M n x) = _
  generalize AdicCompletion.eval I M n x = y
  induction y using Submodule.Quotient.induction_on with
  | _ z => exact ((q n).property z).symm

variable (B : CommRingCat.{u}) [IsNoetherianRing B]
  (K : (Spec B).IdealSheafData) (H : (Spec B).CoherentSheaf)

local instance : H.obj.IsQuasicoherent :=
  ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1

/-- The original affine sections of a coherent quotient unit. -/
abbrev affineCompletionUnit (n : ℕ) :
    moduleSpecΓFunctor.obj H.obj →ₗ[B]
      ((completionFunctor (Spec B) K).obj H).affineSectionsTower.obj (op n) :=
  (moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n)).app H.obj)).hom

/-- The original affine units have precisely the ideal-power kernels. -/
theorem affineCompletionUnit_ker (n : ℕ) :
    (affineCompletionUnit B K H n).ker =
      affineIdeal B K ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj H.obj)) := by
  ext x
  change moduleSpecΓFunctor.map
    ((idealSheafQuotientUnit (Spec B) (K ^ n)).app H.obj) x = 0 ↔ _
  rw [← affineQuotientEquiv_mk B K H.obj n x]
  rw [← (affineQuotientEquiv B K H.obj n).map_zero,
    (affineQuotientEquiv B K H.obj n).injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero _

/-- Every original affine quotient unit is onto on original sections. -/
theorem affineCompletionUnit_surjective (n : ℕ) :
    Function.Surjective (affineCompletionUnit B K H n) := by
  intro y
  obtain ⟨q, rfl⟩ := (affineQuotientEquiv B K H.obj n).surjective y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨x, (affineQuotientEquiv_mk B K H.obj n x).symm⟩

/-- All-order compatibility retains the original quotient units. -/
theorem affineCompletionUnit_transition {n m : ℕ} (h : n ≤ m) :
    (AdicCompletion.towerTransition
      ((completionFunctor (Spec B) K).obj H).affineSectionsTower h).comp
        (affineCompletionUnit B K H m) = affineCompletionUnit B K H n := by
  apply LinearMap.ext
  intro x
  change moduleSpecΓFunctor.map
    (idealSheafQuotientMap (Spec B) (K ^ m) (idealSheaf_pow_le (Spec B) K h) H.obj)
      (moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ m)).app H.obj) x) =
    moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n)).app H.obj) x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, idealSheafQuotientUnit_map]

/-- The original native completion maps completed-linearly to the original
compatible affine sections. -/
def affineCompletionToSections :
    let F := (completionFunctor (Spec B) K).obj H
    let := F.affineFormalSectionsModule
    AdicCompletion (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj) →ₗ[
      AdicCompletion (affineIdeal B K) B] F.affineFormalSections :=
  AdicCompletion.completionPresentation (affineIdeal B K)
    ((completionFunctor (Spec B) K).obj H).affineSectionsTower
    ((completionFunctor (Spec B) K).obj H).affineSections_isCompatibleSystem
    (affineCompletionUnit B K H)
    (fun h => affineCompletionUnit_transition B K H h)
    (fun n => (affineCompletionUnit_ker B K H n).ge)

/-- The original completed comparison is bijective, from the exact quotient
coordinates, without assuming faithful completion of the affine ring. -/
theorem affineCompletionToSections_bijective :
    Function.Bijective (affineCompletionToSections B K H) := by
  apply AdicCompletion.completionToSections_bijective (affineIdeal B K)
    ((completionFunctor (Spec B) K).obj H).affineSectionsTower
    (affineCompletionUnit B K H)
    (fun h => affineCompletionUnit_transition B K H h)
    (fun n => (affineCompletionUnit_ker B K H n).ge) 0 0
  · intro n
    simpa only [Nat.add_zero] using (affineCompletionUnit_ker B K H n).le
  · intro n x hx
    exact (affineCompletionUnit_surjective B K H n) x

/-- The native completed comparison and every original quotient coordinate
are constructed together, before their public projections are specialized. -/
def affineCompletionSectionsComparison :
    let F := (completionFunctor (Spec B) K).obj H
    let := F.affineFormalSectionsModule
    {e : AdicCompletion (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj) ≃ₗ[
      AdicCompletion (affineIdeal B K) B] F.affineFormalSections //
      ∀ x n, (e x).val (op n) = affineQuotientEquiv B K H.obj n
        (AdicCompletion.eval (affineIdeal B K) _ n x)} :=
  nativeCompletionSectionsComparison (affineIdeal B K)
    ((completionFunctor (Spec B) K).obj H).affineSectionsTower
    ((completionFunctor (Spec B) K).obj H).affineSections_isCompatibleSystem
    (affineCompletionUnit B K H) (fun h => affineCompletionUnit_transition B K H h)
    (fun n => (affineCompletionUnit_ker B K H n).ge)
    (affineQuotientComparison B K H.obj)
    (affineCompletionToSections_bijective B K H)

/-- Canonical completed-linear identification with the original affine
completion system. -/
def affineCompletionSectionsEquiv :
    let F := (completionFunctor (Spec B) K).obj H
    let := F.affineFormalSectionsModule
    AdicCompletion (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj) ≃ₗ[
      AdicCompletion (affineIdeal B K) B] F.affineFormalSections :=
  LinearEquiv.ofBijective (affineCompletionToSections B K H)
    (affineCompletionToSections_bijective B K H)

/-- On an original affine section the comparison is the original quotient
unit at every stage, including stage zero. -/
theorem affineCompletionSectionsEquiv_of (x : moduleSpecΓFunctor.obj H.obj) (n : ℕ) :
    (affineCompletionSectionsEquiv B K H
      (AdicCompletion.of (affineIdeal B K) _ x)).val (op n) =
        affineCompletionUnit B K H n x := rfl

/-- Every coordinate of the completed comparison is the original affine
quotient equivalence applied to native completion evaluation. -/
theorem affineCompletionSectionsEquiv_apply
    (x : AdicCompletion (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj)) (n : ℕ) :
    (affineCompletionSectionsEquiv B K H x).val (op n) =
      affineQuotientEquiv B K H.obj n (AdicCompletion.eval (affineIdeal B K) _ n x) :=
by
  change AdicCompletion.quotientToTower (affineIdeal B K)
    ((completionFunctor (Spec B) K).obj H).affineSectionsTower
    (affineCompletionUnit B K H) (fun n => (affineCompletionUnit_ker B K H n).ge) n
      (AdicCompletion.eval (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj) n x) = _
  generalize AdicCompletion.eval (affineIdeal B K) (moduleSpecΓFunctor.obj H.obj) n x = q
  induction q using Submodule.Quotient.induction_on with
  | _ y => exact (affineQuotientEquiv_mk B K H.obj n y).symm

end AlgebraicGeometry.Scheme.Modules.Coherent
