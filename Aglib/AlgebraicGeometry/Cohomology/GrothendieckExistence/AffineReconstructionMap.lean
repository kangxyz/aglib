/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineEffectivityHom

/-!
# The actual affine map used by bounded reconstruction

The completed-linear map is built from the original formal morphism and the
canonical completion comparison of its algebraic target. Its finite-stage
formula keeps the original morphism on affine sections, not a chosen map
between abstractly isomorphic reductions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Native completed-linear map carrier, with its original scalar structure. -/
abbrev NativeReconstructionLinearMap {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (I : Ideal R) (F : ℕᵒᵖ ⥤ ModuleCat R)
    (hF : AdicCompletion.IsCompatibleSystem I F) : Type _ :=
  let := hF.sectionsCompletionModule
  ModuleCat.sectionsSubmodule F →ₗ[AdicCompletion I R] AdicCompletion I P

/-- The native output interface for an original reconstruction map and every
coefficient equation. Keeping this named avoids re-elaborating a geometric
subtype predicate at each specialization. -/
def NativeReconstructionData {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (I : Ideal R) (F G : ℕᵒᵖ ⥤ ModuleCat R)
    (hF : AdicCompletion.IsCompatibleSystem I F)
    (q : ∀ n, (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n))
    (φ : F ⟶ G) : Type _ :=
  {g : NativeReconstructionLinearMap (P := P) I F hF //
    ∀ x n, q n (AdicCompletion.eval I P n (g x)) = φ.app (op n) (x.val (op n))}

/-- Project the map before any geometric native output is specialized. -/
def NativeReconstructionData.map {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    {I : Ideal R} {F G : ℕᵒᵖ ⥤ ModuleCat R}
    {hF : AdicCompletion.IsCompatibleSystem I F}
    {q : ∀ n, (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n)}
    {φ : F ⟶ G} (d : NativeReconstructionData I F G hF q φ) :
    NativeReconstructionLinearMap (P := P) I F hF := d.val

/-- Project every original coefficient equation at the same native boundary. -/
theorem NativeReconstructionData.map_eval {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] {I : Ideal R} {F G : ℕᵒᵖ ⥤ ModuleCat R}
    {hF : AdicCompletion.IsCompatibleSystem I F}
    {q : ∀ n, (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n)}
    {φ : F ⟶ G} (d : NativeReconstructionData I F G hF q φ)
    (x : ModuleCat.sectionsSubmodule F) (n : ℕ) :
    q n (AdicCompletion.eval I P n (d.map x)) = φ.app (op n) (x.val (op n)) :=
  d.property x n

/-- Construct the inverse completed map and its original coordinates while
both coefficient towers and the original natural transformation are abstract. -/
def nativeReconstructionMapComparison {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (I : Ideal R)
    (F G : ℕᵒᵖ ⥤ ModuleCat R)
    (hF : AdicCompletion.IsCompatibleSystem I F)
    (hG : AdicCompletion.IsCompatibleSystem I G)
    (q : ∀ n, (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n))
    (c : let := hG.sectionsCompletionModule
      {e : AdicCompletion I P ≃ₗ[AdicCompletion I R] ModuleCat.sectionsSubmodule G //
        ∀ x n, (e x).val (op n) = q n (AdicCompletion.eval I P n x)})
    (φ : F ⟶ G) :
    NativeReconstructionData I F G hF q φ := by
  let := hF.sectionsCompletionModule
  let := hG.sectionsCompletionModule
  let f := hF.sectionsMapCompletion hG (fun j => (φ.app j).hom)
    (fun g x => ConcreteCategory.congr_hom (φ.naturality g) x)
  refine ⟨c.val.symm.toLinearMap.comp f, ?_⟩
  intro x n
  exact (c.property (c.val.symm (f x)) n).symm.trans
    (congrArg (fun y => y.val (op n)) (c.val.apply_symm_apply (f x)))

/-- Keep construction of the completed comparison and its inverse map in the
same abstract tower boundary, avoiding a concrete scalar-instance conversion. -/
def nativeReconstructionFromQuotientComparisons {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (I : Ideal R)
    (F G : ℕᵒᵖ ⥤ ModuleCat R)
    (hF : AdicCompletion.IsCompatibleSystem I F)
    (hG : AdicCompletion.IsCompatibleSystem I G)
    (uMap : ∀ n, P →ₗ[R] G.obj (op n))
    (hu : ∀ {m n} (h : m ≤ n), (AdicCompletion.towerTransition G h).comp (uMap n) = uMap m)
    (hp : ∀ n, (I ^ n • ⊤ : Submodule R P) ≤ (uMap n).ker)
    (q : ∀ n, {e : (P ⧸ (I ^ n • ⊤ : Submodule R P)) ≃ₗ[R] G.obj (op n) //
      ∀ x, e (Submodule.Quotient.mk x) = uMap n x})
    (hb : Function.Bijective (AdicCompletion.completionPresentation I G hG uMap hu hp))
    (φ : F ⟶ G) :
    NativeReconstructionData I F G hF (fun n => (q n).val) φ :=
  nativeReconstructionMapComparison I F G hF hG (fun n => (q n).val)
    (nativeCompletionSectionsComparison I G hG uMap hu hp q hb) φ

variable (B : CommRingCat.{u}) [IsNoetherianRing B]
  (K : (Spec B).IdealSheafData) (H : (Spec B).CoherentSheaf)

local instance : H.obj.IsQuasicoherent :=
  ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1

variable {B K H} {F : AdicSystem (Spec B) K}
  (α : F ⟶ (completionFunctor (Spec B) K).obj H)

/-- The original reconstructed map and all of its stage coordinates are kept
in a single certificate so later projections do not recheck its construction. -/
def affineReconstructionMapData :
    NativeReconstructionData (P := moduleSpecΓFunctor.obj H.obj) (affineIdeal B K)
      F.affineSectionsTower ((completionFunctor (Spec B) K).obj H).affineSectionsTower
      F.affineSections_isCompatibleSystem
      (fun n => (affineQuotientComparison B K H.obj n).val)
      (AdicSystem.affineSectionsMap α) :=
  nativeReconstructionFromQuotientComparisons (P := moduleSpecΓFunctor.obj H.obj) (affineIdeal B K)
    F.affineSectionsTower ((completionFunctor (Spec B) K).obj H).affineSectionsTower
    F.affineSections_isCompatibleSystem
    ((completionFunctor (Spec B) K).obj H).affineSections_isCompatibleSystem
    (affineCompletionUnit B K H) (fun h => affineCompletionUnit_transition B K H h)
    (fun n => (affineCompletionUnit_ker B K H n).ge)
    (affineQuotientComparison B K H.obj) (affineCompletionToSections_bijective B K H)
    (AdicSystem.affineSectionsMap α)

/-- The original affine formal morphism with its target expressed as the
native completion of the original coherent affine module. -/
def affineReconstructionMap :
    NativeReconstructionLinearMap (P := moduleSpecΓFunctor.obj H.obj) (affineIdeal B K)
      F.affineSectionsTower F.affineSections_isCompatibleSystem :=
  (affineReconstructionMapData α).map

end AlgebraicGeometry.Scheme.Modules.Coherent
