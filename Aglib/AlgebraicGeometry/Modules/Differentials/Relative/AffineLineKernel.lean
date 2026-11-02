/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.ExteriorBaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawSections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.RingTheory.Kaehler.Exterior.GenericKernel
public import Mathlib.RingTheory.Flat.TorsionFree


/-!
# The actual pulled-back line kills the original raw kernel

The target is the original pullback of an actual line. Its sections are
invertible, hence torsion-free. The same common fraction field proves
injectivity of the original localized raw map internally.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u vK


open CommRingCat.KaehlerDifferential
open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable (Λ A B : Type u) (K : Type vK) [CommRing Λ] [CommRing A] [CommRing B] [Field K]
  [Algebra Λ A] [Algebra A B] [Algebra Λ B] [IsScalarTower Λ A B]
  [Algebra A K] [Algebra B K] [Algebra Λ K]
  [IsScalarTower A B K] [IsScalarTower Λ A K] [IsScalarTower Λ B K]
  [IsFractionRing A K] [IsFractionRing B K]

omit [Algebra Λ B] [IsScalarTower Λ A B] [IsScalarTower Λ B K] in
include K in
/-- Any original raw coefficient into an actual line has pulled-back kernel
containing that of the original raw differential pullback. No generic
injectivity or torsion-freeness premise is supplied by the consumer. -/
theorem rawPullback_ker_le_lineCoefficient
    (n : ℕ) (L : Invertible.LineBundle (Spec (.of A)))
    (φ : moduleExteriorPower (Spec (.of A))
      (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ A)))) n ⟶ L.val) :
    let α := CommRingCat.ofHom (algebraMap Λ A)
    let σ := CommRingCat.ofHom (algebraMap A B)
    LinearMap.ker
      (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n)).hom ≤
    LinearMap.ker (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ)).hom := by
  intro α σ
  have hAK (a : A) : algebraMap A K a = algebraMap B K (σ a) :=
    IsScalarTower.algebraMap_apply A B K a
  have hΛK (r : Λ) : algebraMap Λ K r = algebraMap A K (α r) :=
    IsScalarTower.algebraMap_apply Λ A K r
  let := α.hom.toAlgebra
  let := σ.hom.toAlgebra
  let := (α ≫ σ).hom.toAlgebra
  let : IsScalarTower Λ A B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq hAK
  let : IsScalarTower Λ A K := IsScalarTower.of_algebraMap_eq hΛK
  let : IsScalarTower Λ B K := IsScalarTower.to₁₃₄ Λ A B K
  let LB := Invertible.pullbackLineBundle (Spec.map σ) L
  let Q := moduleSpecΓFunctor.obj LB.val
  let : Module.Invertible B Q := Invertible.invertible_globalSections LB
  let : Module.IsTorsionFree B Q := inferInstance
  let e := rawPullbackSourceSectionsEquiv α σ n
  let t := rawPullbackTargetSectionsEquiv α σ n
  let G := (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ)).hom
  let g : B ⊗[A] (⋀[A]^n (KaehlerDifferential Λ A)) →ₗ[B] Q :=
    G.comp e.symm.toLinearMap
  have hker := KaehlerDifferential.mapExteriorBaseChange_ker_le Λ A B K n g
  intro z hz
  have hn : affineRawLinearMap α σ n (e z) = 0 :=
    (rawPullbackSections_apply α σ n z).symm.trans
      ((congrArg t hz).trans (map_zero t))
  have hg := hker hn
  change G (e.symm (e z)) = 0 at hg
  exact (congrArg G (e.symm_apply_apply z)).symm.trans hg

end AlgebraicGeometry.Scheme.Modules.Differentials
