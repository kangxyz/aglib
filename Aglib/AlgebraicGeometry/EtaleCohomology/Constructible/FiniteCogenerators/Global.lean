/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.ConstantFactorization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.GenericModelExistence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.GenericDetection

/-! # Actual global finite constant cogenerators

The original global normal-model maps are jointly monic on the actual finite
integral reduced stratum cover. Original affine restriction FP factors each
map through an actual finite morphism over the whole original base. Their
literal finite product therefore gives the existing finite-cogenerator record.
The finite values are arbitrary finite abelian groups, with no prescribed
modulus. No finite-normalization assumption or constructibility-to-FP
implication is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge

/-- The original global normal-model maps factor through actual finite targets,
so the literal finite product of those original factors is monic. -/
def finiteConstantProductEmbeddingOfGlobalModels
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (t : FiniteIntegralLocallyClosedCover F)
    (m : ∀ k, GlobalNormalGenericModel (t.inclusion k) F)
    (hFP : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsFinitelyPresentable.{u + 1} ((inverseImage j).obj F)) :
    FiniteConstantProductEmbedding F := by
  let q (k : t.index) := finiteConstantFactorization (m k).morphism (m k).value F hFP
    (m k).extensionMap
  let A (k : t.index) := (directImage (q k).morphism).obj
    (ConstantFinite.coefficient (m k).value (q k).source)
  let a (k : t.index) : F ⟶ globalModelTargets t m k := (m k).extensionMap
  let b (k : t.index) : F ⟶ A k := (q k).map
  let c (k : t.index) : A k ⟶ globalModelTargets t m k := by
    let h : Over.mk ((m k).morphism) ⟶ Over.mk ((q k).morphism) :=
      Over.homMk (q k).comparison (q k).over
    exact (AffineIntegralConstants.constantPushforwardFunctor (X := X) (m k).value).map h.op
  have h (k : t.index) : b k ≫ c k = a k := (q k).factor
  have : Mono (Pi.lift a) := mono_globalModelProduct t m
  have hm : Mono (Pi.lift b) := mono_productLift_of_factors a b c h
  exact {
    index := t.index
    finite_index := t.finite_index
    source := fun k => (q k).source
    morphism := fun k => (q k).morphism
    finite_morphism := fun k => (q k).finite_morphism
    value := fun k => (m k).value
    finite_value := fun k => (m k).value_finite
    map := Pi.lift b
    mono := hm }

/-- An actual finite integral stratum cover and FP on each original affine
restriction give genuinely finite global constant cogenerators. -/
def finiteConstantProductEmbeddingOfIntegralCover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (t : FiniteIntegralLocallyClosedCover F)
    (hFP : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsFinitelyPresentable.{u + 1} ((inverseImage j).obj F)) :
    FiniteConstantProductEmbedding F := by
  have (k : t.index) : IsIntegral (t.stratum k) := t.integral k
  have (k : t.index) : IsImmersion (t.inclusion k) := t.immersion k
  exact finiteConstantProductEmbeddingOfGlobalModels F t
    (fun k => globalNormalGenericModel (t.inclusion k) F (t.locally_constant k)) hFP

/-- A geometrically constructible sheaf on the original Noetherian base has
actual finite global constant cogenerators when its original affine restrictions
are ambient finitely presentable. The finite values have no prescribed modulus. -/
def finiteConstantProductEmbeddingOfIsNoetherian
    (X : Scheme.{u}) [IsNoetherian X] (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsConstructible F)
    (hFP : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsFinitelyPresentable.{u + 1} ((inverseImage j).obj F)) :
    FiniteConstantProductEmbedding F :=
  finiteConstantProductEmbeddingOfIntegralCover F (finiteIntegralLocallyClosedCover F hF) hFP

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
