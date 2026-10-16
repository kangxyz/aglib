/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Products.BaseChange

/-!
# Finite morphisms into actual projective-product pullbacks

An actual finite map into the original fibre product has derived amplitude
zero on bounded coherent objects. Composing with the original product
projection therefore preserves coherent homology with the sum-of-dimensions
bound. A separately specified original morphism is retained by its displayed
factorization. Closed graph-product embeddings are included by their native
finite-morphism instance.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed ambient derived categories of actual scheme modules. -/
local instance finiteProjectiveProductStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] {S : Scheme.{u}} [IsLocallyNoetherian S]
  (f : S ⟶ Spec (.of R)) {m : ℕ} (ι : Fin m → Type u) (d : Fin m → ℕ)
  (e : ∀ i, ι i ≃ Fin (d i + 1))

include e

/-- Finite over an actual projective-product pullback implies bounded coherent
derived image for the original factored morphism, with the exact product bound. -/
theorem finiteOverProjectiveProduct_derived_bounded_coherent
    {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (i : Z ⟶ pullback f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom)
    [AlgebraicGeometry.IsFinite i] (p : Z ⟶ S)
    (hp : i ≫ pullback.fst f
      (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom = p)
    (K : DerivedCategory.Plus Z.Modules) (l b : ℤ) [K.IsGE l] [K.IsLE b]
    (hK : Scheme.Modules.coherentHomologyObjects Z K) :
    Scheme.Modules.coherentHomologyObjects S
        ((Scheme.Modules.derivedPushforwardPlus p).obj K) ∧
      ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsGE l ∧
        ((Scheme.Modules.derivedPushforwardPlus p).obj K).IsLE (b + ∑ j, d j) := by
  let : ∀ j, Fintype (ι j) := fun j => Fintype.ofEquiv (Fin (d j + 1)) (e j).symm
  let : IsLocallyNoetherian
      (pullback f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom) :=
    isLocallyNoetherian_productPullback R f ι
  let N := (Scheme.Modules.derivedPushforwardPlus i).obj K
  obtain ⟨hN, hNl, hNb⟩ := finite_derived_bounded_coherent i K l b hK
  let : N.IsGE l := hNl
  let : N.IsLE b := hNb
  have ht := projectiveProductProjection_derived_bounded_coherent R f ι d e N l b hN
  let D : (Scheme.Modules.derivedPushforwardPlus p).obj K ≅
      (Scheme.Modules.derivedPushforwardPlus
        (pullback.fst f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom)).obj N := by
    rw [← hp]
    exact (Scheme.Modules.derivedPushforwardPlusCompIso i
      (pullback.fst f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom)).app K
  let : ((Scheme.Modules.derivedPushforwardPlus
      (pullback.fst f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom)).obj N).IsGE l :=
    ht.2.1
  let : ((Scheme.Modules.derivedPushforwardPlus
      (pullback.fst f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom)).obj N).IsLE
      (b + ∑ j, d j) := ht.2.2
  exact ⟨(Scheme.Modules.coherentHomologyObjects S).prop_of_iso D.symm ht.1,
    DerivedCategory.Plus.TStructure.t.isGE_of_iso D.symm l,
    DerivedCategory.Plus.TStructure.t.isLE_of_iso D.symm (b + ∑ j, d j)⟩

/-- The original image of every finite-type quasicoherent coefficient in any
integer degree is coherent with the displayed uniform product bound. The
source's local Noetherianity is constructed internally from the finite map. -/
theorem finiteOverProjectiveProduct_derivedSingle_bounded_coherent
    {Z : Scheme.{u}}
    (i : Z ⟶ pullback f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom)
    [AlgebraicGeometry.IsFinite i] (p : Z ⟶ S)
    (hp : i ≫ pullback.fst f
      (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom = p)
    (M : Z.Modules) (hM : affineLocallyFiniteType Z M) (k : ℤ) :
    Scheme.Modules.coherentHomologyObjects S
        ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M)) ∧
      ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M)).IsGE k ∧
        ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M)).IsLE (k + ∑ j, d j) := by
  let : ∀ j, Fintype (ι j) := fun j => Fintype.ofEquiv (Fin (d j + 1)) (e j).symm
  let : IsLocallyNoetherian
      (pullback f (finiteProductOver (fun j => Over.mk (toSpec R (ι j)))).hom) :=
    isLocallyNoetherian_productPullback R f ι
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  exact finiteOverProjectiveProduct_derived_bounded_coherent R f ι d e i p hp
    ((DerivedCategory.Plus.singleFunctor Z.Modules k).obj M) k k
    (Scheme.Modules.coherentHomologyObjects_single Z M hM k)

end AlgebraicGeometry.Scheme.Cohomology
