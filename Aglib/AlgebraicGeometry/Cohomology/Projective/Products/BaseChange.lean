/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Products.Derived
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Products.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Finite.Coherent

/-!
# Bounded coherent images of actual projective-product pullbacks

The original first projection of the actual fibre product is identified
with the native finite product tower through the sole geometric comparison.
Its original projection equation and the native derived-composition
isomorphism retain the installed direct image. The comparison isomorphism
is finite, so the sole finite-image theorem transfers the input with the
same bounds. No new product or derived model is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed ambient derived categories of actual scheme modules. -/
local instance projectiveProductPullbackStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] {S : Scheme.{u}} [IsLocallyNoetherian S]
  (f : S ⟶ Spec (.of R)) {m : ℕ} (ι : Fin m → Type u) (d : Fin m → ℕ)
  (e : ∀ i, ι i ≃ Fin (d i + 1))

include e

/-- The original projective-product first projection preserves bounded coherent
homology with the exact sum-of-dimensions bound. Source local Noetherianity
follows from `ProjectiveSpace.isLocallyNoetherian_productPullback`. -/
theorem projectiveProductProjection_derived_bounded_coherent
    [IsLocallyNoetherian
      (pullback f (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom)]
    (K : DerivedCategory.Plus
      (pullback f (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom).Modules)
    (l b : ℤ) [K.IsGE l] [K.IsLE b]
    (hK : Scheme.Modules.coherentHomologyObjects
      (pullback f (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom) K) :
    Scheme.Modules.coherentHomologyObjects S
        ((Scheme.Modules.derivedPushforwardPlus
          (pullback.fst f (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom)).obj K) ∧
      ((Scheme.Modules.derivedPushforwardPlus
        (pullback.fst f
          (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom)).obj K).IsGE l ∧
        ((Scheme.Modules.derivedPushforwardPlus
          (pullback.fst f (finiteProductOver (fun i => Over.mk (toSpec R (ι i)))).hom)).obj K).IsLE
            (b + ∑ i, d i) := by
  let P : Fin m → Over (Spec (.of R)) := fun i => Over.mk (toSpec R (ι i))
  let Q : Fin m → Over S := fun i => (Over.pullback f).obj (P i)
  let E := productBaseChangeIso R f ι
  let : IsLocallyNoetherian (finiteProductOver Q).left :=
    isLocallyNoetherian_of_isOpenImmersion E.inv
  let N := (Scheme.Modules.derivedPushforwardPlus E.hom).obj K
  obtain ⟨hN, hNl, hNb⟩ := finite_derived_bounded_coherent E.hom K l b hK
  let : N.IsGE l := hNl
  let : N.IsLE b := hNb
  let a : ∀ i, (Q i).left ⟶ ProjectiveSpace R (ι i) :=
    fun i => pullback.fst (toSpec R (ι i)) f
  have H (i : Fin m) : IsPullback (a i) (Q i).hom (toSpec R (ι i)) f :=
    IsPullback.of_hasPullback (toSpec R (ι i)) f
  have ht := finiteProjectiveProduct_derived_bounded_coherent R f Q ι d e a H N l b hN
  have hp : E.hom ≫ (finiteProductOver Q).hom =
      pullback.fst f (finiteProductOver P).hom := productBaseChangeIso_hom_base R f ι
  let D : (Scheme.Modules.derivedPushforwardPlus
        (pullback.fst f (finiteProductOver P).hom)).obj K ≅
      (Scheme.Modules.derivedPushforwardPlus (finiteProductOver Q).hom).obj N := by
    rw [← hp]
    exact (Scheme.Modules.derivedPushforwardPlusCompIso E.hom (finiteProductOver Q).hom).app K
  let : ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver Q).hom).obj N).IsGE l := ht.2.1
  let : ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver Q).hom).obj N).IsLE
      (b + ∑ i, d i) := ht.2.2
  exact ⟨(Scheme.Modules.coherentHomologyObjects S).prop_of_iso D.symm ht.1,
    DerivedCategory.Plus.TStructure.t.isGE_of_iso D.symm l,
    DerivedCategory.Plus.TStructure.t.isLE_of_iso D.symm (b + ∑ i, d i)⟩

end AlgebraicGeometry.Scheme.Cohomology
