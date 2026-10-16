/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Projection.Derived
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Bounded coherent images of finite native projective products

Each component is an actual Cartesian base change of polynomial projective
space. The sole native finite over-product is built by original binary
products, so its successor projection is another actual projective-space
projection. Native derived composition iterates the proved bounded coherent
image theorem. The empty family is the actual identity of the base, and
the upper bound is the sum of the displayed projective dimensions.
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
local instance projectiveProductsStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : Type u) [CommRing R] {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The original finite product of actual projective-space base changes sends
bounded coherent homology in `[l,b]` to bounded coherent homology in
`[l,b+∑ᵢ dᵢ]`. The empty family uses the original identity of the base.
The locally Noetherian source guard forms the shared coherent property and
also follows from properness of the displayed finite product. -/
theorem finiteProjectiveProduct_derived_bounded_coherent (f : S ⟶ Spec (.of R)) :
    ∀ {m : ℕ} (P : Fin m → Over S) (ι : Fin m → Type u) (d : Fin m → ℕ)
      (_e : ∀ i, ι i ≃ Fin (d i + 1))
      (a : ∀ i, (P i).left ⟶ ProjectiveSpace R (ι i))
      (_h : ∀ i, IsPullback (a i) (P i).hom (toSpec R (ι i)) f)
      [IsLocallyNoetherian (finiteProductOver P).left]
      (K : DerivedCategory.Plus (finiteProductOver P).left.Modules) (l b : ℤ)
      [K.IsGE l] [K.IsLE b],
      Scheme.Modules.coherentHomologyObjects (finiteProductOver P).left K →
      Scheme.Modules.coherentHomologyObjects S
          ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj K) ∧
        ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj K).IsGE l ∧
          ((Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj K).IsLE
            (b + ∑ i, d i) := by
  intro m
  induction m with
  | zero =>
    intro P ι d e a h _ K l b _ _ hK
    let E : (Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj K ≅ K :=
      (((Scheme.Modules.pushforward (𝟙 S)).rightDerivedFunctorPlusIso
        (Scheme.Modules.pushforwardId S)) ≪≫
        Functor.rightDerivedFunctorPlusIdIso S.Modules).app K
    refine ⟨(Scheme.Modules.coherentHomologyObjects S).prop_of_iso E.symm hK,
      DerivedCategory.Plus.TStructure.t.isGE_of_iso E.symm l, ?_⟩
    simpa using DerivedCategory.Plus.TStructure.t.isLE_of_iso E.symm b
  | succ m ih =>
    intro P ι d e a h _ K l b _ _ hK
    let : ∀ i, Fintype (ι i) := fun i => Fintype.ofEquiv (Fin (d i + 1)) (e i).symm
    let : ∀ i, IsProper (P i).hom := fun i =>
      MorphismProperty.of_isPullback (h i) inferInstance
    let T := finiteProductOver (fun i : Fin m => P i.succ)
    let : ∀ i : Fin m, IsProper (P i.succ).hom := fun i => inferInstance
    let : IsProper T.hom := isProper_finiteProductOver (fun i : Fin m => P i.succ)
    let : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
    let π : (finiteProductOver P).left ⟶ T.left := (prod.snd : P 0 ⨯ T ⟶ T).left
    let α : (finiteProductOver P).left ⟶ ProjectiveSpace R (ι 0) :=
      (prod.fst : P 0 ⨯ T ⟶ P 0).left ≫ a 0
    have H : IsPullback α π (toSpec R (ι 0)) (T.hom ≫ f) :=
      (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (P 0) T)).paste_horiz (h 0)
    let N := (Scheme.Modules.derivedPushforwardPlus π).obj K
    obtain ⟨hN, hNl, hNb⟩ := projectiveProjection_derived_bounded_coherent R (ι 0)
      α π (T.hom ≫ f) H (d 0) (e 0) K l b hK
    let : N.IsGE l := hNl
    let : N.IsLE (b + d 0) := hNb
    have ht := ih (fun i => P i.succ) (fun i => ι i.succ) (fun i => d i.succ)
      (fun i => e i.succ) (fun i => a i.succ) (fun i => h i.succ) N l (b + d 0) hN
    have hp : π ≫ T.hom = (finiteProductOver P).hom :=
      (prod.snd : P 0 ⨯ T ⟶ T).w
    let E : (Scheme.Modules.derivedPushforwardPlus (finiteProductOver P).hom).obj K ≅
        (Scheme.Modules.derivedPushforwardPlus T.hom).obj N := by
      rw [← hp]
      exact (Scheme.Modules.derivedPushforwardPlusCompIso π T.hom).app K
    let : ((Scheme.Modules.derivedPushforwardPlus T.hom).obj N).IsGE l := ht.2.1
    let : ((Scheme.Modules.derivedPushforwardPlus T.hom).obj N).IsLE
        ((b + d 0) + ∑ i : Fin m, d i.succ) := ht.2.2
    refine ⟨(Scheme.Modules.coherentHomologyObjects S).prop_of_iso E.symm ht.1,
      DerivedCategory.Plus.TStructure.t.isGE_of_iso E.symm l, ?_⟩
    simpa only [Fin.sum_univ_succ, Nat.cast_add, add_assoc] using
      DerivedCategory.Plus.TStructure.t.isLE_of_iso E.symm
        ((b + d 0) + ∑ i : Fin m, d i.succ)

end AlgebraicGeometry.Scheme.Cohomology
