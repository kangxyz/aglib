/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Noetherian
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Empty
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.KernelImage
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.QuotientEffectivity

/-! # Exceptional thickenings in ideal-sheaf induction

A strict-ideal induction hypothesis supplies existence on every actual power
thickening of a dense exceptional complement. Positive powers are handled by
the native kernel-image factorization; power zero is the empty scheme. This
is an induction supplier, not an unconditional proper-existence theorem.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Strict increases of the original ideal supply the entire exceptional
thickening tower with its original structure maps, including exponent zero. -/
theorem closedThickeningCompletionEssSurj_of_idealInduction
    (K : X.IdealSheafData) [Nonempty K.subscheme]
    (h : ∀ L : X.IdealSheafData, K < L →
      letI : IsLocallyNoetherian L.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian L.subschemeι
      (completionFunctor L.subscheme
        (idealThickeningIdealSheaf (L.subschemeι ≫ f) I)).EssSurj) :
    letI : IsLocallyNoetherian K.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
    ∀ J : K.subscheme.IdealSheafData, Dense (J.support : Set K.subscheme)ᶜ →
      ClosedThickeningCompletionEssSurj (K.subschemeι ≫ f) I J := by
  let : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
  intro J hJ n
  let : IsLocallyNoetherian (J ^ n).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (J ^ n).subschemeι
  by_cases hn : n = 0
  · subst n
    let : IsEmpty (J ^ 0).subscheme := by
      rw [pow_zero, IdealSheafData.one_eq_top]
      infer_instance
    exact completionFunctorEssSurjOfIsEmpty (J ^ 0).subscheme
      (idealThickeningIdealSheaf ((J ^ 0).subschemeι ≫ (K.subschemeι ≫ f)) I)
  · have hs := K.lt_ker_subschemeι_comp (J ^ n)
      (J.pow_ne_bot_of_dense_compl_support hJ n hn)
    have he := completionEssSurjOfKernelImage I
      ((J ^ n).subschemeι ≫ K.subschemeι) f (h _ hs)
    have hb : ((J ^ n).subschemeι ≫ K.subschemeι) ≫ f =
        (J ^ n).subschemeι ≫ (K.subschemeι ≫ f) := Category.assoc _ _ _
    exact hb ▸ he

end AlgebraicGeometry.Scheme.Cohomology
