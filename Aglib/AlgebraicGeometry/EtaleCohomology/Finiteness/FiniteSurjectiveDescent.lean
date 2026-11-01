/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleNoetherian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageConstructibleInduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Constructibility descent through an actual finite surjection

The original adjunction unit is monic by faithful inverse image. Its actual
cokernel is constructible, since finite direct image preserves constructibility
on a Noetherian target. The original finite-composition comparison then gives
induction in the cohomological degree, with precisely the preceding-degree
image of that cokernel. No proper base change, trace splitting, flatness,
reducedness or bound on the degree of the finite cover is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- The literal coefficient unit is monic for every surjective scheme map. -/
theorem mono_inverseImage_unit_of_surjective
    {Y X : Scheme.{u}} (p : Y ⟶ X) [Surjective p]
    (F : AbelianSheaf.{u, u + 1} X) :
    Mono ((inverseImageAdjunction p).unit.app F) := by
  let : (inverseImage p).Faithful := Proper.Reduction.inverseImage_faithful_of_surjective p
  exact Adjunction.unit_mono_of_L_faithful (inverseImageAdjunction p) F

/-- The same original finite-cover unit has a constructible cokernel. -/
theorem isConstructible_cokernel_finite_unit
    {Y X : Scheme.{u}} [IsNoetherian X] (p : Y ⟶ X) [IsFinite p]
    {F : AbelianSheaf.{u, u + 1} X} (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible (cokernel ((inverseImageAdjunction p).unit.app F)) := by
  exact Constructible.isConstructible_cokernel _ hF
    (Finite.isConstructible_directImage_of_isNoetherian p
      (Constructible.isConstructible_pullback_of_qcqs p hF))

/-- In positive degree the preceding-degree hypothesis is on the actual
cokernel, and the covering hypothesis is on the same original composite. -/
theorem higherDirectImage_isConstructible_succ_of_finiteSurjective
    {Y X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) (p : Y ⟶ X) [IsFinite p] [Surjective p]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ)
    (hQ : Constructible.IsConstructible ((higherDirectImage f n).obj
      (cokernel ((inverseImageAdjunction p).unit.app F))))
    (hcover : Constructible.IsConstructible ((higherDirectImage (p ≫ f) (n + 1)).obj
      ((inverseImage p).obj F))) :
    Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj F) := by
  let : Mono ((inverseImageAdjunction p).unit.app F) :=
    mono_inverseImage_unit_of_surjective p F
  apply higherDirectImage_isConstructible_succ_of_mono f
    ((inverseImageAdjunction p).unit.app F) n hQ
  exact (Constructible.isConstructible_iff_of_iso
    (Finite.higherDirectImageCompFiniteIso f p (n + 1) ((inverseImage p).obj F))).mp hcover

/-- Constructibility of all images through one actual finite surjection
implies constructibility downstairs, by degree induction rather than a
supplied descent certificate. Only constructible coefficients upstairs occur. -/
theorem higherDirectImage_isConstructible_of_finiteSurjective
    {Y X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) (p : Y ⟶ X) [IsFinite p] [Surjective p]
    (hcover : ∀ (q : ℕ) (G : AbelianSheaf.{u, u + 1} Y),
      Constructible.IsConstructible G →
      Constructible.IsConstructible ((higherDirectImage (p ≫ f) q).obj G)) :
    ∀ (q : ℕ) (F : AbelianSheaf.{u, u + 1} X), Constructible.IsConstructible F →
      Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  intro q
  induction q with
  | zero =>
    intro F hF
    let a := (inverseImageAdjunction p).unit.app F
    let : Mono a := mono_inverseImage_unit_of_surjective p F
    have hE := (Constructible.isConstructible_iff_of_iso
      (Finite.higherDirectImageCompFiniteIso f p 0 ((inverseImage p).obj F))).mp
        (hcover 0 _ (Constructible.isConstructible_pullback_of_qcqs p hF))
    have hdirect := (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app
        ((directImage p).obj ((inverseImage p).obj F)))).mp hE
    have hFdirect := Constructible.isConstructible_of_mono_of_noetherian
      ((directImage f).map a) hdirect
    exact (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app F)).mpr hFdirect
  | succ n ih =>
    intro F hF
    exact higherDirectImage_isConstructible_succ_of_finiteSurjective f p F n
      (ih _ (isConstructible_cokernel_finite_unit p hF))
      (hcover (n + 1) _ (Constructible.isConstructible_pullback_of_qcqs p hF))

end AlgebraicGeometry.Scheme.EtaleCohomology
