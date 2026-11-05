/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryCartesian
public import Aglib.CategoryTheory.NatTrans.RestrictedIsIso

/-! # The original bounded exchange functors and natural transformation

Fix the actual restricted source and target functors first, then the original
whiskered mate with those exact functor carriers. Its invertibility is proved
as a natural transformation before constructing its natural isomorphism. This
separates the actual q0 proof from the data-return boundary without changing
any original component, coefficient or map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
attribute [local instance] hasSheafifyLarge

/-- The actual annihilator property on the original coefficients. -/
def boundedCoefficientProperty (X : Scheme.{u}) (n : ℕ) :
    ObjectProperty (AbelianSheaf.{u, u + 1} X) := fun F => n • 𝟙 F = 0

/-- The original restricted source functor, fixed before the mate is supplied. -/
def boundedBaseChangeSource {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (n : ℕ) :
    (boundedCoefficientProperty X n).FullSubcategory ⥤ AbelianSheaf.{u, u + 1} S' :=
  (boundedCoefficientProperty X n).ι ⋙ (directImage f ⋙ inverseImage g)

/-- The original restricted target functor, with its literal object dictionary. -/
def boundedBaseChangeTarget {X X' S' : Scheme.{u}}
    (f' : X' ⟶ S') (g' : X' ⟶ X) (n : ℕ) :
    (boundedCoefficientProperty X n).FullSubcategory ⥤ AbelianSheaf.{u, u + 1} S' :=
  (boundedCoefficientProperty X n).ι ⋙ (inverseImage g' ⋙ directImage f')

/-- The actual original mate restricted to these fixed functors. -/
def boundedBaseChangeMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (w : f' ≫ g = g' ≫ f) (n : ℕ) :
    boundedBaseChangeSource f g n ⟶ boundedBaseChangeTarget f' g' n :=
  Functor.whiskerLeft (boundedCoefficientProperty X n).ι (baseChangeMap f f' g g' w)

/-- The original q0 theorem on the original coefficient objects, before
projecting full-subcategory objects or constructing a restricted instance. -/
theorem baseChangeMap_smooth_bounded_isIsoOn
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : IsPullback g' f' f g) [Smooth g]
    (n : ℕ) (hn : 0 < n) :
    NatTrans.IsIsoOn (boundedCoefficientProperty X n)
      (baseChangeMap f f' g g' h.w.symm) :=
  fun F hF => baseChangeMap_smooth_bounded_isIso_of_isPullback
    f f' g g' h F n hn hF

/-- Ordinary smooth exchange proves invertibility of the actual entire
restricted transformation, without returning a concrete inverse object. -/
theorem boundedBaseChangeMap_isIso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : IsPullback g' f' f g) [Smooth g]
    (n : ℕ) (hn : 0 < n) :
    IsIso (boundedBaseChangeMap f f' g g' h.w.symm n) :=
  NatTrans.isIso_whiskerLeft_of_isIsoOn
    (baseChangeMap f f' g g' h.w.symm) (boundedCoefficientProperty X n)
    (baseChangeMap_smooth_bounded_isIsoOn f f' g g' h n hn)

/-- The whole original bounded smooth exchange, on the already fixed
functors and original natural transformation. -/
def smoothBoundedBaseChangeNatIso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : IsPullback g' f' f g) [Smooth g]
    (n : ℕ) (hn : 0 < n) :
    boundedBaseChangeSource f g n ≅ boundedBaseChangeTarget f' g' n := by
  let : IsIso (boundedBaseChangeMap f f' g g' h.w.symm n) :=
    boundedBaseChangeMap_isIso f f' g g' h n hn
  exact asIso (boundedBaseChangeMap f f' g g' h.w.symm n)

end AlgebraicGeometry.Scheme.EtaleCohomology
