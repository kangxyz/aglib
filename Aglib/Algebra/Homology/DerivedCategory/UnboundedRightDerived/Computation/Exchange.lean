/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Amplitude
public import
  Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.TruncationComparison
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactAmplitude

/-!
# Finite-amplitude extension of an original derived exchange

Two left exact functors with Grothendieck abelian sources and two exact
horizontal functors define the endpoints of an unbounded exchange. Uniform
vanishing in one positive degree for each left exact functor extends
invertibility of the supplied transformation from bounded-below objects to
all objects. The transformation is retained literally; no substitute
endpoint isomorphism, shift compatibility, or left completeness is used.

Each of the four categories has one selected derived realization. Category,
Hom, derived, and the two Grothendieck size universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe sA sA' uA vA wA uB vB wB uA' vA' wA' uB' vB' wB'

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [IsGrothendieckAbelian.{sA} A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  [IsGrothendieckAbelian.{sA'} A'] [HasDerivedCategory.{wA'} A']
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  (F : A ⥤ B) (F' : A' ⥤ B')
  [F.Additive] [F'.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits F']
  (G : B ⥤ B') (G' : A ⥤ A') [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- All-object relative bounds for the two original right-derived functors
extend invertibility of this same exchange from bounded-below objects.
No adjunction is required for this step; a geometric consumer supplies its
actual mate as the transformation. -/
theorem isIso_unboundedRightDerivedExchange_of_bounds
    (β : F.unboundedRightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      G'.mapDerivedCategory ⋙ F'.unboundedRightDerivedFunctor)
    (d d' : ℕ)
    (hF : ∀ M : A, IsZero ((F.rightDerived (d + 1)).obj M))
    (hF' : ∀ M : A', IsZero ((F'.rightDerived (d' + 1)).obj M))
    (hβ : ∀ (K : DerivedCategory A) (m : ℤ), K.IsGE m → IsIso (β.app K)) :
    IsIso β := by
  apply DerivedCategory.isIso_natTrans_of_upper_amplitude_of_boundedBelow
    (F.unboundedRightDerivedFunctor ⋙ G.mapDerivedCategory) β (d : ℤ) (d' : ℤ)
  · intro K n hK
    let : K.IsLE n := hK
    let : (F.unboundedRightDerivedFunctor.obj K).IsLE (n + (d : ℤ)) :=
      F.unboundedRightDerivedFunctor_isLE_of_bound d hF K n
    exact G.mapDerivedCategory_isLE _ (n + (d : ℤ))
  · intro K n hK
    let : K.IsLE n := hK
    let : (G'.mapDerivedCategory.obj K).IsLE n := G'.mapDerivedCategory_isLE K n
    exact F'.unboundedRightDerivedFunctor_isLE_of_bound d' hF' _ n
  · exact hβ

end CategoryTheory.Functor
