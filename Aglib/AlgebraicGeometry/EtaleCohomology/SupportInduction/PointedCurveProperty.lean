/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.UniformClosedResidualRefinement
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentAffineRestriction
public import Aglib.RingTheory.Nagata.ClosedSupportNormalization
public import Mathlib.FieldTheory.IsSepClosed

/-! # The pointed curve property for coefficient-dimension induction

The rank bounds the coefficient ring, independently of the source ring.
Both rings may be nonreduced, and the original coefficient arrow may have a
kernel. The source family retains its whole section and affine field fibres;
its total scheme is not assumed affine. Arbitrary Cartesian presentations
are admitted so the actual residual class needs no change of carrier.

This file defines the induction proposition. It does not assert the
proposition or supply an unproved local-zero producer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Target-pointed H1 effacement, uniform in all Nagata source and coefficient
arrows and all genuine injective module coefficients of the bounded rank.
The marked field is separably closed, not necessarily algebraically closed.
The conclusion is zero on the entire Cartesian target refinement. -/
def PointedCurveModuleInjectiveH1Effacement (d : ℕ) : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S],
    IsNagataRing.{u, 0} R → IsNagataRing.{u, 0} S →
    ringKrullDim S ≤ (d : ℕ) →
    ∀ {G Y : Scheme.{u}} (p : G ⟶ Spec (CommRingCat.of R))
      [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
      [QuasiCompact p] [QuasiSeparated p]
      (σ : Spec (CommRingCat.of R) ⟶ G),
      σ ≫ p = 𝟙 _ →
      (∀ (F : Type u) [Field F] (f : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
        IsAffine (pullback p f : Scheme.{u})) →
      ∀ (β : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
        (a : Y ⟶ G) (b : Y ⟶ Spec (CommRingCat.of S)),
        IsPullback a b p β →
        ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
          ∀ (I : ModuleSheaf (Spec (CommRingCat.of S)) (ULift.{u + 1} (ZMod n)))
            [Injective I]
            (c : Sheaf.H.{u + 2} ((inverseImage b).obj
              ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of S))
                (ULift.{u + 1} (ZMod n)))).obj I)) 1)
            (Ω : Type u) [Field Ω] [IsSepClosed Ω]
            (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
            ∃ (U : G.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
              xU ≫ U.hom = x ≫ σ ∧
              cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ 1 c = 0

end AlgebraicGeometry.Scheme.EtaleCohomology
