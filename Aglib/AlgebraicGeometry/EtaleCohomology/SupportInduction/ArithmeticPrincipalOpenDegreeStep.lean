/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticPrincipalClosedDegreeStep
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.PrincipalOpenRankZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.PrincipalClosedSupport
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Aglib.CategoryTheory.Limits.Shapes.PullbackPastingIso

/-! # Arithmetic principal-open effacement in every finite coefficient rank

The rank-zero branch uses the actual principal-open isomorphism, in every
degree. The successor branch uses the genuine smaller-rank residual. Only
strictly lower positive-degree open-summand vanishing is an outer input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  HasExt.standard HasDerivedCategory.standard

/-- The actual principal-open zero produces a pointed refinement at every
coefficient rank, retaining the fixed degree and original class. -/
theorem exists_arithmetic_principalOpen_degree_refinement_of_lower_rank
    (q : ℕ) (hq : 0 < q) (d : ℕ)
    (ih : ∀ r < d, ArithmeticPointedCurveModuleEffacement.{u} q r)
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    (hd : ringKrullDim S ≤ (d : ℕ))
    {G Y : Scheme.{u}} (p : G ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of R) ⟶ G) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (f : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      IsAffine (pullback p f : Scheme.{u}))
    (β : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    (a : Y ⟶ G) (b : Y ⟶ Spec (CommRingCat.of S)) (H : IsPullback a b p β)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (CommRingCat.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (s : S) (hs : s ≠ 0)
    (hopen : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen S s).ι b) _ q c = 0)
    (hlower : ∀ (U : G.Etale),
      let t := pullback.snd U.hom a
      let j' := pullback.snd (principalSupportOpen S s).ι b
      let bU := pullback.fst (principalSupportOpen S s).ι b
      let j₂ := pullback.snd j' t
      let bU₂ := pullback.fst j' t ≫ bU
      ∀ r : ℕ, 1 ≤ r → r < q →
        IsZero ((higherDirectImage j₂ r).obj ((inverseImage bU₂).obj
          ((SheafOfModules.toSheaf (constantRing (principalSupportOpen S s).toScheme
            (ULift.{u + 1} (ZMod n)))).obj
            ((moduleInverseImage (principalSupportOpen S s).ι
              (ULift.{u + 1} (ZMod n))).obj I)))))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ∃ (U : G.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  cases d with
  | zero =>
    have hc : c = 0 := principalOpen_class_eq_zero_of_rank_zero S s hs hd b _ q c hopen
    refine ⟨Scheme.Etale.mk (𝟙 G), x ≫ σ, ?_, ?_⟩
    · exact Category.comp_id _
    · rw [hc, map_zero]
  | succ d =>
    exact exists_arithmetic_principalClosed_degree_refinement_of_lower_rank
      q hq d ih R S hd p σ hσ haff β a b H n hn hunit I c s hs hopen hlower Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
