/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.PrincipalClosedStep
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.PrincipalClosedRankZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientCompositeZero

/-! # Principal-open effacement in every finite coefficient rank

Rank zero discharges the literal closed branch by emptiness. Positive rank
uses the full smaller-rank hypothesis on the actual residual. The original
class may be presented before an actual coefficient isomorphism; its output
zero is returned through that same isomorphism and original composite map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eT

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  HasExt.standard HasDerivedCategory.standard

/-- The actual principal-open branch supplies pointed local zero at every
rank. The base case uses closed-branch emptiness, and the successor case
applies the full smaller-rank property rather than a supplied local zero. -/
theorem exists_pointed_principalOpen_H1_refinement_of_lower_rank
    (d : ℕ) (ih : ∀ r < d, PointedCurveModuleInjectiveH1Effacement.{u} r)
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain S]
    (hR : IsNagataRing.{u, 0} R) (hS : IsNagataRing.{u, 0} S)
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
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (s : S) (hs : s ≠ 0)
    (hopen : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen S s).ι b) _ 1 c = 0)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ∃ (U : G.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ 1 c = 0 := by
  cases d with
  | zero =>
    let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
    let : Smooth b := MorphismProperty.of_isPullback H inferInstance
    let : IsLocalization (⊥ : Submonoid S) S := IsLocalization.self bot_le
    have hc : c = 0 := principalClosed_H1_zero_of_open_zero_at_rank_zero
      S S S (⊥ : Submonoid S) s hs hd n hn I b
      (pullback.snd (principalSupportOpen S s).ι b)
      (pullback.fst (principalSupportOpen S s).ι b)
      (IsPullback.of_hasPullback _ _)
      (pullback.snd (principalSupportClosedMap S s) b)
      (pullback.fst (principalSupportClosedMap S s) b)
      (IsPullback.of_hasPullback _ _) c hopen
    refine ⟨Scheme.Etale.mk (𝟙 G), x ≫ σ, ?_, ?_⟩
    · exact Category.comp_id _
    · rw [hc, map_zero]
  | succ d =>
    exact exists_pointed_principalClosed_H1_refinement_of_lower_rank
      d ih R S hR hS hd p σ hσ haff β a b H n hn hunit I c s hs hopen Ω x

/-- A produced original composite open-zero gives a genuine target
refinement killing that same original class, even when its actual injective
coefficient carrier is reached through a specified coefficient isomorphism. -/
theorem exists_pointed_principalOpen_composite_H1_zero_of_lower_rank
    (d : ℕ) (ih : ∀ r < d, PointedCurveModuleInjectiveH1Effacement.{u} r)
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain S]
    (hR : IsNagataRing.{u, 0} R) (hS : IsNagataRing.{u, 0} S)
    (hd : ringKrullDim S ≤ (d : ℕ))
    {G Y T : Scheme.{u}} (p : G ⟶ Spec (CommRingCat.of R))
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
    [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
    (v : Y ⟶ T) (F : AbelianSheaf.{u, u + 1} T)
    (E : (inverseImage v).obj F ≅ (inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of S))
        (ULift.{u + 1} (ZMod n)))).obj I))
    (c : Sheaf.H.{eT} F 1) (s : S) (hs : s ≠ 0)
    (hopen : cohomologyPullback.{u, eT, u + 2}
      (pullback.snd (principalSupportOpen S s).ι b ≫ v) F 1 c = 0)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ∃ (U : G.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, eT, u + 2} (pullback.snd U.hom a ≫ v) F 1 c = 0 := by
  let cY := Sheaf.H.map E.hom 1 (cohomologyPullback.{u, eT, u + 2} v F 1 c)
  have hzero : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen S s).ι b) _ 1 cY = 0 :=
    coefficient_restriction_zero_of_composite_zero v
      (pullback.snd (principalSupportOpen S s).ι b) F _ E.hom 1 c hopen
  obtain ⟨U, xU, hxU, hcU⟩ := exists_pointed_principalOpen_H1_refinement_of_lower_rank
    d ih R S hR hS hd p σ hσ haff β a b H n hn hunit I cY s hs hzero Ω x
  exact ⟨U, xU, hxU,
    (coefficient_iso_restriction_zero_iff_composite_zero
      v (pullback.snd U.hom a) F _ E 1 c).mp hcU⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
