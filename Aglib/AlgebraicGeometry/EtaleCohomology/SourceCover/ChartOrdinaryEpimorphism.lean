/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ChartOrdinaryExchange
public import Aglib.CategoryTheory.Adjunction.Mates.ChartComponent

/-! # Ordinary chart epimorphy before choosing an étale-site object -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

/-- Transport the actual raw-chart ordinary comparison through arbitrary given
boundary isomorphisms, before specializing the chart to an étale-site object. -/
theorem sourceChartOrdinaryTransport_epi
    {X S X' S' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g) [Smooth g]
    (j : T ⟶ X) (F : AbelianSheaf.{u, u + 1} T)
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    {K L : AbelianSheaf.{u, u + 1} S'}
    (s : K ≅ (inverseImage g).obj ((directImage (j ≫ f)).obj F))
    (t : (directImage (pullback.snd j g' ≫ f')).obj
      ((inverseImage (pullback.fst j g')).obj F) ≅ L) : type_of% (
  SourceChartMates.component_epi s
    ((baseChangeMap (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
      ((IsPullback.of_hasPullback j g').paste_vert H).w.symm).app F) t
    (sourceChartOrdinaryExchange_isIso f f' g g' H j F n hn hF)
    ) :=
  SourceChartMates.component_epi s
    ((baseChangeMap (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
      ((IsPullback.of_hasPullback j g').paste_vert H).w.symm).app F) t
    (sourceChartOrdinaryExchange_isIso f f' g g' H j F n hn hF)

end AlgebraicGeometry.Scheme.EtaleCohomology
