/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ChartOrdinaryExchange
public import Aglib.CategoryTheory.Adjunction.Mates.ComparisonEpimorphism

/-! # Ordinary chart epimorphy before native chart specialization -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge

theorem sourceChartComparison_epi
    {X S X' S' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g) [Smooth g]
    (j : T ⟶ X)
    (P : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} T)
    (Q : AbelianSheaf.{u, u + 1} X' ⥤ AbelianSheaf.{u, u + 1} (pullback j g'))
    (A : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S)
    (B : AbelianSheaf.{u, u + 1} X' ⥤ AbelianSheaf.{u, u + 1} S')
    (e : P ⋙ inverseImage (pullback.fst j g') ≅ inverseImage g' ⋙ Q)
    (s : A ≅ P ⋙ directImage (j ≫ f))
    (t : B ≅ Q ⋙ directImage (pullback.snd j g' ≫ f'))
    (δ : A ⋙ inverseImage g ⟶ inverseImage g' ⋙ B)
    (hδ : δ = SourceChartMates.comparison e
      (baseChangeMap (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
        ((IsPullback.of_hasPullback j g').paste_vert H).w.symm) s t)
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n)
    (hF : n • 𝟙 (P.obj F) = 0) : type_of% (
  SourceChartMates.comparison_epi_of_eq e
    (baseChangeMap (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
      ((IsPullback.of_hasPullback j g').paste_vert H).w.symm) s t δ hδ F
    (sourceChartOrdinaryExchange_isIso f f' g g' H j (P.obj F) n hn hF)
    ) :=
  SourceChartMates.comparison_epi_of_eq e
    (baseChangeMap (j ≫ f) (pullback.snd j g' ≫ f') g (pullback.fst j g')
      ((IsPullback.of_hasPullback j g').paste_vert H).w.symm) s t δ hδ F
    (sourceChartOrdinaryExchange_isIso f f' g g' H j (P.obj F) n hn hF)

end AlgebraicGeometry.Scheme.EtaleCohomology
