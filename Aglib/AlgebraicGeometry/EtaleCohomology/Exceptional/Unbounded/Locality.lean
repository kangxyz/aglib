/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RestrictionCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.EtaleCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperBaseChange
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.MateCubeRestriction

/-! # Local relative bounds for the original unbounded proper exchange

The original exchange is local on an etale cover. Its precise restriction
cube and unconditional etale exchange identify the map detected by the cover.
The proper corollary consumes two explicit all-object bounds on each local
square. Those bounds may vary with the chart; no global bound, absolute base
cohomological dimension, or geometric bound supplier is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u v wX wS wX' wS' wY wT wY' wT' wAY wAT wAY' wAT'

variable (Λ : Type (u + 1)) [Ring Λ]

section Restriction
variable {X S X' S' Y T Y' T' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf Y' Λ)]
  [HasDerivedCategory.{wT'} (ModuleSheaf T' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (p : Y ⟶ T) (p' : Y' ⟶ T') (q : T' ⟶ T) (q' : Y' ⟶ Y)
  (jS : T ⟶ S) (jX : Y ⟶ X) (jS' : T' ⟶ S') (jX' : Y' ⟶ X')
  [Etale jS] [Etale jX] [Etale jS'] [Etale jX']
  (sf : IsPullback p jX jS f) (sf' : IsPullback p' jX' jS' f')
  (hg : q ≫ jS = jS' ≫ g) (hg' : q' ≫ jX = jX' ≫ g')
  (h : f' ≫ g = g' ≫ f) (h' : p' ≫ q = q' ≫ p)

include sf sf' hg hg' in
/-- The actual restricted global exchange is invertible whenever the actual
local exchange is; original etale exchange supplies both vertical comparisons. -/
theorem moduleUnboundedDerivedBaseChange_restriction_isIso
    [IsIso (moduleUnboundedDerivedBaseChangeMap Λ p p' q q' h')]
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    IsIso ((moduleUnboundedDerivedInverseImage Λ jS').map
      ((moduleUnboundedDerivedBaseChangeMap Λ f f' g g' h).app K)) := by
  let : IsIso (moduleUnboundedDerivedBaseChangeMap Λ f p jS jX sf.w) :=
    moduleUnboundedDerivedBaseChange_isIso_of_etale p jX jS f sf Λ
  let : IsIso (moduleUnboundedDerivedBaseChangeMap Λ f' p' jS' jX' sf'.w) :=
    moduleUnboundedDerivedBaseChange_isIso_of_etale p' jX' jS' f' sf' Λ
  exact (moduleUnboundedDerivedBaseChangeMap_restriction_cube Λ f f' g g' p p' q q'
    jS jX jS' jX' sf.w sf'.w hg hg' h h').isIso_source_map_app K
end Restriction

namespace Proper

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}} {ι : Type v}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)
  (U : ι → S'.Etale)
  (hU : ∀ s : S', ∃ (i : ι) (x : (U i).left), (U i).hom x = s)
  (Y T Y' : ι → Scheme.{u})
  [modelsY : ∀ i, HasDerivedCategory.{wY} (ModuleSheaf (Y i) Λ)]
  [modelsT : ∀ i, HasDerivedCategory.{wT} (ModuleSheaf (T i) Λ)]
  [modelsY' : ∀ i, HasDerivedCategory.{wY'} (ModuleSheaf (Y' i) Λ)]
  [modelsT' : ∀ i, HasDerivedCategory.{wT'} (ModuleSheaf (U i).left Λ)]
  [modelsAY : ∀ i, HasDerivedCategory.{wAY} (AbelianSheaf.{u, u + 1} (Y i))]
  [modelsAT : ∀ i, HasDerivedCategory.{wAT} (AbelianSheaf.{u, u + 1} (T i))]
  [modelsAY' : ∀ i, HasDerivedCategory.{wAY'} (AbelianSheaf.{u, u + 1} (Y' i))]
  [modelsAT' : ∀ i, HasDerivedCategory.{wAT'} (AbelianSheaf.{u, u + 1} (U i).left)]
  (p : ∀ i, Y i ⟶ T i) (p' : ∀ i, Y' i ⟶ (U i).left)
  (q : ∀ i, (U i).left ⟶ T i) (q' : ∀ i, Y' i ⟶ Y i)
  (jS : ∀ i, T i ⟶ S) (jX : ∀ i, Y i ⟶ X) (jX' : ∀ i, Y' i ⟶ X')
  [etaleS : ∀ i, Etale (jS i)]
  (sf : ∀ i, IsPullback (p i) (jX i) (jS i) f)
  (sf' : ∀ i, IsPullback (p' i) (jX' i) (U i).hom f')
  (hg : ∀ i, q i ≫ jS i = (U i).hom ≫ g)
  (hg' : ∀ i, q' i ≫ jX i = jX' i ≫ g')
  (localSq : ∀ i, IsPullback (q' i) (p' i) (p i) (q i))

include sq hU sf sf' hg hg' localSq

omit modelsAY modelsAT modelsAY' modelsAT' in
/-- Chart-dependent pairs of explicit relative bounds imply invertibility of
the actual original unbounded proper exchange, with no quasi-compactness or
global uniform-bound hypothesis. The geometric bounds are inputs, not claims. -/
theorem properModuleUnboundedDerivedBaseChange_isIso_of_local_bounds
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) (d d' : ι → ℕ)
    (hp : ∀ i (M : ModuleSheaf (Y i) Λ),
      IsZero (((moduleDirectImage (p i) Λ).rightDerived (d i + 1)).obj M))
    (hp' : ∀ i (M : ModuleSheaf (Y' i) Λ),
      IsZero (((moduleDirectImage (p' i) Λ).rightDerived (d' i + 1)).obj M)) :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  have hK (K : DerivedCategory (ModuleSheaf X Λ)) :
      IsIso ((moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) := by
    apply isIso_of_moduleUnboundedDerived_etale_inverseImages Λ U hU
    intro i
    let : Etale (jX i) := MorphismProperty.of_isPullback (sf i) (etaleS i)
    let : Etale (jX' i) := MorphismProperty.of_isPullback (sf' i) inferInstance
    let : IsProper (p i) := MorphismProperty.of_isPullback (sf i).flip inferInstance
    let : IsIso (moduleUnboundedDerivedBaseChangeMap Λ (p i) (p' i) (q i) (q' i)
        (localSq i).w.symm) :=
      properModuleUnboundedDerivedBaseChange_isIso_of_bounds Λ
        (p i) (p' i) (q i) (q' i) (localSq i) N hN hΛ (d i) (d' i) (hp i) (hp' i)
    exact moduleUnboundedDerivedBaseChange_restriction_isIso Λ f f' g g'
      (p i) (p' i) (q i) (q' i) (jS i) (jX i) (U i).hom (jX' i)
      (sf i) (sf' i) (hg i) (hg' i) sq.w.symm (localSq i).w.symm K
  let := hK
  exact NatIso.isIso_of_isIso_app
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm)

end Proper

end AlgebraicGeometry.Scheme.EtaleCohomology
