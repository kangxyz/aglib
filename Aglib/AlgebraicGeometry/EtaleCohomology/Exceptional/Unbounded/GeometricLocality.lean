/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.GeometricBounds
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Locality

/-! # Geometric bounds discharge the original local proper-exchange inputs

Each supplied quasi-compact target chart has an actual geometric relative
bound. Those bounds, rather than extra vanishing hypotheses, enter the
accepted local-to-global theorem for the same original unbounded exchange.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u v wX wS wX' wS' wY wT wY' wT' wAY wAT wAY' wAT'

variable (Λ : Type (u + 1)) [Ring Λ]

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
  [compactCharts : ∀ i, CompactSpace (T i)]
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

/-- Actual geometric relative bounds on quasi-compact charts imply the original
unbounded proper exchange; no cohomological bound remains as an input. -/
theorem properModuleUnboundedDerivedBaseChange_isIso_of_compact_local_charts
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    IsIso (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) := by
  have hbound (i : ι) : ∃ D : ℕ,
      (∀ F : AbelianSheaf.{u, u + 1} (Y i), Sheaf.IsTorsion F →
        IsZero ((higherDirectImage (p i) (D + 1)).obj F)) ∧
      (∀ F : AbelianSheaf.{u, u + 1} (Y' i), Sheaf.IsTorsion F →
        IsZero ((higherDirectImage (p' i) (D + 1)).obj F)) := by
    let : IsProper (p i) := MorphismProperty.of_isPullback (sf i).flip inferInstance
    exact exists_higherDirectImage_torsion_bounds_of_isPullback
      (p i) (p' i) (q i) (q' i) (localSq i)
  choose d hd hd' using hbound
  exact properModuleUnboundedDerivedBaseChange_isIso_of_local_bounds
    Λ f f' g g' sq U hU Y T Y' p p' q q' jS jX jX' sf sf' hg hg' localSq
    N hN hΛ d d
    (fun i => moduleRightDerived_bound_of_torsion_bound Λ (p i) N hN hΛ (d i) (hd i))
    (fun i => moduleRightDerived_bound_of_torsion_bound Λ (p' i) N hN hΛ (d i) (hd' i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
