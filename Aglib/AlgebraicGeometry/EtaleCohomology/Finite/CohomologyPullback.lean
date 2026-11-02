/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Original finite-direct-image pullback comparisons

The canonical finite base-change mate and original finite-cohomology
comparison identify the actual two pullback maps. The four Ext universes
remain independent. No global-cohomology invariance is assumed or asserted
without the corresponding property of the original cover pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) [IsFinite f] (f' : X' ⟶ S')
  (g : S' ⟶ S) (g' : X' ⟶ X) (h : IsPullback g' f' f g)
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

include h

/-- Surjectivity of the original direct-image pullback is precisely
surjectivity on the actual finite cover. -/
theorem cohomologyPullback_directImage_surjective_iff :
    Function.Surjective (cohomologyPullback g ((directImage f).obj F) q) ↔
      Function.Surjective (cohomologyPullback g' F q) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let β := (baseChangeMap f f' g g' h.w.symm).app F
  let : IsIso β := finiteBaseChange_app_isIso f f' g g' h F
  let e := finiteCohomologyDirectImageAddEquiv f F q
  let e' := finiteCohomologyDirectImageAddEquiv f' ((inverseImage g').obj F) q
  have hb : Function.Bijective (Sheaf.H.map β q) :=
    cohomologyMapIso_bijective (asIso β) q
  have hs : (e' ∘ Sheaf.H.map β q) ∘
      cohomologyPullback g ((directImage f).obj F) q = cohomologyPullback g' F q ∘ e := by
    funext a
    exact finiteCohomologyDirectImageAddEquiv_baseChange f f' g g' h F q a
  calc
    _ ↔ Function.Surjective ((e' ∘ Sheaf.H.map β q) ∘
        cohomologyPullback g ((directImage f).obj F) q) :=
      (Function.Surjective.of_comp_iff' (e'.bijective.comp hb) _).symm
    _ ↔ Function.Surjective (cohomologyPullback g' F q ∘ e) := by rw [hs]
    _ ↔ _ := Function.Surjective.of_comp_iff _ e.surjective

/-- Injectivity of the original direct-image pullback is precisely
injectivity on the actual finite cover. -/
theorem cohomologyPullback_directImage_injective_iff :
    Function.Injective (cohomologyPullback g ((directImage f).obj F) q) ↔
      Function.Injective (cohomologyPullback g' F q) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let β := (baseChangeMap f f' g g' h.w.symm).app F
  let : IsIso β := finiteBaseChange_app_isIso f f' g g' h F
  let e := finiteCohomologyDirectImageAddEquiv f F q
  let e' := finiteCohomologyDirectImageAddEquiv f' ((inverseImage g').obj F) q
  have hb : Function.Bijective (Sheaf.H.map β q) :=
    cohomologyMapIso_bijective (asIso β) q
  have hs : (e' ∘ Sheaf.H.map β q) ∘
      cohomologyPullback g ((directImage f).obj F) q = cohomologyPullback g' F q ∘ e := by
    funext a
    exact finiteCohomologyDirectImageAddEquiv_baseChange f f' g g' h F q a
  calc
    _ ↔ Function.Injective ((e' ∘ Sheaf.H.map β q) ∘
        cohomologyPullback g ((directImage f).obj F) q) :=
      (Function.Injective.of_comp_iff (e'.injective.comp hb.injective) _).symm
    _ ↔ Function.Injective (cohomologyPullback g' F q ∘ e) := by rw [hs]
    _ ↔ _ := Function.Injective.of_comp_iff' _ e.bijective

/-- Bijectivity of the unchanged original finite-direct-image comparison. -/
theorem cohomologyPullback_directImage_bijective_iff :
    Function.Bijective (cohomologyPullback g ((directImage f).obj F) q) ↔
      Function.Bijective (cohomologyPullback g' F q) :=
  and_congr (cohomologyPullback_directImage_injective_iff f f' g g' h F q)
    (cohomologyPullback_directImage_surjective_iff f f' g g' h F q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
