/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.RawCartesianIteration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeIterationCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionForgetCoherence

/-!
# Original consecutive raw base change on native torsion inputs

The composite map lands on the literal iterated raw compactification. The
original ambient exchange pasting and original native inclusion/compositor
compatibility prove the torsion-restricted equation. Comparison with the single
pullback source or with normalized models is separate.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX₁ wT wM₁ wX₂ wU wM₂

variable {X S T U : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S) (c : U ⟶ T)

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wM₁} (ModuleSheaf ((C.baseChange b)).Xbar Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wM₂} (ModuleSheaf (((C.baseChange b).baseChange c)).Xbar Λ)]

/-- Derived-category instance on module sheaves over `(pullback b C.p)`, using the instance on
`((C.baseChange b)).Xbar`.
-/
local instance rawIterationFirstNativeModel :
    HasDerivedCategory.{wM₁} (ModuleSheaf (pullback b C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM₁} (ModuleSheaf ((C.baseChange b)).Xbar Λ))
/-- Derived-category instance on module sheaves over `(pullback c ((C.baseChange b)).p)`, using the
instance on `(((C.baseChange b).baseChange c)).Xbar`.
-/
local instance rawIterationSecondNativeModel :
    HasDerivedCategory.{wM₂} (ModuleSheaf (pullback c ((C.baseChange b)).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM₂} (ModuleSheaf (((C.baseChange b).baseChange c)).Xbar Λ))

/-- The original composite exchange on the literal iterated raw model. -/
def moduleRawIterationCompositeMap :
    moduleRawCompactificationFunctor C Λ ⋙ moduleDerivedInverseImage Λ (c ≫ b) ⟶
      moduleDerivedInverseImageTorsion ((pullback.snd c (pullback.fst b f)) ≫ (pullback.snd b f))
        Λ ⋙ moduleRawCompactificationFunctor ((C.baseChange b).baseChange c) Λ :=
  compositeExchange
    (moduleCompactifiedBaseChangeMap C.j C.p (((C.baseChange b).baseChange c)).j (((C.baseChange
      b).baseChange c)).p
      ((pullback.snd c (pullback.fst b f)) ≫ (pullback.snd b f)) ((pullback.snd c (C.baseChange
        b).p) ≫ (pullback.snd b C.p)) (c ≫ b)
      (isPullback_rawIterationOpen C b c) (isPullback_rawIterationProper C b c) Λ)
    (moduleDerivedInverseImageTorsionForgetIso ((pullback.snd c (pullback.fst b f)) ≫
      (pullback.snd b f)) Λ).symm

/-- Consecutive raw base change retains the original native inverse-image
compositors and the original exchange maps, on all native torsion inputs. -/
theorem moduleRawBaseChangeIteration_pasting :
    ∀ K, ActualHorizontalMateEquation
      (moduleRawCompactificationBaseChangeIso C b Λ).hom
      (moduleRawCompactificationBaseChangeIso (C.baseChange b) c Λ).hom
      (moduleRawIterationCompositeMap C b c Λ)
      (moduleDerivedInverseImageCompIso Λ b c).hom
      (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f) (pullback.snd c (pullback.fst
        b f))).hom K :=
  compositeExchange_pasting_of_equations
    (moduleCompactifiedBaseChangeMap C.j C.p ((C.baseChange b)).j ((C.baseChange b)).p
      (pullback.snd b f) (pullback.snd b C.p) b
      (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip Λ)
    (moduleCompactifiedBaseChangeMap ((C.baseChange b)).j ((C.baseChange b)).p (((C.baseChange
      b).baseChange c)).j (((C.baseChange b).baseChange c)).p (pullback.snd c (pullback.fst b f))
      (pullback.snd c (C.baseChange b).p) c
      (isPullback_rawCompactificationOpen (C.baseChange b) c) (IsPullback.of_hasPullback c
        ((C.baseChange b)).p).flip Λ)
    (moduleCompactifiedBaseChangeMap C.j C.p (((C.baseChange b).baseChange c)).j (((C.baseChange
      b).baseChange c)).p
      ((pullback.snd c (pullback.fst b f)) ≫ (pullback.snd b f)) ((pullback.snd c (C.baseChange
        b).p) ≫ (pullback.snd b C.p)) (c ≫ b)
      (isPullback_rawIterationOpen C b c) (isPullback_rawIterationProper C b c) Λ)
    (moduleDerivedInverseImageTorsionForgetIso (pullback.snd b f) Λ).symm
    (moduleDerivedInverseImageTorsionForgetIso (pullback.snd c (pullback.fst b f)) Λ).symm
    (moduleDerivedInverseImageTorsionForgetIso ((pullback.snd c (pullback.fst b f)) ≫
      (pullback.snd b f)) Λ).symm
    (moduleDerivedInverseImageCompIso Λ b c)
    (moduleDerivedInverseImageCompIso Λ (pullback.snd b f) (pullback.snd c (pullback.fst b f)))
    (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f) (pullback.snd c (pullback.fst b
      f)))
    (moduleRawCompactificationBaseChangeIso C b Λ).hom
    (moduleRawCompactificationBaseChangeIso (C.baseChange b) c Λ).hom
    (moduleRawIterationCompositeMap C b c Λ)
    (moduleRawCompactificationBaseChangeIso_hom_fac C b Λ)
    (moduleRawCompactificationBaseChangeIso_hom_fac (C.baseChange b) c Λ) rfl
    (moduleCompactifiedBaseChangeMap_pasting C.j C.p ((C.baseChange b)).j ((C.baseChange b)).p
      (((C.baseChange b).baseChange c)).j (((C.baseChange b).baseChange c)).p
      (pullback.snd b f) (pullback.snd b C.p) b (pullback.snd c (pullback.fst b f)) (pullback.snd
        c (C.baseChange b).p) c (isPullback_rawCompactificationOpen C b)
      (IsPullback.of_hasPullback b C.p).flip (isPullback_rawCompactificationOpen (C.baseChange b) c)
      (IsPullback.of_hasPullback c ((C.baseChange b)).p).flip (isPullback_rawIterationOpen C b c)
      (isPullback_rawIterationProper C b c) Λ)
    (moduleDerivedInverseImageTorsionForgetIso_pasting Λ (pullback.snd b f) (pullback.snd c
      (pullback.fst b f)))

end AlgebraicGeometry.Scheme.EtaleCohomology
