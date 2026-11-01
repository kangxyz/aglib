/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIdentityComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeCompatibility


/-!
# Original compactified base change under an actual target ambient isomorphism

The source refinement is the original identity; the target refinement is the
specified scheme isomorphism with its actual open and structural triangles.
The original exchange is compared through its original unit-induced transition.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wS wX' wC wD wT

variable {X Y S X' C D T : Scheme.{u}}
  (j : X ⟶ Y) (p : Y ⟶ S)
  (jC : X' ⟶ C) (pC : C ⟶ T) (jD : X' ⟶ D) (pD : D ⟶ T)
  [IsOpenImmersion j] [IsOpenImmersion jC] [IsOpenImmersion jD]
  (a : X' ⟶ X) (qC : C ⟶ Y) (qD : D ⟶ Y) (b : T ⟶ S)
  (k : C ⟶ D) [IsIso k]
  (sq : IsPullback jC (𝟙 X') k jD) (hkp : k ≫ pD = pC) (hkq : k ≫ qD = qC)
  (hjC : IsPullback a jC j qC) (hjD : IsPullback a jD j qD)
  (hpC : IsPullback qC pC p b) (hpD : IsPullback qD pD p b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

include hkq in
/-- Original exchange to isomorphic target ambient models commutes with the
actual original refinement transition, without relabelling either model. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_targetIso :
    TargetIsoBaseChangeEquation
      (moduleUnboundedCompactifiedBaseChangeMap j p jC pC a qC b hjC hpC Λ)
      (moduleUnboundedCompactifiedBaseChangeMap j p jD pD a qD b hjD hpD Λ)
      (imageComparison (moduleUnboundedDerivedProperRefinementComparison jC jD k sq Λ)
        (moduleUnboundedDerivedDirectImageOverIso Λ pC pD k hkp)) := by
  have sq₀ : IsPullback j (𝟙 X) (𝟙 Y) j := IsPullback.of_vert_isIso ⟨by simp⟩
  have hh : IsPullback qC k (𝟙 Y) qD :=
    IsPullback.of_vert_isIso ⟨by simpa only [Category.comp_id] using hkq.symm⟩
  exact targetIsoBaseChange_of_identity_source
    (moduleUnboundedDerivedProperRefinementComparison j j (𝟙 Y) sq₀ Λ)
    (moduleUnboundedDerivedProperRefinementComparison jC jD k sq Λ)
    (moduleUnboundedDerivedDirectImageOverIso Λ p p (𝟙 Y) (Category.id_comp p))
    (moduleUnboundedDerivedDirectImageOverIso Λ pC pD k hkp)
    (moduleUnboundedDerivedBaseChangeMap Λ p pC b qC hpC.w.symm)
    (moduleUnboundedDerivedBaseChangeMap Λ p pD b qD hpD.w.symm)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jC j qC hjC Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a jD j qD hjD Λ)
    (moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
      j j (𝟙 Y) sq₀ jC jD k sq a qC qD hjC hjD hh Λ
      p p (Category.id_comp p) pC pD hkp b hpC hpD)
    (moduleUnboundedRawImageComparison_id j sq₀ Λ p)

end AlgebraicGeometry.Scheme.EtaleCohomology
