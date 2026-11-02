/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Independence
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramNaturality

/-!
# Actual normalized base change as an isomorphism of compactification diagrams

The literal raw exchange followed by closed densification is natural for the
original refinement transitions. Canonical comparisons commute with this
isomorphism without any cofinality assertion about normalized base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX' wT wN wR

variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]

/-- The original source compactification diagram followed by the actual base pullback. -/
def moduleCompactificationBaseChangeSourceDiagram :
    (Hom.DenseCompactification f)ᵒᵖ ⥤
      ((moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
        DerivedCategory.Plus (ModuleSheaf T Λ)) :=
  moduleCompactificationDiagram (f := f) Λ ⋙
    (Functor.whiskeringRight _ _ _).obj (moduleDerivedInverseImage Λ b)

/-- The target diagram preceded by the native torsion-valued source pullback. -/
def moduleCompactificationBaseChangeTargetDiagram :
    (Hom.DenseCompactification (pullback.fst b f))ᵒᵖ ⥤
      ((moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
        DerivedCategory.Plus (ModuleSheaf T Λ)) :=
  moduleCompactificationDiagram (f := pullback.fst b f) Λ ⋙
    (Functor.whiskeringLeft _ _ _).obj (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)

/-- Every source transition remains the image of the original invertible refinement map. -/
instance moduleCompactificationBaseChangeSourceDiagram_map_isIso
    {C D : (Hom.DenseCompactification f)ᵒᵖ} (r : C ⟶ D) :
    IsIso ((moduleCompactificationBaseChangeSourceDiagram f b Λ).map r) := by
  change IsIso (Functor.whiskerRight ((moduleCompactificationDiagram (f := f) Λ).map r)
    (moduleDerivedInverseImage Λ b))
  infer_instance

/-- Every target transition remains the image of the original invertible refinement map. -/
instance moduleCompactificationBaseChangeTargetDiagram_map_isIso
    {C D : (Hom.DenseCompactification (pullback.fst b f))ᵒᵖ} (r : C ⟶ D) :
    IsIso ((moduleCompactificationBaseChangeTargetDiagram f b Λ).map r) := by
  change IsIso (Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
    ((moduleCompactificationDiagram (f := pullback.fst b f) Λ).map r))
  infer_instance

/-- The actual normalized base-change components form a natural isomorphism of diagrams. -/
def moduleCompactificationBaseChangeDiagramIso :
    moduleCompactificationBaseChangeSourceDiagram f b Λ ≅
      (Hom.DenseCompactification.baseChange b).op ⋙
        moduleCompactificationBaseChangeTargetDiagram f b Λ :=
  NatIso.ofComponents
    (fun C => moduleNormalizedCompactificationBaseChangeIso C.unop b Λ)
    (by
      intro C D r
      exact moduleNormalizedCompactificationBaseChangeIso_naturality r.unop b Λ)

/-- The diagram isomorphism has exactly the original normalized model components. -/
theorem moduleCompactificationBaseChangeDiagramIso_app (C : Hom.DenseCompactification f) :
    (moduleCompactificationBaseChangeDiagramIso f b Λ).app (op C) =
      moduleNormalizedCompactificationBaseChangeIso C b Λ := rfl

/-- Actual normalized base change intertwines all canonical compactification comparisons. -/
theorem moduleCompactificationBaseChangeComparison (C D : Hom.DenseCompactification f) :
    moduleNormalizedCompactificationBaseChangeIso C b Λ ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
          (moduleCompactificationComparison (pullback.fst b f) Λ
            (Hom.DenseCompactification.baseChangeObj b C)
            (Hom.DenseCompactification.baseChangeObj b D)) =
      Functor.isoWhiskerRight (moduleCompactificationComparison f Λ C D)
          (moduleDerivedInverseImage Λ b) ≪≫
        moduleNormalizedCompactificationBaseChangeIso D b Λ := by
  have hn := Functor.cofilteredComparison_natIso
    (Hom.DenseCompactification.baseChange b) (moduleCompactificationBaseChangeDiagramIso f b Λ) C D
  dsimp only [moduleCompactificationBaseChangeSourceDiagram,
    moduleCompactificationBaseChangeTargetDiagram] at hn
  rw [← Functor.cofilteredComparison_postcomp, ← Functor.cofilteredComparison_postcomp] at hn
  exact hn

end AlgebraicGeometry.Scheme.EtaleCohomology
