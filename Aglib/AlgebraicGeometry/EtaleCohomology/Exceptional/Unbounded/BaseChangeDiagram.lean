/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChangeNaturality
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationIndependence
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
def moduleUnboundedCompactificationBaseChangeSourceDiagram :
    (Hom.DenseCompactification f)ᵒᵖ ⥤
      (DerivedCategory (ModuleSheaf X Λ) ⥤
        DerivedCategory (ModuleSheaf T Λ)) :=
  moduleUnboundedCompactificationDiagram (f := f) Λ ⋙
    (Functor.whiskeringRight _ _ _).obj (moduleUnboundedDerivedInverseImage Λ b)

/-- The target diagram preceded by the native source pullback. -/
def moduleUnboundedCompactificationBaseChangeTargetDiagram :
    (Hom.DenseCompactification (pullback.fst b f))ᵒᵖ ⥤
      (DerivedCategory (ModuleSheaf X Λ) ⥤
        DerivedCategory (ModuleSheaf T Λ)) :=
  moduleUnboundedCompactificationDiagram (f := pullback.fst b f) Λ ⋙
    (Functor.whiskeringLeft _ _ _).obj (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ

omit [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  targetModels rawModels in
/-- Every source transition remains the image of the original invertible refinement map. -/
theorem moduleUnboundedCompactificationBaseChangeSourceDiagram_map_isIso
    {C D : (Hom.DenseCompactification f)ᵒᵖ} (r : C ⟶ D) :
    IsIso ((moduleUnboundedCompactificationBaseChangeSourceDiagram f b Λ).map r) := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  change IsIso (Functor.whiskerRight ((moduleUnboundedCompactificationDiagram (f := f) Λ).map r)
    (moduleUnboundedDerivedInverseImage Λ b))
  infer_instance

omit [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] sourceModels rawModels in
/-- Every target transition remains the image of the original invertible refinement map. -/
theorem moduleUnboundedCompactificationBaseChangeTargetDiagram_map_isIso
    {C D : (Hom.DenseCompactification (pullback.fst b f))ᵒᵖ} (r : C ⟶ D) :
    IsIso ((moduleUnboundedCompactificationBaseChangeTargetDiagram f b Λ).map r) := by
  let := moduleUnboundedCompactificationDiagram_map_isIso
    (f := pullback.fst b f) Λ N hN hΛ
  change IsIso (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
    ((moduleUnboundedCompactificationDiagram (f := pullback.fst b f) Λ).map r))
  infer_instance

/-- The actual normalized base-change components form a natural isomorphism of diagrams. -/
def moduleUnboundedCompactificationBaseChangeDiagramIso :
    moduleUnboundedCompactificationBaseChangeSourceDiagram f b Λ ≅
      (Hom.DenseCompactification.baseChange b).op ⋙
        moduleUnboundedCompactificationBaseChangeTargetDiagram f b Λ :=
  NatIso.ofComponents
    (fun C => moduleUnboundedNormalizedCompactificationBaseChangeIso C.unop b Λ N hN hΛ)
    (by
      intro C D r
      exact moduleUnboundedNormalizedCompactificationBaseChangeIso_naturality r.unop b Λ N hN hΛ)

/-- The diagram isomorphism has exactly the original normalized model components. -/
theorem moduleUnboundedCompactificationBaseChangeDiagramIso_app (C : Hom.DenseCompactification f) :
    (moduleUnboundedCompactificationBaseChangeDiagramIso f b Λ N hN hΛ).app (op C) =
      moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ := rfl

/-- Actual normalized base change intertwines all canonical compactification comparisons. -/
theorem moduleUnboundedCompactificationBaseChangeComparison (C D : Hom.DenseCompactification f) :
    moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
          (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
            (Hom.DenseCompactification.baseChangeObj b C)
            (Hom.DenseCompactification.baseChangeObj b D)) =
      Functor.isoWhiskerRight (moduleUnboundedCompactificationComparison f Λ N hN hΛ C D)
          (moduleUnboundedDerivedInverseImage Λ b) ≪≫
        moduleUnboundedNormalizedCompactificationBaseChangeIso D b Λ N hN hΛ := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  let := moduleUnboundedCompactificationDiagram_map_isIso
    (f := pullback.fst b f) Λ N hN hΛ
  let : ∀ (C D : (Hom.DenseCompactification f)ᵒᵖ) (r : C ⟶ D),
      IsIso ((moduleUnboundedCompactificationBaseChangeSourceDiagram f b Λ).map r) :=
    fun _ _ r => moduleUnboundedCompactificationBaseChangeSourceDiagram_map_isIso f b Λ N hN hΛ r
  let : ∀ (C D : (Hom.DenseCompactification (pullback.fst b f))ᵒᵖ) (r : C ⟶ D),
      IsIso ((moduleUnboundedCompactificationBaseChangeTargetDiagram f b Λ).map r) :=
    fun _ _ r => moduleUnboundedCompactificationBaseChangeTargetDiagram_map_isIso f b Λ N hN hΛ r
  have hn := Functor.cofilteredComparison_natIso
    (Hom.DenseCompactification.baseChange b)
    (moduleUnboundedCompactificationBaseChangeDiagramIso f b Λ N hN hΛ) C D
  dsimp only [moduleUnboundedCompactificationBaseChangeSourceDiagram,
    moduleUnboundedCompactificationBaseChangeTargetDiagram] at hn
  rw [← Functor.cofilteredComparison_postcomp, ← Functor.cofilteredComparison_postcomp] at hn
  exact hn

end AlgebraicGeometry.Scheme.EtaleCohomology
