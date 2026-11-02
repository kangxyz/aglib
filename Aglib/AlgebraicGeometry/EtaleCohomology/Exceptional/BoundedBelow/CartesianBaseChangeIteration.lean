/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourcePastingConclusion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianSourcePolygon
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoCompositionCongruence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeIteration

/-! # Consecutive exceptional base change for actual given Cartesian presentations -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wX₁ wX₂ wL₁ wL₂ wLi wLs wS wT wU
  wM wM₁ wM₂ wN₁ wN₂ wNi wNs wR₁ wR₂ wRi wRs wRR
variable {X X₁ X₂ S T U : Scheme.{u}}
  (f : X ⟶ S) (f₁ : X₁ ⟶ T) (f₂ : X₂ ⟶ U)
  (b : T ⟶ S) (c : U ⟶ T) (a : X₁ ⟶ X) (d : X₂ ⟶ X₁)
  (sq₁ : IsPullback a f₁ f b) (sq₂ : IsPullback d f₂ f₁ c)
  [QuasiCompact f] [QuasiCompact f₁] [QuasiCompact f₂]
  [Nonempty (Hom.DenseCompactification f)]
  [Nonempty (Hom.DenseCompactification f₁)] [Nonempty (Hom.DenseCompactification f₂)]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hX₁ : HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [hX₂ : HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [hL₁ : HasDerivedCategory.{wL₁} (ModuleSheaf (pullback b f) Λ)]
  [hL₂ : HasDerivedCategory.{wL₂} (ModuleSheaf (pullback c f₁) Λ)]
  [hLi : HasDerivedCategory.{wLi} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [hLs : HasDerivedCategory.{wLs} (ModuleSheaf (pullback (c ≫ b) f) Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [hU : HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [models₁ : ∀ C : Hom.DenseCompactification f₁,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ)]
  [models₂ : ∀ C : Hom.DenseCompactification f₂,
    HasDerivedCategory.{wM₂} (ModuleSheaf C.Xbar Λ)]
  [literal₁ : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN₁} (ModuleSheaf C.Xbar Λ)]
  [literal₂ : ∀ C : Hom.DenseCompactification (pullback.fst c f₁),
    HasDerivedCategory.{wN₂} (ModuleSheaf C.Xbar Λ)]
  [iterated : ∀ C : Hom.DenseCompactification (pullback.fst c (pullback.fst b f)),
    HasDerivedCategory.{wNi} (ModuleSheaf C.Xbar Λ)]
  [single : ∀ C : Hom.DenseCompactification (pullback.fst (c ≫ b) f),
    HasDerivedCategory.{wNs} (ModuleSheaf C.Xbar Λ)]
  [raw₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ)]
  [raw₂ : ∀ C : Hom.DenseCompactification f₁,
    HasDerivedCategory.{wR₂} (ModuleSheaf (pullback c C.p) Λ)]
  [rawIterated : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wRi} (ModuleSheaf (pullback c C.p) Λ)]
  [rawSingle : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wRs} (ModuleSheaf (pullback (c ≫ b) C.p) Λ)]

local instance cartesianIterationLiteral₁ :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
local instance cartesianIterationLiteral₂ :
    Nonempty (Hom.DenseCompactification (pullback.fst c f₁)) :=
  ⟨baseChangeObj c (moduleExceptionalSuppliedCompactification f₁)⟩
local instance cartesianIterationIterated :
    Nonempty (Hom.DenseCompactification (pullback.fst c (pullback.fst b f))) :=
  ⟨baseChangeObj c (moduleExceptionalSuppliedCompactification (pullback.fst b f))⟩
local instance cartesianIterationSingle :
    Nonempty (Hom.DenseCompactification (pullback.fst (c ≫ b) f)) :=
  ⟨baseChangeObj (c ≫ b) (moduleExceptionalSuppliedCompactification f)⟩

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wRR}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]

include C in
/-- The original exchanges of two given Cartesian squares paste to the original
exchange of their actual pasted square. All literal and presentation models remain
independent; the new bases need no qcqs hypothesis. -/
theorem moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_iteration
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ActualHorizontalMateEquation
      (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f f₁ b a sq₁ Λ).hom
      (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f₁ f₂ c d sq₂ Λ).hom
      (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty
        f f₂ (c ≫ b) (d ≫ a) (sq₂.paste_horiz sq₁) Λ).hom
      (moduleDerivedInverseImageCompIso Λ b c).hom
      (moduleDerivedInverseImageTorsionCompIso Λ a d).hom K := by
  let e₁ := sq₁.flip.isoPullback
  let e₂ := sq₂.flip.isoPullback
  let eb := pullbackSourceIso f₁ e₁ sq₁.flip.isoPullback_hom_fst c
  let eBI := e₂ ≪≫ eb
  have heBI : eBI.hom ≫ pullback.fst c (pullback.fst b f) = f₂ :=
    sourceIso_comp_fac (pullback.fst c (pullback.fst b f)) (pullback.fst c f₁) f₂
      eb e₂ (pullbackSourceIso_hom_fst f₁ e₁ sq₁.flip.isoPullback_hom_fst c)
      sq₂.flip.isoPullback_hom_fst
  have hb := sourceIsoBaseChange_targetTransport
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst b f) f₁
      e₁ sq₁.flip.isoPullback_hom_fst Λ)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f₁ c Λ)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty (pullback.fst b f) c Λ).hom
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst c (pullback.fst b f))
      (pullback.fst c f₁) eb
      (pullbackSourceIso_hom_fst f₁ e₁ sq₁.flip.isoPullback_hom_fst c) Λ)
    (moduleSourceBaseChangeSquareIso (pullback.fst b f) f₁ e₁
      sq₁.flip.isoPullback_hom_fst c Λ)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst c f₁) f₂
      e₂ sq₂.flip.isoPullback_hom_fst Λ)
    (moduleCartesianBaseChangeSourceIso f₁ f₂ c d sq₂ Λ)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst c (pullback.fst b f))
      f₂ eBI heBI Λ)
    (moduleDerivedInverseImageTorsionCompIso Λ eb.hom e₂.hom)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_baseChange
      (pullback.fst b f) f₁ e₁ sq₁.flip.isoPullback_hom_fst c Λ)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_composition
      (pullback.fst c (pullback.fst b f)) (pullback.fst c f₁) f₂ eb e₂
      (pullbackSourceIso_hom_fst f₁ e₁ sq₁.flip.isoPullback_hom_fst c)
      sq₂.flip.isoPullback_hom_fst Λ)
  have hs := moduleExceptionalDirectImagePlusSourceIsoOfNonempty_composition_of_eq
    (pullback.fst (c ≫ b) f) (pullback.fst c (pullback.fst b f)) f₂
    (iteratedSourceIso b c) eBI (iteratedSourceIso_hom_fst b c) heBI Λ
    (sq₂.paste_horiz sq₁).flip.isoPullback (sq₂.paste_horiz sq₁).flip.isoPullback_hom_fst
    (cartesianPresentation_isoPullback_pasting_sourceIso f f₁ f₂ b c a d sq₁ sq₂)
  have hp := cartesianSourceExchange_pasting
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty (pullback.fst b f) c Λ).hom
    (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f₁ f₂ c d sq₂ Λ).hom
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f (c ≫ b) Λ).hom
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst b f) f₁
      e₁ sq₁.flip.isoPullback_hom_fst Λ)
    (moduleCartesianBaseChangeSourceIso f f₁ b a sq₁ Λ)
    _ _ _ _ _ _ _ _ _ _
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_iteration f b c Λ C)
    hb hs (moduleCartesianBaseChangeSourceIso_pasting f f₁ f₂ b c a d sq₁ sq₂ Λ)
  exact cartesianSourceExchange_pasting_conclusion _ _ _ _ _ _ _ hp K

end AlgebraicGeometry.Scheme.EtaleCohomology
