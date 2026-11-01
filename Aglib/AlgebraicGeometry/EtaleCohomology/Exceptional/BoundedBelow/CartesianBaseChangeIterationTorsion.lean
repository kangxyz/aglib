/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChangeIteration

/-! # Consecutive given-presentation base change on native torsion output -/

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

local instance cartesianTorsionIterationLiteral₁ :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
local instance cartesianTorsionIterationLiteral₂ :
    Nonempty (Hom.DenseCompactification (pullback.fst c f₁)) :=
  ⟨baseChangeObj c (moduleExceptionalSuppliedCompactification f₁)⟩
local instance cartesianTorsionIterationIterated :
    Nonempty (Hom.DenseCompactification (pullback.fst c (pullback.fst b f))) :=
  ⟨baseChangeObj c (moduleExceptionalSuppliedCompactification (pullback.fst b f))⟩
local instance cartesianTorsionIterationSingle :
    Nonempty (Hom.DenseCompactification (pullback.fst (c ≫ b) f)) :=
  ⟨baseChangeObj (c ≫ b) (moduleExceptionalSuppliedCompactification f)⟩

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wRR}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]


include C in
/-- Faithful native torsion output retains the same original given-square pasting
law and the same original base/source inverse-image compositors. -/
theorem moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty_iteration
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ActualHorizontalMateEquation
      (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty f f₁ b a sq₁ Λ).hom
      (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty f₁ f₂ c d sq₂ Λ).hom
      (moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
        f f₂ (c ≫ b) (d ≫ a) (sq₂.paste_horiz sq₁) Λ).hom
      (moduleDerivedInverseImageTorsionCompIso Λ b c).hom
      (moduleDerivedInverseImageTorsionCompIso Λ a d).hom K := by
  apply ObjectProperty.hom_ext
  exact moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_iteration
    f f₁ f₂ b c a d sq₁ sq₂ Λ C K

end AlgebraicGeometry.Scheme.EtaleCohomology
