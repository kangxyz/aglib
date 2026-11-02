/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChangeLiteral

/-! # The literal Cartesian specialization on native torsion output -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wL wT wM wN wR
variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (g : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback g f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ C : Hom.DenseCompactification (pullback.fst g f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback g C.p) Λ)]

local instance literalTorsionNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst g f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj g (moduleExceptionalSuppliedCompactification f)⟩

/-- The native torsion Cartesian comparison also retains the original literal exchange. -/
theorem moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty_literal :
    moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
        f (pullback.fst g f) g (pullback.snd g f) (IsPullback.of_hasPullback g f).flip Λ =
      moduleExceptionalDirectImagePlusTorsionBaseChangeIsoOfNonempty f g Λ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun i => i.hom.app K)
    (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_literal f g Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
