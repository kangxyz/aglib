/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleEvaluation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitGeometry

/-! # The original terminal test in an étale direct-image square

The native pasted pullback comparison sends the actual terminal test to the
base change of the original chart-terminal comparison. This geometric identity
retains the actual site arrows needed for original chart evaluation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

/-- The original terminal tests commute with the actual étale site square. -/
theorem siteEtaleDirectImageRestriction_terminal {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.Etale) :
    (Continuity.siteEtalePostcomposeTerminalIso ((siteBaseChange f).obj U)).inv ≫
        (siteEtalePostcompose (pullback.snd U.hom f)).map
          (siteBaseChangeTerminalIso (pullback.fst U.hom f)).inv ≫
        (siteEtaleDirectImageRestrictionIso f U.hom).hom.app (etaleTerminal U.left) =
      (siteBaseChange f).map (Continuity.siteEtalePostcomposeTerminalIso U).inv := by
  apply (Scheme.Etale.forget X).map_injective
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫ (siteBaseChangeTerminalIso (pullback.fst U.hom f)).inv.left ≫
      (pullbackRightPullbackFstIso U.hom f (𝟙 U.left)).hom) =
    pullback.lift (pullback.fst U.hom f ≫ 𝟙 U.left) (pullback.snd U.hom f) _
  exact congrArg (fun a => a.left)
    (Over.pullbackPostcomposeIso_terminal f (Over.mk U.hom)
      ((Scheme.Etale.forget (pullback U.hom f)).map
        (siteBaseChangeTerminalIso (pullback.fst U.hom f)).inv))

end AlgebraicGeometry.Scheme.EtaleCohomology
