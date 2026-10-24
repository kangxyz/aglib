/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageRestriction

/-!
# Actual module-valued étale direct-image exchange

The original chart-pullback isomorphism is coefficient-free. Applying the
native continuous-site pushforward construction with module coefficients,
and the original inverse-image/restriction comparison, gives this exchange.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  (Λ : Type (u + 1)) [Ring Λ]

/-- Actual module-valued restriction of direct image on the native pullback chart. -/
def moduleValuedEtaleDirectImageRestrictionIso :
    moduleValuedDirectImage f Λ ⋙ moduleValuedEtaleRestriction g Λ ≅
      moduleValuedEtaleRestriction (pullback.snd g f) Λ ⋙
        moduleValuedDirectImage (pullback.fst g f) Λ := by
  let : (siteEtalePostcompose g ⋙ siteBaseChange f).IsContinuous
      (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology X) :=
    Functor.isContinuous_comp _ _ (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)
  let : (siteBaseChange (pullback.fst g f) ⋙
      siteEtalePostcompose (pullback.snd g f)).IsContinuous
      (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology X) :=
    Functor.isContinuous_comp _ _ (Scheme.smallEtaleTopology T)
      (Scheme.smallEtaleTopology (pullback g f)) (Scheme.smallEtaleTopology X)
  exact Functor.sheafPushforwardContinuousIso (siteEtaleDirectImageRestrictionIso f g).symm
    (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology X)

/-- The exchange retains the original module-valued inverse-image functors. -/
def moduleValuedEtaleBaseChangeIso :
    moduleValuedDirectImage f Λ ⋙ moduleValuedInverseImage g Λ ≅
      moduleValuedInverseImage (pullback.snd g f) Λ ⋙
        moduleValuedDirectImage (pullback.fst g f) Λ :=
  Functor.isoWhiskerLeft (moduleValuedDirectImage f Λ) (moduleValuedInverseImageEtaleIso g Λ) ≪≫
    moduleValuedEtaleDirectImageRestrictionIso f g Λ ≪≫
    Functor.isoWhiskerRight (moduleValuedInverseImageEtaleIso (pullback.snd g f) Λ).symm
      (moduleValuedDirectImage (pullback.fst g f) Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
