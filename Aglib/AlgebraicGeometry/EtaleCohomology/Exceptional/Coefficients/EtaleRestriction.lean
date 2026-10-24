/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction

/-!
# Original étale restriction with arbitrary module coefficients

Restriction is actual precomposition with postcomposition of étale charts.
The comparison with the original module-valued inverse image is normalized
by the original site adjunction and its counit on every test scheme. The
native constant-ring lower-shriek construction uses this comparison together
with `moduleInverseImageTransportIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
  (Λ : Type (u + 1)) [Ring Λ]

/-- Actual restriction of module-valued sheaves to an étale chart. -/
abbrev moduleValuedEtaleRestriction : ModuleValuedSheaf X Λ ⥤ ModuleValuedSheaf S Λ :=
  (siteEtalePostcompose f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

/-- The original site adjunction gives restriction as a left adjoint to actual direct image. -/
def moduleValuedEtaleRestrictionAdjunction :
    moduleValuedEtaleRestriction f Λ ⊣ moduleValuedDirectImage f Λ :=
  (siteEtalePostcomposeAdj f).sheafPushforwardContinuous (E := ModuleCat.{u + 1} Λ)
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X)

/-- The original module-valued inverse image on an étale chart is actual restriction. -/
def moduleValuedInverseImageEtaleIso :
    moduleValuedInverseImage f Λ ≅ moduleValuedEtaleRestriction f Λ :=
  (moduleValuedInverseImageAdjunction f Λ).leftAdjointUniq
    (moduleValuedEtaleRestrictionAdjunction f Λ)

/-- Restriction comparison retains the original module-valued inverse-image unit. -/
@[reassoc]
theorem moduleValuedInverseImageEtaleIso_unit (F : ModuleValuedSheaf X Λ) :
    (moduleValuedInverseImageAdjunction f Λ).unit.app F ≫
      (moduleValuedDirectImage f Λ).map ((moduleValuedInverseImageEtaleIso f Λ).hom.app F) =
    (moduleValuedEtaleRestrictionAdjunction f Λ).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- On each test scheme the normalized unit is the actual counit of the site adjunction. -/
@[reassoc]
theorem moduleValuedInverseImageEtaleIso_unit_app
    (F : ModuleValuedSheaf X Λ) (U : X.Etale) :
    ((moduleValuedInverseImageAdjunction f Λ).unit.app F).hom.app (op U) ≫
      ((moduleValuedInverseImageEtaleIso f Λ).hom.app F).hom.app
        (op ((siteBaseChange f).obj U)) =
    F.obj.map ((siteEtalePostcomposeAdj f).counit.app U).op :=
  congrArg (fun h => h.hom.app (op U)) (moduleValuedInverseImageEtaleIso_unit f Λ F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
