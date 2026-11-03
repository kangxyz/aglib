/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.CoefficientOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward.OpenAdjoint


/-!
# The original raw-form arrow on an open chart

Combine the actual derivation-generator comparison and actual wedge
comparison. The original raw pullback arrow is exactly the original raw
open-restriction isomorphism through the native pullback comparison.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X U : Scheme.{u}} {Λ : CommRingCat.{u}}
  (a : X ⟶ Spec Λ) (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

/-- The actual raw coefficient is the original raw restriction adjoint. -/
theorem rawFormsCoefficient_restrictAdjoint :
    rawFormsCoefficient a j n =
      (Scheme.Modules.restrictAdjunction j).homEquiv _ _ (rawFormsOpenIso a j n).hom := by
  exact (congrArg (fun t => exteriorCoefficientMap j t n)
    (differentialCoefficient_restrictAdjoint a j)).trans
      (exteriorCoefficientMap_restrictAdjoint j (relativeDifferentialSheaf a)
        (relativeDifferentialSheaf (j ≫ a)) (relativeDifferentialRestrictIso a j).hom n)

/-- The original raw pullback agrees with original restriction, including its arrow. -/
theorem rawFormsPullback_restrict :
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.app
      (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
        rawFormsPullback a j n = (rawFormsOpenIso a j n).hom := by
  let adj := Scheme.Modules.restrictAdjunction j
  let padj := Scheme.Modules.pullbackPushforwardAdjunction j
  let m := moduleExteriorPower X (relativeDifferentialSheaf a) n
  let e := (Scheme.Modules.restrictFunctorIsoPullback j).hom.app m
  apply (adj.homEquiv _ _).injective
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app adj padj m
  have hn := adj.homEquiv_naturality_right e (rawFormsPullback a j n)
  exact hn.trans
    ((congrArg (fun t => t ≫ (Scheme.Modules.pushforward j).map
      (rawFormsPullback a j n)) hu).trans
      ((Adjunction.homEquiv_unit padj _ _ (rawFormsPullback a j n)).symm.trans
        ((rawFormsPullback_adjoint a j n).trans (rawFormsCoefficient_restrictAdjoint a j n))))

end AlgebraicGeometry.Scheme.Modules.Differentials
