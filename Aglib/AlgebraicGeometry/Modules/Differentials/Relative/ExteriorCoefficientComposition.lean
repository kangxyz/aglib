/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.CoefficientComposition
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward.Composition


/-!
# Composition of the original raw differential coefficients

The actual differential and exterior coefficient composition equations
retain the original structure associativity, raw exterior map and native
pushforward comparison. This is the raw arrow used in chart transport.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y Z T : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ X) (c : Z ⟶ Y) (n : ℕ)

/-- Actual raw coefficients compose with the original exterior structure comparison. -/
theorem rawFormsCoefficient_comp :
    rawFormsCoefficient a (c ≫ b) n ≫ (Scheme.Modules.pushforward (c ≫ b)).map
      ((moduleExteriorPowerFunctor Z n).map
        (relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom) =
    rawFormsCoefficient a b n ≫ (Scheme.Modules.pushforward b).map
      (rawFormsCoefficient (b ≫ a) c n) ≫
      (Scheme.Modules.pushforwardComp c b).hom.app
        (moduleExteriorPower Z (relativeDifferentialSheaf (c ≫ (b ≫ a))) n) := by
  have hpost := exteriorCoefficientMap_postcomp (c ≫ b)
    (relativeDifferentialSheaf a) (relativeDifferentialSheaf ((c ≫ b) ≫ a))
    (differentialCoefficient a (c ≫ b)) n
    (relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom
  have hdiff := congrArg (fun t => exteriorCoefficientMap (c ≫ b) t n)
    (differentialCoefficient_comp a b c)
  exact hpost.trans (hdiff.trans
    (exteriorCoefficientMap_comp b c (relativeDifferentialSheaf a)
      (relativeDifferentialSheaf (b ≫ a)) (relativeDifferentialSheaf (c ≫ (b ≫ a)))
      (differentialCoefficient a b) (differentialCoefficient (b ≫ a) c) n))

end AlgebraicGeometry.Scheme.Modules.Differentials
