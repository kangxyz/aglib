/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction


/-!
# Composition of the original relative differential coefficients

The original coefficient arrows compose through the native pushforward
comparison and the original associativity comparison of structure maps.
The equation is checked on the original universal derivation generators.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y Z T : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ X) (c : Z ⟶ Y)

/-- The actual relative coefficient maps compose with their original structure maps. -/
theorem differentialCoefficient_comp :
    differentialCoefficient a (c ≫ b) ≫ (Scheme.Modules.pushforward (c ≫ b)).map
      (relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom =
    differentialCoefficient a b ≫ (Scheme.Modules.pushforward b).map
      (differentialCoefficient (b ≫ a) c) ≫
      (Scheme.Modules.pushforwardComp c b).hom.app
        (relativeDifferentialSheaf (c ≫ (b ≫ a))) := by
  apply relativeDifferentialSheaf_hom_ext a _
  intro V z
  change (relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom.val.app
    (op ((c ≫ b) ⁻¹ᵁ V.unop))
      ((differentialCoefficient a (c ≫ b)).val.app V
        ((relativeDifferentialDerivation a).d z)) =
    (differentialCoefficient (b ≫ a) c).val.app (op (b ⁻¹ᵁ V.unop))
      ((differentialCoefficient a b).val.app V ((relativeDifferentialDerivation a).d z))
  have hleft := congrArg
    ((relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom.val.app
      (op ((c ≫ b) ⁻¹ᵁ V.unop))) (differentialCoefficient_d a (c ≫ b) V.unop z)
  have hright := congrArg
    ((differentialCoefficient (b ≫ a) c).val.app (op (b ⁻¹ᵁ V.unop)))
    (differentialCoefficient_d a b V.unop z)
  exact hleft.trans
    ((relativeDifferentialCongrIso_hom_d ((c ≫ b) ≫ a) (Category.assoc c b a)
      (op ((c ≫ b) ⁻¹ᵁ V.unop)) ((c ≫ b).app V.unop z)).trans
      ((differentialCoefficient_d (b ≫ a) c (b ⁻¹ᵁ V.unop)
        (b.app V.unop z)).symm.trans hright.symm))

end AlgebraicGeometry.Scheme.Modules.Differentials
