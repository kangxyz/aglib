/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Congruence


/-!
# Identity normalization of the original differential coefficient

After its original structural-map congruence, the identity coefficient is the
native inverse pushforward identity. This is proved on universal differentials.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- The original identity coefficient, including the actual structural congruence. -/
theorem differentialCoefficient_id {X T : Scheme.{u}} (a : X ⟶ T) :
    differentialCoefficient a (𝟙 X) ≫ (pushforward (𝟙 X)).map
      (relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom =
      (pushforwardId X).inv.app (relativeDifferentialSheaf a) := by
  apply relativeDifferentialSheaf_hom_ext a _
  intro U r
  change (relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom.val.app U
    ((differentialCoefficient a (𝟙 X)).val.app U
      ((relativeDifferentialDerivation a).d r)) =
        (relativeDifferentialDerivation a).d r
  have hd := differentialCoefficient_d a (𝟙 X) U.unop r
  have hc := relativeDifferentialCongrIso_hom_d ((𝟙 X) ≫ a)
    (Category.id_comp a) U r
  exact (congrArg
    ((relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom.val.app U) hd).trans hc

end AlgebraicGeometry.Scheme.Modules.Differentials
