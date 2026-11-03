/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficientComposition
public import Aglib.AlgebraicGeometry.Modules.Pullback.CompositeAdjoint


/-!
# Composition of the original raw pullback arrows

The proved original coefficient composition is transposed through the same
native adjunctions and pullback-composition comparison. The resulting
square retains the original raw arrows and structure associativity.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y Z T : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ X) (c : Z ⟶ Y) (n : ℕ)

/-- Original raw pullback composes with its actual structural comparison. -/
theorem rawFormsPullback_comp :
    (Scheme.Modules.pullbackComp c b).inv.app
      (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
      (Scheme.Modules.pullback c).map (rawFormsPullback a b n) ≫
        rawFormsPullback (b ≫ a) c n =
    rawFormsPullback a (c ≫ b) n ≫ (moduleExteriorPowerFunctor Z n).map
      (relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b)
  let e := (moduleExteriorPowerFunctor Z n).map
    (relativeDifferentialCongrIso ((c ≫ b) ≫ a) (Category.assoc c b a)).hom
  apply (adj.homEquiv _ _).injective
  have hleft := Scheme.Modules.pullbackCompositeAdjoint b c
    (moduleExteriorPower X (relativeDifferentialSheaf a) n)
    (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n)
    (moduleExteriorPower Z (relativeDifferentialSheaf (c ≫ (b ≫ a))) n)
    (rawFormsPullback a b n) (rawFormsPullback (b ≫ a) c n)
  simp only [rawFormsPullback_adjoint] at hleft
  have hright := adj.homEquiv_naturality_right (rawFormsPullback a (c ≫ b) n) e
  have hunit := congrArg (fun t => t ≫ (Scheme.Modules.pushforward (c ≫ b)).map e)
    (rawFormsPullback_adjoint a (c ≫ b) n)
  exact hleft.trans ((rawFormsCoefficient_comp a b c n).symm.trans
    (hunit.symm.trans hright.symm))

end AlgebraicGeometry.Scheme.Modules.Differentials
