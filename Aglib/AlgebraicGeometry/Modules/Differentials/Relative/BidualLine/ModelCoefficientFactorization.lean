/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BaseForms
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BidualLine.ModelCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# Factorization of the original model differential coefficient

The same native adjunction identifies the original coefficient with raw pullback
followed by canonical bidual evaluation. The stable constructor owner is unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {Λ A : CommRingCat.{u}} [IsDomain A]
  (ρ : Λ ⟶ A) (β : X ⟶ Spec A) [IsDominant β]
  [LocallyOfFiniteType (β ≫ Spec.map ρ)]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (hX : RegularStalks X) (hdX : topologicalKrullDim X ≤ 2)
  (n : ℕ) (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential ρ))

/-- The original adjoint coefficient factors through the same raw pullback and
canonical bidual evaluation. No new differential or exterior map is introduced. -/
theorem modelDifferentialCoefficient_eq_rawFormsPullback_bidualMap :
    modelDifferentialCoefficient ρ β hβ hX hdX n b =
      (pullback β).map (baseRawFormsIso ρ n).inv ≫
        rawFormsPullback (Spec.map ρ) β n ≫
          Invertible.bidualMap X
            (moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n) := by
  exact congrArg (fun f => (pullback β).map (baseRawFormsIso ρ n).inv ≫ f)
    ((pullbackPushforwardAdjunction β).homEquiv_naturality_right_symm
      (rawFormsCoefficient (Spec.map ρ) β n)
      (Invertible.bidualMap X
        (moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n)))

end AlgebraicGeometry.Scheme.Modules.Differentials
