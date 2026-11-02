/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BaseForms
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BidualLine.Model
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.LinearAlgebra.ExteriorPower.TopDegree


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / BidualLine / ModelCoefficient

Source: `IntegralTrace/ModelCoefficient.lean`.
Incoming SHA256: `c4cd5f6ebd4abe49f67b518559d5fc18671a7aabbc53c77e0c1fdf604a8ca2db`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
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

/-- The actual pulled-back raw base module maps into the same proved model line. -/
def modelDifferentialCoefficient :
    (pullback β).obj (tilde (ModuleCat.of A
      (⋀[A]^n (CommRingCat.KaehlerDifferential ρ)))) ⟶
        (modelDifferentialLine ρ β hβ hX hdX n b).val :=
  (pullback β).map (baseRawFormsIso ρ n).inv ≫
    ((pullbackPushforwardAdjunction β).homEquiv _ _).symm
      (bidualFormsCoefficient (Spec.map ρ) β n)

end AlgebraicGeometry.Scheme.Modules.Differentials
