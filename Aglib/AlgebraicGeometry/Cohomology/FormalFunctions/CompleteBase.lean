/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Thickening
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.RingTheory.AdicCompletion.FiniteModule

/-!
# Formal functions over a complete Noetherian base

Proper coherent cohomology is finite for its original structural action, hence
complete over a complete Noetherian ring. Composing its canonical completion
map with formal functions identifies original cohomology with the compatible
quotient-cohomology families. No module-universe shrinking is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F : X.Modules)
  (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F) (p : ℕ)

local notation "α" => Modules.idealThickeningBaseScalar f

/-- Over a complete Noetherian base, the original cohomology itself is the
inverse-limit module of actual quotient cohomologies. -/
def moduleCohomologyFormalFunctionsCompleteEquiv :
    (moduleCohomologyFunctorOfHom X α p).obj F ≃ₗ[A]
      ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I p) := by
  letI : Module.Finite A ((moduleCohomologyFunctorOfHom X α p).obj F) :=
    moduleCohomology_finite_of_proper A f F hF p
  letI : IsAdicComplete I ((moduleCohomologyFunctorOfHom X α p).obj F) :=
    IsAdicComplete.of_finite A I _
  exact (AdicCompletion.ofLinearEquiv I _).trans
    (moduleCohomologyFormalFunctionsEquiv I f F hF p)

/-- The complete-base equivalence sends a class to its original reductions. -/
theorem moduleCohomologyFormalFunctionsCompleteEquiv_apply
    (x : (moduleCohomologyFunctorOfHom X α p).obj F) (n : ℕ) :
    (moduleCohomologyFormalFunctionsCompleteEquiv I f F hF p x).val (op n) =
      moduleCohomologyMapOfHom X α (Modules.idealQuotientπ X α F (I ^ n)) p x :=
  moduleCohomologyFormalFunctionsEquiv_of I f F hF p x n

/-- Over a complete Noetherian base, original cohomology is the compatible
family module for the actual infinitesimal-thickening cohomologies. -/
def moduleCohomologyFormalFunctionsCompleteThickeningEquiv :
    (moduleCohomologyFunctorOfHom X α p).obj F ≃ₗ[A]
      ModuleCat.sectionsSubmodule (properIdealThickeningCohomologyTower f F hF I p) := by
  letI : Module.Finite A ((moduleCohomologyFunctorOfHom X α p).obj F) :=
    moduleCohomology_finite_of_proper A f F hF p
  letI : IsAdicComplete I ((moduleCohomologyFunctorOfHom X α p).obj F) :=
    IsAdicComplete.of_finite A I _
  exact (AdicCompletion.ofLinearEquiv I _).trans
    (moduleCohomologyFormalFunctionsThickeningEquiv f F hF I p)

/-- The complete-base thickening comparison sends each class to its actual
geometric restrictions, not an abstractly chosen compatible family. -/
theorem moduleCohomologyFormalFunctionsCompleteThickeningEquiv_apply
    (x : (moduleCohomologyFunctorOfHom X α p).obj F) (n : ℕ) :
    (moduleCohomologyFormalFunctionsCompleteThickeningEquiv I f F hF p x).val (op n) =
      moduleCohomologyPullback (Modules.idealThickeningι f (I ^ n)) F p x :=
  moduleCohomologyFormalFunctionsThickeningEquiv_of f F hF I p x n

end AlgebraicGeometry.Scheme.Cohomology
