/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.GradedCohomologyCompletion
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyHomogeneous

/-!
# Formal functions over an affine Noetherian base

The forward map is the canonical map induced by the original coefficient
reductions. Finite generation of the actual geometric Rees cohomology supplies
the two independent uniform bounds internally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
variable (F : X.Modules)
variable (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F) (p : ℕ)

/-- The original structural base-ring map used in affine formal functions. -/
abbrev affineFormalFunctionsScalar {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

local notation "α" => affineFormalFunctionsScalar f

include hF in
/-- The original completion comparison is bijective for a coherent coefficient proper
 over an affine Noetherian base. No Rees finiteness or stabilization is assumed. -/
theorem moduleCohomologyFormalFunctions_bijective :
    Function.Bijective (idealPowerCohomologyCompletionMap X α F I p) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : F.IsQuasicoherent := Modules.QuasiCoherent.quasicoherent_of_affineCharts F
    (fun R j _ => (hF R j).1)
  let := reesCohomologyModule I f F p
  let := reesCohomologyModule I f F (p + 1)
  let := reesCohomology_finite I f F hF p
  let := reesCohomology_finite I f F hF (p + 1)
  exact idealPowerCohomologyCompletionMap_bijective_of_finite_reesCohomology
    X α F I p (reesCohomology_monomial_lof I f F p)
      (reesCohomology_monomial_lof I f F (p + 1))

/-- Formal functions for the original coefficient and the original ideal-power quotient tower. -/
def moduleCohomologyFormalFunctionsEquiv :
    AdicCompletion I ((moduleCohomologyFunctorOfHom X α p).obj F) ≃ₗ[A]
      ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I p) :=
  LinearEquiv.ofBijective (idealPowerCohomologyCompletionMap X α F I p)
    (moduleCohomologyFormalFunctions_bijective I f F hF p)

/-- The forward equivalence is the canonical original reduction map, literally. -/
theorem moduleCohomologyFormalFunctionsEquiv_toLinearMap :
    (moduleCohomologyFormalFunctionsEquiv I f F hF p).toLinearMap =
      idealPowerCohomologyCompletionMap X α F I p := rfl

/-- On original classes every coordinate is the original cohomology reduction. -/
theorem moduleCohomologyFormalFunctionsEquiv_of
    (x : (moduleCohomologyFunctorOfHom X α p).obj F) (n : ℕ) :
    (moduleCohomologyFormalFunctionsEquiv I f F hF p (AdicCompletion.of I _ x)).val
        (op n) =
      moduleCohomologyMapOfHom X α (Modules.idealQuotientπ X α F (I ^ n)) p x := rfl

end AlgebraicGeometry.Scheme.Cohomology
