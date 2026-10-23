/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Approximation.ClosedFiber
public import Mathlib.RingTheory.FinitePresentation

/-!
# From algebra-map approximation to actual closed-fibre line bundles

An actual completed line bundle supplies its own finite coefficient data by
native module descent. Precision one of the original algebra maps then
specializes that data back to the original base, retaining an actual
isomorphism on the original ideal closed fibre.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual coefficient-completion base change, in the order of the native
finite-subalgebra limiting cone. -/
abbrev completionBaseChange (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Scheme.{u} :=
  Limits.pullback (Spec.algebraMap R (AdicCompletion I R)) f

/-- The original completion evaluation gives the original closed-fibre map
to the actual completion base change. -/
abbrev completionClosedFiberMap (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) :
    idealThickeningSpace f I ⟶ completionBaseChange f I :=
  closedFiberCoefficientMap f I (AdicCompletion.evalOneₐ I)

/-- Actual precision-one algebra-map approximation specializes every given
completed line bundle to an actual bundle over the original Noetherian base,
with an actual isomorphism on the original closed fibre. -/
theorem exists_lineBundle_of_completion_of_algHom_approximation
    [IsNoetherianRing R] (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] (I : Ideal R)
    (happrox : ∀ (C : Type u) [CommRing C] [Algebra R C]
      [Algebra.FinitePresentation R C] (b : C →ₐ[R] AdicCompletion I R),
      ∃ a : C →ₐ[R] R,
        (Ideal.Quotient.mkₐ R I).comp a = (AdicCompletion.evalOneₐ I).comp b)
    (L : LineBundle (completionBaseChange f I)) :
    ∃ M : LineBundle X,
      Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅
        (pullback (completionClosedFiberMap f I)).obj L.val) := by
  obtain ⟨s, N, ⟨e⟩⟩ := exists_lineBundle_finiteType_model R (AdicCompletion I R) f L
  let C := Algebra.FiniteTypeSubalgebraLimit.stage R (AdicCompletion I R) s
  have : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let b : C →ₐ[R] AdicCompletion I R := C.val
  obtain ⟨a, ha⟩ := happrox C b
  let M := pullbackLineBundle (coefficientSpecialization f a) N
  refine ⟨M, ⟨?_⟩⟩
  apply coefficientSpecializationClosedFiberIso f I a b (AdicCompletion.evalOneₐ I) ha
    N.val L.val
  exact ((pullbackCongr (finiteType_coneProjection_eq f s)).app N.val).symm ≪≫ e

/-- The same application retains a specified original closed-fibre comparison
of the completed line bundle with a supplied closed-fibre bundle. -/
theorem exists_lineBundle_lift_of_completion_of_algHom_approximation
    [IsNoetherianRing R] (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] (I : Ideal R)
    (happrox : ∀ (C : Type u) [CommRing C] [Algebra R C]
      [Algebra.FinitePresentation R C] (b : C →ₐ[R] AdicCompletion I R),
      ∃ a : C →ₐ[R] R,
        (Ideal.Quotient.mkₐ R I).comp a = (AdicCompletion.evalOneₐ I).comp b)
    (L : LineBundle (completionBaseChange f I))
    (L₀ : LineBundle (idealThickeningSpace f I))
    (e₀ : (pullback (completionClosedFiberMap f I)).obj L.val ≅ L₀.val) :
    ∃ M : LineBundle X, Nonempty ((pullback (idealThickeningι f I)).obj M.val ≅ L₀.val) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_of_completion_of_algHom_approximation f I happrox L
  exact ⟨M, ⟨e ≪≫ e₀⟩⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
