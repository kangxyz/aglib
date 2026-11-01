/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.GenericPoint
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange

/-! # Original Kummer H1 detection at the generic point

The actual finite-etale roots group represents a finite locally constant
coefficient on an integral scheme. Its splitting cover uses the existing
Galois dictionaries and the algebraic-closure residue point. Under explicit
normality of every stalk, original generic pullback is injective; the actual
roots coefficient isomorphism then gives injectivity of the original h1Map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Group
open GroupCohomology.Kummer.Coefficients

universe u w w'

namespace GroupCohomology.Kummer

variable (X : Scheme.{u}) [IsIntegral X]

/-- Positive invertible roots are finite locally constant, using the actual
finite-etale group scheme and an actual geometric point of the integral base. -/
theorem mu_isFiniteLocallyConstant (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) : IsFiniteLocallyConstant (mu X n) := by
  let : IsFinite (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_finite X n hn
  let : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_etale X n hn hinv
  exact representedSheaf_isFiniteLocallyConstant
    (s := Scheme.FiniteEtale.algebraicClosureResiduePoint X (genericPoint X))
    (MultiplicativeGroup.rootsGroupScheme X n)

namespace CoefficientBaseChange

variable [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec X.functionField))]

/-- The original Kummer coefficient-normalized generic pullback is injective. -/
theorem h1Map_injective_genericPoint (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Injective (h1Map (X.fromSpecStalk (genericPoint X)) n hn hinv) := by
  exact (coefficientIso
    (rootsPullbackIso (X.fromSpecStalk (genericPoint X)) n hn hinv)).injective.comp
      (h1Pullback_injective_genericPoint X (mu X n)
        (mu_isFiniteLocallyConstant X n hn hinv))

end CoefficientBaseChange

end GroupCohomology.Kummer
