/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.RootsH2
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.RootsPullback
public import Aglib.FieldTheory.PurelyInseparable.RationalFunction

/-! # Original root H2 over separably closed, possibly imperfect constants

The actual perfect-closure field is algebraic over a rational function field
with algebraically closed constants. Original root pullback along its purely
inseparable extension is injective. Multiplicative cohomology invariance is
neither assumed nor asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

variable (k E : Type u) [Field k] [IsSepClosed k] [Field E]
  [Algebra (RatFunc k) E] [Algebra.IsAlgebraic (RatFunc k) E]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

include k

attribute [local instance] hasSheafifyLarge

/-- Original degree-two root cohomology vanishes over every algebraic function
field with separably closed constants, without a perfectness assumption. -/
theorem rootsH2_subsingleton_of_separablyClosed_ratFunc
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of E), ⊤))) :
    Subsingleton (Sheaf.H.{w} (mu (Spec (.of E)) n) 2) := by
  let L := Field.perfectFunctionField E
  obtain ⟨a, ha, _⟩ := Field.exists_ratFuncAlgebra_perfectFunctionField k E
  let : Algebra (RatFunc (AlgebraicClosure k)) L := a
  let : Algebra.IsAlgebraic (RatFunc (AlgebraicClosure k)) L := ha
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Spec (.of L))) :=
    hasExtStandard.{u, u + 1} (Spec (.of L))
  let : Subsingleton (Sheaf.H.{u + 2} (mu (Spec (.of L)) n) 2) :=
    rootsH2_subsingleton_of_algebraic_ratFunc (AlgebraicClosure k) L n hn
      (levelInvertible (Spec.algebraMap E L) n hinv)
  exact (Kummer.rootsCohomologyPullback_bijective_of_isPurelyInseparable
    E L n hn hinv 2).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
