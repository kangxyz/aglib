/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.FiniteEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ArtinPullback

/-! # Original root-cohomology pullback across purely inseparable field extensions -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'

/-- Prime-to-characteristic root cohomology is unchanged by an arbitrary purely
inseparable field extension. The map is the original cohomology pullback with
its canonical root-coefficient comparison, not a replacement cohomology model. -/
theorem rootsCohomologyPullback_bijective_of_isPurelyInseparable
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of L)))]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of K), ⊤))) (q : ℕ) :
    Function.Bijective
      (rootsCohomologyPullback (Spec.algebraMap K L) n hn hinv q) := by
  let := FiniteEtale.PurelyInseparable.specBaseChange_isEquivalence K L
  exact rootsCohomologyPullback_bijective_of_artin_finiteEtale_equivalence
    (Spec.algebraMap K L) n hn hinv q

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
