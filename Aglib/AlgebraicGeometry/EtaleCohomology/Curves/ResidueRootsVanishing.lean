/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ResidueField.CurveAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.RootsVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Standard

/-! # Original root cohomology of actual curve residue fields

The original structural constant action is used in both branches of the actual
residue-field dichotomy. Algebraic residue fields remain separably closed;
one-variable algebraic function fields use the proved field endpoint.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

/-- All actual residue fields of a finite-type dimension-at-most-one scheme
have zero original positive-invertible root cohomology in degrees at least two. -/
theorem residueRoots_subsingleton
    {k : Type u} [Field k] [IsSepClosed k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1) (x : X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (X.residueField x)))]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (mu (Spec (X.residueField x)) n) q) := by
  let := residueAlgebra X p x
  rcases residueField_algebraic_or_ratFunc X p hdim x with h | ⟨a, ha, ht⟩
  · let := h
    let : HenselianLocalRing (X.residueField x) := Field.henselian _
    let : IsSepClosed (X.residueField x) :=
      Algebra.IsAlgebraic.isSepClosed (F := k) (E := X.residueField x)
    let : IsSepClosed (IsLocalRing.ResidueField (X.residueField x)) :=
      Algebra.IsAlgebraic.isSepClosed
        (F := X.residueField x) (E := IsLocalRing.ResidueField (X.residueField x))
    exact @StrictlyLocal.subsingleton_H_standard.{u, w}
      (X.residueField x) _ (Field.henselian _) _ _ _
      (mu (Spec (X.residueField x)) n) q (by omega)
  · let := a
    let := ha
    let := ht
    exact Fields.roots_cohomology_subsingleton_of_separablyClosed_ratFunc
      k (X.residueField x) n hn hunit q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
