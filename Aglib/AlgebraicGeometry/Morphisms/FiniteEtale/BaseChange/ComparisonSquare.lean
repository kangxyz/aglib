/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism

/-!
# Actual finite-etale cover comparisons through a commutative square

An equality of original composite arrows gives the corresponding comparison
of iterated native pullbacks. If the comparison on the fibre bases is an
isomorphism, the prescribed fibre cover is recovered over the original base.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {Z X T K L : Scheme.{u}}
  (a : X ⟶ Z) (b : T ⟶ Z) (i : K ⟶ X) (j : L ⟶ T)
  (e : L ≅ K) (h : j ≫ b = e.hom ≫ i ≫ a)

/-- Compare the two actual iterated pullbacks using the stated original
commutative square. -/
def baseChangeComparisonSquareIso (Y : FiniteEtale Z) :
    (baseChange j).obj ((baseChange b).obj Y) ≅
      (baseChange e.hom).obj ((baseChange i).obj ((baseChange a).obj Y)) :=
  (baseChangeComp b j).symm.app Y ≪≫
    (eqToIso (congrArg baseChange (h.trans (Category.assoc _ _ _).symm))).app Y ≪≫
      (baseChangeComp a (e.hom ≫ i)).app Y ≪≫
        (baseChangeComp i e.hom).app ((baseChange a).obj Y)

/-- Recover an isomorphism with the specified original fibre cover from a
comparison after a canonical isomorphism of fibre bases. -/
def originalCoverIsoOfComparisonSquare (Y : FiniteEtale Z) (C : FiniteEtale K)
    (d : (baseChange j).obj ((baseChange b).obj Y) ≅ (baseChange e.hom).obj C) :
    (baseChange i).obj ((baseChange a).obj Y) ≅ C := by
  let F := baseChange e.hom
  letI : F.Full := baseChange_full_of_isIso _
  letI : F.Faithful := baseChange_faithful_of_isIso _
  exact F.preimageIso ((baseChangeComparisonSquareIso a b i j e h Y).symm ≪≫ d)

end AlgebraicGeometry.Scheme.FiniteEtale
