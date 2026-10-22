/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.LiftAlongSquare

/-!
# Transporting fibre-cover lifting along an original over-isomorphism

An actual isomorphism over the base transports essential surjectivity of
finite-etale restriction to the original scheme and its original fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- A specified native over-isomorphism transports fibre-cover lifting without
replacing the original pullback functor by an abstract equivalent model. -/
theorem baseChange_essSurj_of_overIso {S T X Y : Scheme.{u}}
    (r : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ S) (e : Over.mk g ≅ Over.mk f)
    [(baseChange (pullback.fst g r)).EssSurj] :
    (baseChange (pullback.fst f r)).EssSurj where
  mem_essImage C := by
    let k : pullback g r ≅ pullback f r :=
      (Over.forget T).mapIso ((Over.pullback r).mapIso e)
    have h : pullback.fst f r ≫ e.inv.left = k.inv ≫ pullback.fst g r := by
      change pullback.fst f r ≫ e.inv.left =
        ((Over.pullback r).map e.inv).left ≫ pullback.fst g r
      exact (pullback.lift_fst _ _ _).symm
    obtain ⟨W, ⟨hW⟩⟩ := exists_cover_pullback_of_square e.inv.left
      (pullback.fst f r) (pullback.fst g r) k.inv h ((baseChange k.hom).obj C)
    refine ⟨W, ⟨?_⟩⟩
    exact hW ≪≫ (baseChangeComp k.hom k.inv).symm.app C ≪≫
      (eqToIso (congrArg baseChange k.inv_hom_id)).app C ≪≫
        (baseChangeId (pullback f r)).app C

end AlgebraicGeometry.Scheme.FiniteEtale
