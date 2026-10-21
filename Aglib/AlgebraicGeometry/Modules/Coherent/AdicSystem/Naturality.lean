/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Transitions

/-! # Naturality of the original all-order formal reductions -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} {K : X.IdealSheafData} [IsLocallyNoetherian X]
variable {F G : AdicSystem X K}

/-- Every actual natural transformation intertwines the canonical reductions. -/
@[reassoc]
theorem reductionIsoOfLE_naturality (f : F ⟶ G) {n m : ℕ} (h : n ≤ m) :
    (idealSheafQuotientFunctor X (K ^ n)).map (f.hom.app (op m)) ≫
        (G.reductionIsoOfLE h).hom =
      (F.reductionIsoOfLE h).hom ≫ f.hom.app (op n) := by
  apply (cancel_epi ((idealSheafQuotientUnit X (K ^ n)).app (F.obj.obj (op m)))).mp
  rw [← Category.assoc,
    ← (idealSheafQuotientUnit X (K ^ n)).naturality (f.hom.app (op m))]
  simp only [Functor.id_map]
  rw [Category.assoc, G.unit_reductionIsoOfLE_hom h,
    ← Category.assoc, F.unit_reductionIsoOfLE_hom h]
  exact (f.hom.naturality (homOfLE h).op).symm

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
