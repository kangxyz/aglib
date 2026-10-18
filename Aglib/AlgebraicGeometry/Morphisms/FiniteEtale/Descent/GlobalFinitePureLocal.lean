/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalAffineFieldCharts
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalPullbackReflection

/-!
# GlobalFinitePureLocal

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]

/-- The local equivalence on a chart of an arbitrary base uses exactly the
projection obtained by restricting the original field-base-change map. -/
theorem affineFieldRestriction_isEquivalence {X U : Scheme.{u}} [IsAffine U]
    (p : X ⟶ Spec (CommRingCat.of K)) (i : U ⟶ X) :
    (baseChange (pullback.fst i (pullback.fst p (Spec.algebraMap K L)))).IsEquivalence := by
  let e := pullbackRightPullbackFstIso p (Spec.algebraMap K L) i
  let g := pullback.fst (i ≫ p) (Spec.algebraMap K L)
  let : (baseChange g).IsEquivalence := affineFieldProjection_isEquivalence K L (i ≫ p)
  apply baseChange_isEquivalence_of_isoSquare e.symm (Iso.refl U) _ g
  simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
    pullbackRightPullbackFstIso_inv_fst p (Spec.algebraMap K L) i

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 981cebc410a705a00c6e910a67e44961ddf349fe1455d03ccb89136e8a13d095.
Definitions, hypotheses and universes are retained modulo native names. -/
