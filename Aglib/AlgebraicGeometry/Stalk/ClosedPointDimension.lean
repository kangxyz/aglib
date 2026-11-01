/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.KrullDimension
public import Mathlib.Tactic.NormNum

/-! # Closed points of an integral one-dimensional scheme

The original coheight argument is moved unchanged from the product-formula
owner. Its public name and complete hypotheses are retained; neither
Noetherianity, properness nor smoothness occurs in this theorem.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.ProductFormula

universe u
variable (X : Scheme.{u}) [IsIntegral X]

attribute [local instance] specializationOrder in
/-- On an integral dimension-one scheme, every closed point is codimension one.
No smoothness or regularity theorem is used. -/
theorem closedPoint_coheight_one (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : IsClosed ({x} : Set X)) : Order.coheight x = 1 := by
  have hd : Order.krullDim X = 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hu : Order.coheight x ≤ 1 := by
    exact_mod_cast (Order.coheight_le_krullDim x).trans_eq hd
  have hn : Order.coheight x ≠ 0 := by
    rw [Order.coheight_ne_zero]
    intro hmax
    have he : x = genericPoint X :=
      le_antisymm (genericPoint_specializes x) (hmax (genericPoint_specializes x))
    have hg : IsClosed ({genericPoint X} : Set X) := he ▸ hx
    have hs : ({genericPoint X} : Set X) = Set.univ :=
      hg.closure_eq.symm.trans (genericPoint_spec X).def
    let : Subsingleton X := ⟨fun y z => by
      have hy : y = genericPoint X := Set.mem_singleton_iff.mp (hs.symm ▸ Set.mem_univ y)
      have hz : z = genericPoint X := Set.mem_singleton_iff.mp (hs.symm ▸ Set.mem_univ z)
      exact hy.trans hz.symm⟩
    have hf := Order.krullDim_nonpos_of_subsingleton (α := X)
    rw [hd] at hf
    norm_num at hf
  exact le_antisymm hu (Order.one_le_iff_ne_zero.mpr hn)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree.ProductFormula
