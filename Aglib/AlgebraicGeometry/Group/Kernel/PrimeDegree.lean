/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricDegree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Prime geometric degree gives a cyclic actual kernel

The actual finite-etale group morphism has prime degree on every
algebraically closed geometric fibre. No coefficient marking or cyclicity
conclusion is supplied as an input.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.Kernel.PrimeDegree`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`46287e1784c368df3403d8949bdf4d6c66c251691a48579ec8ab9a9f4481c665`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open AlgebraicGeometry.Scheme.OverField (Base FScheme)
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers

namespace AlgebraicGeometry.Scheme.Group.Kernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {F : Type u} [Field F] {G E : Grp (FScheme F)} (p : G ⟶ E)

/-- Prime geometric degree forces geometric cyclicity of this actual kernel.
No cyclic group or geometric group is an input. -/
theorem cyclicCoefficient_of_prime_degree {n : ℕ} (hn : n.Prime) [IsFinite p.hom.hom.left]
    [Etale p.hom.hom.left] (hd : HasGeometricDegree p.hom.hom n) :
    CyclicCoefficient (group p) n where
  positive := hn.pos
  finite := inferInstance
  etale := inferInstance
  geometric_cyclic K _ _ s := by
    have hc : Nat.card (Over.mk s ⟶ (group p).X) = n :=
      (Nat.card_congr (pointsEquiv p (Over.mk s))).trans (hd K s 1)
    let : Fact n.Prime := ⟨hn⟩
    have hcyc := isCyclic_of_prime_card hc
    have eqv := (zmodCyclicMulEquiv hcyc).symm
    rw [hc] at eqv
    exact ⟨eqv⟩

end AlgebraicGeometry.Scheme.Group.Kernel
