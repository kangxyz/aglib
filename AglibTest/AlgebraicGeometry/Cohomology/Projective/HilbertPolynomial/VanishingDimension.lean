/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.VanishingDimension

/-! Closed zeros use actual ample sections and properness, without integrality or regularity. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    {L : LineBundle X} (hL : L.IsAmple) (s : Γ(L.val, ⊤))
    (hd : 0 < topologicalKrullDim X) :
    ∃ x : X, x ∉ nonvanishingOpen L s ∧ IsClosed ({x} : Set X) :=
  hL.exists_closed_zero_of_pos_dimension p s hd

example (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (L : LineBundle X) (s : Γ(L.val, ⊤)) (x : X)
    (hx : IsClosed ({x} : Set X)) (hs : x ∉ nonvanishingOpen L s) :
    topologicalKrullDim X ≤
      topologicalKrullDim (((nonvanishingOpen L s : Set X)ᶜ) : Set X) + 1 :=
  topologicalKrullDim_le_vanishingDimension_add_one_of_closed_zero k p L s x hx hs

end
