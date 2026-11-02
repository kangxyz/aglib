/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.GenericStalk

/-! Generic-support finite length is stated on the original module stalk. -/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

example {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (x : support M)
    (hx : x ∈ genericPoints (support M)) :
    IsFiniteLength (X.presheaf.stalk x.1) ((moduleStalk X x.1).obj M) :=
  Stalk.finiteLength_stalk_of_genericPoint_support M hM x hx

end
