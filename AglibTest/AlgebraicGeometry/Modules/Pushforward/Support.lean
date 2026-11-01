/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.Support

/-! Closed support comparison keeps original schemes and has no coherence hypothesis. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

example {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (M : X.Modules) :
    support ((Scheme.Modules.pushforward i).obj M) = i '' support M :=
  support_pushforward_of_isClosedImmersion i M

example {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] :
    topologicalKrullDim (support ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf))) = topologicalKrullDim X :=
  topologicalKrullDim_support_pushforward_unit i

end
