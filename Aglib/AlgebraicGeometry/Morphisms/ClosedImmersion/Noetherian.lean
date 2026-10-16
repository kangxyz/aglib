/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-! # Noetherianity of the source of an actual closed immersion -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The source hypothesis needed to form coherent G-theory is derived from
the closed immersion and local noetherianity of its ambient scheme. -/
theorem closedSource_isLocallyNoetherian {Z X : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] : IsLocallyNoetherian Z :=
  LocallyOfFiniteType.isLocallyNoetherian i

/-- A closed subscheme of a noetherian scheme is itself noetherian. -/
theorem closedSource_isNoetherian {Z X : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] : IsNoetherian Z := by
  let : IsLocallyNoetherian Z := closedSource_isLocallyNoetherian i
  let : CompactSpace Z := i.isClosedEmbedding.compactSpace
  exact ⟨⟩

end AlgebraicGeometry.Scheme
