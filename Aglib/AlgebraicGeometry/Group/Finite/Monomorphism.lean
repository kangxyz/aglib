/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.Monomorphism
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Grp

/-! The original finite group map is an isomorphism when it is monic of equal degree. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {G H : Grp (FScheme k)}
  [IsFinite G.X.hom] [IsFinite H.X.hom]
  (f : G ⟶ H) [Mono f.hom.hom]
  (h : Hom.finiteSchemeDegree k G.X.hom = Hom.finiteSchemeDegree k H.X.hom)

/-- The same group map is invertible, by its original scheme map. -/
def isoOfMonoOfFiniteSchemeDegreeEq : G ≅ H := by
  have he := Hom.isIso_of_mono_of_finiteSchemeDegree_eq f.hom.hom h
  let e := @asIso _ _ _ _ f.hom.hom he
  let : IsMonHom e.hom := f.hom.isMonHom_hom
  exact Grp.mkIso' e

/-- The forward map of this isomorphism is exactly the original group map. -/
theorem isoOfMonoOfFiniteSchemeDegreeEq_hom : (isoOfMonoOfFiniteSchemeDegreeEq f h).hom = f := by
  apply Grp.hom_ext
  rfl

end AlgebraicGeometry.Scheme.Group
