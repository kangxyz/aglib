/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleLocalIsomorphism

/-! # Original abelian etale sheaves on the empty scheme

The zero endomorphism is an isomorphism by original pointed local detection:
every test object's point would map to a point of the empty base. No alternate
sheaf category or model of cohomology is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Etale

universe u v

/-- Every original abelian sheaf on an empty scheme is zero. -/
theorem isZero_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}) : IsZero F := by
  let : IsIso (0 : F ⟶ F) :=
    isIso_of_pointed_refinement_bijective (0 : F ⟶ F)
      (fun T t => isEmptyElim (show X from T.hom t))
  exact IsZero.of_epi_eq_zero (0 : F ⟶ F) rfl

end AlgebraicGeometry.Scheme.Etale
