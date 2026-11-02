/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Polarization

/-! The symmetric projective embedding keeps the original field group and inversion. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [IsHProjective G.hom] :
    ∃ (I : Type u) (_ : Finite I) (j : G.left ⟶ ProjectiveSpace k I),
      IsClosedImmersion j ∧ j ≫ ProjectiveSpace.toSpec k I = G.hom ∧
        pullbackClass ((𝟙 G)⁻¹).left
          (pullbackClass j (classOf _ (ProjectiveSpace.twistingLineBundle k I 1))) =
        pullbackClass j (classOf _ (ProjectiveSpace.twistingLineBundle k I 1)) :=
  Scheme.Group.Multiplication.exists_symmetric_projective_embedding G

end
