/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.AffinePushforward

/-! Affine comparison keeps the same original source coefficient and structural scalars. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] (ι : Type u) {X : Scheme.{u}}
    (a b : X ⟶ ProjectiveSpace k ι) [IsAffineHom a] [IsAffineHom b]
    (hab : a ≫ toSpec k ι = b ≫ toSpec k ι) (M : X.Modules) [M.IsQuasicoherent] :
    projectiveEulerChar k ι ((Scheme.Modules.pushforward a).obj M) =
      projectiveEulerChar k ι ((Scheme.Modules.pushforward b).obj M) :=
  projectiveEulerChar_pushforward_eq_of_toSpec_eq k ι a b hab M

end
