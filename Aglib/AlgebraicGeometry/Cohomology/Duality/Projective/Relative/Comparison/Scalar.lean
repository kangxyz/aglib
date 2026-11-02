/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear
public import Aglib.AlgebraicGeometry.Modules.Pullback.Linear

/-!
# Structural scalars on actual differential coefficients

The ordinary pushforward and its native pullback adjunction preserve the
specified structural scalar action. Tensoring with the actual top differential
sheaf then gives structural linearity of the original coefficient functor.
No geometric finiteness or flatness condition is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Cohomology

/-- The actual differential-coefficient functor preserves every specified structural
scalar, through the native pullback adjunction and original tensor functor. -/
theorem relativeTopDifferentialCoefficientsFunctor_linearOfHom {S : Type u} [CommRing S]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (α : S →+* Γ(Y, ⊤)) (n : ℕ) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    (relativeTopDifferentialCoefficientsFunctor p n).Linear S := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  let : (Scheme.Modules.pullback p).Linear S := pullback_linearOfHom p α
  change (Scheme.Modules.pullback p ⋙ moduleTensorLeftFunctor X _).Linear S
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
