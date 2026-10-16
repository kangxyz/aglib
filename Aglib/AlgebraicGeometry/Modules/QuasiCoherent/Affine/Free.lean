/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Free sheaves from affine module bases

The actual tilde functor sends the given module-basis representation to the
free sheaf on the same index type. This is the canonical tilde/Finsupp
comparison, with no alternate module or free-sheaf object.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean` at frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`.
The source cut is the basis comparison alone, independent of module base change.
-/

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}}

/-- The tilde sheaf of a module with the given basis is the free sheaf on that basis index. -/
def tildeBasisIso {I : Type u} (M : ModuleCat.{u} R) (b : Basis I R M) :
    tilde M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) I :=
  (tilde.functor R).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp I

end AlgebraicGeometry.Scheme.Modules
