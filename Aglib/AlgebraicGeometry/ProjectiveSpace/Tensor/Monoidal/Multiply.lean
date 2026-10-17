/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Multiplication
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Multiplication by a global twist section on tensor twists

A global section `s` of `O(a)` multiplies the twist factor of `O(d) ⊗ F`, giving the natural
transformation `twistingTensorMultiply a d s` from tensoring by `O(d)` to tensoring by
`O(a + d)`; it is the coefficient map of the multiplication morphism `twistingMultiplyGlobal`.
On an original pure tensor it multiplies the twist factor (`twistingTensorMultiply_section`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Multiplication by a global section `s` of `O(a)` on the twist factor: the natural
transformation from tensoring by `O(d)` to tensoring by `O(a + d)`. -/
def twistingTensorMultiply (a d : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤)) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d) ⟶
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (a + d)) :=
  moduleTensorCoefficientMap (ProjectiveSpace R ι) (twistingMultiplyGlobal R ι a d s)

/-- On an original pure tensor, twist multiplication multiplies the twist factor. -/
theorem twistingTensorMultiply_section (a d : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules) (U : (ProjectiveSpace R ι).Opens)
    (t : Γ(twistingSheaf R ι d, U)) (n : Γ(F, U)) :
    ((twistingTensorMultiply R ι a d s).app F).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F U t n) =
      moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (a + d)) F U
        (twistingSectionMul R ι a d U
          ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) t) n :=
  moduleTensorCoefficientMap_section (twistingMultiplyGlobal R ι a d s) F U t n

end AlgebraicGeometry.ProjectiveSpace
