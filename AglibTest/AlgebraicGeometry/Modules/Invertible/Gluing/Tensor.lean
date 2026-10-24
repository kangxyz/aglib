/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Tensor

/-! Focused consumer of the tensor product of glued line bundles: the sheafified tensor product
of two glued sheaves is the glued sheaf of the product cocycle, its forward map is the section
product, and classes add. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : iSup U = ⊤)
  (c c' : UnitCocycle U)

example : (moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf ≅ (c * c').sheaf :=
  c.tensorIso c' hU

example : (c.tensorIso c' hU).hom = c.tensorMap c' := rfl

example (V : X.Opens) (s : Γ(c.sheaf, V)) (t : Γ(c'.sheaf, V)) :
    (c.tensorMap c').val.app (op V) (moduleTensorSection X c.sheaf c'.sheaf V s t) =
      c.sectionMul c' V s t :=
  c.tensorMap_section c' V s t

example :
    classOf X ((c * c').lineBundle hU) =
      classOf X (c.lineBundle hU) + classOf X (c'.lineBundle hU) :=
  c.classOf_lineBundle_mul c' hU

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.classOf_lineBundle_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnitCocycle.classOf_lineBundle_mul

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.tensorIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnitCocycle.tensorIso
