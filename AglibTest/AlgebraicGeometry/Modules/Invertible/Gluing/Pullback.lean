/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Pullback

/-! Focused consumer of the pullback of a glued line module: compatible transition units give
`f^* c.sheaf ≅ c'.sheaf`, the comparison sends pulled-back generators to generators, it is
stable under integer powers of the cocycles, and morphisms out of a glued sheaf are determined
by the chart generators. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} {U : ι → Y.Opens} {U' : ι → X.Opens}
  (c : UnitCocycle U) (c' : UnitCocycle U') (hU : ∀ i, f ⁻¹ᵁ U i = U' i)
  (ht : UnitCocycle.TransitionPullback f c c') (hYU : iSup U = ⊤)

/-- The pullback of the glued sheaf is the glued sheaf of the pulled-back cocycle. -/
example : (Scheme.Modules.pullback f).obj c.sheaf ≅ c'.sheaf :=
  c.pullbackIso f c' hU ht hYU

/-- The comparison sends the pulled-back generator to the generator on every chart subopen. -/
example (i : ι) {V : X.Opens} (hV : V ≤ U' i) :
    (c.pullbackIso f c' hU ht hYU).hom.val.app (op V)
        (c.pullbackGenerator f i (hV.trans (hU i).ge)) = c'.generator i hV :=
  c.pullbackIso_hom_pullbackGenerator f c' hU ht hYU i hV

/-- Integer powers of compatible cocycles are compatible, so every power pulls back. -/
example (n : ℤ) : (Scheme.Modules.pullback f).obj (c.zpow n).sheaf ≅ (c'.zpow n).sheaf :=
  (c.zpow n).pullbackIso f (c'.zpow n) hU (ht.zpow n) hYU

/-- Morphisms out of a glued sheaf are determined by the images of the chart generators. -/
example {M : Y.Modules} {g h : c.sheaf ⟶ M}
    (hgh : ∀ i, g.val.app (op (U i)) (c.generator i le_rfl) =
      h.val.app (op (U i)) (c.generator i le_rfl)) : g = h :=
  c.hom_ext_generator hYU hgh

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.hom_ext_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.hom_ext_generator

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.TransitionPullback.zpow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.TransitionPullback.zpow

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.pullbackIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.pullbackIso

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.pullbackIso_hom_pullbackGenerator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.pullbackIso_hom_pullbackGenerator

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.pullbackIso_inv_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.pullbackIso_inv_generator
