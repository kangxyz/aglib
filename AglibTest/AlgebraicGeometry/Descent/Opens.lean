/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.Opens

/-! Focused consumer of the descent of open subschemes along fppf coverings (plan row F6): the
sheaf property of `Scheme.opensPresheaf` for the fppf topology and descent along one flat
surjective morphism locally of finite presentation, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

example : Presieve.IsSheaf Scheme.fppfTopology Scheme.opensPresheaf.{u} :=
  Scheme.isSheaf_opensPresheaf_fppfTopology

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (U : X.Opens) (hU : pullback.fst f f ⁻¹ᵁ U = pullback.snd f f ⁻¹ᵁ U) :
    ∃! V : Y.Opens, f ⁻¹ᵁ V = U :=
  Scheme.existsUnique_preimage_eq_of_flat_of_surjective f U hU

/--
info: 'AlgebraicGeometry.Scheme.existsUnique_preimage_eq_of_isOpenMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.existsUnique_preimage_eq_of_isOpenMap

/--
info: 'AlgebraicGeometry.Scheme.isSheaf_opensPresheaf_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheaf_opensPresheaf_fppfTopology

/--
info: 'AlgebraicGeometry.Scheme.preimage_imageOpens_eq_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.preimage_imageOpens_eq_of_flat

/--
info: 'AlgebraicGeometry.Scheme.existsUnique_preimage_eq_of_flat_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.existsUnique_preimage_eq_of_flat_of_surjective
