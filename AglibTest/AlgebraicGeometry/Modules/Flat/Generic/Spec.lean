/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec

/-! Focused consumer of generic flatness over an affine integral Noetherian base (plan row
F12; Nitsure Thm 4.2 for `S = Spec A`). The hypotheses are local finite type of the structure
morphism, quasi-compactness of the source and affine-local finite type of the
quasicoherent coefficient; the conclusion is the stalk condition of `relativeFlat` over the
basic open of the exhibited element `a ≠ 0`. -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

example {X : Scheme} {A : CommRingCat} [IsDomain A] [IsNoetherianRing A] (f : X ⟶ Spec A)
    [LocallyOfFiniteType f] [CompactSpace X] (F : X.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    ∃ a : A, a ≠ 0 ∧ ∀ x : X, a ∉ (f x).asIdeal →
      Module.Flat ((Spec A).presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj F)) :=
  exists_ne_zero_flat_stalk_of_locallyOfFiniteType f F hF

/-- The coherent category of a locally Noetherian source supplies the finite-type input. -/
example {X : Scheme} [IsLocallyNoetherian X] {A : CommRingCat} [IsDomain A]
    [IsNoetherianRing A] (f : X ⟶ Spec A) [LocallyOfFiniteType f] [CompactSpace X]
    (F : X.CoherentSheaf) :
    ∃ U : (Spec A).Opens, (U : Set (Spec A)).Nonempty ∧ ∀ x : X, f x ∈ U →
      Module.Flat ((Spec A).presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj F.obj)) :=
  exists_nonempty_open_flat_stalk_of_locallyOfFiniteType f F.obj F.property

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_ne_zero_flat_stalk_of_locallyOfFiniteType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_ne_zero_flat_stalk_of_locallyOfFiniteType

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_nonempty_open_flat_stalk_of_locallyOfFiniteType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_nonempty_open_flat_stalk_of_locallyOfFiniteType

/--
info: 'AlgebraicGeometry.Scheme.Modules.flat_stalk_specMap_of_flat_localizedModule_away' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms flat_stalk_specMap_of_flat_localizedModule_away

/--
info: 'AlgebraicGeometry.Scheme.Modules.flat_stalk_of_flat_stalk_restrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms flat_stalk_of_flat_stalk_restrict
