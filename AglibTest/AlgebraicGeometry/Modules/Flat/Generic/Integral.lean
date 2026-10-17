/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Integral

/-! Focused consumer of generic flatness over an integral Noetherian base (plan row F12;
Nitsure Thm 4.2). The structure morphism is locally of finite type and quasi-compact; the
coefficient is an actual coherent sheaf of a locally Noetherian source. -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

example {X S : Scheme} [IsLocallyNoetherian X] (f : X ⟶ S) [IsIntegral S]
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] (F : X.CoherentSheaf) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ ∀ x : X, f x ∈ U →
      Module.Flat (S.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj ((moduleStalk X x).obj F.obj)) :=
  exists_nonempty_open_flat_stalk_of_isIntegral f F.obj F.property

example {X S : Scheme} (f : X ⟶ S) [IsIntegral S] [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ relativeFlat (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) :=
  exists_nonempty_open_relativeFlat_of_isIntegral f F hF

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_nonempty_open_flat_stalk_of_isIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_nonempty_open_flat_stalk_of_isIntegral

/--
info: 'AlgebraicGeometry.Scheme.Modules.flat_stalk_comp_of_flat_stalk_of_isOpenImmersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms flat_stalk_comp_of_flat_stalk_of_isOpenImmersion

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_nonempty_open_relativeFlat_of_isIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_nonempty_open_relativeFlat_of_isIntegral

/--
info: 'AlgebraicGeometry.Scheme.Modules.flat_stalk_restrict_of_flat_stalk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms flat_stalk_restrict_of_flat_stalk
