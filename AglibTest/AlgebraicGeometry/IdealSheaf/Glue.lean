/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.Glue

/-! Focused consumer of the gluing of ideal sheaves along open covers: the glued ideal sheaf
pulls back to the given ideal sheaves along the members of the cover, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

example {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] (I : ∀ i, (U i).IdealSheafData)
    (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)))
    (i : ι) : (Scheme.IdealSheafData.glue f I hf hI).comap (f i) = I i :=
  Scheme.IdealSheafData.comap_glue hf hI i

example {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] (I : ∀ i, (U i).IdealSheafData)
    (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j))) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (f i) = I i :=
  Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion hf hI

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_glue

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion
