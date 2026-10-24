/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.GlueDisjoint

/-! Focused consumer of the gluing of ideal sheaves along a disjoint open cover, with axiom
guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- Ideal sheaves on a disjoint open cover glue, with no compatibility hypothesis. -/
example {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ x : X, ∃ i y, f i y = x)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))
    (I : ∀ i, (U i).IdealSheafData) (i : ι) :
    (Scheme.IdealSheafData.glueOfDisjoint f hcov hdisj I).comap (f i) = I i :=
  Scheme.IdealSheafData.comap_glueOfDisjoint f hcov hdisj I i

/-- The glued ideal sheaf is determined by its restrictions. -/
example {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ x : X, ∃ i y, f i y = x)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))
    (I : ∀ i, (U i).IdealSheafData) (K : X.IdealSheafData) (hK : ∀ i, K.comap (f i) = I i) :
    K = Scheme.IdealSheafData.glueOfDisjoint f hcov hdisj I :=
  (Scheme.IdealSheafData.eq_glueOfDisjoint_iff f hcov hdisj I K).mpr hK

/-- On an empty scheme every ideal sheaf is the unit ideal sheaf. -/
example {X : Scheme.{u}} [IsEmpty X] (I : X.IdealSheafData) : I = ⊤ :=
  Scheme.IdealSheafData.eq_of_isEmpty I ⊤

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_glueOfDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_glueOfDisjoint
