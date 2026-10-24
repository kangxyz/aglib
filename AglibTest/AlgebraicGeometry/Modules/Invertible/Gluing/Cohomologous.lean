/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Cohomologous
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.PullbackCocycle

/-! Focused consumer of cohomologous unit cocycles: cohomologous cocycles glue to isomorphic
sheaves and conversely, the trivial cocycle glues to the structure sheaf, twisting gives a
cohomologous cocycle, and the pulled-back cocycle glues to the pullback. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : iSup U = ⊤)

example (c c' : UnitCocycle U) (u : ∀ i, (Γ(X, U i))ˣ) (h : UnitCocycle.Cohomologous c c' u) :
    c.sheaf ≅ c'.sheaf :=
  UnitCocycle.sheafIsoOfCohomologous hU h

example (c c' : UnitCocycle U) (φ : c.sheaf ≅ c'.sheaf) :
    ∃ u : ∀ i, (Γ(X, U i))ˣ, UnitCocycle.Cohomologous c c' u :=
  UnitCocycle.exists_cohomologous_of_iso φ

example : (1 : UnitCocycle U).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  UnitCocycle.oneSheafIso hU

example (c : UnitCocycle U) (w : ∀ i, (Γ(X, U i))ˣ) :
    classOf X ((c.twist w).lineBundle hU) = classOf X (c.lineBundle hU) :=
  ((UnitCocycle.classOf_lineBundle_eq_iff hU c (c.twist w)).mpr
    ⟨w, c.cohomologous_twist w⟩).symm

example (c : UnitCocycle U) :
    classOf X (c.lineBundle hU) = 0 ↔ ∃ u : ∀ i, (Γ(X, U i))ˣ, UnitCocycle.Cohomologous 1 c u :=
  UnitCocycle.classOf_lineBundle_eq_zero_iff hU c

example {Y : Scheme.{u}} (f : Y ⟶ X) {U' : ι → Y.Opens} (hf : ∀ i, f ⁻¹ᵁ U i = U' i)
    (c : UnitCocycle U) :
    classOf Y (pullbackLineBundle f (c.lineBundle hU)) =
      classOf Y ((c.pullbackCocycle f hf).lineBundle
        (UnitCocycle.iSup_eq_top_of_preimage hf hU)) :=
  c.classOf_pullbackLineBundle f hf hU

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.classOf_lineBundle_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnitCocycle.classOf_lineBundle_eq_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.classOf_lineBundle_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnitCocycle.classOf_lineBundle_eq_zero_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle.classOf_pullbackLineBundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms UnitCocycle.classOf_pullbackLineBundle
