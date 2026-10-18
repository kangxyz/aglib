/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.IdealSheaf.Fppf

/-! Focused consumer of closed subschemes as a presheaf on schemes (plan row F6): the singleton
sheaf condition along flat, surjective, quasi-compact morphisms, Zariski and fppf separatedness,
the Zariski sheaf property, and the fpqc and fppf sheaf properties, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] :
    Presieve.IsSheafFor Scheme.idealSheafPresheaf.{u} (Presieve.singleton f) :=
  Scheme.isSheafFor_idealSheafPresheaf_singleton_of_flat_of_surjective_of_quasiCompact f

example : Presieve.IsSeparated Scheme.fppfTopology Scheme.idealSheafPresheaf.{u} :=
  Scheme.isSeparated_idealSheafPresheaf_fppfTopology

example (hZar : Presieve.IsSheaf Scheme.zariskiTopology Scheme.idealSheafPresheaf.{u}) :
    Presieve.IsSheaf Scheme.fppfTopology Scheme.idealSheafPresheaf.{u} :=
  Scheme.isSheaf_idealSheafPresheaf_fppfTopology_of_isSheaf_zariskiTopology hZar

example : Presieve.IsSheaf Scheme.zariskiTopology Scheme.idealSheafPresheaf.{u} :=
  Scheme.isSheaf_idealSheafPresheaf_zariskiTopology

example : Presieve.IsSheaf Scheme.fpqcTopology Scheme.idealSheafPresheaf.{u} :=
  Scheme.isSheaf_idealSheafPresheaf_fpqcTopology

example : Presieve.IsSheaf Scheme.fppfTopology Scheme.idealSheafPresheaf.{u} :=
  Scheme.isSheaf_idealSheafPresheaf_fppfTopology

/--
info: 'AlgebraicGeometry.Scheme.isSheafFor_idealSheafPresheaf_singleton_of_flat_of_surjective_of_quasiCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheafFor_idealSheafPresheaf_singleton_of_flat_of_surjective_of_quasiCompact

/--
info: 'AlgebraicGeometry.Scheme.isSeparated_idealSheafPresheaf_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSeparated_idealSheafPresheaf_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.isSeparated_idealSheafPresheaf_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSeparated_idealSheafPresheaf_fppfTopology

/--
info: 'AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fpqcTopology_of_isSheaf_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fpqcTopology_of_isSheaf_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fppfTopology_of_isSheaf_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fppfTopology_of_isSheaf_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_zariskiTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_zariskiTopology

/--
info: 'AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fpqcTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fpqcTopology

/--
info: 'AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isSheaf_idealSheafPresheaf_fppfTopology
