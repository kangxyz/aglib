/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.GroupLaw

/-! Focused consumer of the group law of a scheme representing the fppf Picard sheaf on locally
Noetherian test schemes, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry Scheme.RelativePicard
open scoped CategoryTheory.MonObj

universe u

variable {S X : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S)
  (P : Scheme.LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The representing scheme is a group object of `Over S`, as consumed by group-scheme
arguments. -/
example : GrpObj P.obj :=
  letI := picardCommGrpObj p P e
  inferInstance

/-- The group law of `P` is the addition of `Pic_{X/S,(fppf)}` on locally Noetherian points. -/
example {T : Scheme.LocallyNoetherianOver S} (f g : T.obj ⟶ P.obj) :
    letI := picardCommGrpObj p P e
    picardHomAddEquiv p P e T (Additive.ofMul (f * g)) =
      picardHomAddEquiv p P e T (Additive.ofMul f) +
        picardHomAddEquiv p P e T (Additive.ofMul g) := by
  let := picardCommGrpObj p P e
  simp only [picardHomAddEquiv_apply]
  exact picard_homEquiv_mul p P e f g

example {T : Scheme.LocallyNoetherianOver S} (f : T.obj ⟶ P.obj) :
    letI := picardCommGrpObj p P e
    e.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)) =
        (0 : (fppfPicardSheaf p).obj.obj (op T.obj)) ∧
      e.homEquiv (ObjectProperty.homMk f⁻¹) =
        -e.homEquiv' (F := (Scheme.locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj)
          (ObjectProperty.homMk f) :=
  ⟨picard_homEquiv_one p P e T, picard_homEquiv_inv p P e f⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardCommGrpObj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardCommGrpObj

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picard_homEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picard_homEquiv_mul

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardHomAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.picardHomAddEquiv
