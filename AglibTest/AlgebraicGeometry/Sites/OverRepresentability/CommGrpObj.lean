/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.CommGrpObj

/-! Focused consumer of the group law of a scheme locally of finite type over a locally
Noetherian base representing a presheaf of abelian groups on locally Noetherian test schemes, with
axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry Scheme.LocallyNoetherianOver
open scoped CategoryTheory.MonObj

universe w u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{w})
  (P : Scheme.LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (e : ((Scheme.locallyNoetherianOverInclusion S).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat).RepresentableBy P)

/-- `P` is a commutative group object of `Over S`; in particular `T ⟶ P` is a commutative group
for every `T` over `S`. -/
example (T : Over S) :
    letI := commGrpObjOfRepresentableBy F P e
    CommGroup (T ⟶ P.obj) :=
  letI := commGrpObjOfRepresentableBy F P e
  inferInstance

/-- The representation is additive on locally Noetherian points. -/
example {T : Scheme.LocallyNoetherianOver S} (f g : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P e
    e.homEquiv (ObjectProperty.homMk (f * g)) =
      e.homEquiv' (F := (Scheme.locallyNoetherianOverInclusion S).op ⋙ F)
          (ObjectProperty.homMk f) +
        e.homEquiv' (F := (Scheme.locallyNoetherianOverInclusion S).op ⋙ F)
          (ObjectProperty.homMk g) :=
  homEquiv_mul F P e f g

/-- The unit and the inverse correspond to zero and negation. -/
example {T : Scheme.LocallyNoetherianOver S} (f : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P e
    e.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)) = (0 : F.obj (op T.obj)) ∧
      e.homEquiv (ObjectProperty.homMk f⁻¹) =
        -e.homEquiv' (F := (Scheme.locallyNoetherianOverInclusion S).op ⋙ F)
          (ObjectProperty.homMk f) :=
  ⟨homEquiv_one F P e T, homEquiv_inv F P e f⟩

/-- The representation as an isomorphism of abelian groups. -/
example (T : Scheme.LocallyNoetherianOver S) (f g : T.obj ⟶ P.obj) :
    letI := commGrpObjOfRepresentableBy F P e
    homAddEquiv F P e T (Additive.ofMul (f * g)) =
      homAddEquiv F P e T (Additive.ofMul f) + homAddEquiv F P e T (Additive.ofMul g) :=
  letI := commGrpObjOfRepresentableBy F P e
  map_add (homAddEquiv F P e T) (Additive.ofMul f) (Additive.ofMul g)

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.commGrpObjOfRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.commGrpObjOfRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.homEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.homEquiv_mul

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.homAddEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.homAddEquiv
