/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyOfFiniteTypeOver

/-! Focused consumer of schemes locally of finite type over a base: closure under the terminal
object and binary products, the cartesian monoidal full subcategory, the inclusion into locally
Noetherian schemes over a locally Noetherian base, and the restriction of representations, with
axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry

universe w u

variable {S : Scheme.{u}}

/-- The full subcategory is cartesian monoidal, with the fibre products of `Over S`. -/
example (Y Z : Scheme.LocallyOfFiniteTypeOver S) :
    ((Y ⊗ Z).obj = Y.obj ⊗ Z.obj) ∧ LocallyOfFiniteType (Y ⊗ Z).obj.hom :=
  ⟨rfl, inferInstance⟩

/-- The terminal object `𝟙 S` and binary products are locally of finite type over `S`. -/
example : (Scheme.locallyOfFiniteTypeOver S).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) ∧
    (Scheme.locallyOfFiniteTypeOver S).IsClosedUnderLimitsOfShape (Discrete WalkingPair) ∧
    (Scheme.locallyOfFiniteTypeOver S).IsClosedUnderIsomorphisms :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Over a locally Noetherian base, schemes locally of finite type are locally Noetherian. -/
example [IsLocallyNoetherian S] (T : Scheme.LocallyOfFiniteTypeOver S) :
    IsLocallyNoetherian T.obj.left :=
  Scheme.locallyOfFiniteTypeOver_le_locallyNoetherianOver S _ T.property

/-- A representation on locally Noetherian test schemes by a scheme locally of finite type
restricts to test schemes locally of finite type. -/
example [IsLocallyNoetherian S] {F : (Scheme.LocallyNoetherianOver S)ᵒᵖ ⥤ Type w}
    {P : Scheme.LocallyNoetherianOver S} [LocallyOfFiniteType P.obj.hom] (e : F.RepresentableBy P)
    {T : Scheme.LocallyOfFiniteTypeOver S} (f : T ⟶ P.toLocallyOfFiniteTypeOver) :
    (Scheme.LocallyNoetherianOver.representableByLocallyOfFiniteType e).homEquiv f =
      e.homEquiv (ObjectProperty.homMk f.hom) :=
  Scheme.LocallyNoetherianOver.representableByLocallyOfFiniteType_homEquiv e f

/--
info: 'AlgebraicGeometry.Scheme.isClosedUnderBinaryProducts_locallyOfFiniteTypeOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isClosedUnderBinaryProducts_locallyOfFiniteTypeOver

/--
info: 'AlgebraicGeometry.Scheme.isClosedUnderLimitsOfShape_discrete_pEmpty_locallyOfFiniteTypeOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.isClosedUnderLimitsOfShape_discrete_pEmpty_locallyOfFiniteTypeOver

/--
info: 'AlgebraicGeometry.Scheme.locallyOfFiniteTypeOver_le_locallyNoetherianOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.locallyOfFiniteTypeOver_le_locallyNoetherianOver

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.representableByLocallyOfFiniteType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.representableByLocallyOfFiniteType
