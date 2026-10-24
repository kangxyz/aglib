/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.Monomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! Focused consumer of closed subschemes along a monomorphism: the inverse bijections
`IdealSheafData.map` and `IdealSheafData.comap`, their compatibility with cartesian squares, base
change of properties of closed subschemes over a base, and the properness criterion for
preimmersions, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- Along an immersion, a closed subscheme that is closed in the target is the pullback of its
image. -/
example {X Y : Scheme.{u}} (j : X ⟶ Y) [IsImmersion j] (I : X.IdealSheafData)
    [IsClosedImmersion (I.subschemeι ≫ j)] :
    (I.map j).comap j = I ∧ ∃ w : (I.map j).subscheme ⟶ X, w ≫ j = (I.map j).subschemeι :=
  ⟨Scheme.IdealSheafData.comap_map_of_mono_of_isClosedImmersion I j, I.exists_lift_map_subschemeι j⟩

/-- A closed subscheme of the target contained in the source is the image of its pullback, and
its pullback is closed in the target. -/
example {X Y : Scheme.{u}} (j : X ⟶ Y) [Mono j] (J : Y.IdealSheafData) (w : J.subscheme ⟶ X)
    (hw : w ≫ j = J.subschemeι) :
    J.comap j = w.ker ∧ (J.comap j).map j = J ∧
      IsClosedImmersion ((J.comap j).subschemeι ≫ j) :=
  ⟨Scheme.IdealSheafData.comap_eq_ker_of_comp_eq J j w hw,
    Scheme.IdealSheafData.map_comap_of_comp_eq J j w hw,
    Scheme.IdealSheafData.isClosedImmersion_comap_subschemeι_comp J j w hw⟩

/-- Without a monomorphism hypothesis, a closed subscheme of the target that factors through `j`
is still the image of its pullback, and closedness in the target passes along cartesian squares. -/
example {X Y X₂ Y₂ : Scheme.{u}} (j : X ⟶ Y) (J : Y.IdealSheafData) (w : J.subscheme ⟶ X)
    (hw : w ≫ j = J.subschemeι) {j₂ : X₂ ⟶ Y₂} {a : X₂ ⟶ X} {b : Y₂ ⟶ Y}
    (h : IsPullback j₂ a b j) (I : X.IdealSheafData) [IsClosedImmersion (I.subschemeι ≫ j)] :
    (J.comap j).map j = J ∧ IsClosedImmersion ((I.comap a).subschemeι ≫ j₂) :=
  ⟨Scheme.IdealSheafData.map_comap_of_comp_eq J j w hw,
    Scheme.IdealSheafData.isClosedImmersion_comap_subschemeι_comp_of_isPullback h I⟩

/-- For a closed immersion `j` every closed subscheme of the source is closed in the target, and
the bijection round-trips. -/
example {X Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j] (I : X.IdealSheafData) :
    ((Scheme.IdealSheafData.mapEquivOfMono j).symm
      (Scheme.IdealSheafData.mapEquivOfMono j ⟨I, inferInstance⟩)).1 = I := by
  simp

/-- The image and the closedness condition commute with base change along a cartesian square. -/
example {X₁ Y₁ X₂ Y₂ : Scheme.{u}} {j₁ : X₁ ⟶ Y₁} {j₂ : X₂ ⟶ Y₂} {a : X₂ ⟶ X₁} {b : Y₂ ⟶ Y₁}
    (h : IsPullback j₂ a b j₁) [IsImmersion j₁] (I : X₁.IdealSheafData)
    [IsClosedImmersion (I.subschemeι ≫ j₁)] :
    (I.map j₁).comap b = (I.comap a).map j₂ ∧ IsClosedImmersion ((I.comap a).subschemeι ≫ j₂) :=
  ⟨Scheme.IdealSheafData.map_comap_of_isPullback h I,
    Scheme.IdealSheafData.isClosedImmersion_comap_subschemeι_comp_of_isPullback h I⟩

/-- Flatness over the base passes to pullbacks of closed subschemes along cartesian squares. -/
example {X₁ X₂ T₁ T₂ : Scheme.{u}} {a : X₂ ⟶ X₁} {p₁ : X₁ ⟶ T₁} {p₂ : X₂ ⟶ T₂} {f : T₂ ⟶ T₁}
    (h : IsPullback a p₂ p₁ f) (I : X₁.IdealSheafData) (hI : Flat (I.subschemeι ≫ p₁)) :
    Flat ((I.comap a).subschemeι ≫ p₂) :=
  Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback @Flat h I hI

/-- A closed subscheme of an immersed scheme is proper over a base exactly when it is closed in
the proper ambient scheme. -/
example {X Y T : Scheme.{u}} (j : X ⟶ Y) [IsImmersion j] (q : Y ⟶ T) [IsProper q]
    (I : X.IdealSheafData) :
    IsProper (I.subschemeι ≫ j ≫ q) ↔ IsClosedImmersion (I.subschemeι ≫ j) :=
  I.isProper_subschemeι_comp_iff_isClosedImmersion rfl

/-- Over a separated ambient scheme, a proper closed subscheme of an immersed scheme is closed. -/
example {X Y T : Scheme.{u}} (j : X ⟶ Y) [IsImmersion j] (q : Y ⟶ T) [IsSeparated q]
    (I : X.IdealSheafData) (hI : IsProper (I.subschemeι ≫ j ≫ q)) :
    IsClosedImmersion (I.subschemeι ≫ j) :=
  I.isClosedImmersion_subschemeι_comp_of_isProper rfl hI

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_mono_of_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_mono_of_isClosedImmersion

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_comp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_comp_eq

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.mapEquivOfMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.mapEquivOfMono

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.isProper_subschemeι_comp_iff_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.isProper_subschemeι_comp_iff_isClosedImmersion
