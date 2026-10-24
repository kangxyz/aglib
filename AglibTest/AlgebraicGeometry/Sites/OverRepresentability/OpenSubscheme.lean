/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.OpenSubscheme

/-! Focused consumer of the representability of open subfunctors of representable functors by
open subschemes of the representing object (property (*) of Stacks, Tag 01JI, for the universal
element), with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.LocalRepresentability

universe v u

/-- **An open subfunctor of a representable functor is representable.** -/
example {S : Scheme.{u}} {P : ObjectProperty (Over S)} [IsOpenLocal P]
    {F : P.FullSubcategoryᵒᵖ ⥤ Type v} {X : P.FullSubcategory} (e : F.RepresentableBy X)
    {G : Subfunctor F} (hG : IsOpenSubfunctor G) : G.toFunctor.IsRepresentable :=
  (hG.representableBy e).isRepresentable

/-- A morphism to the open subscheme corresponds to its composite with the inclusion, and the
universal element is the restriction of the universal element of `F`. -/
example {S : Scheme.{u}} {P : ObjectProperty (Over S)} [IsOpenLocal P]
    {F : P.FullSubcategoryᵒᵖ ⥤ Type v} {X : P.FullSubcategory} (e : F.RepresentableBy X)
    (G : Subfunctor F) (V : X.obj.left.Opens)
    (hV : ∀ ⦃Z : P.FullSubcategory⦄ (a : Z ⟶ X),
      e.homEquiv a ∈ G.obj (op Z) ↔ a.hom.left ⁻¹ᵁ V = ⊤)
    {Z : P.FullSubcategory} (a : Z ⟶ restrictOpens X V) :
    ((representableByRestrictOpens e G V hV).homEquiv a : F.obj (op Z)) =
        e.homEquiv (a ≫ restrictOpensι X V) ∧
      ((representableByRestrictOpens e G V hV).homEquiv (𝟙 _) :
          F.obj (op (restrictOpens X V))) =
        F.map (restrictOpensι X V).op (e.homEquiv (𝟙 X)) :=
  ⟨representableByRestrictOpens_homEquiv_coe e G V hV a,
    representableByRestrictOpens_homEquiv_id_coe e G V hV⟩

/--
info: 'AlgebraicGeometry.Scheme.LocalRepresentability.representableByRestrictOpens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.representableByRestrictOpens
