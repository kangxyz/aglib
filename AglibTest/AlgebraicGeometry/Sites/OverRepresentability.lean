/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.BaseCover
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Consumer checks for Zariski-local representability over a base

The functor of points of a scheme `X` over `S`, with values in `Type (u + 1)`, is re-derived as
representable through `OverSubfunctorCover` from an open cover of `X`: the subfunctors are the
points landing in the members of the cover, represented by the open subschemes, and the glued
scheme is isomorphic to `X` over `S`. When `X` is locally Noetherian, the same cover restricted
to locally Noetherian test schemes checks the locally Noetherian variant. Through an open cover
of the base, the restrictions are represented by the pullbacks of `X`, which checks
`isRepresentable_of_openCover_base`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Scheme.LocalRepresentability

universe u

namespace AglibTest.OverRepresentability

variable {S : Scheme.{u}} (X : Over S) {ι : Type u} (V : ι → X.left.Opens)

/-- The functor of points of `X` over `S`, with values in `Type (u + 1)`. -/
abbrev pointsFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  uliftYoneda.{u + 1}.obj X

/-- The points of `X` landing in `V i`. -/
def sub (i : ι) : Subfunctor (pointsFunctor X) where
  obj _ := {ξ | ξ.down.left ⁻¹ᵁ V i = ⊤}
  map {_ _} f ξ hξ := by
    change (f.unop ≫ ξ.down).left ⁻¹ᵁ V i = ⊤
    rw [Over.comp_left, Scheme.Hom.comp_preimage, show ξ.down.left ⁻¹ᵁ V i = ⊤ from hξ]
    exact Scheme.Hom.preimage_top _

lemma isOpen_sub (i : ι) : IsOpenOverSubfunctor (sub X V i) := by
  intro T ξ
  refine ⟨ξ.down.left ⁻¹ᵁ V i, fun Z g => ?_⟩
  change (g ≫ ξ.down).left ⁻¹ᵁ V i = ⊤ ↔ g.left ⁻¹ᵁ (ξ.down.left ⁻¹ᵁ V i) = ⊤
  rw [Over.comp_left, Scheme.Hom.comp_preimage]

lemma comp_ι_preimage {T : Over S} (i : ι) (h : T ⟶ overOpens X (V i)) :
    (h ≫ overOpensι X (V i)).left ⁻¹ᵁ V i = ⊤ := by
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  change h.left ⁻¹ᵁ ((V i).ι ⁻¹ᵁ V i) = ⊤
  rw [Scheme.Opens.ι_preimage_self]
  exact Scheme.Hom.preimage_top _

/-- The open subscheme `V i` represents the points of `X` landing in `V i`. -/
def representableBySub (i : ι) :
    (sub X V i).toFunctor.RepresentableBy (overOpens X (V i)) where
  homEquiv {_} :=
    { toFun h := ⟨⟨h ≫ overOpensι X (V i)⟩, comp_ι_preimage X V i h⟩
      invFun ξ := overOpensLift ξ.1.down (V i) ξ.2
      left_inv h := Over.OverMorphism.ext ((cancel_mono (V i).ι).1
        (congrArg (fun f => f.left) (overOpensLift_ι _ (V i) (comp_ι_preimage X V i h))))
      right_inv ξ := Subtype.ext (ULift.ext _ _ (overOpensLift_ι _ (V i) ξ.2)) }
  homEquiv_comp _ _ := Subtype.ext (ULift.ext _ _ (Category.assoc _ _ _))

lemma covers_sub (hV : ∀ x : X.left, ∃ i, x ∈ V i) ⦃T : Over S⦄
    (ξ : (pointsFunctor X).obj (op T)) (x : T.left) :
    ∃ (i : ι) (Z : Over S) (g : Z ⟶ T), x ∈ Set.range g.left ∧
      (pointsFunctor X).map g.op ξ ∈ (sub X V i).obj (op Z) := by
  obtain ⟨i, hi⟩ := hV (ξ.down.left x)
  refine ⟨i, overOpens T (ξ.down.left ⁻¹ᵁ V i), overOpensι T _, ?_, ?_⟩
  · change x ∈ Set.range (ξ.down.left ⁻¹ᵁ V i).ι
    rw [Scheme.Opens.range_ι]
    exact hi
  · change (overOpensι T _ ≫ ξ.down).left ⁻¹ᵁ V i = ⊤
    rw [Over.comp_left, Scheme.Hom.comp_preimage]
    exact Scheme.Opens.ι_preimage_self _

/-- An open cover of `X` as a cover of its functor of points by representable open
subfunctors. -/
abbrev cover (hV : ∀ x : X.left, ∃ i, x ∈ V i) : OverSubfunctorCover (pointsFunctor X) where
  I := ι
  sub := sub X V
  isOpen := isOpen_sub X V
  X i := overOpens X (V i)
  representableBy := representableBySub X V
  covers := covers_sub X V hV

lemma isSheaf_pointsFunctor :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (pointsFunctor X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The functor of points of `X`, with values in `Type (u + 1)`, is represented by the scheme
glued from the open cover. -/
def representableByGlued (hV : ∀ x : X.left, ∃ i, x ∈ V i) :
    (pointsFunctor X).RepresentableBy (cover X V hV).glued :=
  (cover X V hV).representableByGlued (isSheaf_pointsFunctor X)

/-- The glued scheme is isomorphic to `X` over `S`. -/
def gluedIso (hV : ∀ x : X.left, ∃ i, x ∈ V i) : (cover X V hV).glued ≅ X :=
  (representableByGlued X V hV).uniqueUpToIso
    (Functor.representableByUliftFunctorEquiv.symm (Functor.RepresentableBy.yoneda X))

/-- The chart `V i ⟶ glued` corresponds to the universal point of `V i`, the inclusion. -/
example (hV : ∀ x : X.left, ∃ i, x ∈ V i) (i : ι) :
    ((representableByGlued X V hV).homEquiv ((cover X V hV).ι i)).down = overOpensι X (V i) :=
  (congrArg ULift.down ((cover X V hV).representableByGlued_homEquiv_ι
    (isSheaf_pointsFunctor X) i)).trans (Category.id_comp _)

example (hV : ∀ x : X.left, ∃ i, x ∈ V i) : (pointsFunctor X).IsRepresentable :=
  (cover X V hV).isRepresentable (isSheaf_pointsFunctor X)

/-- On locally Noetherian test schemes, the restricted functor of points of a locally Noetherian
`X` is represented by a locally Noetherian scheme, through the locally Noetherian variant. -/
example [IsLocallyNoetherian X.left] (hV : ∀ x : X.left, ∃ i, x ∈ V i) :
    ((ObjectProperty.ι fun T : Over S => IsLocallyNoetherian T.left).op ⋙
      pointsFunctor X).IsRepresentable :=
  isRepresentable_of_isLocallyNoetherian (isZariskiSheaf_comp_ι (isSheaf_pointsFunctor X))
    ((cover X V hV).restrict (fun T : Over S => IsLocallyNoetherian T.left)
      fun i => (inferInstance : IsLocallyNoetherian (V i).toScheme))

/-- Restricted to schemes over an open `U ⊆ S`, the functor of points of `X` is represented by
the pullback of `X` to `U`. -/
def restrictRepresentableBy (U : S.Opens) :
    ((Over.map U.ι).op ⋙ pointsFunctor X).RepresentableBy ((Over.pullback U.ι).obj X) where
  homEquiv {T} := ((Over.mapPullbackAdj U.ι).homEquiv T X).symm.trans Equiv.ulift.symm
  homEquiv_comp f g :=
    ULift.ext _ _ ((Over.mapPullbackAdj U.ι).homEquiv_naturality_left_symm f g)

/-- Representability through an open cover of the base. -/
theorem isRepresentable_of_baseCover {κ : Type u} (U : κ → S.Opens) (hU : ∀ s : S, ∃ i, s ∈ U i) :
    (pointsFunctor X).IsRepresentable :=
  overZariskiLocalRepresentability S (pointsFunctor X) (isSheaf_pointsFunctor X) κ
    (fun i => (U i).toScheme) (fun i => (U i).ι) (fun _ => inferInstance)
    (fun s => (hU s).imp fun i hi => by rw [Scheme.Opens.range_ι]; exact hi)
    (fun i => (restrictRepresentableBy X (U i)).isRepresentable)

/-- A mirror of F13's `Scheme.locallyNoetherianOver S`
(`Aglib/AlgebraicGeometry/Properties/Noetherian/LocallyNoetherianOver.lean`, not imported here):
an abbreviation of the same property. -/
abbrev locallyNoetherianOver' (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun T => IsLocallyNoetherian T.left

example (S : Scheme.{u}) : IsOpenLocal (locallyNoetherianOver' S) :=
  inferInstance

/-- The locally Noetherian variant applies to presheaves on the mirrored category of locally
Noetherian test schemes, with values in `Type (u + 1)`. -/
example {S : Scheme.{u}} (F : (locallyNoetherianOver' S).FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (hF : IsZariskiSheaf F) (𝒰 : SubfunctorCover F) : F.IsRepresentable :=
  isRepresentable_of_isLocallyNoetherian hF 𝒰

/-- The representing object of the locally Noetherian variant is locally Noetherian. -/
example {S : Scheme.{u}} (F : (locallyNoetherianOver' S).FullSubcategoryᵒᵖ ⥤ Type (u + 1))
    (hF : IsZariskiSheaf F) (𝒰 : SubfunctorCover F) :
    Nonempty (F.RepresentableBy 𝒰.glued) ∧ IsLocallyNoetherian 𝒰.glued.obj.left :=
  ⟨⟨𝒰.representableByGlued hF⟩, 𝒰.glued.property⟩

end AglibTest.OverRepresentability

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.representableByGlued'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.representableByGlued

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.isRepresentable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover.isRepresentable

/-- info:
'AlgebraicGeometry.Scheme.LocalRepresentability.OverSubfunctorCover.representableByGlued'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.LocalRepresentability.OverSubfunctorCover.representableByGlued

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.OverSubfunctorCover.isRepresentable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.OverSubfunctorCover.isRepresentable

/-- info:
'AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isLocallyNoetherian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isLocallyNoetherian

/-- info: 'AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_openCover_base'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_openCover_base

/-- info: 'AglibTest.OverRepresentability.isRepresentable_of_baseCover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.OverRepresentability.isRepresentable_of_baseCover

/-- info: 'AglibTest.OverRepresentability.gluedIso' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.OverRepresentability.gluedIso
