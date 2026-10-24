/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Representable

/-!
# Open subschemes represent open subfunctors of representable functors

Let `P` be a property of schemes over `S` that passes to open immersions and is local for open
covers (`IsOpenLocal`), and let `F` be a presheaf on `P.FullSubcategory` represented by `X`
(`e : F.RepresentableBy X`, with universal element `ξ = e.homEquiv (𝟙 X)`). Let `G ⊆ F` be a
subfunctor and `V ⊆ X` an open with property (*) of Stacks, Tag 01JI (Definition 26.15.3) for
the pair `(X, ξ)`: a morphism `a : Z ⟶ X` corresponds to an element of `G` if and only if it
factors through `V` (`a ⁻¹ᵁ V = ⊤`). Then the open subscheme `V` (`restrictOpens X V`) represents
`G` (`representableByRestrictOpens`): a morphism `a : Z ⟶ V` corresponds to the element of `F`
given by `a ≫ V.ι` (`representableByRestrictOpens_homEquiv_coe`), and the universal element of
`G` is the restriction of `ξ` to `V` (`representableByRestrictOpens_homEquiv_id_coe`).

In particular an open subfunctor (`IsOpenSubfunctor`, "representable by open immersions") of a
representable functor is representable, by the open subscheme of the representing object given by
the universal element (`IsOpenSubfunctor.representableBy`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}} {P : ObjectProperty (Over S)} [IsOpenLocal P]

section RestrictOpens

variable (T : P.FullSubcategory) (W : T.obj.left.Opens)

theorem restrictOpensι_hom_left : (restrictOpensι T W).hom.left = W.ι :=
  rfl

instance isOpenImmersion_restrictOpensι_hom_left :
    IsOpenImmersion (restrictOpensι T W).hom.left :=
  inferInstanceAs (IsOpenImmersion W.ι)

/-- A morphism into `restrictOpens T W`, followed by the inclusion, maps into `W`. -/
theorem preimage_comp_restrictOpensι {Z : P.FullSubcategory} (a : Z ⟶ restrictOpens T W) :
    (a ≫ restrictOpensι T W).hom.left ⁻¹ᵁ W = ⊤ := by
  change (a.hom.left ≫ W.ι) ⁻¹ᵁ W = ⊤
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

variable {T W} in
/-- Morphisms into `restrictOpens T W` are determined by their composites with the inclusion. -/
theorem restrictOpensι_cancel {Z : P.FullSubcategory} {a b : Z ⟶ restrictOpens T W}
    (h : a ≫ restrictOpensι T W = b ≫ restrictOpensι T W) : a = b := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  have h' : a.hom.left ≫ W.ι = b.hom.left ≫ W.ι := congrArg (fun f => f.hom.left) h
  exact (cancel_mono W.ι).1 h'

variable {T} in
/-- The lift to `restrictOpens T W` of a morphism to `T` mapping into `W`. -/
def restrictOpensLift {Z : P.FullSubcategory} (a : Z ⟶ T) (h : a.hom.left ⁻¹ᵁ W = ⊤) :
    Z ⟶ restrictOpens T W :=
  ObjectProperty.homMk (overOpensLift a.hom W h)

variable {T} in
@[reassoc (attr := simp)]
theorem restrictOpensLift_ι {Z : P.FullSubcategory} (a : Z ⟶ T) (h : a.hom.left ⁻¹ᵁ W = ⊤) :
    restrictOpensLift W a h ≫ restrictOpensι T W = a :=
  ObjectProperty.hom_ext _ (overOpensLift_ι a.hom W h)

end RestrictOpens

variable {F : P.FullSubcategoryᵒᵖ ⥤ Type v} {X : P.FullSubcategory}

/-- **An open subscheme of a representing object represents the corresponding subfunctor**: if
`e` represents `F` by `X`, `G ⊆ F` is a subfunctor and `V ⊆ X` is an open such that a morphism
`a : Z ⟶ X` corresponds to an element of `G` exactly when it factors through `V` (property (*)
of Stacks, Tag 01JI, for the universal element), then the open subscheme `V` represents `G`,
with `a : Z ⟶ V` corresponding to `a ≫ V.ι`. -/
def representableByRestrictOpens (e : F.RepresentableBy X) (G : Subfunctor F)
    (V : X.obj.left.Opens)
    (hV : ∀ ⦃Z : P.FullSubcategory⦄ (a : Z ⟶ X),
      e.homEquiv a ∈ G.obj (op Z) ↔ a.hom.left ⁻¹ᵁ V = ⊤) :
    G.toFunctor.RepresentableBy (restrictOpens X V) where
  homEquiv {Z} := Equiv.ofBijective
    (fun a => ⟨e.homEquiv (a ≫ restrictOpensι X V),
      (hV _).2 (preimage_comp_restrictOpensι X V a)⟩)
    ⟨fun a b hab => restrictOpensι_cancel (e.homEquiv.injective (congrArg Subtype.val hab)),
      fun x => ⟨restrictOpensLift V (e.homEquiv.symm x.1)
        ((hV _).1 (by rw [Equiv.apply_symm_apply]; exact x.2)), Subtype.ext (by
          change e.homEquiv (restrictOpensLift V (e.homEquiv.symm x.1) _ ≫
            restrictOpensι X V) = x.1
          rw [restrictOpensLift_ι, Equiv.apply_symm_apply])⟩⟩
  homEquiv_comp {Z Z'} f a := Subtype.ext (by
    change e.homEquiv ((f ≫ a) ≫ restrictOpensι X V) =
      F.map f.op (e.homEquiv (a ≫ restrictOpensι X V))
    rw [Category.assoc, e.homEquiv_comp])

variable (e : F.RepresentableBy X) (G : Subfunctor F) (V : X.obj.left.Opens)
  (hV : ∀ ⦃Z : P.FullSubcategory⦄ (a : Z ⟶ X),
    e.homEquiv a ∈ G.obj (op Z) ↔ a.hom.left ⁻¹ᵁ V = ⊤)

/-- The representing equivalence of `representableByRestrictOpens` sends `a : Z ⟶ V` to the
element of `F` given by `a ≫ V.ι`. -/
theorem representableByRestrictOpens_homEquiv_coe {Z : P.FullSubcategory}
    (a : Z ⟶ restrictOpens X V) :
    ((representableByRestrictOpens e G V hV).homEquiv a : F.obj (op Z)) =
      e.homEquiv (a ≫ restrictOpensι X V) :=
  rfl

/-- **The universal element of `G`** is the restriction to `V` of the universal element of
`F`. -/
theorem representableByRestrictOpens_homEquiv_id_coe :
    ((representableByRestrictOpens e G V hV).homEquiv (𝟙 _) : F.obj (op (restrictOpens X V))) =
      F.map (restrictOpensι X V).op (e.homEquiv (𝟙 X)) := by
  have h := e.homEquiv_comp (restrictOpensι X V) (𝟙 X)
  rw [Category.comp_id] at h
  rw [representableByRestrictOpens_homEquiv_coe, Category.id_comp, h]

variable {G} in
/-- **An open subfunctor of a representable functor is representable**: if `e` represents `F` by
`X` and `G ⊆ F` is open (`IsOpenSubfunctor`), then `G` is represented by the open subscheme of `X`
attached by `hG` to the universal element `e.homEquiv (𝟙 X)`. -/
def IsOpenSubfunctor.representableBy (hG : IsOpenSubfunctor G) :
    G.toFunctor.RepresentableBy (restrictOpens X (hG (e.homEquiv (𝟙 X))).choose) :=
  representableByRestrictOpens e G _ fun Z a => by
    have h := e.homEquiv_comp a (𝟙 X)
    rw [Category.comp_id] at h
    rw [h]
    exact (hG (e.homEquiv (𝟙 X))).choose_spec a

end AlgebraicGeometry.Scheme.LocalRepresentability
