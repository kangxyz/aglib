/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Representable

/-!
# Zariski-local representability for presheaves on schemes over a base

Let `S` be a scheme and `F : (Over S)ᵒᵖ ⥤ Type v` a presheaf, with values in any universe `v`
(for example `Type (u + 1)`, the values of the Picard and Quot functors; no smallness hypothesis
is needed). Suppose (Stacks, Tag 01JJ, Lemma 26.15.4, stated there for functors on all schemes;
here relative to `S`, the form used by Kleiman, arXiv:math/0504020v1, Introduction, p. 14, and
proof of Thm 4.8, pp. 28–29, to assemble the Picard scheme from open subfunctors):

- `F` is a sheaf for `Scheme.zariskiTopology.over S`;
- `𝒰 : OverSubfunctorCover F` consists of subfunctors `𝒰.sub i ⊆ F` that are open
  (`IsOpenOverSubfunctor`: the pullback of `𝒰.sub i` along any `ξ ∈ F(T)` is an open subscheme of
  `T`; Stacks, Tag 01JI), represented by schemes `𝒰.X i` over `S`, and covering `F`
  Zariski-locally.

Then `F` is represented by the scheme `𝒰.glued` over `S` glued from the `𝒰.X i`
(`OverSubfunctorCover.representableByGlued`, `OverSubfunctorCover.isRepresentable`), with open
charts `𝒰.ι i : 𝒰.X i ⟶ 𝒰.glued` corresponding to the universal elements of the `𝒰.sub i`.

The proof restricts `F` to the full subcategory `⊤` of `Over S` and applies the general
statement for full subcategories of a property `P` that passes to open immersions and is local for
open covers (`IsOpenLocal P`; `SubfunctorCover.representableByGlued`).
`OverSubfunctorCover.restrict` restricts a cover to any such full subcategory, for example locally
Noetherian test schemes, when the representing schemes lie in it.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}}

section Restrict

variable (P : ObjectProperty (Over S)) {F : (Over S)ᵒᵖ ⥤ Type v}

/-- The restriction of a subfunctor of `F` to the full subcategory of `P`. -/
def restrictSubfunctor (G : Subfunctor F) : Subfunctor (P.ι.op ⋙ F) where
  obj T := G.obj (op T.unop.obj)
  map f := G.map (P.ι.op.map f)

lemma mem_restrictSubfunctor_obj (G : Subfunctor F) (T : P.FullSubcategoryᵒᵖ)
    (x : F.obj (op T.unop.obj)) : x ∈ (restrictSubfunctor P G).obj T ↔ x ∈ G.obj (op T.unop.obj) :=
  Iff.rfl

/-- A subfunctor `G ⊆ F` of a presheaf on `Over S` is open (Stacks, Tag 01JI, "representable by
open immersions"): for every `T` and `ξ ∈ F(T)` there is an open `U ⊆ T` such that a morphism
`g : Z ⟶ T` over `S` pulls `ξ` back into `G` if and only if `g` factors through `U`. -/
def IsOpenOverSubfunctor (G : Subfunctor F) : Prop :=
  ∀ ⦃T : Over S⦄ (ξ : F.obj (op T)), ∃ U : T.left.Opens,
    ∀ ⦃Z : Over S⦄ (g : Z ⟶ T), F.map g.op ξ ∈ G.obj (op Z) ↔ g.left ⁻¹ᵁ U = ⊤

variable {P} in
lemma IsOpenOverSubfunctor.restrict {G : Subfunctor F} (hG : IsOpenOverSubfunctor G) :
    IsOpenSubfunctor (restrictSubfunctor P G) := fun _ ξ => by
  obtain ⟨U, hU⟩ := hG ξ
  exact ⟨U, fun _ g => hU g.hom⟩

/-- A representation of a subfunctor on `Over S` restricts to the full subcategory of `P`. -/
def representableByRestrict {G : Subfunctor F} {X : Over S} (e : G.toFunctor.RepresentableBy X)
    (hX : P X) : (restrictSubfunctor P G).toFunctor.RepresentableBy ⟨X, hX⟩ where
  homEquiv := P.fullyFaithfulι.homEquiv.trans e.homEquiv
  homEquiv_comp f g := Subtype.ext (congrArg Subtype.val (e.homEquiv_comp f.hom g.hom))

lemma covers_restrict [IsOpenLocal P] {ι : Type*} {G : ι → Subfunctor F}
    (hG : ∀ i, IsOpenOverSubfunctor (G i))
    (hcov : ∀ ⦃T : Over S⦄ (ξ : F.obj (op T)) (x : T.left), ∃ (i : ι) (Z : Over S) (g : Z ⟶ T),
      x ∈ Set.range g.left ∧ F.map g.op ξ ∈ (G i).obj (op Z))
    ⦃T : P.FullSubcategory⦄ (ξ : (P.ι.op ⋙ F).obj (op T)) (x : T.obj.left) :
    ∃ (i : ι) (Z : P.FullSubcategory) (g : Z ⟶ T), x ∈ Set.range g.hom.left ∧
      (P.ι.op ⋙ F).map g.op ξ ∈ (restrictSubfunctor P (G i)).obj (op Z) := by
  obtain ⟨i, Z, g, ⟨z, hz⟩, hmem⟩ := hcov ξ x
  obtain ⟨U, hU⟩ := hG i ξ
  refine ⟨i, restrictOpens T U, restrictOpensι T U, ?_, (hU _).2 (Scheme.Opens.ι_preimage_self U)⟩
  change x ∈ Set.range U.ι
  rw [Scheme.Opens.range_ι]
  have hzU : z ∈ g.left ⁻¹ᵁ U := by
    rw [(hU g).1 hmem]
    trivial
  rw [← hz]
  exact hzU

/-- The covering condition of `OverSubfunctorCover` follows from Zariski-local surjectivity of
`⨆ i, G i ⊆ F`: for every `ξ ∈ F(T)`, the morphisms pulling `ξ` back into some `G i` form a
covering sieve for `Scheme.zariskiTopology.over S`. -/
lemma covers_of_sieveOfSection_mem {ι : Type*} {G : ι → Subfunctor F}
    (h : ∀ ⦃T : Over S⦄ (ξ : F.obj (op T)),
      (⨆ i, G i).sieveOfSection ξ ∈ Scheme.zariskiTopology.over S T)
    ⦃T : Over S⦄ (ξ : F.obj (op T)) (x : T.left) :
    ∃ (i : ι) (Z : Over S) (g : Z ⟶ T), x ∈ Set.range g.left ∧ F.map g.op ξ ∈ (G i).obj (op Z) := by
  have hmem := h ξ
  rw [GrothendieckTopology.mem_over_iff, Scheme.mem_grothendieckTopology_iff] at hmem
  obtain ⟨𝒱, h𝒱⟩ := hmem
  have hR : (Sieve.overEquiv T ((⨆ i, G i).sieveOfSection ξ)).arrows (𝒱.f (𝒱.idx x)) :=
    h𝒱 _ _ (.mk _)
  rw [Sieve.overEquiv_iff] at hR
  change F.map (Over.homMk (𝒱.f (𝒱.idx x)) : Over.mk (𝒱.f (𝒱.idx x) ≫ T.hom) ⟶ T).op ξ ∈
    (⨆ i, G i).obj (op (Over.mk (𝒱.f (𝒱.idx x) ≫ T.hom))) at hR
  rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hR
  obtain ⟨i, hi⟩ := hR
  exact ⟨i, Over.mk (𝒱.f (𝒱.idx x) ≫ T.hom), Over.homMk (𝒱.f (𝒱.idx x)), 𝒱.covers x, hi⟩

/-- A representation on the full subcategory `⊤` of `Over S` is a representation on `Over S`. -/
def representableByOfTop {Y : (⊤ : ObjectProperty (Over S)).FullSubcategory}
    (e : ((⊤ : ObjectProperty (Over S)).ι.op ⋙ F).RepresentableBy Y) :
    F.RepresentableBy Y.obj where
  homEquiv {T} :=
    ((⊤ : ObjectProperty (Over S)).fullyFaithfulι.homEquiv (X := ⟨T, trivial⟩) (Y := Y)).symm.trans
      e.homEquiv
  homEquiv_comp {T T'} f g :=
    e.homEquiv_comp
      (ObjectProperty.homMk f : (⟨T, trivial⟩ : (⊤ : ObjectProperty (Over S)).FullSubcategory) ⟶
        ⟨T', trivial⟩)
      (ObjectProperty.homMk g)

end Restrict

/-- An open cover of a presheaf `F` on `Over S` by representable subfunctors (the hypotheses of
Stacks, Tag 01JJ, Lemma 26.15.4, besides the sheaf property, relative to `S`; Definition 26.15.3,
Tag 01JI): open subfunctors `sub i` represented by schemes `X i` over `S`, such that every
`ξ ∈ F(T)` lies Zariski-locally on `T` in some `sub i`. -/
structure OverSubfunctorCover (F : (Over S)ᵒᵖ ⥤ Type v) where
  /-- The index type of the cover. -/
  I : Type u
  /-- The subfunctors of the cover. -/
  sub : I → Subfunctor F
  /-- Each subfunctor is open. -/
  isOpen : ∀ i, IsOpenOverSubfunctor (sub i)
  /-- The representing schemes over `S`. -/
  X : I → Over S
  /-- `X i` represents `sub i`. -/
  representableBy : ∀ i, (sub i).toFunctor.RepresentableBy (X i)
  /-- The subfunctors cover `F` Zariski-locally. -/
  covers : ∀ ⦃T : Over S⦄ (ξ : F.obj (op T)) (x : T.left), ∃ (i : I) (Z : Over S) (g : Z ⟶ T),
    x ∈ Set.range g.left ∧ F.map g.op ξ ∈ (sub i).obj (op Z)

namespace OverSubfunctorCover

variable {F : (Over S)ᵒᵖ ⥤ Type v} (𝒰 : OverSubfunctorCover F)

/-- The restriction of `𝒰` to the full subcategory of `P`, when the representing schemes
satisfy `P`. -/
abbrev restrict (P : ObjectProperty (Over S)) [IsOpenLocal P] (hX : ∀ i, P (𝒰.X i)) :
    SubfunctorCover (P.ι.op ⋙ F) where
  I := 𝒰.I
  sub i := restrictSubfunctor P (𝒰.sub i)
  isOpen i := (𝒰.isOpen i).restrict
  X i := ⟨𝒰.X i, hX i⟩
  representableBy i := representableByRestrict P (𝒰.representableBy i) (hX i)
  covers := covers_restrict P 𝒰.isOpen 𝒰.covers

/-- The cover on the full subcategory `⊤` of `Over S`. -/
abbrev toTop : SubfunctorCover ((⊤ : ObjectProperty (Over S)).ι.op ⋙ F) :=
  𝒰.restrict ⊤ fun _ => trivial

/-- The scheme over `S` glued from the representing schemes. -/
abbrev glued : Over S :=
  𝒰.toTop.glued.obj

/-- The chart `X i ⟶ glued`, an open immersion over `S`. -/
abbrev ι (i : 𝒰.I) : 𝒰.X i ⟶ 𝒰.glued :=
  (𝒰.toTop.ιp i).hom

instance (i : 𝒰.I) : IsOpenImmersion (𝒰.ι i).left :=
  𝒰.toTop.isOpenImmersion_ιOver i

lemma ι_jointly_surjective (x : 𝒰.glued.left) : ∃ i, x ∈ Set.range (𝒰.ι i).left :=
  𝒰.toTop.ιp_jointly_surjective x

/-- **Stacks, Tag 01JJ** (Lemma 26.15.4), relative to `S`: a Zariski sheaf on `Over S` covered
by representable open subfunctors is represented by the scheme over `S` glued from the
representing schemes. This is the gluing step of Kleiman, arXiv:math/0504020v1, proof of
Thm 4.8, pp. 28–29. -/
def representableByGlued (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F) :
    F.RepresentableBy 𝒰.glued :=
  representableByOfTop (𝒰.toTop.representableByGlued (isZariskiSheaf_comp_ι hF))

/-- The chart `X i ⟶ glued` corresponds to the universal element of `sub i`. -/
lemma representableByGlued_homEquiv_ι (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F)
    (i : 𝒰.I) :
    (𝒰.representableByGlued hF).homEquiv (𝒰.ι i) = ((𝒰.representableBy i).homEquiv (𝟙 _)).1 :=
  𝒰.toTop.map_ιp_univ (isZariskiSheaf_comp_ι hF) i

/-- A morphism `g : Z ⟶ 𝒰.glued` pulls the universal element back into `sub i` if and only if it
lands in the chart `X i`: the subfunctor `sub i` is the open subscheme `X i` of `𝒰.glued`. -/
lemma representableByGlued_homEquiv_mem_iff
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F) (i : 𝒰.I) {Z : Over S}
    (g : Z ⟶ 𝒰.glued) :
    (𝒰.representableByGlued hF).homEquiv g ∈ (𝒰.sub i).obj (op Z) ↔
      Set.range g.left ⊆ Set.range (𝒰.ι i).left :=
  𝒰.toTop.map_univ_mem_iff (isZariskiSheaf_comp_ι hF) i (Z := ⟨Z, trivial⟩)
    (ObjectProperty.homMk g)

include 𝒰 in
/-- **Stacks, Tag 01JJ** (Lemma 26.15.4), relative to `S`; Kleiman, arXiv:math/0504020v1, proof
of Thm 4.8, pp. 28–29. -/
theorem isRepresentable (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F) :
    F.IsRepresentable :=
  (𝒰.representableByGlued hF).isRepresentable

end OverSubfunctorCover

end AlgebraicGeometry.Scheme.LocalRepresentability
