/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Open subfunctors of presheaves on schemes over a base

This file sets up the hypotheses of the Zariski-local representability criterion for presheaves
on schemes over a base `S` (Stacks, Tag 01JJ, Lemma 26.15.4, which Stacks states for functors on
all schemes; here relative to `S`). The test schemes are the
objects of a full subcategory `P.FullSubcategory` of `Over S`, for a property `P` of schemes over
`S` that passes to open immersions and is local for jointly surjective families of open
immersions (`IsOpenLocal`); examples are `⊤` and "locally Noetherian".

For a presheaf `F` on `P.FullSubcategory` with values in any universe:

- `IsZariskiSheaf F`: `F` satisfies the sheaf condition for every jointly surjective family of
  open immersions into an object of `P.FullSubcategory`;
- `IsOpenSubfunctor G`: for a subfunctor `G ⊆ F`, every `ξ ∈ F(T)` has an open `U ⊆ T` such that
  `g : Z ⟶ T` pulls `ξ` back into `G` if and only if `g` factors through `U` (Stacks, Tag 01JI,
  Definition 26.15.3, "representable by open immersions");
- `SubfunctorCover F`: open subfunctors `sub i ⊆ F` with representing objects `X i`, covering `F`
  Zariski-locally (Definition 26.15.3 asks for an open covering `T = ⋃ U_i` with
  `ξ|_{U_i} ∈ sub i`; for open subfunctors this is the pointwise condition `covers`).

`isZariskiSheaf_comp_ι` shows that the restriction of a sheaf for `Scheme.zariskiTopology.over S`
satisfies `IsZariskiSheaf`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}}

/-! ### Open immersions over `S` -/

/-- The open subscheme `U` of `T`, as a scheme over `S`. -/
abbrev overOpens (T : Over S) (U : T.left.Opens) : Over S :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of the open subscheme `U` of `T`, as a morphism over `S`. -/
abbrev overOpensι (T : Over S) (U : T.left.Opens) : overOpens T U ⟶ T :=
  Over.homMk U.ι

instance (T : Over S) (U : T.left.Opens) : IsOpenImmersion (overOpensι T U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

lemma range_subset_range_ι_of_preimage_eq_top {Z T : Scheme.{u}} (g : Z ⟶ T) (U : T.Opens)
    (h : g ⁻¹ᵁ U = ⊤) : Set.range g ⊆ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have : x ∈ g ⁻¹ᵁ U := by rw [h]; trivial
  exact this

lemma range_subset_range_of_preimage_opensRange_eq_top {Z T Y : Scheme.{u}} (g : Z ⟶ T)
    (j : Y ⟶ T) [IsOpenImmersion j] (h : g ⁻¹ᵁ j.opensRange = ⊤) :
    Set.range g ⊆ Set.range j := by
  rintro _ ⟨x, rfl⟩
  have : x ∈ g ⁻¹ᵁ j.opensRange := by rw [h]; trivial
  exact this

/-- The lift of a morphism over `S` through an open immersion over `S` containing its range. -/
def overLift {W Z T : Over S} (j : W ⟶ T) [IsOpenImmersion j.left] (g : Z ⟶ T)
    (h : Set.range g.left ⊆ Set.range j.left) : Z ⟶ W :=
  Over.homMk (IsOpenImmersion.lift j.left g.left h) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w g])

@[reassoc (attr := simp)]
lemma overLift_comp {W Z T : Over S} (j : W ⟶ T) [IsOpenImmersion j.left] (g : Z ⟶ T)
    (h : Set.range g.left ⊆ Set.range j.left) : overLift j g h ≫ j = g := by
  ext
  simp [overLift, IsOpenImmersion.lift_fac]

/-- A morphism over `S` whose preimage of `U` is everything factors through `U`. -/
abbrev overOpensLift {Z T : Over S} (g : Z ⟶ T) (U : T.left.Opens) (h : g.left ⁻¹ᵁ U = ⊤) :
    Z ⟶ overOpens T U :=
  overLift (overOpensι T U) g (range_subset_range_ι_of_preimage_eq_top g.left U h)

@[reassoc (attr := simp)]
lemma overOpensLift_ι {Z T : Over S} (g : Z ⟶ T) (U : T.left.Opens) (h : g.left ⁻¹ᵁ U = ⊤) :
    overOpensLift g U h ≫ overOpensι T U = g :=
  overLift_comp _ _ _

lemma isOpenImmersion_pullback_fst_left {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : IsOpenImmersion g.left) : IsOpenImmersion (pullback.fst f g).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((IsPullback.of_hasPullback f g).map (Over.forget S)).flip hg

lemma isOpenImmersion_pullback_snd_left {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : IsOpenImmersion f.left) : IsOpenImmersion (pullback.snd f g).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((IsPullback.of_hasPullback f g).map (Over.forget S)) hf

/-! ### Test schemes -/

/-- A property `P` of schemes over `S` that passes to open immersions and holds for a scheme
covered by open immersions from schemes satisfying `P`. Examples: `⊤`, and locally Noetherian
schemes over `S`. -/
class IsOpenLocal (P : ObjectProperty (Over S)) : Prop where
  of_isOpenImmersion {W T : Over S} (g : W ⟶ T) (hg : IsOpenImmersion g.left) : P T → P W
  of_jointlySurjective {T : Over S} {ι : Type u} (W : ι → Over S) (g : ∀ i, W i ⟶ T)
    (hg : ∀ i, IsOpenImmersion (g i).left) (hcov : ∀ x : T.left, ∃ i, x ∈ Set.range (g i).left)
    (hW : ∀ i, P (W i)) : P T

instance : IsOpenLocal (⊤ : ObjectProperty (Over S)) where
  of_isOpenImmersion _ _ _ := trivial
  of_jointlySurjective _ _ _ _ _ := trivial

variable {P : ObjectProperty (Over S)}

/-- The Zariski sheaf condition for a presheaf on `P.FullSubcategory`: the sheaf condition holds
for every jointly surjective family of open immersions into an object, indexed by a type in
`Type u`. -/
def IsZariskiSheaf (F : P.FullSubcategoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃T : P.FullSubcategory⦄ ⦃ι : Type u⦄ (W : ι → P.FullSubcategory) (g : ∀ i, W i ⟶ T),
    (∀ i, IsOpenImmersion (g i).hom.left) → (∀ x : T.obj.left, ∃ i, x ∈ Set.range (g i).hom.left) →
      (Presieve.ofArrows W g).IsSheafFor F

/-- A subfunctor `G` of `F` is open (Stacks, Tag 01JI, "representable by open immersions"): for
every `T` and `ξ ∈ F(T)` there is an open `U ⊆ T` such that a morphism `g : Z ⟶ T` pulls `ξ`
back into `G` if and only if `g` factors through `U`. -/
def IsOpenSubfunctor {F : P.FullSubcategoryᵒᵖ ⥤ Type v} (G : Subfunctor F) : Prop :=
  ∀ ⦃T : P.FullSubcategory⦄ (ξ : F.obj (op T)), ∃ U : T.obj.left.Opens,
    ∀ ⦃Z : P.FullSubcategory⦄ (g : Z ⟶ T), F.map g.op ξ ∈ G.obj (op Z) ↔ g.hom.left ⁻¹ᵁ U = ⊤

/-- An open cover of a presheaf `F` on `P.FullSubcategory` by representable subfunctors (the
hypotheses of Stacks, Tag 01JJ, Lemma 26.15.4, besides the sheaf property): open subfunctors
`sub i` represented by objects `X i`, such that every `ξ ∈ F(T)` lies Zariski-locally on `T` in
some `sub i`. -/
structure SubfunctorCover (F : P.FullSubcategoryᵒᵖ ⥤ Type v) where
  /-- The index type of the cover. -/
  I : Type u
  /-- The subfunctors of the cover. -/
  sub : I → Subfunctor F
  /-- Each subfunctor is open. -/
  isOpen : ∀ i, IsOpenSubfunctor (sub i)
  /-- The representing objects. -/
  X : I → P.FullSubcategory
  /-- `X i` represents `sub i`. -/
  representableBy : ∀ i, (sub i).toFunctor.RepresentableBy (X i)
  /-- The subfunctors cover `F` Zariski-locally. -/
  covers : ∀ ⦃T : P.FullSubcategory⦄ (ξ : F.obj (op T)) (x : T.obj.left),
    ∃ (i : I) (Z : P.FullSubcategory) (g : Z ⟶ T), x ∈ Set.range g.hom.left ∧
      F.map g.op ξ ∈ (sub i).obj (op Z)

lemma map_comp_op_apply {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type v) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : F.obj (op Z)) : F.map (f ≫ g).op x = F.map f.op (F.map g.op x) := by
  rw [op_comp, Functor.map_comp_apply]

namespace SubfunctorCover

variable {F : P.FullSubcategoryᵒᵖ ⥤ Type v} (𝒰 : SubfunctorCover F)

/-- The universal element of the chart `X i`. -/
def ξ (i : 𝒰.I) : F.obj (op (𝒰.X i)) :=
  ((𝒰.representableBy i).homEquiv (𝟙 _)).1

lemma homEquiv_coe (i : 𝒰.I) {Z : P.FullSubcategory} (g : Z ⟶ 𝒰.X i) :
    ((𝒰.representableBy i).homEquiv g).1 = F.map g.op (𝒰.ξ i) := by
  have h := (𝒰.representableBy i).homEquiv_comp g (𝟙 _)
  rw [Category.comp_id] at h
  rw [h]
  rfl

lemma ξ_mem (i : 𝒰.I) : 𝒰.ξ i ∈ (𝒰.sub i).obj (op (𝒰.X i)) :=
  ((𝒰.representableBy i).homEquiv (𝟙 _)).2

lemma map_ξ_mem (i : 𝒰.I) {Z : P.FullSubcategory} (g : Z ⟶ 𝒰.X i) :
    F.map g.op (𝒰.ξ i) ∈ (𝒰.sub i).obj (op Z) := by
  rw [← 𝒰.homEquiv_coe]
  exact ((𝒰.representableBy i).homEquiv g).2

lemma map_ξ_injective (i : 𝒰.I) {Z : P.FullSubcategory} {g g' : Z ⟶ 𝒰.X i}
    (h : F.map g.op (𝒰.ξ i) = F.map g'.op (𝒰.ξ i)) : g = g' :=
  (𝒰.representableBy i).homEquiv.injective (Subtype.ext (by rw [homEquiv_coe, homEquiv_coe, h]))

/-- The open of `X i` over which the universal element of `X i` lies in `sub j`. -/
def V (i j : 𝒰.I) : (𝒰.X i).obj.left.Opens :=
  (𝒰.isOpen j (𝒰.ξ i)).choose

lemma map_ξ_mem_iff (i j : 𝒰.I) {Z : P.FullSubcategory} (g : Z ⟶ 𝒰.X i) :
    F.map g.op (𝒰.ξ i) ∈ (𝒰.sub j).obj (op Z) ↔ g.hom.left ⁻¹ᵁ 𝒰.V i j = ⊤ :=
  (𝒰.isOpen j (𝒰.ξ i)).choose_spec g

lemma V_self (i : 𝒰.I) : 𝒰.V i i = ⊤ := by
  have h := (𝒰.map_ξ_mem_iff i i (𝟙 _)).1 (by simpa using 𝒰.ξ_mem i)
  simpa [Scheme.Hom.id_preimage] using h

end SubfunctorCover

/-! ### The sheaf condition -/

/-- For a sheaf on `Over S` for the Zariski topology, the sheaf condition holds for every jointly
surjective family of open immersions over `S`. -/
lemma isSheafFor_ofArrows_of_isSheaf {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F) {T : Over S} {ι : Type u}
    (W : ι → Over S) (g : ∀ i, W i ⟶ T) (hg : ∀ i, IsOpenImmersion (g i).left)
    (hcov : ∀ x : T.left, ∃ i, x ∈ Set.range (g i).left) :
    (Presieve.ofArrows W g).IsSheafFor F := by
  let 𝒱 : T.left.OpenCover :=
    { I₀ := ι
      X i := (W i).left
      f i := (g i).left
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨hcov, hg⟩ }
  rw [Presieve.isSheafFor_iff_generate]
  apply hF
  change Sieve.ofArrows W g ∈ Scheme.zariskiTopology.over S T
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact 𝒱.mem_grothendieckTopology

/-- The restriction to `P.FullSubcategory` of a Zariski sheaf on `Over S` satisfies
`IsZariskiSheaf`. -/
lemma isZariskiSheaf_comp_ι [IsOpenLocal P] {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F) : IsZariskiSheaf (P.ι.op ⋙ F) := by
  intro T ι W g hg hcov
  have h := isSheafFor_ofArrows_of_isSheaf hF (fun i => (W i).obj) (fun i => (g i).hom) hg hcov
  rw [Presieve.isSheafFor_arrows_iff] at h ⊢
  intro x hx
  refine h x ?_
  intro i j Z gi gj hij
  let c : Z ⟶ pullback (g i).hom (g j).hom := pullback.lift gi gj hij
  have hQ : P (pullback (g i).hom (g j).hom) :=
    IsOpenLocal.of_isOpenImmersion (pullback.fst _ _)
      (isOpenImmersion_pullback_fst_left _ _ (hg j)) (W i).property
  let Q : P.FullSubcategory := ⟨_, hQ⟩
  have hc := hx i j Q (ObjectProperty.homMk (pullback.fst _ _))
    (ObjectProperty.homMk (pullback.snd _ _)) (ObjectProperty.hom_ext _ pullback.condition)
  have e₁ : gi = c ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have e₂ : gj = c ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
  change F.map gi.op (x i) = F.map gj.op (x j)
  change F.map (pullback.fst (g i).hom (g j).hom).op (x i) =
    F.map (pullback.snd (g i).hom (g j).hom).op (x j) at hc
  rw [e₁, e₂, map_comp_op_apply, map_comp_op_apply, hc]

end AlgebraicGeometry.Scheme.LocalRepresentability
