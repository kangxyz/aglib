/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Effective descent along composites of families, for prestacks

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a prestack for a Grothendieck topology `J` on `C`.

* `LocallyDiscreteOpToCat.pullHom_comp`, `LocallyDiscreteOpToCat.pullHom_id'`: `pullHom` of a
  composite and of an identity morphism.
* `eq_of_pullHom_eq`, `exists_pullHom_eq`: morphisms `b₁^* M₁ ⟶ b₂^* M₂` over `W` are determined
  by, and glue from, compatible families of their `pullHom`s along the arrows of a covering sieve
  of `W` (the full faithfulness `fullyFaithfulToDescentData` for that sieve).
* `isEquivalence_toDescentData_comp`: let `f i : X i ⟶ S` be a `J`-covering family and
  `g i j : Y i j ⟶ X i` be `J`-covering families such that `F.toDescentData f` and every
  `F.toDescentData (g i)` are equivalences. Then `F.toDescentData` of the composite family
  `g i j ≫ f i` is an equivalence.

The construction is in the namespace `Pseudofunctor.CompDescent`. A descent datum `E` along the
composite family restricts to descent data along the families `g i`
(`DescentData.restrictComp`); these are effective (`CompDescent.descendedObj`,
`CompDescent.objIso`). For a test object `W` with `a₁ : W ⟶ X i₁` and `a₂ : W ⟶ X i₂` over `S`,
the descent morphism between the pullbacks of `descendedObj i₁` and `descendedObj i₂`
(`CompDescent.gluedHom`) is glued from the descent morphisms of `E` along the covering sieve
`CompDescent.factorSieve` of the arrows to `W` along which `a₁` and `a₂` factor through the
families `g i₁` and `g i₂`. This gives a descent datum along `f`
(`CompDescent.gluedDescentData`) whose pullback to the composite family is isomorphic to `E`
(`CompDescent.pullIso`).

The presieve form, `Pseudofunctor.IsStackFor.bind`, is in [Composition](Composition.lean).

(`citation needed`: a locator for the composition statement for stacks; Giraud, *Cohomologie non
abélienne*, Chapter II, is the expected source but was not inspected. For sheaves of types the
statement is [Elephant, Lemma C2.1.7(i)], as cited by Mathlib's `Presieve.isSheafFor_bind`.)
-/

@[expose] public section

noncomputable section

universe t t' v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

/-- `pullHom` of a composite. -/
@[reassoc]
lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

/-- `pullHom` of an identity morphism. (Mathlib's `pullHom_id` is `pullHom` along an
identity.) -/
@[simp]
lemma pullHom_id' ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

end LocallyDiscreteOpToCat

variable {J : GrothendieckTopology C} [F.IsPrestack J]

omit [F.IsPrestack J] in
/-- The morphisms of the descent datum of an object. -/
lemma toDescentData_obj_hom_eq {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
        (by rw [← hf₁]; rfl)).inv.toNatTrans.app M ≫
        (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by rw [← hf₂]; rfl)).hom.toNatTrans.app
          M :=
  rfl

include J in
/-- Morphisms are determined by their `pullHom` along the arrows of a covering sieve. -/
lemma eq_of_pullHom_eq {W : C} {R : Sieve W} (hR : R ∈ J W) ⦃X₁ X₂ : C⦄
    ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ (b₁ : W ⟶ X₁) (b₂ : W ⟶ X₂)
    {x y : (F.map b₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map b₂.op.toLoc).toFunctor.obj M₂}
    (h : ∀ ⦃Z : C⦄ (t : Z ⟶ W), R t →
      pullHom x t (t ≫ b₁) (t ≫ b₂) = pullHom y t (t ≫ b₁) (t ≫ b₂)) : x = y := by
  have hff := F.fullyFaithfulToDescentData (J := J) (fun (a : R.arrows.category) ↦ a.obj.hom)
    (by rwa [Sieve.ofArrows_category', Sieve.generate_sieve])
  apply hff.map_injective
  ext a
  change (F.map a.obj.hom.op.toLoc).toFunctor.map x = (F.map a.obj.hom.op.toLoc).toFunctor.map y
  rw [map_eq_pullHom x a.obj.hom _ _ rfl rfl, map_eq_pullHom y a.obj.hom _ _ rfl rfl,
    h _ a.property]

-- Mathlib's `mapComp'` coherence lemmas are stated with objects that agree with those of the
-- goal only up to unfolding (`Cat` objects as objects of the underlying category).
set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by composition isomorphisms. -/
lemma pullHom_conj ⦃W X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    (b₁ : W ⟶ X₁) (b₂ : W ⟶ X₂) ⦃Z : C⦄ (t : Z ⟶ W)
    (ψ : (F.map (t ≫ b₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (t ≫ b₂).op.toLoc).toFunctor.obj M₂) ⦃Z' : C⦄ (s : Z' ⟶ Z) :
    pullHom (M₁ := (F.map b₁.op.toLoc).toFunctor.obj M₁)
      (M₂ := (F.map b₂.op.toLoc).toFunctor.obj M₂)
      ((F.mapComp' b₁.op.toLoc t.op.toLoc (t ≫ b₁).op.toLoc rfl).inv.toNatTrans.app M₁ ≫ ψ ≫
        (F.mapComp' b₂.op.toLoc t.op.toLoc (t ≫ b₂).op.toLoc rfl).hom.toNatTrans.app M₂)
      s (s ≫ t) (s ≫ t) =
    (F.mapComp' b₁.op.toLoc (s ≫ t).op.toLoc ((s ≫ t) ≫ b₁).op.toLoc rfl).inv.toNatTrans.app M₁ ≫
      pullHom ψ s ((s ≫ t) ≫ b₁) ((s ≫ t) ≫ b₂) (by rw [Category.assoc])
        (by rw [Category.assoc]) ≫
      (F.mapComp' b₂.op.toLoc (s ≫ t).op.toLoc ((s ≫ t) ≫ b₂).op.toLoc rfl).hom.toNatTrans.app
        M₂ := by
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl rfl rfl,
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _
      (b₂.op.toLoc ≫ t.op.toLoc ≫ s.op.toLoc) rfl rfl (Category.assoc _ _ _)]

-- The descent morphisms of `toDescentData` are compared with `pullHom`s whose objects agree with
-- theirs only up to unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Compatible `pullHom`-type morphisms over the arrows of a covering sieve glue. -/
lemma exists_pullHom_eq {W : C} {R : Sieve W} (hR : R ∈ J W) ⦃X₁ X₂ : C⦄
    ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ (b₁ : W ⟶ X₁) (b₂ : W ⟶ X₂)
    (Φ : ∀ ⦃Z : C⦄ (t : Z ⟶ W), R t →
      ((F.map (t ≫ b₁).op.toLoc).toFunctor.obj M₁ ⟶ (F.map (t ≫ b₂).op.toLoc).toFunctor.obj M₂))
    (hΦ : ∀ ⦃Z Z' : C⦄ (t : Z ⟶ W) (ht : R t) (s : Z' ⟶ Z),
      pullHom (Φ t ht) s ((s ≫ t) ≫ b₁) ((s ≫ t) ≫ b₂) (by rw [Category.assoc])
        (by rw [Category.assoc]) = Φ (s ≫ t) (R.downward_closed ht s)) :
    ∃ x : (F.map b₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map b₂.op.toLoc).toFunctor.obj M₂,
      ∀ ⦃Z : C⦄ (t : Z ⟶ W) (ht : R t), pullHom x t (t ≫ b₁) (t ≫ b₂) = Φ t ht := by
  have hff := F.fullyFaithfulToDescentData (J := J) (fun (a : R.arrows.category) ↦ a.obj.hom)
    (by rwa [Sieve.ofArrows_category', Sieve.generate_sieve])
  let κ : ∀ ⦃Z : C⦄ (t : Z ⟶ W), R t →
      ((F.map t.op.toLoc).toFunctor.obj ((F.map b₁.op.toLoc).toFunctor.obj M₁) ⟶
        (F.map t.op.toLoc).toFunctor.obj ((F.map b₂.op.toLoc).toFunctor.obj M₂)) :=
    fun Z t ht ↦
      (F.mapComp' b₁.op.toLoc t.op.toLoc (t ≫ b₁).op.toLoc rfl).inv.toNatTrans.app M₁ ≫
        Φ t ht ≫ (F.mapComp' b₂.op.toLoc t.op.toLoc (t ≫ b₂).op.toLoc rfl).hom.toNatTrans.app M₂
  have hκ : ∀ ⦃Z Z' : C⦄ (t : Z ⟶ W) (ht : R t) (s : Z' ⟶ Z),
      pullHom (κ t ht) s (s ≫ t) (s ≫ t) = κ (s ≫ t) (R.downward_closed ht s) := by
    intro Z Z' t ht s
    simp only [κ]
    rw [pullHom_conj, hΦ]
  let φ : (F.toDescentData (fun (a : R.arrows.category) ↦ a.obj.hom)).obj
      ((F.map b₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.toDescentData (fun (a : R.arrows.category) ↦ a.obj.hom)).obj
      ((F.map b₂.op.toLoc).toFunctor.obj M₂) :=
    { hom a := κ a.obj.hom a.property
      comm Y q a₁ a₂ s₁ s₂ hs₁ hs₂ := by
        have e₁ := map_eq_pullHom (κ a₁.obj.hom a₁.property) s₁ q q hs₁ hs₁
        have e₂ := map_eq_pullHom (κ a₂.obj.hom a₂.property) s₂ q q hs₂ hs₂
        have k₁ : pullHom (κ a₁.obj.hom a₁.property) s₁ q q hs₁ hs₁ =
            κ q (by rw [← hs₁]; exact R.downward_closed a₁.property s₁) := by
          subst hs₁
          exact hκ _ _ s₁
        have k₂ : pullHom (κ a₂.obj.hom a₂.property) s₂ q q hs₂ hs₂ =
            κ q (by rw [← hs₂]; exact R.downward_closed a₂.property s₂) := by
          subst hs₂
          exact hκ _ _ s₂
        rw [e₁, e₂, k₁, k₂, toDescentData_obj_hom_eq, toDescentData_obj_hom_eq]
        simp }
  refine ⟨hff.preimage φ, fun Z t ht ↦ ?_⟩
  have := congrArg (fun ψ ↦ ψ.hom ⟨Over.mk t, ht⟩) (hff.map_preimage φ)
  change (F.map t.op.toLoc).toFunctor.map (hff.preimage φ) = κ t ht at this
  rw [map_eq_pullHom (hff.preimage φ) t (t ≫ b₁) (t ≫ b₂) rfl rfl] at this
  simp only [κ] at this
  have := congrArg (fun z ↦
    (F.mapComp' b₁.op.toLoc t.op.toLoc (t ≫ b₁).op.toLoc rfl).hom.toNatTrans.app M₁ ≫ z ≫
      (F.mapComp' b₂.op.toLoc t.op.toLoc (t ≫ b₂).op.toLoc rfl).inv.toNatTrans.app M₂) this
  simpa using this

section Comp

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
  {κ : ι → Type t'} {Y : ∀ i, κ i → C} (g : ∀ i j, Y i j ⟶ X i)

omit [F.IsPrestack J] in
/-- The restriction of a descent datum for the composite family to the family `g i`. -/
def DescentData.restrictComp (E : F.DescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1))
    (i : ι) : F.DescentData (g i) where
  obj j := E.obj ⟨i, j⟩
  hom Z q j₁ j₂ c₁ c₂ hc₁ hc₂ := E.hom (q ≫ f i) (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) c₁ c₂
    (by rw [← hc₁, Category.assoc]) (by rw [← hc₂, Category.assoc])
  pullHom_hom Z' Z s q q' hq j₁ j₂ c₁ c₂ hc₁ hc₂ sc₁ sc₂ hsc₁ hsc₂ :=
    E.pullHom_hom s (q ≫ f i) (q' ≫ f i) (by rw [← hq, Category.assoc])
      (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) c₁ c₂
      (by rw [← hc₁, Category.assoc]) (by rw [← hc₂, Category.assoc]) sc₁ sc₂ hsc₁ hsc₂
  hom_self Z q j c hc := E.hom_self (q ≫ f i) (i := ⟨i, j⟩) c (by rw [← hc, Category.assoc])
  hom_comp Z q j₁ j₂ j₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ :=
    E.hom_comp (q ≫ f i) (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) (i₃ := ⟨i, j₃⟩) c₁ c₂ c₃
      (by rw [← hc₁, Category.assoc]) (by rw [← hc₂, Category.assoc])
      (by rw [← hc₃, Category.assoc])

omit [F.IsPrestack J] in
lemma DescentData.restrictComp_hom
    (E : F.DescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1)) (i : ι) ⦃Z : C⦄
    (q : Z ⟶ X i) ⦃j₁ j₂ : κ i⦄ (c₁ : Z ⟶ Y i j₁) (c₂ : Z ⟶ Y i j₂) (hc₁ : c₁ ≫ g i j₁ = q)
    (hc₂ : c₂ ≫ g i j₂ = q) :
    (E.restrictComp f g i).hom q c₁ c₂ hc₁ hc₂ =
      E.hom (q ≫ f i) (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) c₁ c₂
        (by rw [← hc₁, Category.assoc]) (by rw [← hc₂, Category.assoc]) :=
  rfl

omit [F.IsPrestack J] in
/-- Descent morphisms over equal base morphisms agree. -/
lemma DescentData.hom_congr_base {ι' : Type*} {X' : ι' → C} {f' : ∀ i, X' i ⟶ S}
    (D : F.DescentData f') ⦃Z : C⦄ {q q' : Z ⟶ S} (hq : q = q') ⦃i₁ i₂ : ι'⦄
    (f₁ : Z ⟶ X' i₁) (f₂ : Z ⟶ X' i₂) (hf₁ : f₁ ≫ f' i₁ = q) (hf₂ : f₂ ≫ f' i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom q' f₁ f₂ (hf₁.trans hq) (hf₂.trans hq) := by
  subst hq
  rfl

variable [∀ i, (F.toDescentData (g i)).IsEquivalence]

namespace CompDescent

variable (E : F.DescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1))

omit [F.IsPrestack J] in
/-- The object over `X i` descended from `E` along `g i`. -/
def descendedObj (i : ι) : F.obj (.mk (op (X i))) :=
  (F.toDescentData (g i)).objPreimage (E.restrictComp f g i)

omit [F.IsPrestack J] in
/-- The descent datum of `descendedObj` is the restriction of `E`. -/
def objIso (i : ι) : (F.toDescentData (g i)).obj (descendedObj f g E i) ≅ E.restrictComp f g i :=
  (F.toDescentData (g i)).objObjPreimageIso _

omit [F.IsPrestack J] in
/-- The component of `objIso` over `Y i j`, with its source and target stated explicitly (the
source and target of `(objIso f g E i).hom.hom j` agree with them only after unfolding
`toDescentData` and `restrictComp`). -/
def objIsoHom (i : ι) (j : κ i) :
    (F.map (g i j).op.toLoc).toFunctor.obj (descendedObj f g E i) ⟶ E.obj ⟨i, j⟩ :=
  (objIso f g E i).hom.hom j

omit [F.IsPrestack J] in
/-- The inverse component of `objIso` over `Y i j`, with explicit source and target. -/
def objIsoInv (i : ι) (j : κ i) :
    E.obj ⟨i, j⟩ ⟶ (F.map (g i j).op.toLoc).toFunctor.obj (descendedObj f g E i) :=
  (objIso f g E i).inv.hom j

omit [F.IsPrestack J] in
@[reassoc (attr := simp)]
lemma objIsoHom_inv (i : ι) (j : κ i) :
    objIsoHom f g E i j ≫ objIsoInv f g E i j = 𝟙 _ := by
  have h := congrArg (fun φ ↦ DescentData.Hom.hom φ j) (objIso f g E i).hom_inv_id
  exact h

omit [F.IsPrestack J] in
@[reassoc (attr := simp)]
lemma objIsoInv_hom (i : ι) (j : κ i) :
    objIsoInv f g E i j ≫ objIsoHom f g E i j = 𝟙 _ := by
  have h := congrArg (fun φ ↦ DescentData.Hom.hom φ j) (objIso f g E i).inv_hom_id
  exact h

omit [F.IsPrestack J] in
@[reassoc (attr := simp)]
lemma map_objIsoHom_inv (i : ι) (j : κ i) ⦃Z : C⦄ (c : Z ⟶ Y i j) :
    (F.map c.op.toLoc).toFunctor.map (objIsoHom f g E i j) ≫
      (F.map c.op.toLoc).toFunctor.map (objIsoInv f g E i j) = 𝟙 _ := by
  rw [← Functor.map_comp, objIsoHom_inv, Functor.map_id]

omit [F.IsPrestack J] in
@[reassoc (attr := simp)]
lemma map_objIsoInv_hom (i : ι) (j : κ i) ⦃Z : C⦄ (c : Z ⟶ Y i j) :
    (F.map c.op.toLoc).toFunctor.map (objIsoInv f g E i j) ≫
      (F.map c.op.toLoc).toFunctor.map (objIsoHom f g E i j) = 𝟙 _ := by
  rw [← Functor.map_comp, objIsoInv_hom, Functor.map_id]

omit [F.IsPrestack J] in
/-- `objIsoHom` is a morphism of descent data: its compatibility with the descent morphisms of
`toDescentData` and of `E`. -/
lemma objIsoHom_comm (i : ι) ⦃Z : C⦄ (b : Z ⟶ X i) (j j' : κ i) (c : Z ⟶ Y i j)
    (c' : Z ⟶ Y i j') (hc : c ≫ g i j = b) (hc' : c' ≫ g i j' = b) :
    (F.map c.op.toLoc).toFunctor.map (objIsoHom f g E i j) ≫
        E.hom (b ≫ f i) (i₁ := ⟨i, j⟩) (i₂ := ⟨i, j'⟩) c c' (by rw [← hc, Category.assoc])
          (by rw [← hc', Category.assoc]) =
      (F.mapComp' (g i j).op.toLoc c.op.toLoc b.op.toLoc (by rw [← hc]; rfl)).inv.toNatTrans.app
          (descendedObj f g E i) ≫
        (F.mapComp' (g i j').op.toLoc c'.op.toLoc b.op.toLoc
          (by rw [← hc']; rfl)).hom.toNatTrans.app (descendedObj f g E i) ≫
        (F.map c'.op.toLoc).toFunctor.map (objIsoHom f g E i j') :=
  ((objIso f g E i).hom.comm b c c' hc hc').trans (Category.assoc _ _ _)

omit [F.IsPrestack J] in
/-- The comparison of `descendedObj` with `E` over `c : Z ⟶ Y i j`, `c ≫ g i j = b`. -/
@[simps]
def comparisonIso (i : ι) ⦃Z : C⦄ (b : Z ⟶ X i) (j : κ i) (c : Z ⟶ Y i j) (hc : c ≫ g i j = b) :
    (F.map b.op.toLoc).toFunctor.obj (descendedObj f g E i) ≅
      (F.map c.op.toLoc).toFunctor.obj (E.obj ⟨i, j⟩) where
  hom := (F.mapComp' (g i j).op.toLoc c.op.toLoc b.op.toLoc
      (by rw [← hc]; rfl)).hom.toNatTrans.app _ ≫
    (F.map c.op.toLoc).toFunctor.map (objIsoHom f g E i j)
  inv := (F.map c.op.toLoc).toFunctor.map (objIsoInv f g E i j) ≫
    (F.mapComp' (g i j).op.toLoc c.op.toLoc b.op.toLoc (by rw [← hc]; rfl)).inv.toNatTrans.app _
  hom_inv_id := by
    rw [Category.assoc, map_objIsoHom_inv_assoc, Cat.Hom.hom_inv_id_toNatTrans_app]
  inv_hom_id := by
    rw [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc, map_objIsoInv_hom]

omit [F.IsPrestack J] in
lemma comparisonIso_hom_comp (i : ι) ⦃Z : C⦄ (b : Z ⟶ X i) (j j' : κ i) (c : Z ⟶ Y i j)
    (c' : Z ⟶ Y i j') (hc : c ≫ g i j = b) (hc' : c' ≫ g i j' = b) (q : Z ⟶ S)
    (hq : b ≫ f i = q) :
    (comparisonIso f g E i b j c hc).hom ≫ E.hom q (i₁ := ⟨i, j⟩) (i₂ := ⟨i, j'⟩) c c'
      (by rw [← hq, ← hc, Category.assoc]) (by rw [← hq, ← hc', Category.assoc]) =
      (comparisonIso f g E i b j' c' hc').hom := by
  subst hq
  rw [comparisonIso_hom, comparisonIso_hom, Category.assoc,
    objIsoHom_comm f g E i b j j' c c' hc hc',
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

omit [F.IsPrestack J] in
lemma comparisonIso_inv_eq (i : ι) ⦃Z : C⦄ (b : Z ⟶ X i) (j j' : κ i) (c : Z ⟶ Y i j)
    (c' : Z ⟶ Y i j') (hc : c ≫ g i j = b) (hc' : c' ≫ g i j' = b) (q : Z ⟶ S)
    (hq : b ≫ f i = q) :
    (comparisonIso f g E i b j' c' hc').inv =
      E.hom q (i₁ := ⟨i, j'⟩) (i₂ := ⟨i, j⟩) c' c (by rw [← hq, ← hc', Category.assoc])
        (by rw [← hq, ← hc, Category.assoc]) ≫ (comparisonIso f g E i b j c hc).inv := by
  subst hq
  rw [← cancel_epi (comparisonIso f g E i b j' c' hc').hom, Iso.hom_inv_id,
    ← comparisonIso_hom_comp f g E i b j j' c c' hc hc' _ rfl]
  simp only [Category.assoc, DescentData.hom_comp_assoc]
  rw [E.hom_self (b ≫ f i) (i := ⟨i, j⟩) c (by rw [← hc, Category.assoc]), Category.id_comp,
    Iso.hom_inv_id]

omit [F.IsPrestack J] in
/-- The descended morphism over `Z`, before gluing. -/
def localHom ⦃Z : C⦄ ⦃i₁ i₂ : ι⦄ (b₁ : Z ⟶ X i₁) (b₂ : Z ⟶ X i₂) (hb : b₁ ≫ f i₁ = b₂ ≫ f i₂)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = b₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = b₂) :
    (F.map b₁.op.toLoc).toFunctor.obj (descendedObj f g E i₁) ⟶
      (F.map b₂.op.toLoc).toFunctor.obj (descendedObj f g E i₂) :=
  (comparisonIso f g E i₁ b₁ j₁ c₁ hc₁).hom ≫
    E.hom (b₁ ≫ f i₁) (i₁ := ⟨i₁, j₁⟩) (i₂ := ⟨i₂, j₂⟩) c₁ c₂ (by rw [← hc₁, Category.assoc])
      (by rw [hb, ← hc₂, Category.assoc]) ≫
      (comparisonIso f g E i₂ b₂ j₂ c₂ hc₂).inv

omit [F.IsPrestack J] in
lemma localHom_eq ⦃Z : C⦄ ⦃i₁ i₂ : ι⦄ (b₁ : Z ⟶ X i₁) (b₂ : Z ⟶ X i₂)
    (hb : b₁ ≫ f i₁ = b₂ ≫ f i₂)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = b₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = b₂)
    (j₁' : κ i₁) (c₁' : Z ⟶ Y i₁ j₁') (hc₁' : c₁' ≫ g i₁ j₁' = b₁)
    (j₂' : κ i₂) (c₂' : Z ⟶ Y i₂ j₂') (hc₂' : c₂' ≫ g i₂ j₂' = b₂) :
    localHom f g E b₁ b₂ hb j₁ c₁ hc₁ j₂ c₂ hc₂ =
      localHom f g E b₁ b₂ hb j₁' c₁' hc₁' j₂' c₂' hc₂' := by
  simp only [localHom]
  rw [← comparisonIso_hom_comp f g E i₁ b₁ j₁ j₁' c₁ c₁' hc₁ hc₁' _ rfl,
    comparisonIso_inv_eq f g E i₂ b₂ j₂ j₂' c₂ c₂' hc₂ hc₂' (b₁ ≫ f i₁) hb.symm]
  simp only [Category.assoc, DescentData.hom_comp_assoc]

omit [F.IsPrestack J] in
-- The `pullHom` and `mapComp'` coherence lemmas of Mathlib are stated with objects that agree with
-- ours only up to unfolding; this declaration needs the relaxed transparency of Mathlib's own
-- proofs of these lemmas.
set_option backward.isDefEq.respectTransparency false in
lemma pullHom_comparisonIso_hom (i : ι) ⦃Z : C⦄ (b : Z ⟶ X i) (j : κ i) (c : Z ⟶ Y i j)
    (hc : c ≫ g i j = b) ⦃Z' : C⦄ (s : Z' ⟶ Z) :
    pullHom (comparisonIso f g E i b j c hc).hom s (s ≫ b) (s ≫ c) rfl rfl =
      (comparisonIso f g E i (s ≫ b) j (s ≫ c) (by rw [Category.assoc, hc])).hom := by
  simp only [comparisonIso_hom]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc, mapComp'_inv_naturality]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc (g i j).op.toLoc c.op.toLoc
    s.op.toLoc b.op.toLoc (c.op.toLoc ≫ s.op.toLoc) (b.op.toLoc ≫ s.op.toLoc)
    (by rw [← hc]; rfl) rfl rfl]
  simp

omit [F.IsPrestack J] in
lemma pullHom_comparisonIso_inv (i : ι) ⦃Z : C⦄ (b : Z ⟶ X i) (j : κ i) (c : Z ⟶ Y i j)
    (hc : c ≫ g i j = b) ⦃Z' : C⦄ (s : Z' ⟶ Z) :
    pullHom (comparisonIso f g E i b j c hc).inv s (s ≫ c) (s ≫ b) rfl rfl =
      (comparisonIso f g E i (s ≫ b) j (s ≫ c) (by rw [Category.assoc, hc])).inv := by
  rw [← cancel_epi (comparisonIso f g E i (s ≫ b) j (s ≫ c) (by rw [Category.assoc, hc])).hom,
    Iso.hom_inv_id, ← pullHom_comparisonIso_hom f g E i b j c hc s,
    ← pullHom_comp _ _ s (s ≫ b) (s ≫ c) (s ≫ b) rfl rfl rfl, Iso.hom_inv_id, pullHom_id']

omit [F.IsPrestack J] in
lemma pullHom_localHom ⦃Z : C⦄ ⦃i₁ i₂ : ι⦄ (b₁ : Z ⟶ X i₁) (b₂ : Z ⟶ X i₂)
    (hb : b₁ ≫ f i₁ = b₂ ≫ f i₂)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = b₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = b₂) ⦃Z' : C⦄ (s : Z' ⟶ Z) :
    pullHom (localHom f g E b₁ b₂ hb j₁ c₁ hc₁ j₂ c₂ hc₂) s (s ≫ b₁) (s ≫ b₂) rfl rfl =
      localHom f g E (s ≫ b₁) (s ≫ b₂) (by rw [Category.assoc, Category.assoc, hb])
        j₁ (s ≫ c₁) (by rw [Category.assoc, hc₁]) j₂ (s ≫ c₂) (by rw [Category.assoc, hc₂]) := by
  simp only [localHom]
  rw [pullHom_comp _ _ s (s ≫ b₁) (s ≫ c₁) (s ≫ b₂) rfl rfl rfl,
    pullHom_comp _ _ s (s ≫ c₁) (s ≫ c₂) (s ≫ b₂) rfl rfl rfl,
    pullHom_comparisonIso_hom, pullHom_comparisonIso_inv,
    E.pullHom_hom s (b₁ ≫ f i₁) ((s ≫ b₁) ≫ f i₁) (by rw [Category.assoc])
      (i₁ := ⟨i₁, j₁⟩) (i₂ := ⟨i₂, j₂⟩) c₁ c₂ (by rw [← hc₁, Category.assoc])
      (by rw [hb, ← hc₂, Category.assoc]) (s ≫ c₁) (s ≫ c₂) rfl rfl]

omit [F.IsPrestack J] in
lemma pullHom_localHom' ⦃Z : C⦄ ⦃i₁ i₂ : ι⦄ (b₁ : Z ⟶ X i₁) (b₂ : Z ⟶ X i₂)
    (hb : b₁ ≫ f i₁ = b₂ ≫ f i₂)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = b₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = b₂) ⦃Z' : C⦄ (s : Z' ⟶ Z)
    (b₁' : Z' ⟶ X i₁) (b₂' : Z' ⟶ X i₂) (hb₁' : s ≫ b₁ = b₁') (hb₂' : s ≫ b₂ = b₂') :
    pullHom (localHom f g E b₁ b₂ hb j₁ c₁ hc₁ j₂ c₂ hc₂) s b₁' b₂' hb₁' hb₂' =
      localHom f g E b₁' b₂' (by rw [← hb₁', ← hb₂', Category.assoc, Category.assoc, hb])
        j₁ (s ≫ c₁) (by rw [← hb₁', Category.assoc, hc₁])
        j₂ (s ≫ c₂) (by rw [← hb₂', Category.assoc, hc₂]) := by
  subst hb₁' hb₂'
  exact pullHom_localHom f g E b₁ b₂ hb j₁ c₁ hc₁ j₂ c₂ hc₂ s

/-- The sieve of `W` of the arrows along which `a₁` and `a₂` factor through the families `g`. -/
def factorSieve ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂) : Sieve W :=
  (Sieve.ofArrows _ (g i₁)).pullback a₁ ⊓ (Sieve.ofArrows _ (g i₂)).pullback a₂

omit [F.IsPrestack J] in
lemma mem_factorSieve ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂) ⦃Z : C⦄
    (t : Z ⟶ W) (b₁ : Z ⟶ X i₁) (b₂ : Z ⟶ X i₂) (h₁ : t ≫ a₁ = b₁) (h₂ : t ≫ a₂ = b₂)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = b₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = b₂) :
    factorSieve g a₁ a₂ t :=
  ⟨⟨_, c₁, _, ⟨j₁⟩, hc₁.trans h₁.symm⟩, ⟨_, c₂, _, ⟨j₂⟩, hc₂.trans h₂.symm⟩⟩

omit [F.IsPrestack J] in
/-- The chosen local morphism over an arrow of `factorSieve`. -/
def chosenLocalHom ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂)
    (ha : a₁ ≫ f i₁ = a₂ ≫ f i₂) ⦃Z : C⦄ (t : Z ⟶ W) (ht : factorSieve g a₁ a₂ t) :
    (F.map (t ≫ a₁).op.toLoc).toFunctor.obj (descendedObj f g E i₁) ⟶
      (F.map (t ≫ a₂).op.toLoc).toFunctor.obj (descendedObj f g E i₂) :=
  localHom f g E (t ≫ a₁) (t ≫ a₂) (by rw [Category.assoc, Category.assoc, ha])
    (Sieve.ofArrows.i ht.1) (Sieve.ofArrows.h ht.1) (Sieve.ofArrows.fac ht.1)
    (Sieve.ofArrows.i ht.2) (Sieve.ofArrows.h ht.2) (Sieve.ofArrows.fac ht.2)

omit [F.IsPrestack J] in
lemma chosenLocalHom_eq ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂)
    (ha : a₁ ≫ f i₁ = a₂ ≫ f i₂) ⦃Z : C⦄ (t : Z ⟶ W) (ht : factorSieve g a₁ a₂ t)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = t ≫ a₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = t ≫ a₂) :
    chosenLocalHom f g E a₁ a₂ ha t ht = localHom f g E (t ≫ a₁) (t ≫ a₂)
      (by rw [Category.assoc, Category.assoc, ha]) j₁ c₁ hc₁ j₂ c₂ hc₂ :=
  localHom_eq f g E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

omit [F.IsPrestack J] in
lemma pullHom_chosenLocalHom ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂)
    (ha : a₁ ≫ f i₁ = a₂ ≫ f i₂) ⦃Z Z' : C⦄ (t : Z ⟶ W) (ht : factorSieve g a₁ a₂ t)
    (s : Z' ⟶ Z) :
    pullHom (chosenLocalHom f g E a₁ a₂ ha t ht) s ((s ≫ t) ≫ a₁) ((s ≫ t) ≫ a₂)
      (by rw [Category.assoc]) (by rw [Category.assoc]) =
      chosenLocalHom f g E a₁ a₂ ha (s ≫ t) ((factorSieve g a₁ a₂).downward_closed ht s) := by
  rw [chosenLocalHom, pullHom_localHom' f g E _ _ _ _ _ _ _ _ _ s ((s ≫ t) ≫ a₁) ((s ≫ t) ≫ a₂)
    (by rw [Category.assoc]) (by rw [Category.assoc])]
  exact (chosenLocalHom_eq f g E a₁ a₂ ha (s ≫ t) _ _ _ _ _ _ _).symm

variable (hg : ∀ i, Sieve.ofArrows (Y i) (g i) ∈ J (X i))

include hg in
omit [F.IsPrestack J] in
lemma factorSieve_mem ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂) :
    factorSieve g a₁ a₂ ∈ J W :=
  J.intersection_covering (J.pullback_stable a₁ (hg i₁)) (J.pullback_stable a₂ (hg i₂))

/-- The descended morphisms. -/
def gluedHom ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂)
    (ha : a₁ ≫ f i₁ = a₂ ≫ f i₂) :
    (F.map a₁.op.toLoc).toFunctor.obj (descendedObj f g E i₁) ⟶
      (F.map a₂.op.toLoc).toFunctor.obj (descendedObj f g E i₂) :=
  (exists_pullHom_eq (J := J) (factorSieve_mem g hg a₁ a₂) a₁ a₂ (chosenLocalHom f g E a₁ a₂ ha)
    (fun _ _ t ht s ↦ pullHom_chosenLocalHom f g E a₁ a₂ ha t ht s)).choose

lemma pullHom_gluedHom ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂)
    (ha : a₁ ≫ f i₁ = a₂ ≫ f i₂) ⦃Z : C⦄ (t : Z ⟶ W)
    (b₁ : Z ⟶ X i₁) (b₂ : Z ⟶ X i₂) (h₁ : t ≫ a₁ = b₁) (h₂ : t ≫ a₂ = b₂)
    (j₁ : κ i₁) (c₁ : Z ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = b₁)
    (j₂ : κ i₂) (c₂ : Z ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = b₂) :
    pullHom (gluedHom f g E hg a₁ a₂ ha) t b₁ b₂ h₁ h₂ =
      localHom f g E b₁ b₂ (by rw [← h₁, ← h₂, Category.assoc, Category.assoc, ha])
        j₁ c₁ hc₁ j₂ c₂ hc₂ := by
  subst h₁ h₂
  have ht := mem_factorSieve g a₁ a₂ t _ _ rfl rfl j₁ c₁ hc₁ j₂ c₂ hc₂
  rw [gluedHom, (exists_pullHom_eq (J := J) (factorSieve_mem g hg a₁ a₂) a₁ a₂
    (chosenLocalHom f g E a₁ a₂ ha)
    (fun _ _ t ht s ↦ pullHom_chosenLocalHom f g E a₁ a₂ ha t ht s)).choose_spec t ht]
  exact chosenLocalHom_eq f g E a₁ a₂ ha t ht j₁ c₁ hc₁ j₂ c₂ hc₂

lemma gluedHom_eq ⦃W : C⦄ ⦃i₁ i₂ : ι⦄ (a₁ : W ⟶ X i₁) (a₂ : W ⟶ X i₂)
    (ha : a₁ ≫ f i₁ = a₂ ≫ f i₂)
    (j₁ : κ i₁) (c₁ : W ⟶ Y i₁ j₁) (hc₁ : c₁ ≫ g i₁ j₁ = a₁)
    (j₂ : κ i₂) (c₂ : W ⟶ Y i₂ j₂) (hc₂ : c₂ ≫ g i₂ j₂ = a₂) :
    gluedHom f g E hg a₁ a₂ ha = localHom f g E a₁ a₂ ha j₁ c₁ hc₁ j₂ c₂ hc₂ := by
  have h := pullHom_gluedHom f g E hg a₁ a₂ ha (𝟙 W) a₁ a₂ (Category.id_comp _)
    (Category.id_comp _) j₁ c₁ hc₁ j₂ c₂ hc₂
  rwa [pullHom_id] at h

include hg in
/-- The descent datum for `f` glued from `E`. -/
def gluedDescentData : F.DescentData f where
  obj i := descendedObj f g E i
  hom W q i₁ i₂ a₁ a₂ ha₁ ha₂ := gluedHom f g E hg a₁ a₂ (by rw [ha₁, ha₂])
  pullHom_hom Y' Y g' q q' hq i₁ i₂ a₁ a₂ ha₁ ha₂ ga₁ ga₂ hga₁ hga₂ := by
    refine eq_of_pullHom_eq (J := J) (factorSieve_mem g hg ga₁ ga₂) ga₁ ga₂ (fun Z t ht ↦ ?_)
    obtain ⟨j₁, c₁, hc₁⟩ := (Sieve.ofArrows.exists ht.1).imp
      fun _ ↦ Exists.imp fun _ ↦ Eq.symm
    obtain ⟨j₂, c₂, hc₂⟩ := (Sieve.ofArrows.exists ht.2).imp
      fun _ ↦ Exists.imp fun _ ↦ Eq.symm
    rw [pullHom_pullHom, pullHom_gluedHom f g E hg a₁ a₂ _ (t ≫ g') (t ≫ ga₁) (t ≫ ga₂)
      (by rw [Category.assoc, hga₁]) (by rw [Category.assoc, hga₂]) j₁ c₁ hc₁ j₂ c₂ hc₂,
      pullHom_gluedHom f g E hg ga₁ ga₂ _ t (t ≫ ga₁) (t ≫ ga₂) rfl rfl j₁ c₁ hc₁ j₂ c₂ hc₂]
  hom_self W q i a ha := by
    refine eq_of_pullHom_eq (J := J) (factorSieve_mem g hg a a) a a (fun Z t ht ↦ ?_)
    obtain ⟨j, c, hc⟩ := (Sieve.ofArrows.exists ht.1).imp
      fun _ ↦ Exists.imp fun _ ↦ Eq.symm
    rw [pullHom_gluedHom f g E hg a a _ t (t ≫ a) (t ≫ a) rfl rfl j c hc j c hc, pullHom_id']
    simp only [localHom]
    rw [E.hom_self ((t ≫ a) ≫ f i) (i := ⟨i, j⟩) c (by rw [← hc, Category.assoc]),
      Category.id_comp, Iso.hom_inv_id]
  hom_comp W q i₁ i₂ i₃ a₁ a₂ a₃ ha₁ ha₂ ha₃ := by
    refine eq_of_pullHom_eq (J := J) (J.intersection_covering (factorSieve_mem g hg a₁ a₂)
      (factorSieve_mem g hg a₂ a₃)) a₁ a₃ (fun Z t ht ↦ ?_)
    obtain ⟨j₁, c₁, hc₁⟩ := (Sieve.ofArrows.exists ht.1.1).imp
      fun _ ↦ Exists.imp fun _ ↦ Eq.symm
    obtain ⟨j₂, c₂, hc₂⟩ := (Sieve.ofArrows.exists ht.1.2).imp
      fun _ ↦ Exists.imp fun _ ↦ Eq.symm
    obtain ⟨j₃, c₃, hc₃⟩ := (Sieve.ofArrows.exists ht.2.2).imp
      fun _ ↦ Exists.imp fun _ ↦ Eq.symm
    rw [pullHom_comp _ _ t (t ≫ a₁) (t ≫ a₂) (t ≫ a₃) rfl rfl rfl,
      pullHom_gluedHom f g E hg a₁ a₂ _ t _ _ rfl rfl j₁ c₁ hc₁ j₂ c₂ hc₂,
      pullHom_gluedHom f g E hg a₂ a₃ _ t _ _ rfl rfl j₂ c₂ hc₂ j₃ c₃ hc₃,
      pullHom_gluedHom f g E hg a₁ a₃ _ t _ _ rfl rfl j₁ c₁ hc₁ j₃ c₃ hc₃]
    simp only [localHom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [E.hom_congr_base (q := t ≫ a₂ ≫ f i₂) (q' := t ≫ a₁ ≫ f i₁)
      (by rw [ha₁, ha₂]) (i₁ := ⟨i₂, j₂⟩) (i₂ := ⟨i₃, j₃⟩) c₂ c₃,
      DescentData.hom_comp_assoc]

/-- The comparison `objIsoHom` is compatible with the descent morphisms of the pullback of
`gluedDescentData` to the composite family and those of `E`. -/
lemma pullIso_comm ⦃Z : C⦄ (q : Z ⟶ S) ⦃i₁ i₂ : ι⦄ (j₁ : κ i₁) (j₂ : κ i₂)
    (c₁ : Z ⟶ Y i₁ j₁) (c₂ : Z ⟶ Y i₂ j₂) (hc₁ : c₁ ≫ g i₁ j₁ ≫ f i₁ = q)
    (hc₂ : c₂ ≫ g i₂ j₂ ≫ f i₂ = q) :
    (F.map c₁.op.toLoc).toFunctor.map (objIsoHom f g E i₁ j₁) ≫
        E.hom q (i₁ := ⟨i₁, j₁⟩) (i₂ := ⟨i₂, j₂⟩) c₁ c₂ hc₁ hc₂ =
      ((F.mapComp' (g i₁ j₁).op.toLoc c₁.op.toLoc (c₁ ≫ g i₁ j₁).op.toLoc
          rfl).inv.toNatTrans.app (descendedObj f g E i₁) ≫
        gluedHom f g E hg (c₁ ≫ g i₁ j₁) (c₂ ≫ g i₂ j₂)
          (by rw [Category.assoc, Category.assoc, hc₁, hc₂]) ≫
        (F.mapComp' (g i₂ j₂).op.toLoc c₂.op.toLoc (c₂ ≫ g i₂ j₂).op.toLoc
          rfl).hom.toNatTrans.app (descendedObj f g E i₂)) ≫
      (F.map c₂.op.toLoc).toFunctor.map (objIsoHom f g E i₂ j₂) := by
  rw [gluedHom_eq f g E hg _ _ _ j₁ c₁ rfl j₂ c₂ rfl]
  simp only [localHom, comparisonIso_hom, comparisonIso_inv, Category.assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc, map_objIsoInv_hom, Category.comp_id]
  rw [E.hom_congr_base (q := q) (q' := c₁ ≫ g i₁ j₁ ≫ f i₁) hc₁.symm (i₁ := ⟨i₁, j₁⟩)
    (i₂ := ⟨i₂, j₂⟩) c₁ c₂]

omit [F.IsPrestack J] in
/-- The isomorphisms `objIsoHom`, `objIsoInv`. -/
@[simps]
def objIsoApp (i : ι) (j : κ i) :
    (F.map (g i j).op.toLoc).toFunctor.obj (descendedObj f g E i) ≅ E.obj ⟨i, j⟩ where
  hom := objIsoHom f g E i j
  inv := objIsoInv f g E i j

include hg in
/-- The glued descent datum restricts to `E` along the composite family. -/
def pullIso :
    (DescentData.pullFunctor F (f := f) (f' := fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1)
      (p := 𝟙 S)
      (α := Sigma.fst) (p' := fun ij ↦ g ij.1 ij.2)
      (fun _ ↦ (Category.comp_id _).symm)).obj (gluedDescentData f g E hg) ≅ E :=
  DescentData.isoMk (fun ij ↦ objIsoApp f g E ij.1 ij.2) (by
    rintro Z q ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ c₁ c₂ hc₁ hc₂
    have hPD : ((DescentData.pullFunctor F (fun ij : Σ i, κ i ↦
        (Category.comp_id (g ij.1 ij.2 ≫ f ij.1)).symm)).obj (gluedDescentData f g E hg)).hom
          q c₁ c₂ hc₁ hc₂ =
        (F.mapComp' (g i₁ j₁).op.toLoc c₁.op.toLoc (c₁ ≫ g i₁ j₁).op.toLoc
          rfl).inv.toNatTrans.app _ ≫
        gluedHom f g E hg (c₁ ≫ g i₁ j₁) (c₂ ≫ g i₂ j₂)
          (by rw [Category.assoc, Category.assoc, hc₁, hc₂]) ≫
        (F.mapComp' (g i₂ j₂).op.toLoc c₂.op.toLoc (c₂ ≫ g i₂ j₂).op.toLoc
          rfl).hom.toNatTrans.app _ :=
      DescentData.pullFunctorObjHom_eq
        (w := fun ij : Σ i, κ i ↦ (Category.comp_id (g ij.1 ij.2 ≫ f ij.1)).symm) _ q c₁ c₂ q
        (c₁ ≫ g i₁ j₁) (c₂ ≫ g i₂ j₂) hc₁ hc₂ (Category.comp_id q) rfl rfl
    rw [hPD]
    exact pullIso_comm f g E hg q j₁ j₂ c₁ c₂ hc₁ hc₂)

end CompDescent

variable (hg : ∀ i, Sieve.ofArrows (Y i) (g i) ∈ J (X i))

include hg in
/-- **Effective descent along composites of families, for prestacks.** Let `F` be a `J`-prestack,
`f : X i ⟶ S` a `J`-covering family with `F.toDescentData f` an equivalence, and for every `i` a
`J`-covering family `g i j : Y i j ⟶ X i` with `F.toDescentData (g i)` an equivalence. Then
`F.toDescentData` of the composite family `g i j ≫ f i` is an equivalence. -/
theorem isEquivalence_toDescentData_comp (hf : Sieve.ofArrows X f ∈ J S)
    [(F.toDescentData f).IsEquivalence] :
    (F.toDescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1)).IsEquivalence := by
  have hh : Sieve.ofArrows _ (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1) ∈ J S := by
    refine J.transitive hf _ (fun Y a ha ↦ ?_)
    obtain ⟨Y', b, _, ⟨i⟩, rfl⟩ := ha
    refine J.superset_covering (fun Z t ht ↦ ?_) (J.pullback_stable b (hg i))
    obtain ⟨_, d, _, ⟨j⟩, hd⟩ := ht
    rw [Sieve.pullback_apply]
    exact ⟨_, d, _, ⟨(⟨i, j⟩ : Σ i, κ i)⟩, by simp [reassoc_of% hd]⟩
  have hff := F.fullyFaithfulToDescentData (J := J) _ hh
  have := hff.full
  have := hff.faithful
  let w : ∀ ij : Σ i, κ i, g ij.1 ij.2 ≫ f ij.1 = (g ij.1 ij.2 ≫ f ij.1) ≫ 𝟙 S :=
    fun ij ↦ (Category.comp_id _).symm
  let eh : F.toDescentData f ⋙ DescentData.pullFunctor F (p := 𝟙 S) (α := Sigma.fst)
      (p' := fun ij ↦ g ij.1 ij.2) w ≅
      F.toDescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1) :=
    DescentData.toDescentDataCompPullFunctorIso _ _ ≪≫
      (Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _) ≪≫ Functor.leftUnitor _
  have : (F.toDescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1)).EssSurj := ⟨fun E ↦
    ⟨(F.toDescentData f).objPreimage (CompDescent.gluedDescentData f g E hg),
      ⟨(eh.app _).symm ≪≫ (DescentData.pullFunctor F w).mapIso
        ((F.toDescentData f).objObjPreimageIso (CompDescent.gluedDescentData f g E hg)) ≪≫
          CompDescent.pullIso f g E hg⟩⟩⟩
  exact { }

end Comp

end CategoryTheory.Pseudofunctor
