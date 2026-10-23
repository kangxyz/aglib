/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.TupleBaseChange
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite-product comparison of original family cochains

The map on original free tuple presheaves need not be invertible. Nevertheless,
its additive Hom comparison with precomposed coefficients is invertible when
the actual functor on slices preserves finite products. The proof uses the
original free-family Yoneda equivalence and restriction along the actual tuple
product isomorphisms. The original cochain map, including all its face maps,
is retained, rather than replaced by an unrelated degreewise isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf.Cech.FamilyBaseChange

universe u v w

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (P : C ⥤ D) {W : C} {W' : D} {ι : Type w}
  (U : ι → Over W) (V : ι → Over W') (e : P.obj W ≅ W')
  (eU : ∀ i, (Over.post P ⋙ Over.map e.hom).obj (U i) ≅ V i)
  [HasFiniteProducts (Over W)] [HasFiniteProducts (Over W')]
  [PreservesFiniteProducts (Over.post P ⋙ Over.map e.hom)]

/-- The canonical comparison of the actual finite products in the slices. -/
def productIso {n : ℕ} (a : Fin (n + 1) → ι) :
    (Over.post P ⋙ Over.map e.hom).obj (∏ᶜ fun k => U (a k)) ≅
      ∏ᶜ fun k => V (a k) :=
  PreservesProduct.iso (Over.post P ⋙ Over.map e.hom) (fun k => U (a k)) ≪≫
    Pi.mapIso (fun k => eU (a k))

/-- The product comparison retains every original projection. -/
@[reassoc]
theorem productIso_hom_π {n : ℕ} (a : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (productIso P U V e eU a).hom ≫ Pi.π (fun k => V (a k)) k =
      (Over.post P ⋙ Over.map e.hom).map (Pi.π (fun k => U (a k)) k) ≫
        (eU (a k)).hom := by
  simp only [productIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    PreservesProduct.iso_hom, piComparison_comp_π_assoc]

/-- The tuple product isomorphism in the original category. -/
def tupleIso {n : ℕ} (a : Fin (n + 1) → ι) :
    P.obj (∏ᶜ fun k => U (a k)).left ≅ (∏ᶜ fun k => V (a k)).left :=
  (Over.forget W').mapIso (productIso P U V e eU a)

/-- Every tuple projection commutes with the original comparison. -/
@[reassoc]
theorem tupleIso_hom_π {n : ℕ} (a : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (tupleIso P U V e eU a).hom ≫ (Pi.π (fun k => V (a k)) k).left =
      P.map (Pi.π (fun k => U (a k)) k).left ≫ (eU (a k)).hom.left :=
  congrArg (fun f => f.left) (productIso_hom_π P U V e eU a k)

/-- The tuple comparison retains the original arrow to the family target. -/
@[reassoc]
theorem tupleIso_hom_hom {n : ℕ} (a : Fin (n + 1) → ι) :
    (tupleIso P U V e eU a).hom ≫ (∏ᶜ fun k => V (a k)).hom =
      P.map (∏ᶜ fun k => U (a k)).hom ≫ e.hom :=
  Over.w (productIso P U V e eU a).hom

variable {P U V e eU}

/-- The actual product map induced by any reindexing, including deletion faces. -/
def productReindex {n m : ℕ} (a : Fin (n + 1) → ι)
    (b : Fin (m + 1) → Fin (n + 1)) :
    (∏ᶜ fun k => U (a k)) ⟶ ∏ᶜ fun k => U (a (b k)) :=
  Pi.lift fun k => Pi.π (fun k => U (a k)) (b k)

@[reassoc (attr := simp)]
theorem productReindex_π {n m : ℕ} (a : Fin (n + 1) → ι)
    (b : Fin (m + 1) → Fin (n + 1)) (k : Fin (m + 1)) :
    productReindex (U := U) a b ≫ Pi.π (fun k => U (a (b k))) k =
      Pi.π (fun k => U (a k)) (b k) :=
  Pi.lift_comp_π _ _

variable (P U V e eU)

/-- The geometric tuple comparisons commute with every original face and
repetition map, before passing to coefficients. -/
@[reassoc]
theorem productIso_reindex {n m : ℕ} (a : Fin (n + 1) → ι)
    (b : Fin (m + 1) → Fin (n + 1)) :
    (productIso P U V e eU a).hom ≫ productReindex (U := V) a b =
      (Over.post P ⋙ Over.map e.hom).map (productReindex (U := U) a b) ≫
        (productIso P U V e eU (a ∘ b)).hom := by
  apply Pi.hom_ext
  intro k
  let K : Over W ⥤ Over W' := Over.post P ⋙ Over.map e.hom
  have h : (productIso P U V e eU (a ∘ b)).hom ≫
      Pi.π (fun k => V (a (b k))) k =
      K.map (Pi.π (fun k => U (a (b k))) k) ≫ (eU (a (b k))).hom :=
    productIso_hom_π P U V e eU (a ∘ b) k
  rw [Category.assoc, productReindex_π, productIso_hom_π, Category.assoc, h,
    ← Category.assoc, ← K.map_comp, productReindex_π]

/-- Applying the tuple map to the original product generator gives precisely
the tuple of projections of the canonical product comparison. -/
theorem tupleMap_productGenerator {n : ℕ} (a : Fin (n + 1) → ι) :
    tupleMap P U V e eU
        (productToTuple U (X := op (∏ᶜ fun k => U (a k)).left)
          ⟨a, 𝟙 (∏ᶜ fun k => U (a k)).left⟩) =
      productToTuple V (X := op (P.obj (∏ᶜ fun k => U (a k)).left))
        ⟨a, (tupleIso P U V e eU a).hom⟩ := by
  apply tuple_ext
  · apply ULift.ext
    change P.map (𝟙 _ ≫ (∏ᶜ fun k => U (a k)).hom) ≫ e.hom =
      (tupleIso P U V e eU a).hom ≫ (∏ᶜ fun k => V (a k)).hom
    rw [Category.id_comp]
    exact (tupleIso_hom_hom P U V e eU a).symm
  · intro k
    change (⟨a k, P.map (𝟙 _ ≫ (Pi.π (fun k => U (a k)) k).left) ≫
        (eU (a k)).hom.left⟩ : Σ j, _ ⟶ (V j).left) =
      ⟨a k, (tupleIso P U V e eU a).hom ≫ (Pi.π (fun k => V (a k)) k).left⟩
    have h : P.map (𝟙 (∏ᶜ fun k => U (a k)).left ≫
        (Pi.π (fun k => U (a k)) k).left) ≫ (eU (a k)).hom.left =
        (tupleIso P U V e eU a).hom ≫ (Pi.π (fun k => V (a k)) k).left :=
      (congrArg (fun q => P.map q ≫ (eU (a k)).hom.left)
        (Category.id_comp (Pi.π (fun k => U (a k)) k).left)).trans
          (tupleIso_hom_π P U V e eU a k).symm
    exact congrArg (fun q => (⟨a k, q⟩ :
      Σ j, P.obj (∏ᶜ fun k => U (a k)).left ⟶ (V j).left)) h

section HomCoordinates

variable {P V e eU}

/-- The original free tuple term is the free family of the actual slice products. -/
def freeTupleProductIso (n : ℕ) :
    (freeComplex (familyMap U)).X n ≅
      familyPresheaf (fun a : Fin (n + 1) → ι => (∏ᶜ fun k => U (a k)).left) ⋙
        AddCommGrpCat.free :=
  ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso (tupleProductIso U n)

/-- Original tuple cochains are sections at the original tuple products. -/
def tupleHomEquiv (A : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ) :
    ((freeComplex (familyMap U)).X n ⟶ A) ≃
      ∀ a : Fin (n + 1) → ι, A.obj (op (∏ᶜ fun k => U (a k)).left) :=
  (Iso.homCongr (freeTupleProductIso U n) (Iso.refl A)).trans
    (freeFamilyHomEquiv (fun a : Fin (n + 1) → ι => (∏ᶜ fun k => U (a k)).left) A)

/-- The section coordinates evaluate the original free product generator. -/
theorem tupleHomEquiv_apply (A : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ)
    (q : (freeComplex (familyMap U)).X n ⟶ A) (a : Fin (n + 1) → ι) :
    tupleHomEquiv U A n q a =
      q.app (op (∏ᶜ fun k => U (a k)).left)
        (FreeAbelianGroup.of (productToTuple U
          (X := op (∏ᶜ fun k => U (a k)).left)
          ⟨a, 𝟙 (∏ᶜ fun k => U (a k)).left⟩)) := by
  let T : C := (∏ᶜ fun k => U (a k)).left
  let s : (familyPresheaf
      (fun a : Fin (n + 1) → ι => (∏ᶜ fun k => U (a k)).left)).obj (op T) :=
    ⟨a, 𝟙 T⟩
  have h : tupleHomEquiv U A n q a = q.app (op T)
      (FreeAbelianGroup.map ((tupleProductIso U n).inv.app (op T))
        (FreeAbelianGroup.of s)) := rfl
  exact h.trans (congrArg (fun x => q.app (op T) x)
    (FreeAbelianGroup.map_of_apply (f := (tupleProductIso U n).inv.app (op T)) s))

/-- Restricting a product generator uses its actual representing arrow. -/
theorem tupleRestrict_productGenerator {n : ℕ} (a : Fin (n + 1) → ι)
    {T : C} (g : T ⟶ (∏ᶜ fun k => U (a k)).left) :
    tupleRestrict (familyMap U) g.op
        (productToTuple U (X := op (∏ᶜ fun k => U (a k)).left)
          ⟨a, 𝟙 (∏ᶜ fun k => U (a k)).left⟩) =
      productToTuple U (X := op T) ⟨a, g⟩ := by
  apply tuple_ext
  · apply ULift.ext
    change g ≫ (𝟙 _ ≫ (∏ᶜ fun k => U (a k)).hom) =
      g ≫ (∏ᶜ fun k => U (a k)).hom
    rw [Category.id_comp]
  · intro k
    change (⟨a k, g ≫ (𝟙 _ ≫ (Pi.π (fun k => U (a k)) k).left)⟩ :
      Σ j, T ⟶ (U j).left) = ⟨a k, g ≫ (Pi.π (fun k => U (a k)) k).left⟩
    rw [Category.id_comp]

end HomCoordinates

omit [HasFiniteProducts (Over W)] [HasFiniteProducts (Over W')]
  [PreservesFiniteProducts (Over.post P ⋙ Over.map e.hom)] in
/-- The actual cochain comparison sends each free tuple generator to the
original mapped tuple, with no finite-product coordinates unfolded. -/
theorem additiveHomMap_generator (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ)
    (q : (freeComplex (familyMap V)).X n ⟶ A) (Y : Cᵒᵖ)
    (t : Tuple (familyMap U) n Y) :
    (((additiveHomMap P U V e eU A).f n) q).app Y (FreeAbelianGroup.of t) =
      q.app (P.op.obj Y) (FreeAbelianGroup.of (tupleMap P U V e eU t)) := by
  have h := congrArg (fun k : (freeComplex (familyMap U)).X n ⟶ P.op ⋙ A =>
    k.app Y (FreeAbelianGroup.of t)) (additiveHomMap_f_apply P U V e eU A n q)
  have h' : (Functor.whiskerRight (tupleNatTrans P U V e eU n) AddCommGrpCat.free ≫
      Functor.whiskerLeft P.op q).app Y (FreeAbelianGroup.of t) =
      q.app (P.op.obj Y) (FreeAbelianGroup.of (tupleMap P U V e eU t)) := by
    exact congrArg (fun x => q.app (P.op.obj Y) x)
      (FreeAbelianGroup.map_of_apply (f := (tupleNatTrans P U V e eU n).app Y) t)
  exact h.trans h'

/-- In the original product coordinates, the actual cochain comparison is
restriction along the genuine tuple product isomorphism. -/
theorem additiveHomMap_section (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ)
    (q : (freeComplex (familyMap V)).X n ⟶ A) (a : Fin (n + 1) → ι) :
    tupleHomEquiv U (P.op ⋙ A) n ((additiveHomMap P U V e eU A).f n q) a =
      A.map (tupleIso P U V e eU a).hom.op (tupleHomEquiv V A n q a) := by
  let T₀ : C := (∏ᶜ fun k => U (a k)).left
  let T₁ : D := (∏ᶜ fun k => V (a k)).left
  let t₀ : Tuple (familyMap U) n (op T₀) :=
    productToTuple U (X := op T₀) ⟨a, 𝟙 T₀⟩
  let t₁ : Tuple (familyMap V) n (op T₁) :=
    productToTuple V (X := op T₁) ⟨a, 𝟙 T₁⟩
  let g : P.obj T₀ ⟶ T₁ := (tupleIso P U V e eU a).hom
  have ht : tupleMap P U V e eU t₀ = tupleRestrict (familyMap V) g.op t₁ :=
    (tupleMap_productGenerator P U V e eU a).trans
      (tupleRestrict_productGenerator V a g).symm
  have hn : q.app (op (P.obj T₀))
      (FreeAbelianGroup.of (tupleRestrict (familyMap V) g.op t₁)) =
      A.map g.op (q.app (op T₁) (FreeAbelianGroup.of t₁)) := by
    have hq := q.naturality_apply g.op (FreeAbelianGroup.of t₁)
    have hf : ((freeComplex (familyMap V)).X n).map g.op (FreeAbelianGroup.of t₁) =
        FreeAbelianGroup.of (tupleRestrict (familyMap V) g.op t₁) :=
      FreeAbelianGroup.map_of_apply (f := tupleRestrict (familyMap V) g.op) t₁
    exact (congrArg (fun x => q.app (op (P.obj T₀)) x) hf).symm.trans hq
  exact (tupleHomEquiv_apply U (P.op ⋙ A) n
      ((additiveHomMap P U V e eU A).f n q) a).trans
    ((additiveHomMap_generator P U V e eU A n q (op T₀) t₀).trans
      ((congrArg (fun t => q.app (op (P.obj T₀)) (FreeAbelianGroup.of t)) ht).trans
        (hn.trans (congrArg (fun x => A.map g.op x)
          (tupleHomEquiv_apply V A n q a).symm))))

/-- Every degree of the original additive Hom comparison is bijective. This
uses only the actual product comparisons, not full faithfulness of the site functor. -/
theorem additiveHomMap_f_bijective (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ) :
    Function.Bijective ((additiveHomMap P U V e eU A).f n) := by
  let E : (∀ a : Fin (n + 1) → ι, A.obj (op (∏ᶜ fun k => V (a k)).left)) ≃
      (∀ a : Fin (n + 1) → ι, A.obj (op (P.obj (∏ᶜ fun k => U (a k)).left))) :=
    Equiv.piCongrRight (fun a : Fin (n + 1) → ι =>
      ((forget AddCommGrpCat).mapIso (A.mapIso (tupleIso P U V e eU a).op)).toEquiv)
  have h : (tupleHomEquiv U (P.op ⋙ A) n) ∘
      ((additiveHomMap P U V e eU A).f n) = E ∘ (tupleHomEquiv V A n) := by
    funext q a
    exact additiveHomMap_section P U V e eU A n q a
  have hb : Function.Bijective ((tupleHomEquiv U (P.op ⋙ A) n) ∘
      ((additiveHomMap P U V e eU A).f n)) := by
    rw [h]
    exact E.bijective.comp (tupleHomEquiv V A n).bijective
  exact hb.of_comp_left (tupleHomEquiv U (P.op ⋙ A) n).injective

instance additiveHomMap_f_isIso (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ) :
    IsIso ((additiveHomMap P U V e eU A).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (additiveHomMap_f_bijective P U V e eU A n)

instance additiveHomMap_isIso (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) :
    IsIso (additiveHomMap P U V e eU A) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- The original tuple cochain map is an isomorphism with precomposed
coefficients. This is not a filtered-colimit or higher-cohomology assertion. -/
def additiveHomIso (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) :
    additiveHomComplex (familyMap V) A ≅
      additiveHomComplex (familyMap U) (P.op ⋙ A) :=
  asIso (additiveHomMap P U V e eU A)

@[simp]
theorem additiveHomIso_hom (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) :
    (additiveHomIso P U V e eU A).hom = additiveHomMap P U V e eU A := rfl

end CategoryTheory.Presheaf.Cech.FamilyBaseChange
