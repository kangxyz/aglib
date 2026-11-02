/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# The site of elements of an actual presheaf

The site is the opposite of the native category of elements. Its topology
is the native restricted topology along the projection. Incoming arrows
have unique lifts, so the covering sieves are precisely those whose
underlying sieves cover in the original site.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf.ElementsSite

universe u v w

variable {C : Type u} [Category.{v} C] (A : Cᵒᵖ ⥤ Type w)

/-- The original native element category, with the site variance. -/
abbrev Site := A.Elementsᵒᵖ

/-- The native projection to the original site. -/
abbrev projection : Site A ⥤ C := (Functor.Elements.π A).leftOp

/-- The element over the specified site object. -/
abbrev mk (X : C) (x : A.obj (op X)) : Site A := op (A.elementsMk (op X) x)

/-- An arrow with its original underlying site map. -/
def homMk {a b : Site A} (f : (projection A).obj a ⟶ (projection A).obj b)
    (h : A.map f.op b.unop.val = a.unop.val) : a ⟶ b :=
  (Functor.Elements.homMk f.op h).op

lemma projection_map_homMk {a b : Site A}
    (f : (projection A).obj a ⟶ (projection A).obj b)
    (h : A.map f.op b.unop.val = a.unop.val) :
    (projection A).map (homMk A f h) = f := rfl

@[ext]
lemma hom_ext {a b : Site A} {f g : a ⟶ b}
    (h : (projection A).map f = (projection A).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  exact Quiver.Hom.unop_inj h

instance : (projection A).Faithful where
  map_injective := fun h => hom_ext A h

lemma map_val {a b : Site A} (f : a ⟶ b) :
    A.map ((projection A).map f).op b.unop.val = a.unop.val := f.unop.map_val

/-- The domain of the unique incoming lift. -/
def liftObj (a : Site A) {X : C} (f : X ⟶ (projection A).obj a) : Site A :=
  mk A X (A.map f.op a.unop.val)

/-- The incoming lift of a map in the original site. -/
def lift (a : Site A) {X : C} (f : X ⟶ (projection A).obj a) :
    liftObj A a f ⟶ a :=
  homMk A f rfl

lemma projection_obj_liftObj (a : Site A) {X : C} (f : X ⟶ (projection A).obj a) :
    (projection A).obj (liftObj A a f) = X := rfl

lemma projection_map_lift (a : Site A) {X : C} (f : X ⟶ (projection A).obj a) :
    (projection A).map (lift A a f) = f := rfl

/-- Factor an incoming lift through any incoming element arrow. -/
def liftTo {a b : Site A} (g : b ⟶ a) {X : C}
    (f : X ⟶ (projection A).obj b) :
    liftObj A a (f ≫ (projection A).map g) ⟶ b :=
  homMk A f (by
    change A.map f.op b.unop.val =
      A.map (f ≫ (projection A).map g).op a.unop.val
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, map_val])

@[simp]
lemma liftTo_comp {a b : Site A} (g : b ⟶ a) {X : C}
    (f : X ⟶ (projection A).obj b) :
    liftTo A g f ≫ g = lift A a (f ≫ (projection A).map g) := by
  apply hom_ext A
  rfl

/-- An arbitrary incoming arrow has the same lift with an identity underlying map. -/
def toLift {a b : Site A} (g : b ⟶ a) :
    b ⟶ liftObj A a ((projection A).map g) :=
  homMk A (𝟙 _) (by
    change A.map (𝟙 _) (A.map ((projection A).map g).op a.unop.val) = b.unop.val
    simpa only [Functor.map_id, ConcreteCategory.id_apply] using map_val A g)

/-- The inverse identity-base arrow from the selected incoming lift. -/
def fromLift {a b : Site A} (g : b ⟶ a) :
    liftObj A a ((projection A).map g) ⟶ b :=
  homMk A (𝟙 _) (by
    change A.map (𝟙 _) b.unop.val = A.map ((projection A).map g).op a.unop.val
    simpa only [Functor.map_id, ConcreteCategory.id_apply] using (map_val A g).symm)

@[simp]
lemma fromLift_comp {a b : Site A} (g : b ⟶ a) :
    fromLift A g ≫ g = lift A a ((projection A).map g) := by
  apply hom_ext A
  change (𝟙 _) ≫ (projection A).map g = (projection A).map g
  exact Category.id_comp _

lemma toLift_comp {a b : Site A} (g : b ⟶ a) :
    toLift A g ≫ lift A a ((projection A).map g) = g := by
  apply hom_ext A
  change (𝟙 _) ≫ (projection A).map g = (projection A).map g
  exact Category.id_comp _

/-- Membership in a projected sieve is tested on the actual incoming lift. -/
lemma functorPushforward_iff {a : Site A} (S : Sieve a) {X : C}
    (f : X ⟶ (projection A).obj a) :
    S.functorPushforward (projection A) f ↔ S (lift A a f) := by
  constructor
  · rintro ⟨b, g, h, hg, rfl⟩
    simpa only [liftTo_comp] using S.downward_closed hg (liftTo A g h)
  · intro hf
    exact ⟨liftObj A a f, lift A a f, 𝟙 _, hf, by
      change f = (𝟙 _) ≫ f
      exact (Category.id_comp _).symm⟩

@[simp]
lemma functorPullback_functorPushforward {a : Site A} (S : Sieve a) :
    (S.functorPushforward (projection A)).functorPullback (projection A) = S := by
  ext b g
  change S.functorPushforward (projection A) ((projection A).map g) ↔ S g
  rw [functorPushforward_iff]
  constructor
  · intro hg
    simpa only [toLift_comp] using S.downward_closed hg (toLift A g)
  · intro hg
    simpa only [fromLift_comp] using S.downward_closed hg (fromLift A g)

@[simp]
lemma functorPushforward_functorPullback {a : Site A}
    (S : Sieve ((projection A).obj a)) :
    (S.functorPullback (projection A)).functorPushforward (projection A) = S := by
  ext X f
  rw [functorPushforward_iff]
  rfl

/-- The sieve comparison induced by the native projection. -/
def sieveEquiv (a : Site A) : Sieve a ≃o Sieve ((projection A).obj a) where
  toFun := Sieve.functorPushforward (projection A)
  invFun := Sieve.functorPullback (projection A)
  left_inv := functorPullback_functorPushforward A
  right_inv := functorPushforward_functorPullback A
  map_rel_iff' := by
    intro S T
    change S.functorPushforward (projection A) ≤ T.functorPushforward (projection A) ↔ S ≤ T
    constructor
    · intro h
      have h' := Sieve.functorPullback_monotone (projection A) a h
      simpa using h'
    · intro h
      exact Sieve.functorPushforward_monotone (projection A) a h

lemma functorPullback_injective (a : Site A) :
    Function.Injective
      (Sieve.functorPullback (projection A) : Sieve ((projection A).obj a) → Sieve a) :=
  (sieveEquiv A a).symm.injective

@[simp]
lemma functorPushforward_pullback {a b : Site A} (f : b ⟶ a) (S : Sieve a) :
    (S.pullback f).functorPushforward (projection A) =
      (S.functorPushforward (projection A)).pullback ((projection A).map f) := by
  apply functorPullback_injective A b
  rw [Sieve.functorPullback_pullback, functorPullback_functorPushforward,
    functorPullback_functorPushforward]

/-- The existing restricted topology, on the actual element category. -/
abbrev topology (J : GrothendieckTopology C) : GrothendieckTopology (Site A) :=
  (projection A).restrictedTopology J

/-- Unique incoming lifts make the native restricted topology cover preserving. -/
lemma coverPreserving (J : GrothendieckTopology C) :
    CoverPreserving (topology A J) J (projection A) where
  cover_preserve {a S} hS := by
    change (J.toPrecoverage.comap (projection A)).Saturate a S at hS
    induction hS with
    | of a R hR =>
      change Sieve.generate (R.map (projection A)) ∈ J ((projection A).obj a) at hR
      simpa only [Sieve.generate_map_eq_functorPushforward] using hR
    | top a =>
      simpa only [Sieve.functorPushforward_top] using J.top_mem ((projection A).obj a)
    | pullback a S hS b f ih =>
      rw [functorPushforward_pullback]
      exact J.pullback_stable ((projection A).map f) ih
    | transitive a S R hS hR ihS ihR =>
      apply J.transitive ihS
      rintro X f ⟨b, g, h, hg, rfl⟩
      rw [Sieve.pullback_comp, ← functorPushforward_pullback]
      exact J.pullback_stable h (ihR hg)

@[simp]
lemma mem_topology_iff (J : GrothendieckTopology C) {a : Site A} (S : Sieve a) :
    S ∈ topology A J a ↔ S.functorPushforward (projection A) ∈ J ((projection A).obj a) :=
  ⟨(coverPreserving A J).cover_preserve,
    (projection A).mem_restrictedTopology_of_functorPushforward_mem⟩

instance isCocontinuous (J : GrothendieckTopology C) :
    (projection A).IsCocontinuous (topology A J) J where
  cover_lift hS := by
    rw [mem_topology_iff, functorPushforward_functorPullback]
    exact hS

/-- Compatibility is preserved by constructing the common incoming lift. -/
lemma compatiblePreserving (J : GrothendieckTopology C) :
    CompatiblePreserving J (projection A) where
  compatible {_ Z _ _ hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W := liftObj A Z (f₁ ≫ (projection A).map g₁)
    let g₁' : W ⟶ Y₁ := liftTo A g₁ f₁
    let g₂' : W ⟶ Y₂ := homMk A f₂ (by
      change A.map f₂.op Y₂.unop.val =
        A.map (f₁ ≫ (projection A).map g₁).op Z.unop.val
      rw [h]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, map_val])
    have hw : g₁' ≫ g₁ = g₂' ≫ g₂ := by
      apply hom_ext A
      change f₁ ≫ (projection A).map g₁ = f₂ ≫ (projection A).map g₂
      exact h
    exact hx g₁' g₂' hg₁ hg₂ hw

instance isContinuous (J : GrothendieckTopology C) :
    (projection A).IsContinuous (topology A J) J :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving A J) (coverPreserving A J)

end CategoryTheory.Presheaf.ElementsSite
