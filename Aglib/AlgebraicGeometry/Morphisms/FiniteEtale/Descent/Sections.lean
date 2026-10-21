/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Group

/-!
# Global sections and fixed elements of the actual fibre action

Fixed points of the actual native fibre action correspond to actual global sections. Source proves
the adapter using the native classification equivalence, not a new representation-existence
theorem.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Sections`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`016e655c46f1af5f742afa50e24030aaca96209aa1fbc853eba507bfec3a607d`. Selected lines: [[56, 232]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.FixedPoints

universe u

/-- The identity morphism as an actual finite étale cover. -/
abbrev identityCover (B : Scheme.{u}) : Scheme.FiniteEtale B :=
  _root_.AlgebraicGeometry.Scheme.FiniteEtale.mk (𝟙 B)

/-- Actual scheme sections of the structural morphism of `Y`. -/
abbrev globalSection {B : Scheme.{u}} (Y : Scheme.FiniteEtale B) :=
  Over.mk (𝟙 B) ⟶ Y.obj

variable {B : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ B)

/-- The canonical point of the actual singleton fibre of the identity cover. -/
def identityFiberPoint : Fiber s (identityCover B) :=
  Over.homMk s (Category.comp_id s)

/-- The actual fibre of the identity cover has at most one point. -/
instance identityFiberSubsingleton : Subsingleton (Fiber s (identityCover B)) where
  allEq p q := by
    apply Over.OverMorphism.ext
    have hp : p.left = s := (Category.comp_id p.left).symm.trans (Over.w p)
    have hq : q.left = s := (Category.comp_id q.left).symm.trans (Over.w q)
    exact hp.trans hq.symm

/-- Fixed elements of the actual fibre under its natural automorphism action. -/
abbrev fixedFiber (Y : Scheme.FiniteEtale B) :=
  {p : Fiber s Y // ∀ a : FiberAutGroup s, a.hom.app Y p = p}

/-- Evaluate a scheme section at the specified field-valued point. -/
def sectionValue (Y : Scheme.FiniteEtale B) (q : globalSection Y) : Fiber s Y :=
  identityFiberPoint s ≫ q

@[simp] theorem sectionValue_left (Y : Scheme.FiniteEtale B) (q : globalSection Y) :
    (sectionValue s Y q).left = s ≫ q.left := rfl

/-- Every global section evaluates to a fixed element, by naturality and the
singleton fibre of the identity cover. No classification hypothesis is needed. -/
def fixedPointOfSection (Y : Scheme.FiniteEtale B) (q : globalSection Y) : fixedFiber s Y :=
  ⟨sectionValue s Y q, by
    intro a
    have ht : a.hom.app (identityCover B) (identityFiberPoint s) =
        identityFiberPoint s :=
      @Subsingleton.elim (Fiber s (identityCover B)) (identityFiberSubsingleton s) _ _
    have h := evaluate_naturality s a
      (ObjectProperty.homMk q : identityCover B ⟶ Y) (identityFiberPoint s)
    change a.hom.app (identityCover B) (identityFiberPoint s) ≫ q =
      a.hom.app Y (sectionValue s Y q) at h
    rw [ht] at h
    exact h.symm⟩

@[simp] theorem fixedPointOfSection_val (Y : Scheme.FiniteEtale B) (q : globalSection Y) :
    (fixedPointOfSection s Y q).val = sectionValue s Y q := rfl

section Classification

variable [GaloisCategory (Scheme.FiniteEtale B)]
variable [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- A fixed actual fibre element gives the constant equivariant map from the
classified identity cover. -/
def classifiedFixedPoint (Y : Scheme.FiniteEtale B) (p : fixedFiber s Y) :
    (classification s).functor.obj (identityCover B) ⟶
      (classification s).functor.obj Y :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun _ => p.val)
      comm a := by
        apply FintypeCat.hom_ext
        intro q
        change p.val = a.hom.app Y p.val
        exact (p.property a).symm }

/-- Fullness of the actual classification constructs a scheme section from
the constant equivariant map associated to a fixed actual fibre element. -/
def sectionOfFixedPoint (Y : Scheme.FiniteEtale B) (p : fixedFiber s Y) : globalSection Y :=
  ((classification s).functor.preimage (classifiedFixedPoint s Y p)).hom

@[simp] theorem sectionOfFixedPoint_value (Y : Scheme.FiniteEtale B) (p : fixedFiber s Y) :
    sectionValue s Y (sectionOfFixedPoint s Y p) = p.val := by
  have h := (classification s).functor.map_preimage (classifiedFixedPoint s Y p)
  have h' := congrArg (fun f => f.hom.hom) h
  exact ConcreteCategory.congr_hom (C := FintypeCat) h' (identityFiberPoint s)

@[simp] theorem fixedPointOfSection_sectionOfFixedPoint
    (Y : Scheme.FiniteEtale B) (p : fixedFiber s Y) :
    fixedPointOfSection s Y (sectionOfFixedPoint s Y p) = p := by
  apply Subtype.ext
  exact sectionOfFixedPoint_value s Y p

@[simp] theorem sectionOfFixedPoint_fixedPointOfSection
    (Y : Scheme.FiniteEtale B) (q : globalSection Y) :
    sectionOfFixedPoint s Y (fixedPointOfSection s Y q) = q := by
  have h : classifiedFixedPoint s Y (fixedPointOfSection s Y q) =
      (classification s).functor.map (ObjectProperty.homMk q : identityCover B ⟶ Y) := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply FintypeCat.hom_ext
    intro t
    change identityFiberPoint s ≫ q = t ≫ q
    have ht : t = identityFiberPoint s :=
      @Subsingleton.elim (Fiber s (identityCover B)) (identityFiberSubsingleton s) t _
    rw [ht]
  dsimp only [sectionOfFixedPoint]
  rw [h, Functor.preimage_map]
  rfl

/-- The rational-origin descent prerequisite for
`K2-018#prop:k2018-arithmetic-characters` on source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`: actual global scheme sections
correspond exactly to fixed elements of the actual point fibre, conditionally
on the two displayed standard Galois-category classes. -/
def globalSectionEquivFixedFiber (Y : Scheme.FiniteEtale B) :
    globalSection Y ≃ fixedFiber s Y where
  toFun := fixedPointOfSection s Y
  invFun := sectionOfFixedPoint s Y
  left_inv := sectionOfFixedPoint_fixedPointOfSection s Y
  right_inv := fixedPointOfSection_sectionOfFixedPoint s Y

@[simp] theorem globalSectionEquivFixedFiber_value
    (Y : Scheme.FiniteEtale B) (q : globalSection Y) :
    (globalSectionEquivFixedFiber s Y q).val = identityFiberPoint s ≫ q := rfl

theorem globalSectionEquivFixedFiber_value_left
    (Y : Scheme.FiniteEtale B) (q : globalSection Y) :
    (globalSectionEquivFixedFiber s Y q).val.left = s ≫ q.left := rfl

/-- The section constructed from a fixed element is the unique actual section
whose evaluation is that element. -/
theorem sectionOfFixedPoint_unique (Y : Scheme.FiniteEtale B) (p : fixedFiber s Y)
    (q : globalSection Y) (hq : sectionValue s Y q = p.val) :
    q = sectionOfFixedPoint s Y p := by
  apply (globalSectionEquivFixedFiber s Y).injective
  apply Subtype.ext
  change sectionValue s Y q = sectionValue s Y (sectionOfFixedPoint s Y p)
  rw [sectionOfFixedPoint_value]
  exact hq

end Classification

section RationalPoint

variable {F : Type u} [Field F]
variable (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
variable [GaloisCategory (Scheme.FiniteEtale (Spec (CommRingCat.of F)))]
variable [PreGaloisCategory.FiberFunctor (fiberToFinite s)]

/-- Over `Spec F`, a fixed actual fibre element constructs an actual
`F`-rational point of the cover. This is the `Spec F` specialization of the
rational-origin prerequisite for `K2-018#prop:k2018-arithmetic-characters`
on source revision `e73d98b1b5c1e5abcdebf7d058e436d792b87982`. -/
def rationalPointOfFixedPoint (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F)))
    (p : fixedFiber s Y) : Spec (CommRingCat.of F) ⟶ Y.obj.left :=
  (sectionOfFixedPoint s Y p).left

/-- The constructed rational point lies above the identity of `Spec F`. -/
@[simp] theorem rationalPointOfFixedPoint_over
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : fixedFiber s Y) :
    rationalPointOfFixedPoint s Y p ≫ Y.obj.hom = 𝟙 (Spec (CommRingCat.of F)) :=
  Over.w (sectionOfFixedPoint s Y p)

/-- Evaluation at `s` recovers the supplied actual fibre point as a scheme map. -/
@[simp] theorem rationalPointOfFixedPoint_evaluation
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : fixedFiber s Y) :
    s ≫ rationalPointOfFixedPoint s Y p = p.val.left :=
  congrArg Over.Hom.left (sectionOfFixedPoint_value s Y p)

/-- The constructed point is the unique rational scheme section with the
specified evaluation. -/
theorem rationalPointOfFixedPoint_unique
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : fixedFiber s Y)
    (q : Spec (CommRingCat.of F) ⟶ Y.obj.left)
    (hq : q ≫ Y.obj.hom = 𝟙 (Spec (CommRingCat.of F)))
    (hpoint : s ≫ q = p.val.left) : q = rationalPointOfFixedPoint s Y p := by
  have h : sectionValue s Y (Over.homMk q hq) = p.val := by
    apply Over.OverMorphism.ext
    exact hpoint
  exact congrArg Over.Hom.left
    (sectionOfFixedPoint_unique s Y p (Over.homMk q hq) h)

end RationalPoint

end AlgebraicGeometry.Scheme.FiniteEtale.FixedPoints
