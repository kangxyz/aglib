/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.FunctorOfPoints

/-!
# Pullback squares detected on affine points

Let `i : W ⟶ X`, `φ : W ⟶ Z`, `f : X ⟶ Y`, `j : Z ⟶ Y` be maps of schemes over `Spec R` with
`i ≫ f = φ ≫ j` and `i` a monomorphism. If every pair of maps `a : Spec A ⟶ X`, `b : Spec A ⟶ Z`
over `Spec R` with `a ≫ f = b ≫ j`, for an `R`-algebra `A`, lifts to `c : Spec A ⟶ W` with
`c ≫ i = a` and `c ≫ φ = b`, then the square of underlying schemes is a pullback
(`AlgSpecPoints.isPullback_of_lift`).

The lift from a general test scheme `T` glues the affine lifts through the functor of points of
`T` on `R`-algebras (`algSpecPointsEquiv`); the lifts are compatible because `i` is a
monomorphism. This is the Yoneda principle for schemes over an affine base, restricted to affine
test schemes. It is not specific to the Grassmannian; its consumer is the chart description of the
Plücker morphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.AlgSpecPoints

variable {R : CommRingCat.{u}} {W X Y Z : Over (Spec R)}

/-- The lifting property on affine points extends to all schemes over `Spec R`. -/
theorem exists_lift_of_lift (i : W ⟶ X) (φ : W ⟶ Z) (f : X ⟶ Y) (j : Z ⟶ Y) [Mono i]
    (H : ∀ (A : CommAlgCat.{u} R) (a : (algSpec R).obj (op A) ⟶ X)
      (b : (algSpec R).obj (op A) ⟶ Z), a ≫ f = b ≫ j →
        ∃ c : (algSpec R).obj (op A) ⟶ W, c ≫ i = a ∧ c ≫ φ = b)
    (T : Over (Spec R)) (a : T ⟶ X) (b : T ⟶ Z) (hab : a ≫ f = b ≫ j) :
    ∃ c : T ⟶ W, c ≫ i = a ∧ c ≫ φ = b := by
  have hlift : ∀ (A : CommAlgCat.{u} R) (v : (algSpec R).obj (op A) ⟶ T),
      (v ≫ a) ≫ f = (v ≫ b) ≫ j := fun A v => by
    rw [Category.assoc, Category.assoc, hab]
  let c₀ : ∀ (A : CommAlgCat.{u} R) (_ : (algSpec R).obj (op A) ⟶ T),
      (algSpec R).obj (op A) ⟶ W := fun A v => (H A _ _ (hlift A v)).choose
  have hc₀ : ∀ A v, c₀ A v ≫ i = v ≫ a ∧ c₀ A v ≫ φ = v ≫ b := fun A v =>
    (H A _ _ (hlift A v)).choose_spec
  let α : algSpecPoints T ⟶ algSpecPoints W :=
    { app := fun A => TypeCat.ofHom fun v => c₀ A v
      naturality := fun A B h => by
        ext v
        change c₀ B ((algSpec R).map h.op ≫ v) = (algSpec R).map h.op ≫ c₀ A v
        rw [← cancel_mono i]
        simp only [Category.assoc, (hc₀ A v).1, (hc₀ B ((algSpec R).map h.op ≫ v)).1] }
  refine ⟨(algSpecPointsEquiv T W).symm α, ?_, ?_⟩
  · refine hom_ext_of_algSpec fun A v => ?_
    rw [← Category.assoc, show v ≫ (algSpecPointsEquiv T W).symm α = c₀ A v from
      comp_glueHom α v]
    exact (hc₀ A v).1
  · refine hom_ext_of_algSpec fun A v => ?_
    rw [← Category.assoc, show v ≫ (algSpecPointsEquiv T W).symm α = c₀ A v from
      comp_glueHom α v]
    exact (hc₀ A v).2

/-- **A commutative square over `Spec R` with the lifting property on affine points is a pullback
of schemes**, when its first map is a monomorphism. -/
theorem isPullback_of_lift (i : W ⟶ X) (φ : W ⟶ Z) (f : X ⟶ Y) (j : Z ⟶ Y) [Mono i]
    (w : i ≫ f = φ ≫ j)
    (H : ∀ (A : CommAlgCat.{u} R) (a : (algSpec R).obj (op A) ⟶ X)
      (b : (algSpec R).obj (op A) ⟶ Z), a ≫ f = b ≫ j →
        ∃ c : (algSpec R).obj (op A) ⟶ W, c ≫ i = a ∧ c ≫ φ = b) :
    IsPullback i.left φ.left f.left j.left := by
  have hw : i.left ≫ f.left = φ.left ≫ j.left := by
    rw [← Over.comp_left, w, Over.comp_left]
  have hsnd : ∀ s : PullbackCone f.left j.left,
      s.snd ≫ Z.hom = (Over.mk (s.fst ≫ X.hom)).hom := fun s => by
    change s.snd ≫ Z.hom = s.fst ≫ X.hom
    rw [← Over.w j, ← Category.assoc, ← s.condition, Category.assoc, Over.w f]
  let c : ∀ s : PullbackCone f.left j.left, Over.mk (s.fst ≫ X.hom) ⟶ W := fun s =>
    (exists_lift_of_lift i φ f j H (Over.mk (s.fst ≫ X.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd (hsnd s)) (Over.OverMorphism.ext s.condition)).choose
  have hc : ∀ s, (c s).left ≫ i.left = s.fst ∧ (c s).left ≫ φ.left = s.snd := fun s => by
    obtain ⟨h₁, h₂⟩ := (exists_lift_of_lift i φ f j H (Over.mk (s.fst ≫ X.hom))
      (Over.homMk s.fst rfl) (Over.homMk s.snd (hsnd s))
      (Over.OverMorphism.ext s.condition)).choose_spec
    exact ⟨congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw (fun s => (c s).left)
    (fun s => (hc s).1) (fun s => (hc s).2) (fun s m hm _ => ?_))
  rw [← cancel_mono i.left, hm, (hc s).1]

end AlgebraicGeometry.AlgSpecPoints
