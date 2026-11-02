/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Original adjuncts through a conjugate composition comparison

The existing conjugate-unit equation computes the adjunct of a composite
through its original left and right comparisons. This uses the given
adjunctions and maps, with independent category universes.
-/

@[expose] public section

namespace CategoryTheory.Adjunction.RepresentedCoherence

universe uA vA uB vB uC vC

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A}

/-- The original composite adjunct is determined by the actual conjugate
comparisons and the two original adjuncts. -/
theorem homEquiv_comp (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₀ : L₀ ⊣ R₀)
    (c : L₀ ⟶ L₁ ⋙ L₂) (d : R₂ ⋙ R₁ ⟶ R₀)
    (hc : conjugateEquiv (a₁.comp a₂) a₀ c = d)
    (X : A) (Y : B) (Z : C) (r : L₁.obj X ⟶ Y) (s : L₂.obj Y ⟶ Z) :
    a₀.homEquiv X Z (c.app X ≫ L₂.map r ≫ s) =
      a₁.homEquiv X Y r ≫ R₁.map (a₂.homEquiv Y Z s) ≫ d.app Z := by
  let k : (L₁ ⋙ L₂).obj X ⟶ Z := L₂.map r ≫ s
  have hu := unit_conjugateEquiv (a₁.comp a₂) a₀ c X
  rw [hc] at hu
  have hk : a₀.homEquiv X Z (c.app X ≫ k) =
      (a₁.comp a₂).homEquiv X Z k ≫ d.app Z := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
    calc
      _ = (a₀.unit.app X ≫ R₀.map (c.app X)) ≫ R₀.map k :=
        (Category.assoc _ _ _).symm
      _ = ((a₁.comp a₂).unit.app X ≫ d.app ((L₁ ⋙ L₂).obj X)) ≫ R₀.map k :=
        congrArg (fun q => q ≫ R₀.map k) hu.symm
      _ = _ := by rw [Category.assoc, ← d.naturality k, ← Category.assoc]
  calc
    _ = (a₁.comp a₂).homEquiv X Z k ≫ d.app Z := hk
    _ = _ := by
      rw [Adjunction.comp_homEquiv]
      change a₁.homEquiv X (R₂.obj Z) (a₂.homEquiv (L₁.obj X) Z (L₂.map r ≫ s)) ≫
        d.app Z = _
      rw [a₂.homEquiv_naturality_left, a₁.homEquiv_naturality_right]
      exact Category.assoc _ _ _

section OverPullback

open CategoryTheory.Limits

universe uT vT

variable {T : Type uT} [Category.{vT} T] {X Y Z : T}
  (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g]

/-- The original adjunction-defined Over compositor has the literal
iterated pullback projection after its inverse. -/
theorem overPullbackComp_inv_fst (A : Over Z) :
    ((Over.pullbackComp f g).inv.app A).left ≫ pullback.fst A.hom (f ≫ g) =
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g := by
  have h := conjugateEquiv_counit ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom A
  simpa [Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit_app,
    Category.assoc] using congrArg (fun q => q.left) h

/-- Forgetting a restricted Over compositor gives the SAME original full-Over
compositor. The equality is proved on its actual pullback projections. -/
theorem forget_pullbackComp_hom (P Q : MorphismProperty T) [Q.IsMultiplicative]
    [Q.IsStableUnderBaseChange] [Q.RespectsIso]
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) :
    (MorphismProperty.Over.forget P Q X).map
        ((MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app A) =
      (Over.pullbackComp f g).hom.app ((MorphismProperty.Over.forget P Q Z).obj A) := by
  let V := (MorphismProperty.Over.forget P Q Z).obj A
  let c := Over.pullbackComp f g
  let s : (Over.pullback (f ≫ g)).obj V ⟶
      (Over.pullback f).obj ((Over.pullback g).obj V) :=
    (MorphismProperty.Over.forget P Q X).map
      ((MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app A)
  change s = c.hom.app V
  apply (cancel_mono (c.inv.app V)).mp
  rw [Iso.hom_inv_id_app]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (s.left ≫ (c.inv.app V).left) ≫ pullback.fst V.hom (f ≫ g) =
      (𝟙 _) ≫ pullback.fst V.hom (f ≫ g)
    rw [Category.id_comp, Category.assoc, overPullbackComp_inv_fst]
    exact MorphismProperty.Over.pullbackComp_left_fst_fst (P := P) (Q := Q) f g A
  · change (s ≫ c.inv.app V).left ≫ ((Over.pullback (f ≫ g)).obj V).hom =
      (𝟙 _) ≫ ((Over.pullback (f ≫ g)).obj V).hom
    rw [Category.id_comp]
    exact Over.w (s ≫ c.inv.app V)

end OverPullback

end CategoryTheory.Adjunction.RepresentedCoherence
