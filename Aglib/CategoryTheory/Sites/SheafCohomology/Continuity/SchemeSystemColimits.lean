/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-! # Tail colimits and the diagonal of a compatible system

A compatible coefficient system gives an arrow-indexed diagram: the value at
`i ⟶ j` is the sections at stage `j` of the coefficient from stage `i`.
Its tails are indexed by `Under i`. They do not form a covariant Grothendieck
construction in `i`. Instead, filtered span completion proves directly that
compatible tail colimits followed by an outer colimit compute the arrow colimit.
The identity-arrow inclusion is final, so this is also the original diagonal
colimit. All comparison legs are retained, not merely an abstract isomorphism.
-/

@[expose] public noncomputable section

universe u v w z

namespace CategoryTheory

open Limits

namespace SchemeSystemColimits

variable {I : Type u} [Category.{v} I] {C : Type w} [Category.{z} C]

/-- The diagonal retaining the identity arrow at each stage. -/
abbrev diagonal : I ⥤ Arrow I where
  obj i := Arrow.mk (𝟙 i)
  map f := Arrow.homMk f f (by simp)
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by apply Arrow.hom_ext <;> rfl

/-- Codomain is left adjoint to the identity-arrow inclusion. -/
def codomainAdjunction : (Arrow.rightFunc : Arrow I ⥤ I) ⊣ diagonal :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun a i =>
        { toFun := fun f => Arrow.homMk (a.hom ≫ f) f (Category.comp_id _)
          invFun := fun f => f.right
          left_inv := fun _ => rfl
          right_inv := fun f => by
            apply Arrow.hom_ext
            · simpa using (Arrow.w f).symm
            · rfl }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun f g => by
        apply Arrow.hom_ext
        · exact (Category.assoc _ f g).symm
        · rfl }

instance : Functor.Final (diagonal : I ⥤ Arrow I) :=
  Functor.final_of_adjunction codomainAdjunction

/-- The actual tail inclusion, with its source fixed and target varying. -/
abbrev tailToArrow (i : I) : Under i ⥤ Arrow I where
  obj a := Arrow.mk a.hom
  map f := Arrow.homMk (𝟙 i) f.right (by simp)
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

variable (D : Arrow I ⥤ C) (S : I ⥤ C)
  (η : D ⟶ Arrow.leftFunc ⋙ S)

/-- A tail leg with its source and target made explicit. -/
def leg (a : Arrow I) : D.obj a ⟶ S.obj a.left := η.app a

@[reassoc]
lemma leg_naturality {a b : Arrow I} (f : a ⟶ b) :
    D.map f ≫ leg D S η b = leg D S η a ≫ S.map f.left :=
  η.naturality f

/-- The tail cocone into the proposed fixed-source limit sections. -/
def tailCocone (i : I) : Cocone (tailToArrow i ⋙ D) where
  pt := S.obj i
  ι :=
    { app := fun a => leg D S η (Arrow.mk a.hom)
      naturality := fun a b f => by
        change D.map ((tailToArrow i).map f) ≫ leg D S η (Arrow.mk b.hom) =
          leg D S η (Arrow.mk a.hom) ≫ 𝟙 (S.obj i)
        exact (leg_naturality D S η ((tailToArrow i).map f)).trans
          (congrArg (leg D S η (Arrow.mk a.hom) ≫ ·) (S.map_id i)) }

/-- A cocone leg with its constant-functor target made explicit. -/
def coconeLeg {K : Type*} [Category* K] {T : K ⥤ C} (c : Cocone T) (i : K) :
    T.obj i ⟶ c.pt := c.ι.app i

@[reassoc]
lemma coconeLeg_naturality {K : Type*} [Category* K] {T : K ⥤ C}
    (c : Cocone T) {i j : K} (f : i ⟶ j) :
    T.map f ≫ coconeLeg c j = coconeLeg c i := c.w f

/-- Composing the actual tail legs with an outer cocone. -/
def outerCocone (c : Cocone S) : Cocone D where
  pt := c.pt
  ι :=
    { app := fun a => leg D S η a ≫ coconeLeg c a.left
      naturality := fun a b f => by
        change D.map f ≫ (leg D S η b ≫ coconeLeg c b.left) =
          (leg D S η a ≫ coconeLeg c a.left) ≫ 𝟙 c.pt
        rw [Category.comp_id, ← Category.assoc, leg_naturality, Category.assoc]
        exact congrArg (leg D S η a ≫ ·) (coconeLeg_naturality c f.left) }

variable (hη : ∀ i, IsColimit (tailCocone D S η i))

/-- Factoring a cocone on the full arrow diagram through a tail. -/
def tailDesc (c : Cocone D) (i : I) : S.obj i ⟶ c.pt :=
  (hη i).desc (c.whisker (tailToArrow i))

@[reassoc]
lemma tailDesc_fac (c : Cocone D) (a : Arrow I) :
    leg D S η a ≫ tailDesc D S η hη c a.left = coconeLeg c a := by
  cases a with
  | mk i j f => exact (hη i).fac (c.whisker (tailToArrow i)) (Under.mk f)

variable [IsFilteredOrEmpty I]

/-- Filtered span completion is precisely the compatibility needed to collapse tails. -/
lemma tailDesc_naturality (c : Cocone D) {i j : I} (f : i ⟶ j) :
    S.map f ≫ tailDesc D S η hη c j = tailDesc D S η hη c i := by
  apply (hη i).hom_ext
  intro a
  change leg D S η (Arrow.mk a.hom) ≫ (S.map f ≫ _) =
    leg D S η (Arrow.mk a.hom) ≫ _
  obtain ⟨k, g, h, e⟩ := IsFiltered.span a.hom f
  let sq : Arrow.mk a.hom ⟶ Arrow.mk h := Arrow.homMk f g e.symm
  have hn := leg_naturality D S η sq
  change D.map sq ≫ leg D S η (Arrow.mk h) = leg D S η (Arrow.mk a.hom) ≫ S.map f at hn
  have hj : leg D S η (Arrow.mk h) ≫ tailDesc D S η hη c j =
      coconeLeg c (Arrow.mk h) := tailDesc_fac D S η hη c (Arrow.mk h)
  have hi : leg D S η (Arrow.mk a.hom) ≫ tailDesc D S η hη c i =
      coconeLeg c (Arrow.mk a.hom) := tailDesc_fac D S η hη c (Arrow.mk a.hom)
  rw [← Category.assoc, ← hn, Category.assoc, hj, hi]
  exact coconeLeg_naturality c sq

/-- A cocone on the arrow diagram induces an actual compatible outer cocone. -/
def tailDescCocone (c : Cocone D) : Cocone S where
  pt := c.pt
  ι :=
    { app := tailDesc D S η hη c
      naturality := fun _ _ f => by
        simpa using tailDesc_naturality D S η hη c f }

/-- Tail colimits followed by the outer colimit compute the arrow-indexed colimit. -/
def isColimitOuterCocone (c : Cocone S) (hc : IsColimit c) :
    IsColimit (outerCocone D S η c) where
  desc s := hc.desc (tailDescCocone D S η hη s)
  fac s a := by
    let d : c.pt ⟶ s.pt := hc.desc (tailDescCocone D S η hη s)
    change (leg D S η a ≫ coconeLeg c a.left) ≫ d = coconeLeg s a
    have hf : coconeLeg c a.left ≫ d = tailDesc D S η hη s a.left := hc.fac _ _
    rw [Category.assoc, hf]
    exact tailDesc_fac D S η hη s a
  uniq s m hm := by
    let m' : c.pt ⟶ s.pt := m
    let d : c.pt ⟶ s.pt := hc.desc (tailDescCocone D S η hη s)
    change m' = d
    apply hc.hom_ext
    intro i
    change coconeLeg c i ≫ m' = coconeLeg c i ≫ d
    have hf : coconeLeg c i ≫ d = tailDesc D S η hη s i := hc.fac _ _
    rw [hf]
    apply (hη i).hom_ext
    intro a
    change leg D S η (Arrow.mk a.hom) ≫ (coconeLeg c i ≫ m') =
      leg D S η (Arrow.mk a.hom) ≫ tailDesc D S η hη s i
    have hi : leg D S η (Arrow.mk a.hom) ≫ tailDesc D S η hη s i =
        coconeLeg s (Arrow.mk a.hom) := tailDesc_fac D S η hη s (Arrow.mk a.hom)
    rw [hi, ← Category.assoc]
    exact hm (Arrow.mk a.hom)

/-- The general compatible-system diagonal is a colimit, with the canonical legs
`η.app (id_i)` followed by the original outer cocone. -/
def isColimitDiagonal (c : Cocone S) (hc : IsColimit c) :
    IsColimit ((outerCocone D S η c).whisker diagonal) :=
  (Functor.Final.isColimitWhiskerEquiv diagonal _).symm
    (isColimitOuterCocone D S η hη c hc)

end SchemeSystemColimits

end CategoryTheory
