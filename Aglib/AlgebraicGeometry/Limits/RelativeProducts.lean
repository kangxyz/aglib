/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Actual relative squares of a limiting scheme diagram

Taking the relative self-product of a diagram over a fixed scheme preserves a
specified nonempty underlying limit. The cone point is the original native
pullback of the limiting structural map with itself. Its projections are the
original componentwise pullback maps, not unspecified product comparisons.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeProducts

variable (S : Scheme.{u})

/-- The native relative self-product functor, viewed as schemes. -/
def selfProduct : Over S ⥤ Scheme.{u} where
  obj X := pullback X.hom X.hom
  map {X Y} q := pullback.map X.hom X.hom Y.hom Y.hom q.left q.left (𝟙 S)
    (by simp) (by simp)
  map_id X := by apply pullback.hom_ext <;> simp [pullback.map]
  map_comp f g := by apply pullback.hom_ext <;> simp [pullback.map]

/-- First projections of the native self-products. -/
def firstProjection : selfProduct S ⟶ Over.forget S where
  app X := pullback.fst X.hom X.hom
  naturality X Y q := by simp [selfProduct, pullback.map]

/-- Second projections of the native self-products. -/
def secondProjection : selfProduct S ⟶ Over.forget S where
  app X := pullback.snd X.hom X.hom
  naturality X Y q := by simp [selfProduct, pullback.map]

variable {S} {I : Type u} [Category.{u} I] (D : I ⥤ Over S)

/-- The actual relative-product diagram. -/
def diagram : I ⥤ Scheme.{u} := D ⋙ selfProduct S

/-- The actual relative-product cone. -/
def cone (c : Cone D) : Cone (diagram D) := (selfProduct S).mapCone c

/-- Project an arbitrary cone to its first components. -/
def firstCone (s : Cone (diagram D)) : Cone (D ⋙ Over.forget S) :=
  (Cone.postcompose (Functor.whiskerLeft D (firstProjection S))).obj s

/-- Project an arbitrary cone to its second components. -/
def secondCone (s : Cone (diagram D)) : Cone (D ⋙ Over.forget S) :=
  (Cone.postcompose (Functor.whiskerLeft D (secondProjection S))).obj s

variable (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))

/-- The first component of the original universal lift. -/
lemma lift_first_fac (s : Cone (diagram D)) (i : I) :
    hc.lift (firstCone D s) ≫ (c.π.app i).left =
      s.π.app i ≫ pullback.fst (D.obj i).hom (D.obj i).hom := hc.fac _ _

/-- The second component of the original universal lift. -/
lemma lift_second_fac (s : Cone (diagram D)) (i : I) :
    hc.lift (secondCone D s) ≫ (c.π.app i).left =
      s.π.app i ≫ pullback.snd (D.obj i).hom (D.obj i).hom := hc.fac _ _

/-- The two component lifts agree over the original base. -/
lemma lift_condition [Nonempty I] (s : Cone (diagram D)) :
    hc.lift (firstCone D s) ≫ c.pt.hom = hc.lift (secondCone D s) ≫ c.pt.hom := by
  let i : I := Classical.arbitrary I
  let a : s.pt ⟶ c.pt.left := hc.lift (firstCone D s)
  let b : s.pt ⟶ c.pt.left := hc.lift (secondCone D s)
  change a ≫ c.pt.hom = b ≫ c.pt.hom
  have hw : (c.π.app i).left ≫ (D.obj i).hom = c.pt.hom := (c.π.app i).w
  have ha : a ≫ (c.π.app i).left =
      s.π.app i ≫ pullback.fst (D.obj i).hom (D.obj i).hom := lift_first_fac D c hc s i
  have hb : b ≫ (c.π.app i).left =
      s.π.app i ≫ pullback.snd (D.obj i).hom (D.obj i).hom := lift_second_fac D c hc s i
  rw [← hw, ← Category.assoc, ← Category.assoc, ha, hb]
  simp only [Category.assoc, pullback.condition]

/-- The actual relative-product cone is limiting. -/
def isLimitCone [Nonempty I] : IsLimit (cone D c) where
  lift s := pullback.lift (hc.lift (firstCone D s)) (hc.lift (secondCone D s))
    (lift_condition D c hc s)
  fac s i := by
    apply pullback.hom_ext
    · simpa [cone, selfProduct, pullback.map, Category.assoc] using lift_first_fac D c hc s i
    · simpa [cone, selfProduct, pullback.map, Category.assoc] using lift_second_fac D c hc s i
  uniq s m hm := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]
      apply hc.hom_ext
      intro i
      have h := congrArg (fun q ↦ q ≫ pullback.fst (D.obj i).hom (D.obj i).hom) (hm i)
      calc
        _ = s.π.app i ≫ pullback.fst (D.obj i).hom (D.obj i).hom := by
          simpa [cone, selfProduct, pullback.map, Category.assoc] using h
        _ = _ := (lift_first_fac D c hc s i).symm
    · simp only [pullback.lift_snd]
      apply hc.hom_ext
      intro i
      have h := congrArg (fun q ↦ q ≫ pullback.snd (D.obj i).hom (D.obj i).hom) (hm i)
      calc
        _ = s.π.app i ≫ pullback.snd (D.obj i).hom (D.obj i).hom := by
          simpa [cone, selfProduct, pullback.map, Category.assoc] using h
        _ = _ := (lift_second_fac D c hc s i).symm

instance map_isClosedImmersion
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q).left]
    {i j : I} (q : i ⟶ j) : IsClosedImmersion ((diagram D).map q) := by
  change IsClosedImmersion (pullback.map (D.obj i).hom (D.obj i).hom
    (D.obj j).hom (D.obj j).hom (D.map q).left (D.map q).left (𝟙 S)
    (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
    (D.map q).w.symm (D.map q).w.symm

instance map_isAffineHom
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q).left]
    {i j : I} (q : i ⟶ j) : IsAffineHom ((diagram D).map q) := by
  change IsAffineHom (pullback.map (D.obj i).hom (D.obj i).hom
    (D.obj j).hom (D.obj j).hom (D.map q).left (D.map q).left (𝟙 S)
    (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @IsAffineHom) inferInstance inferInstance
    (D.map q).w.symm (D.map q).w.symm

instance obj_compactSpace [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj i).left] (i : I) : CompactSpace ((diagram D).obj i) := by
  change CompactSpace (pullback (D.obj i).hom (D.obj i).hom : Scheme)
  infer_instance

instance obj_quasiSeparatedSpace [∀ i, QuasiSeparatedSpace (D.obj i).left] (i : I) :
    QuasiSeparatedSpace ((diagram D).obj i) := by
  change QuasiSeparatedSpace (pullback (D.obj i).hom (D.obj i).hom : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.obj i).hom (D.obj i).hom)

end AlgebraicGeometry.Scheme.RelativeProducts
