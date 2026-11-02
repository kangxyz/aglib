/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.RepresentedCoherence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Pasted pullback comparisons in the actual Over categories

The selected pullbacks and the native `Over.pullbackComp` are retained. Restriction
to the full morphism-property subcategory uses their original underlying arrows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.IsPullback

/-- A map between the same two cartesian squares is cartesian when it retains
both original projections and the original base factorization. -/
theorem of_two_pullback_projections
    {C : Type u} [Category.{v} C] {P Q A B V X : C}
    {p₁ : P ⟶ A} {p₂ : P ⟶ V} {q₁ : Q ⟶ B} {q₂ : Q ⟶ V}
    {f : A ⟶ X} {g : B ⟶ X} {j : V ⟶ X}
    (hP : IsPullback p₁ p₂ f j) (hQ : IsPullback q₁ q₂ g j)
    (k : P ⟶ Q) (h : A ⟶ B) (hbase : h ≫ g = f)
    (hk₁ : k ≫ q₁ = p₁ ≫ h) (hk₂ : k ≫ q₂ = p₂) :
    IsPullback k p₁ q₁ h := by
  have houter : IsPullback (k ≫ q₂) p₁ j (h ≫ g) := by
    rw [hk₂, hbase]
    exact hP.flip
  exact houter.of_right hk₁ hQ.flip

end CategoryTheory.IsPullback

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Base change followed by postcomposition in a pullback square. -/
def pullbackPostcomposeIso {X S T : C} (f : X ⟶ S) (g : T ⟶ S) :
    pullback (Limits.pullback.fst g f) ⋙ map (Limits.pullback.snd g f) ≅
      map g ⋙ pullback f :=
  NatIso.ofComponents
    (fun U => isoMk (pullbackRightPullbackFstIso g f U.hom)
      (pullbackRightPullbackFstIso_hom_snd g f U.hom))
    (fun {U V} a => by
      apply OverMorphism.ext
      change Limits.pullback.lift (Limits.pullback.fst U.hom (Limits.pullback.fst g f) ≫
          a.left) (Limits.pullback.snd U.hom (Limits.pullback.fst g f)) _ ≫
            (pullbackRightPullbackFstIso g f V.hom).hom =
        (pullbackRightPullbackFstIso g f U.hom).hom ≫
          Limits.pullback.lift (Limits.pullback.fst (U.hom ≫ g) f ≫ a.left)
            (Limits.pullback.snd (U.hom ≫ g) f) _
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst,
          Limits.pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
      · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
          Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd])

/-- The actual pasted comparison retains the original source projection. -/
@[reassoc]
theorem pullbackPostcomposeIso_hom_fst {X S T : C} (f : X ⟶ S) (g : T ⟶ S)
    (U : Over T) :
    ((pullbackPostcomposeIso f g).hom.app U).left ≫
        Limits.pullback.fst (U.hom ≫ g) f =
      Limits.pullback.fst U.hom (Limits.pullback.fst g f) :=
  pullbackRightPullbackFstIso_hom_fst g f U.hom

/-- The actual pasted comparison retains the original base projection. -/
@[reassoc]
theorem pullbackPostcomposeIso_hom_snd {X S T : C} (f : X ⟶ S) (g : T ⟶ S)
    (U : Over T) :
    ((pullbackPostcomposeIso f g).hom.app U).left ≫
        Limits.pullback.snd (U.hom ≫ g) f =
      Limits.pullback.snd U.hom (Limits.pullback.fst g f) ≫ Limits.pullback.snd g f :=
  pullbackRightPullbackFstIso_hom_snd g f U.hom

/-- The first projection as a natural transformation on the original Over category. -/
def pullbackFst {X S : C} (f : X ⟶ S) :
    pullback f ⋙ forget X ⟶ forget S where
  app U := Limits.pullback.fst U.hom f
  naturality _ _ _ := Limits.pullback.lift_fst _ _ _

/-- The whole source projection commutes with the original pasted comparison. -/
theorem pullbackPostcomposeIso_fst {X S T : C} (f : X ⟶ S) (g : T ⟶ S) :
    Functor.whiskerRight (pullbackPostcomposeIso f g).hom (forget X) ≫
        Functor.whiskerLeft (map g) (pullbackFst f) =
      pullbackFst (Limits.pullback.fst g f) := by
  ext U
  exact pullbackPostcomposeIso_hom_fst f g U

/-- The original Over adjunction counit has the selected first pullback projection. -/
theorem mapPullbackAdj_counit_left {X S : C} (f : X ⟶ S) (U : Over S) :
    ((mapPullbackAdj f).counit.app U).left = Limits.pullback.fst U.hom f := by
  simp [mapPullbackAdj_counit_app]

/-- The native compositor preserves the source projection after its forward arrow. -/
@[reassoc]
theorem pullbackComp_hom_fst_fst {X S T : C} (f : S ⟶ X) (g : T ⟶ S)
    (U : Over X) :
    ((pullbackComp g f).hom.app U).left ≫
        Limits.pullback.fst (Limits.pullback.snd U.hom f) g ≫
          Limits.pullback.fst U.hom f = Limits.pullback.fst U.hom (g ≫ f) := by
  have h := Adjunction.RepresentedCoherence.overPullbackComp_inv_fst g f U
  have h' := congrArg (fun k => ((pullbackComp g f).hom.app U).left ≫ k) h
  simpa only [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id_app,
    Over.id_left, Category.id_comp] using h'.symm

/-- The native comparison of iterated base changes for a commuting square. -/
def pullbackSquareIso {X S X' S' : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  (pullbackComp f' g).symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => pullback k) h) ≪≫ pullbackComp g' f

/-- Equality transport retains the original source projection. -/
@[reassoc]
theorem pullback_eqToHom_fst {X S : C} {f g : X ⟶ S} (h : f = g) (U : Over S) :
    (eqToHom (congrArg (fun k => (pullback k).obj U) h)).left ≫
        Limits.pullback.fst U.hom g = Limits.pullback.fst U.hom f := by
  subst g
  exact Category.id_comp _

/-- The actual square comparison preserves projection to the original test object. -/
@[reassoc]
theorem pullbackSquareIso_fst_fst {X S X' S' : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (U : Over S) :
    ((pullbackSquareIso f f' g g' h).hom.app U).left ≫
        Limits.pullback.fst (Limits.pullback.snd U.hom f) g' ≫
          Limits.pullback.fst U.hom f =
      Limits.pullback.fst (Limits.pullback.snd U.hom g) f' ≫
        Limits.pullback.fst U.hom g := by
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Over.comp_left, Category.assoc, pullbackComp_hom_fst_fst, eqToIso.hom, eqToHom_app]
  exact (congrArg
    (fun k : ((pullback (f' ≫ g)).obj U).left ⟶ U.left =>
      ((pullbackComp f' g).inv.app U).left ≫ k)
    (pullback_eqToHom_fst h U)).trans
      (Adjunction.RepresentedCoherence.overPullbackComp_inv_fst f' g U)

/-- The pasted comparison respects both original postcomposition/pullback counits. -/
theorem pullbackPostcomposeIso_counit_app {X S T : C}
    (f : X ⟶ S) (g : T ⟶ S) (U : Over S) :
    (map (Limits.pullback.snd g f)).map
        ((pullbackSquareIso f (Limits.pullback.fst g f) g (Limits.pullback.snd g f)
          Limits.pullback.condition).hom.app U) ≫
        (mapPullbackAdj (Limits.pullback.snd g f)).counit.app ((pullback f).obj U) =
      (pullbackPostcomposeIso f g).hom.app ((pullback g).obj U) ≫
        (pullback f).map ((mapPullbackAdj g).counit.app U) := by
  let q := (pullbackSquareIso f (Limits.pullback.fst g f) g (Limits.pullback.snd g f)
    Limits.pullback.condition).hom.app U
  apply OverMorphism.ext
  simp only [Over.comp_left, map_map_left, pullback_map_left, mapPullbackAdj_counit_left]
  change q.left ≫ Limits.pullback.fst (Limits.pullback.snd U.hom f)
      (Limits.pullback.snd g f) =
    (pullbackRightPullbackFstIso g f (Limits.pullback.snd U.hom g)).hom ≫
      Limits.pullback.lift
        (Limits.pullback.fst (Limits.pullback.snd U.hom g ≫ g) f ≫
          Limits.pullback.fst U.hom g)
        (Limits.pullback.snd (Limits.pullback.snd U.hom g ≫ g) f) _
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    exact pullbackSquareIso_fst_fst f (Limits.pullback.fst g f) g
      (Limits.pullback.snd g f) Limits.pullback.condition U
  · have hw : q.left ≫ Limits.pullback.snd (Limits.pullback.snd U.hom f)
        (Limits.pullback.snd g f) =
        Limits.pullback.snd (Limits.pullback.snd U.hom g) (Limits.pullback.fst g f) := w q
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
    refine (congrArg (fun k => k ≫ Limits.pullback.snd g f) hw).trans ?_
    simp only [Category.assoc, Limits.pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd]

/-- The complete counit square is an equality of the actual natural transformations. -/
theorem pullbackPostcomposeIso_counit {X S T : C} (f : X ⟶ S) (g : T ⟶ S) :
    Functor.whiskerRight
        (pullbackSquareIso f (Limits.pullback.fst g f) g (Limits.pullback.snd g f)
          Limits.pullback.condition).hom (map (Limits.pullback.snd g f)) ≫
        (Functor.associator (pullback f) (pullback (Limits.pullback.snd g f))
          (map (Limits.pullback.snd g f))).hom ≫
        Functor.whiskerLeft (pullback f) (mapPullbackAdj (Limits.pullback.snd g f)).counit ≫
        (Functor.rightUnitor (pullback f)).hom =
      (Functor.associator (pullback g) (pullback (Limits.pullback.fst g f))
          (map (Limits.pullback.snd g f))).hom ≫
        Functor.whiskerLeft (pullback g) (pullbackPostcomposeIso f g).hom ≫
        (Functor.associator (pullback g) (map g) (pullback f)).inv ≫
        Functor.whiskerRight (mapPullbackAdj g).counit (pullback f) ≫
        (Functor.leftUnitor (pullback f)).hom := by
  apply NatTrans.ext
  funext U
  have h := congrArg
    (fun k : (((pullback g ⋙ pullback (Limits.pullback.fst g f)) ⋙
        map (Limits.pullback.snd g f)).obj U) ⟶ (pullback f).obj U =>
      k ≫ 𝟙 ((pullback f).obj U)) (pullbackPostcomposeIso_counit_app f g U)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Category.assoc] using h

/-- The identity terminal chart, postcomposed to the original Over category. -/
def postcomposeTerminalIso {S : C} (U : Over S) :
    (map U.hom).obj (mk (𝟙 U.left)) ≅ U :=
  isoMk (Iso.refl _) (by simp)

/-- The original inverse terminal comparison has its forced source projection.
The supplied arrow is retained; no terminal comparison is reselected. -/
theorem terminalPullback_fst {X S : C} (f : X ⟶ S)
    (t : mk (𝟙 X) ⟶ (pullback f).obj (mk (𝟙 S))) :
    t.left ≫ Limits.pullback.fst (𝟙 S) f = f := by
  have hw : t.left ≫ Limits.pullback.snd (𝟙 S) f = 𝟙 X := w t
  calc
    _ = t.left ≫ Limits.pullback.snd (𝟙 S) f ≫ f := by
      rw [← Limits.pullback.condition, Category.comp_id]
    _ = f := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ f) hw).trans (Category.id_comp f))

/-- The actual terminal arrow commutes with the original pasted-pullback comparison. -/
theorem pullbackPostcomposeIso_terminal {X S : C} (f : X ⟶ S) (U : Over S)
    (t : mk (𝟙 (Limits.pullback U.hom f)) ⟶
      (pullback (Limits.pullback.fst U.hom f)).obj (mk (𝟙 U.left))) :
    (postcomposeTerminalIso ((pullback f).obj U)).inv ≫
        (map (Limits.pullback.snd U.hom f)).map t ≫
        (pullbackPostcomposeIso f U.hom).hom.app (mk (𝟙 U.left)) =
      (pullback f).map (postcomposeTerminalIso U).inv := by
  apply OverMorphism.ext
  change (𝟙 _ ≫ t.left ≫
      (pullbackRightPullbackFstIso U.hom f (𝟙 U.left)).hom) =
    Limits.pullback.lift (Limits.pullback.fst U.hom f ≫ 𝟙 U.left)
      (Limits.pullback.snd U.hom f) _
  refine (Category.id_comp (t.left ≫
    (pullbackRightPullbackFstIso U.hom f (𝟙 U.left)).hom)).trans ?_
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst,
      Limits.pullback.lift_fst]
    exact (terminalPullback_fst (Limits.pullback.fst U.hom f) t).trans
      (Category.comp_id _).symm
  · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      Limits.pullback.lift_snd]
    have hw : t.left ≫ Limits.pullback.snd (𝟙 U.left) (Limits.pullback.fst U.hom f) =
        𝟙 (Limits.pullback U.hom f) := w t
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ Limits.pullback.snd U.hom f) hw).trans
        (Category.id_comp _))

end CategoryTheory.Over

namespace CategoryTheory.MorphismProperty.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (P : MorphismProperty C) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]

/-- Restrict the actual pasted comparison through the full inclusion into Over. -/
def pullbackPostcomposeIso {X S T : C} (f : X ⟶ S) (g : T ⟶ S) (hg : P g) :
    pullback P ⊤ (Limits.pullback.fst g f) ⋙
        map ⊤ (P.pullback_snd g f hg) ≅
      map ⊤ hg ⋙ pullback P ⊤ f :=
  NatIso.ofComponents
    (fun U => Over.isoMk (pullbackRightPullbackFstIso g f U.hom)
      (pullbackRightPullbackFstIso_hom_snd g f U.hom))
    (fun {U V} a => by
      apply (MorphismProperty.Over.forget P ⊤ X).map_injective
      exact (CategoryTheory.Over.pullbackPostcomposeIso f g).hom.naturality
        ((MorphismProperty.Over.forget P ⊤ T).map a))

/-- Forgetting the whole restricted comparison gives the same original natural map. -/
theorem forget_pullbackPostcomposeIso_hom {X S T : C}
    (f : X ⟶ S) (g : T ⟶ S) (hg : P g) :
    Functor.whiskerRight (pullbackPostcomposeIso P f g hg).hom
        (MorphismProperty.Over.forget P ⊤ X) =
      Functor.whiskerLeft (MorphismProperty.Over.forget P ⊤ T)
        (CategoryTheory.Over.pullbackPostcomposeIso f g).hom := by
  ext U
  rfl

/-- The original restricted compositor defines the same commuting-square comparison. -/
def pullbackSquareIso {X S X' S' : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    pullback P ⊤ g ⋙ pullback P ⊤ f' ≅ pullback P ⊤ f ⋙ pullback P ⊤ g' :=
  (pullbackComp (P := P) (Q := ⊤) f' g).symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => pullback P ⊤ k) h) ≪≫
      pullbackComp (P := P) (Q := ⊤) g' f

omit [P.IsStableUnderComposition] in
/-- The whole restricted square has the actual full-Over square as its image. -/
theorem forget_pullbackSquareIso_hom {X S X' S' : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    Functor.whiskerRight (pullbackSquareIso P f f' g g' h).hom
        (MorphismProperty.Over.forget P ⊤ X') =
      Functor.whiskerLeft (MorphismProperty.Over.forget P ⊤ S)
        (CategoryTheory.Over.pullbackSquareIso f f' g g' h).hom := by
  apply NatTrans.ext
  funext U
  have hi (a : X' ⟶ S') (b : S' ⟶ S) :
      (MorphismProperty.Over.forget P ⊤ X').map
          ((pullbackComp (P := P) (Q := ⊤) a b).inv.app U) =
        (CategoryTheory.Over.pullbackComp a b).inv.app
          ((MorphismProperty.Over.forget P ⊤ S).obj U) := by
    have hh := Adjunction.RepresentedCoherence.forget_pullbackComp_hom
      (f := a) (g := b) P ⊤ U
    have he : (MorphismProperty.Over.forget P ⊤ X').mapIso
          ((pullbackComp (P := P) (Q := ⊤) a b).app U) =
        (CategoryTheory.Over.pullbackComp a b).app
          ((MorphismProperty.Over.forget P ⊤ S).obj U) := by
      apply Iso.ext
      exact hh
    exact congrArg Iso.inv he
  simp only [pullbackSquareIso, CategoryTheory.Over.pullbackSquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, hi,
    Adjunction.RepresentedCoherence.forget_pullbackComp_hom, eqToIso.hom, eqToHom_app,
    eqToHom_map]

omit [P.IsStableUnderComposition] in
/-- Restriction preserves the entire original square projection law. -/
theorem pullbackSquareIso_fst_fst {X S X' S' : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (U : P.Over ⊤ S) :
    ((pullbackSquareIso P f f' g g' h).hom.app U).left ≫
        Limits.pullback.fst (Limits.pullback.snd U.hom f) g' ≫
          Limits.pullback.fst U.hom f =
      Limits.pullback.fst (Limits.pullback.snd U.hom g) f' ≫
        Limits.pullback.fst U.hom g := by
  have hh := congrArg (fun η => (η.app U).left)
    (forget_pullbackSquareIso_hom P f f' g g' h)
  exact (congrArg (fun k => k ≫
    Limits.pullback.fst (Limits.pullback.snd U.hom f) g' ≫ Limits.pullback.fst U.hom f)
      hh).trans
    (CategoryTheory.Over.pullbackSquareIso_fst_fst f f' g g' h
      ((MorphismProperty.Over.forget P ⊤ S).obj U))

/-- The original restricted counits satisfy the same pasted comparison equation. -/
theorem pullbackPostcomposeIso_counit_app {X S T : C}
    (f : X ⟶ S) (g : T ⟶ S) (hg : P g) (U : P.Over ⊤ S) :
    (map ⊤ (P.pullback_snd g f hg)).map
        ((pullbackSquareIso P f (Limits.pullback.fst g f) g (Limits.pullback.snd g f)
          Limits.pullback.condition).hom.app U) ≫
        (mapPullbackAdj P ⊤ (Limits.pullback.snd g f)
          (P.pullback_snd g f hg) trivial).counit.app ((pullback P ⊤ f).obj U) =
      (pullbackPostcomposeIso P f g hg).hom.app ((pullback P ⊤ g).obj U) ≫
        (pullback P ⊤ f).map ((mapPullbackAdj P ⊤ g hg trivial).counit.app U) := by
  apply MorphismProperty.Over.Hom.ext
  have hq := congrArg (fun η => (η.app U).left)
    (forget_pullbackSquareIso_hom P f (Limits.pullback.fst g f) g
      (Limits.pullback.snd g f) Limits.pullback.condition)
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app] at hq
  have h := congrArg (fun a => a.left)
    (CategoryTheory.Over.pullbackPostcomposeIso_counit_app f g
      ((MorphismProperty.Over.forget P ⊤ S).obj U))
  simp only [CategoryTheory.Over.comp_left, CategoryTheory.Over.map_map_left,
    CategoryTheory.Over.pullback_map_left, CategoryTheory.Over.mapPullbackAdj_counit_left] at h
  rw [← hq] at h
  exact h

end CategoryTheory.MorphismProperty.Over
