/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationRoots
public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationPoint
public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup.RootsInclusion

/-! The fixed-second-slot character of the original Cartier root evaluation. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]
  (T : FScheme k) (p : T ⟶ (dualGroup G).X)
  (n : ℕ) (hn : (𝟙 G.X) ^ n = 1)

local notation "H" => Functor.obj (Functor.mapGrp (Over.pullback (Over.hom T))) G
local notation "U" => Functor.obj (Over.map (Over.hom T)) (Grp.X H)

/-- The root evaluation with its second argument fixed, in the original relative group. -/
def characterRootsMap : (H).X ⟶ MultiplicativeGroup.rootsScheme T.left n :=
  let adj := Over.mapPullbackAdj T.hom
  let x : U ⟶ G.X := adj.counit.app G.X
  let t : U ⟶ T := Over.homMk (H).X.hom rfl
  let z := lift x (t ≫ p) ≫ evaluationRoots G n hn
  adj.homEquiv (H).X (MultiplicativeGroup.rootsScheme (Base k) n) z ≫
    (MultiplicativeBaseChange.rootsBaseChangeIso T.hom n).hom.hom.hom

/-- Its original root inclusion is the original Cartier character. -/
theorem characterRootsMap_comp_inclusion :
    characterRootsMap G T p n hn ≫ MultiplicativeGroup.rootsInclusion T.left n =
      (characterEquiv G T p).hom.hom := by
  let adj := Over.mapPullbackAdj T.hom
  let x : U ⟶ G.X := adj.counit.app G.X
  let t : U ⟶ T := Over.homMk (H).X.hom rfl
  let w := lift x (t ≫ p)
  let z := w ≫ evaluationRoots G n hn
  let a := adj.homEquiv (H).X (MultiplicativeGroup.rootsScheme (Base k) n) z
  have hl : w.left = groupPullbackBaseMap G p := by
    apply pullback.hom_ext
    · simp only [w, Over.lift_left, pullback.lift_fst]
      change x.left = groupPullbackBaseMap G p ≫ pullback.fst G.X.hom (dualGroup G).X.hom
      rw [groupPullbackBaseMap_fst]
      simp only [x, adj, Over.mapPullbackAdj_counit_app, Over.homMk_left]
      rfl
    · simp only [w, Over.lift_left, pullback.lift_snd]
      change t.left ≫ p.left = groupPullbackBaseMap G p ≫
          pullback.snd G.X.hom (dualGroup G).X.hom
      rw [groupPullbackBaseMap_snd]
      rfl
  have ha := congrArg Subtype.val
    (MultiplicativeBaseChange.rootsBaseChangeIso_sections T.hom n (H).X a)
  change (MultiplicativeGroup.rootsHomEquiv T.left n (H).X
      (characterRootsMap G T p n hn)).val = _ at ha
  have hb : (adj.homEquiv (H).X (MultiplicativeGroup.rootsScheme (Base k) n)).symm a = z :=
    (adj.homEquiv (H).X _).symm_apply_apply z
  rw [hb] at ha
  apply (MultiplicativeGroup.sectionsUnitsEquiv T.left (H).X).injective
  refine ha.trans ?_
  change MultiplicativeGroup.sectionsUnitsEquiv (Base k) U
      (z ≫ MultiplicativeGroup.rootsInclusion (Base k) n) = _
  have hz := comp_evaluationRoots_comp_inclusion G n hn w
  refine (congrArg (MultiplicativeGroup.sectionsUnitsEquiv (Base k) U) hz).trans ?_
  change MultiplicativeGroup.affineHomUnits (H).X.left
      ((w ≫ evaluation G).left ≫ prod.snd) =
    MultiplicativeGroup.affineHomUnits (H).X.left ((characterEquiv G T p).hom.hom.left ≫ prod.snd)
  let f := (evaluation G).left
  let j : (MultiplicativeGroup.scheme (Base k)).left ⟶ MultiplicativeGroup.affineScheme :=
    prod.snd
  have h₁ : ((w ≫ evaluation G).left ≫ prod.snd) = w.left ≫ f ≫ j :=
    Category.assoc w.left f j
  have h₂ : w.left ≫ f ≫ j = groupPullbackBaseMap G p ≫ f ≫ j :=
    congrArg (fun s => s ≫ f ≫ j) hl
  have h₃ : groupPullbackBaseMap G p ≫ f ≫ j = (characterEquiv G T p).hom.hom.left ≫ prod.snd :=
    (characterOfPoint_evaluation G T p).symm
  exact congrArg (MultiplicativeGroup.affineHomUnits (H).X.left) (h₁.trans (h₂.trans h₃))

/-- The actual root-valued Cartier character, with the original group laws. -/
def characterRoots : H ⟶ MultiplicativeGroup.rootsGroupScheme T.left n := by
  let r : (H).X ⟶ (MultiplicativeGroup.rootsGroupScheme T.left n).X :=
    characterRootsMap G T p n hn
  let i := MultiplicativeGroup.rootsInclusionHom T.left n
  have he : r ≫ i.hom.hom = (characterEquiv G T p).hom.hom :=
    characterRootsMap_comp_inclusion G T p n hn
  have hi : IsMonHom (r ≫ i.hom.hom) := by
    rw [he]
    infer_instance
  letI : IsMonHom r := MultiplicativeGroup.isMonHom_of_rootsInclusion_comp r
  exact Grp.homMk r

@[simp] theorem characterRoots_comp_inclusion :
    characterRoots G T p n hn ≫ MultiplicativeGroup.rootsInclusionHom T.left n =
      characterEquiv G T p := by
  apply Grp.hom_ext
  exact characterRootsMap_comp_inclusion G T p n hn

/-- The original root evaluation on two points is the unit of the same
fixed-second-slot root character restricted to the original first point. -/
theorem evaluationRoots_units_eq_characterRoots_on_section (x : T ⟶ G.X) :
    (MultiplicativeGroup.rootsHomEquiv (Base k) n T
        (lift x p ≫ evaluationRoots G n hn)).val =
      Units.map (lift x (𝟙 T)).left.appTop.hom.toMonoidHom
        (MultiplicativeGroup.rootsHomEquiv T.left n (H).X
          (characterRoots G T p n hn).hom.hom).val := by
  let e := MultiplicativeGroup.sectionsUnitsEquiv (Base k) T
  let eT := MultiplicativeGroup.sectionsUnitsEquiv T.left (H).X
  let u := Units.map (lift x (𝟙 T)).left.appTop.hom.toMonoidHom
  have he := congrArg e (comp_evaluationRoots_comp_inclusion G n hn (lift x p))
  have hχ := congrArg eT (characterRootsMap_comp_inclusion G T p n hn)
  have hv := evaluation_units_eq_character_on_section G T x p
  exact he.trans (hv.trans (congrArg u hχ.symm))

omit p in
/-- The original Cartier points represent all root-valued characters at a level killing G. -/
def characterRootsEquiv :
    (T ⟶ (dualGroup G).X) ≃ (H ⟶ MultiplicativeGroup.rootsGroupScheme T.left n) := by
  let E := characterEquiv G T
  let i := MultiplicativeGroup.rootsInclusionHom T.left n
  let i' : (MultiplicativeGroup.rootsGroupScheme T.left n).X ⟶
      (MultiplicativeGroup.groupScheme T.left).X := i.hom.hom
  let : Mono i' := by
    change Mono (MultiplicativeGroup.rootsInclusion T.left n)
    exact inferInstanceAs
      (Mono (equalizer.ι (MultiplicativeGroup.powerMap T.left n)
        (MultiplicativeGroup.oneMap T.left)))
  apply Equiv.ofBijective (fun y => characterRoots G T y n hn)
  constructor
  · intro y z h
    apply E.injective
    exact (characterRoots_comp_inclusion G T y n hn).symm.trans
      ((congrArg (fun a => a ≫ i) h).trans (characterRoots_comp_inclusion G T z n hn))
  · intro c
    let y := E.symm (c ≫ i)
    have h : characterRoots G T y n hn ≫ i = c ≫ i :=
      (characterRoots_comp_inclusion G T y n hn).trans (E.apply_symm_apply (c ≫ i))
    refine ⟨y, ?_⟩
    apply Grp.hom_ext
    apply (cancel_mono i').mp
    exact congrArg (fun a => a.hom.hom) h

end AlgebraicGeometry.Scheme.Group.CartierDuality
