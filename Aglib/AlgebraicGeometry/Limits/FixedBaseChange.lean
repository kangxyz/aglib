/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Native base changes of an inverse system over a fixed scheme

The diagram, cone, and structural natural transformation below use the native
`Over.lift` and `Over.pullback`. The cone point is the original pullback and
its structural map is the original second projection. No approximation or
cartesianity premise is hidden in the limit construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FixedBaseChange

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {S T : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (b : T ⟶ S)

/-- The actual stagewise pullbacks over the fixed target. -/
def diagram : I ⥤ Scheme.{u} :=
  Over.lift D t ⋙ Over.pullback b ⋙ Over.forget T

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual second projections as a natural transformation. -/
def baseStructure : diagram D t b ⟶ (Functor.const I).obj T where
  app i := pullback.snd (t.app i) b
  naturality i j q := by
    change ((Over.pullback b).map ((Over.lift D t).map q)).left ≫
      ((Over.pullback b).obj ((Over.lift D t).obj j)).hom =
      ((Over.pullback b).obj ((Over.lift D t).obj i)).hom ≫ 𝟙 T
    simpa only [Category.comp_id] using
      (Over.w ((Over.pullback b).map ((Over.lift D t).map q)))

variable (c : Cone D) (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)

/-- The base-changed cone with point `pullback p b`. -/
def cone : Cone (diagram D t b) :=
  (Over.pullback b ⋙ Over.forget T).mapCone (Over.liftCone D t c p hp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The structural equation for the original base-changed cone. -/
@[reassoc (attr := simp)]
lemma cone_fac (i : I) :
    (cone D t b c p hp).π.app i ≫ (baseStructure D t b).app i = pullback.snd p b := by
  exact Over.w ((Over.pullback b).map ((Over.liftCone D t c p hp).π.app i))

/-- Base change preserves the original cofiltered limit. -/
def isLimitCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (cone D t b c p hp) := by
  have : Nonempty I := IsCofiltered.nonempty
  exact isLimitOfPreserves (Over.pullback b ⋙ Over.forget T)
    (Over.isLimitLiftCone D t c p hp hc)

instance map_isClosedImmersion
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q)]
    {i j : I} (q : i ⟶ j) : IsClosedImmersion ((diagram D t b).map q) :=
  MorphismProperty.overPullbackMap (P := @IsClosedImmersion) b ((Over.lift D t).map q)
    (inferInstanceAs (IsClosedImmersion (D.map q)))

instance map_isAffineHom
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    {i j : I} (q : i ⟶ j) : IsAffineHom ((diagram D t b).map q) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) b ((Over.lift D t).map q)
    (inferInstanceAs (IsAffineHom (D.map q)))

instance obj_compactSpace [QuasiCompact b] [∀ i, CompactSpace (D.obj i)] (i : I) :
    CompactSpace ((diagram D t b).obj i) := by
  change CompactSpace (pullback (t.app i) b : Scheme)
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (t.app i) b)

instance obj_quasiSeparatedSpace [QuasiSeparated b]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) :
    QuasiSeparatedSpace ((diagram D t b).obj i) := by
  change QuasiSeparatedSpace (pullback (t.app i) b : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) b)

instance baseStructure_locallyOfFiniteType
    [∀ i, LocallyOfFiniteType (t.app i)] (i : I) :
    LocallyOfFiniteType ((baseStructure D t b).app i) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd (t.app i) b))

end AlgebraicGeometry.Scheme.FixedBaseChange
