/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Sheaf
public import Aglib.CategoryTheory.Sites.Descent.Rigidification

/-!
# The origin pullback and the rigidification of pulled-back pairs

Let `p : X ⟶ S` have a section `o`. The gluing of rigidified pairs in
[GluingDescent](GluingDescent.lean) ([Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N);
Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(2), p. 18) writes the rigidification
of a pulled-back pair through the pullback pseudofunctor. This file provides the three facts it
uses.

* `originPullback p o ho`: pullback along the origin sections `o_T : T ⟶ X ×_S T`, as a
  transformation of pseudofunctors on `Over S` (`CompTrans.ofNatTrans` at
  `originSectionNatTrans`).
* `map_rigidification_hom`: the rigidification of a pulled-back pair (`RigidifiedPair.map`) is the
  pseudonaturality isomorphism of `originPullback`, followed by the pullback of the
  rigidification and `pullbackUnitIso`. It goes through `originPullback_nat_hom_app`, which writes
  the pseudonaturality isomorphism through `pullbackComp` and `pullbackCongr`, and through
  `pullbackPseudofunctor_square_app`, stated at variable schemes.
* `mapComp'_unit_pullbackUnitIso`: the composition isomorphism of base pullbacks at the structure
  module is compatible with `pullbackUnitIso` (from `pullbackUnitIso_comp`); it is the cocycle of
  the rigidifications in `GluingDescent.lean` (`baseUnitHom_comp`).

The bridges between the two presentations (Mathlib's pullback functors and the pullback
pseudofunctor) are stated through `CompEq` (`CategoryTheory/Sites/Descent/Rigidification.lean`),
so that the kernel compares the arguments of two equations of composites rather than unfolding the
composites.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

open Scheme.Modules Scheme.Modules.Invertible

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- Pullback of module sheaves along the origin sections `o_T : T ⟶ X ×_S T`, as a transformation
of pseudofunctors on `Over S`. -/
def originPullback :
    CompTrans (pullbackPseudofunctor.restrictAlong (familyScheme p))
      (pullbackPseudofunctor.restrictAlong (Over.forget S)) :=
  CompTrans.ofNatTrans pullbackPseudofunctor (originSectionNatTrans p o ho)

-- `pullbackPseudofunctor_mapComp'_*_app` are stated for `X.Modules`; matching them needs relaxed
-- instance transparency, as in `pullbackPseudofunctor_mapComp'_hom_app`.
set_option backward.isDefEq.respectTransparency false in
/-- The pullback isomorphism of a commutative square `t ≫ m = l ≫ r` of schemes, through the
composition isomorphisms of `pullbackPseudofunctor`, in terms of `pullbackComp` and
`pullbackCongr`. Stated at variable schemes, as an instance of `CompEq` in `C.Modules`; consumers
compare it with equations in the categories of the pseudofunctor through the arguments of
`CompEq`. -/
theorem pullbackPseudofunctor_square_app {A B C D : Scheme.{u}} (t : C ⟶ B) (m : B ⟶ A)
    (l : C ⟶ D) (r : D ⟶ A) (w : t ≫ m = l ≫ r) (L : A.Modules) :
    CompEq (D := C.Modules)
      (X := (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback m).obj L))
      (Y := (Scheme.Modules.pullback (t ≫ m)).obj L)
      (Z := (Scheme.Modules.pullback l).obj ((Scheme.Modules.pullback r).obj L))
      ((pullbackPseudofunctor.mapComp' m.op.toLoc t.op.toLoc (t ≫ m).op.toLoc
        rfl).inv.toNatTrans.app L)
      ((pullbackPseudofunctor.mapComp' r.op.toLoc l.op.toLoc (t ≫ m).op.toLoc
        (by rw [w]; rfl)).hom.toNatTrans.app L)
      ((Scheme.Modules.pullbackComp t m).hom.app L ≫ (Scheme.Modules.pullbackCongr w).hom.app L ≫
        (Scheme.Modules.pullbackComp l r).inv.app L) := by
  unfold CompEq
  rw [pullbackPseudofunctor_mapComp'_inv_app m t (t ≫ m) rfl L,
    pullbackPseudofunctor_mapComp'_hom_app r l (t ≫ m) w.symm L]
  simp [Scheme.Modules.pullbackCongr]

theorem originPullback_nat {V Y : Over S} (y : Y ⟶ V) :
    (originPullback p o ho).nat y =
      CompTrans.ofNatTransNat pullbackPseudofunctor (originSectionNatTrans p o ho) y :=
  rfl

/-- The pseudonaturality isomorphism of `originPullback` along `y : Y ⟶ V`, in terms of Mathlib's
`pullbackComp` and `pullbackCongr`, written with the components of `originSectionNatTrans` and
`Over.forget S` (the first three factors of the rigidification of a pulled-back pair, up to these
components). The generic `CompTrans.ofNatTransNat_hom_app` and `pullbackPseudofunctor_square_app`
are compared through `CompEq.eq`. -/
theorem originPullback_nat_hom_app {V Y : Over S} (y : Y ⟶ V) (L : (pullback p V.hom).Modules) :
    ((originPullback p o ho).nat y).hom.app L =
      (Scheme.Modules.pullbackComp ((originSectionNatTrans p o ho).app Y)
          ((familyScheme p).map y)).hom.app L ≫
        (Scheme.Modules.pullbackCongr ((originSectionNatTrans p o ho).naturality y).symm).hom.app
          L ≫
        (Scheme.Modules.pullbackComp ((Over.forget S).map y)
          ((originSectionNatTrans p o ho).app V)).inv.app L :=
  CompEq.eq
    (CompTrans.ofNatTransNat_hom_app pullbackPseudofunctor (originSectionNatTrans p o ho) y L).symm
    (pullbackPseudofunctor_square_app _ _ _ _ ((originSectionNatTrans p o ho).naturality y).symm L)

-- As for `pullbackPseudofunctor_square_app`.
set_option backward.isDefEq.respectTransparency false in
/-- The rigidification of a pulled-back pair, through `originPullback`. The equation is first
proved in `Y.left.Modules`, where both sides are composites of Mathlib's pullback isomorphisms, and
then compared with the statement through `CompEq.eq`. -/
theorem map_rigidification_hom {V Y : Over S} (y : Y ⟶ V) (P : RigidifiedPair p o ho V) :
    (RigidifiedPair.map y P).rigidification.hom =
      ((originPullback p o ho).nat y).hom.app P.bundle.val ≫
        (Scheme.Modules.pullback y.left).map P.rigidification.hom ≫
          (pullbackUnitIso y.left).hom := by
  have h : CompEq (D := Y.left.Modules)
      (X := (Scheme.Modules.pullback (originSection p o ho Y)).obj
        (RigidifiedPair.map y P).bundle.val)
      (Y := (Scheme.Modules.pullback y.left).obj
        ((Scheme.Modules.pullback (originSection p o ho V)).obj P.bundle.val))
      (((originPullback p o ho).nat y).hom.app P.bundle.val)
      ((Scheme.Modules.pullback y.left).map P.rigidification.hom ≫ (pullbackUnitIso y.left).hom)
      (RigidifiedPair.map y P).rigidification.hom := by
    unfold CompEq
    rw [originPullback_nat_hom_app]
    simp only [RigidifiedPair.map, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
      Functor.mapIso_hom, Category.assoc]
    rfl
  exact (CompEq.eq (rfl : CompEq (((originPullback p o ho).nat y).hom.app P.bundle.val)
    ((Scheme.Modules.pullback y.left).map P.rigidification.hom ≫ (pullbackUnitIso y.left).hom)
    _) h).symm

-- As for `pullbackPseudofunctor_square_app`.
set_option backward.isDefEq.respectTransparency false in
/-- The unit coherence of the rigidifications: the composition isomorphism of the base pullbacks
at the structure module, followed by the pullback-unit isomorphisms. It is the cocycle condition
`baseUnitHom_comp` of `GluingDescent.lean`. -/
theorem mapComp'_unit_pullbackUnitIso {V Y Y' : Over S} (y : Y ⟶ V) (g : Y' ⟶ Y) :
    ((pullbackPseudofunctor.restrictAlong (Over.forget S)).mapComp' y.op.toLoc g.op.toLoc
        (g ≫ y).op.toLoc rfl).hom.toNatTrans.app (SheafOfModules.unit V.left.ringCatSheaf) ≫
      (Scheme.Modules.pullback g.left).map (pullbackUnitIso y.left).hom ≫
        (pullbackUnitIso g.left).hom = (pullbackUnitIso (g ≫ y).left).hom := by
  rw [restrictAlong_mapComp'_hom_app y g (g ≫ y) rfl,
    pullbackPseudofunctor_mapComp'_hom_app _ _ _ ((Over.forget S).map_comp g y).symm]
  rw [← pullbackUnitIso_comp g.left y.left]
  simp only [Category.assoc]
  have h : (Scheme.Modules.pullbackComp ((Over.forget S).map g) ((Over.forget S).map y)).inv.app
      (SheafOfModules.unit V.left.ringCatSheaf) ≫
        (Scheme.Modules.pullbackComp g.left y.left).hom.app
          (SheafOfModules.unit V.left.ringCatSheaf) = 𝟙 _ :=
    (Scheme.Modules.pullbackComp g.left y.left).inv_hom_id_app _
  rw [reassoc_of% h]
  exact pullbackUnitIso_congr ((Over.forget S).map_comp g y).symm

end AlgebraicGeometry.Scheme.RelativePicard
