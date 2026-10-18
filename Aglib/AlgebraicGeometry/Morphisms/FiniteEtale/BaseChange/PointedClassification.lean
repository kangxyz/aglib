/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.GroupScheme

/-!
# Pointed naturality of actual finite-etale classification

Source: general cover functoriality behind
`K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

This equality-aware wrapper uses independent actual field-valued points
`s,t` and an equality `h : s ≫ f = t`. Classification after actual base change
is naturally isomorphic to restriction of classification at `t` along
`GroupBaseChange.inducedGroupHomPointed f s t h`. This is exactly the actual
`pointedMap (Under.homMk f h)`, so the same interface applies to a geometric
base-change inclusion and a rational-origin projection. The latter map's
normalization is already proved by `inducedGroupHomPointed_projection`.

The standard Galois-category and fibre-functor classes for the actual schemes
and points are retained. No classification commuting square is an input.
The inverse-side comparison and marking formulas use the existing unit/counit
constructions. Scheme connectedness, kernel exactness, and their geometric
realization remain separate obligations.

Frozen inputs: `ClassificationNaturality.lean` SHA256
`b42fa423daa3865c6c6832ca02757e2f59c66f1eed0ada955e6a8b9609ededc0` and
`GroupBaseChange.lean` SHA256
`57ddd77dd4f5201968aadac1c2a392084c5a2ac511dcb9553e730d0b344f77ad`.
This standalone wrapper keeps the dependency direction
`ClassificationNaturality → GroupBaseChange → ClassificationNaturalityPointed`.
Each declaration's source pointer uses the module source basis above and
covers this pointed general-cover transport subset only.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange

namespace AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturalityPointed

universe u

variable {S X : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)
  (t : Spec (CommRingCat.of K) ⟶ X) (h : s ≫ f = t)
variable [GaloisCategory (Scheme.FiniteEtale S)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite t)]

/-- Actual base-change classification is naturally restriction along the
actual pointed fibre-group map, for general cover functoriality in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def classificationBaseChangeIsoPointed :
    baseChange f ⋙ (classification s).functor ≅
      (classification t).functor ⋙ ContAction.res FintypeCat (inducedGroupHomPointed f s t h) := by
  subst t
  exact ClassificationNaturality.classificationBaseChangeIso f s

/-- The pointed classification comparison evaluates by the canonical fibre
projection in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF]
theorem classificationBaseChangeIsoPointed_hom_apply (Y : Scheme.FiniteEtale X)
    (q : Fiber s ((baseChange f).obj Y)) :
    ((classificationBaseChangeIsoPointed f s t h).hom.app Y).hom.hom q =
      (fiberBaseChangeEquivPointed f s t h Y).symm q := by
  subst t
  rw [fiberBaseChangeEquivPointed_rfl]
  exact ClassificationNaturality.classificationBaseChangeIso_hom_apply f s Y q

/-- The inverse comparison evaluates by the actual pullback fibre lift in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF]
theorem classificationBaseChangeIsoPointed_inv_apply (Y : Scheme.FiniteEtale X)
    (q : Fiber t Y) :
    ((classificationBaseChangeIsoPointed f s t h).inv.app Y).hom.hom q =
      fiberBaseChangeEquivPointed f s t h Y q := by
  subst t
  rw [fiberBaseChangeEquivPointed_rfl]
  exact ClassificationNaturality.classificationBaseChangeIso_inv_apply f s Y q

/-- The comparison is the actual pullback projection on scheme-valued
points in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF]
theorem classificationBaseChangeIsoPointed_hom_left (Y : Scheme.FiniteEtale X)
    (q : Fiber s ((baseChange f).obj Y)) :
    (((classificationBaseChangeIsoPointed f s t h).hom.app Y).hom.hom q).left =
      q.left ≫ pullback.fst Y.obj.hom f := by
  subst t
  exact ClassificationNaturality.classificationBaseChangeIso_hom_left f s Y q

/-- The inverse comparison is the universal scheme pullback lift, with the
specified point equality, in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF]
theorem classificationBaseChangeIsoPointed_inv_left (Y : Scheme.FiniteEtale X)
    (q : Fiber t Y) :
    (((classificationBaseChangeIsoPointed f s t h).inv.app Y).hom.hom q).left =
      pullback.lift q.left s ((Over.w q).trans h.symm) := by
  subst t
  exact ClassificationNaturality.classificationBaseChangeIso_inv_left f s Y q

/-- The unit/counit inverse-classification comparison with independent
points, for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def descendedBaseChangeIsoPointed :
    (classification t).inverse ⋙ baseChange f ≅
      ContAction.res FintypeCat (inducedGroupHomPointed f s t h) ⋙ (classification s).inverse := by
  subst t
  exact ClassificationNaturality.descendedBaseChangeIso f s

/-- Pullback of a descended finite continuous action is descent of its
restriction along the actual pointed group map, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def coverPullbackIsoPointed (A : ContAction FintypeCat (FiberAutGroup t)) :
    (baseChange f).obj ((classification t).inverse.obj A) ≅
      (classification s).inverse.obj
        ((ContAction.res FintypeCat (inducedGroupHomPointed f s t h)).obj A) :=
  (descendedBaseChangeIsoPointed f s t h).app A

/-- The actual classified fibre marking of a pulled-back descended cover,
for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def pulledbackActionIsoPointed (A : ContAction FintypeCat (FiberAutGroup t)) :
    (classification s).functor.obj ((baseChange f).obj ((classification t).inverse.obj A)) ≅
      (ContAction.res FintypeCat (inducedGroupHomPointed f s t h)).obj A := by
  subst t
  exact ClassificationNaturality.pulledbackActionIso f s A

/-- The marking evaluates by pointed fibre projection followed by the
classification counit in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem pulledbackActionIsoPointed_hom_apply
    (A : ContAction FintypeCat (FiberAutGroup t))
    (q : Fiber s ((baseChange f).obj ((classification t).inverse.obj A))) :
    (pulledbackActionIsoPointed f s t h A).hom.hom.hom q =
      ((classification t).counitIso.hom.app A).hom.hom
        ((fiberBaseChangeEquivPointed f s t h ((classification t).inverse.obj A)).symm q) := by
  subst t
  rw [fiberBaseChangeEquivPointed_rfl]
  exact ClassificationNaturality.pulledbackActionIso_hom_apply f s A q

/-- The inverse marking evaluates by the inverse counit and the pointed
fibre lift in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem pulledbackActionIsoPointed_inv_apply
    (A : ContAction FintypeCat (FiberAutGroup t)) (a : A.obj.V) :
    (pulledbackActionIsoPointed f s t h A).inv.hom.hom a =
      fiberBaseChangeEquivPointed f s t h ((classification t).inverse.obj A)
        (((classification t).counitIso.inv.app A).hom.hom a) := by
  subst t
  rw [fiberBaseChangeEquivPointed_rfl]
  exact ClassificationNaturality.pulledbackActionIso_inv_apply f s A a

/-- The inverse-side comparison has the explicit unit and marking formula
in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem coverPullbackIsoPointed_hom (A : ContAction FintypeCat (FiberAutGroup t)) :
    (coverPullbackIsoPointed f s t h A).hom =
      (classification s).unitIso.hom.app ((baseChange f).obj ((classification t).inverse.obj A)) ≫
        (classification s).inverse.map (pulledbackActionIsoPointed f s t h A).hom := by
  subst t
  exact ClassificationNaturality.descendedCoverPullbackIso_hom f s A

/-- The inverse cover map is inverse marking followed by inverse unit in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem coverPullbackIsoPointed_inv (A : ContAction FintypeCat (FiberAutGroup t)) :
    (coverPullbackIsoPointed f s t h A).inv =
      (classification s).inverse.map (pulledbackActionIsoPointed f s t h A).inv ≫
        (classification s).unitIso.inv.app ((baseChange f).obj ((classification t).inverse.obj
          A)) := by
  subst t
  exact ClassificationNaturality.descendedCoverPullbackIso_inv f s A

/-- Actual scheme points transported by the cover comparison preserve the
pointed classification marking, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem coverPullbackIsoPointed_point (A : ContAction FintypeCat (FiberAutGroup t))
    (q : Fiber s ((baseChange f).obj ((classification t).inverse.obj A))) :
    ((classification s).counitIso.hom.app
        ((ContAction.res FintypeCat (inducedGroupHomPointed f s t h)).obj A)).hom.hom
        (q ≫ (coverPullbackIsoPointed f s t h A).hom.hom) =
      ((classification t).counitIso.hom.app A).hom.hom
        ((fiberBaseChangeEquivPointed f s t h ((classification t).inverse.obj A)).symm q) := by
  subst t
  rw [fiberBaseChangeEquivPointed_rfl]
  exact ClassificationNaturality.descendedCoverPullbackIso_point f s A q

end AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturalityPointed

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 6c19f2893665de7ddc1c0179b3eedd07d24ed810d21dd8075aa3c6076eb2b6a9.
Definitions, hypotheses and universes are retained modulo native names. -/
