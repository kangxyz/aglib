/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Group

/-!
# Classification commutes with actual finite-etale base change

Source: the general finite-cover functoriality behind
`K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

The inputs are an actual scheme morphism `f : S ⟶ X` and a field-valued point
`x` of `S`. The induced continuous fibre-automorphism homomorphism is built
from the actual pullback functor and its canonical fibre isomorphism. That
isomorphism constructs the natural comparison between classification after
pullback and restriction of the classified action. No commuting square for
classification is an input.

For classification we retain exactly the standard classes
`GaloisCategory (Cover S)`, `GaloisCategory (Cover X)`, and the
`PreGaloisCategory.FiberFunctor` classes for the actual fibre functors at `x`
and `x ≫ f`. The unit and counit then construct the inverse-side comparison
between pulling back a descended cover and descending the restricted action.

This module proves general classification transport. It does not verify the
retained scheme Galois-category classes, identify rational origins, prove
geometric connectedness, or construct and transport coefficient torsor laws.
Its frozen dependencies are `GroupDescent.lean` SHA256
`7d198fddef147ce2e7d8b8bf030e8bac7b3a698fa46f9c50b2a3b0308bbeecaf`,
`FiniteEtaleCovers.lean` SHA256
`593e6b847bd845fa2b13de95a7c0b7991a2cf94b70d27a14ca1d24b5833adaa6`, and
`EtaleFundamentalGroups.lean` SHA256
`f45f9cb6815524a8b04347d98bd51d0a95dd787e6499cec65af8a8171c31101f`.
Each declaration's source pointer uses the module source basis above and
covers this general finite-cover transport subset only.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberBaseChangeEquiv_left fiberBaseChangeEquiv_symm_left fiberToFinite
  fiberToFiniteBaseChangeIso)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality

universe u

variable {S X : Scheme.{u}} {K : Type u} [Field K]
variable (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S)

/-- The actual induced continuous group homomorphism used for general
finite-cover functoriality in `K2-018#prop:k2018-arithmetic-characters`, on the
module source basis. Its continuity is already proved on fibre evaluations. -/
def inducedGroupHom : FiberAutGroup x →ₜ* FiberAutGroup (x ≫ f) :=
  { EtaleFundamentalGroups.map f x with continuous_toFun := continuous_map f x }

/-- The underlying group map is exactly the map constructed from actual
scheme pullback in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
-- Keep this original bundled-map simp formula before generic coercion normalization.
@[simp, nolint simpNF] theorem inducedGroupHom_toMonoidHom :
    (inducedGroupHom f x).toMonoidHom = EtaleFundamentalGroups.map f x := rfl

/-- The group map agrees with the actual pointed-scheme map in
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem inducedGroupHom_eq_pointedMap :
    (inducedGroupHom f x).toMonoidHom =
      pointedMap (Under.homMk f rfl : Under.mk x ⟶ Under.mk (x ≫ f)) := rfl

/-- Evaluation of the induced group map is conjugation by the canonical
pullback-fibre isomorphism in `K2-018#eq:k2018-pointed-character`, on the module source basis. -/
@[simp] theorem inducedGroupHom_apply (a : FiberAutGroup x) (Y : Scheme.FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    (inducedGroupHom f x a).hom.app Y p = (fiberBaseChangeEquiv f x Y).symm
      (a.hom.app ((baseChange f).obj Y) (fiberBaseChangeEquiv f x Y p)) :=
  map_apply f x a Y p

/-- The inverse pullback-fibre identification intertwines the actual point
actions in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem fiberBaseChange_equivariant (a : FiberAutGroup x) (Y : Scheme.FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    (fiberBaseChangeEquiv f x Y).symm (a.hom.app ((baseChange f).obj Y) p) =
      (inducedGroupHom f x a).hom.app Y ((fiberBaseChangeEquiv f x Y).symm p) := by
  rw [inducedGroupHom_apply, Equiv.apply_symm_apply]

section Classification

variable [GaloisCategory (Scheme.FiniteEtale S)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite x)]
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (x ≫ f))]

/-- Actual finite-etale base change commutes naturally with classification
and restriction along the actual continuous fibre-group map, the general
cover-functoriality subset of `K2-018#prop:k2018-arithmetic-characters`, on the
module source basis. The canonical fibre isomorphism supplies every component. -/
def classificationBaseChangeIso :
    baseChange f ⋙ (classification x).functor ≅
      (classification (x ≫ f)).functor ⋙
        ContAction.res FintypeCat (inducedGroupHom f x) :=
  NatIso.ofComponents (fun Y => ObjectProperty.isoMk _
    (Action.mkIso ((fiberToFiniteBaseChangeIso f x).symm.app Y) (by
      intro a
      change a.hom.app ((baseChange f).obj Y) ≫
          (fiberToFiniteBaseChangeIso f x).inv.app Y =
        (fiberToFiniteBaseChangeIso f x).inv.app Y ≫
          (EtaleFundamentalGroups.map f x a).hom.app Y
      rw [map_hom_app]
      simp))) (by
    intro Y Z g
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact (fiberToFiniteBaseChangeIso f x).inv.naturality g)

/-- The classification comparison sends a pullback point to its original
point by the canonical fibre equivalence in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem classificationBaseChangeIso_hom_apply (Y : Scheme.FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    ((classificationBaseChangeIso f x).hom.app Y).hom.hom p =
      (fiberBaseChangeEquiv f x Y).symm p := by
  exact finiteBaseChangeIso_inv_apply f x Y p

/-- The inverse classification comparison uses the universal pullback lift
in `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem classificationBaseChangeIso_inv_apply (Y : Scheme.FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    ((classificationBaseChangeIso f x).inv.app Y).hom.hom p =
      fiberBaseChangeEquiv f x Y p := by
  exact finiteBaseChangeIso_hom_apply f x Y p

/-- The comparison's underlying scheme-valued point is the pullback
projection, for the general cover functoriality in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem classificationBaseChangeIso_hom_left (Y : Scheme.FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    (((classificationBaseChangeIso f x).hom.app Y).hom.hom p).left =
      p.left ≫ pullback.fst Y.obj.hom f := by
  rw [classificationBaseChangeIso_hom_apply, fiberBaseChangeEquiv_symm_left]

/-- The inverse comparison's underlying point is the actual pullback lift,
for the general cover functoriality in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem classificationBaseChangeIso_inv_left (Y : Scheme.FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    (((classificationBaseChangeIso f x).inv.app Y).hom.hom p).left =
      pullback.lift p.left x (Over.w p) := by
  rw [classificationBaseChangeIso_inv_apply, fiberBaseChangeEquiv_left]

/-- The classification unit and counit transport natural base-change
compatibility to the inverse classification functors, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def descendedBaseChangeIso :
    (classification (x ≫ f)).inverse ⋙ baseChange f ≅
      ContAction.res FintypeCat (inducedGroupHom f x) ⋙ (classification x).inverse :=
  Iso.inverseCompIso (G := classification (x ≫ f))
    (Iso.isoCompInverse (H := classification x) (classificationBaseChangeIso f x))

/-- The classified fibre of a pulled-back descended cover is marked by
canonical fibre transport followed by the classification counit, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def pulledbackActionIso (A : ContAction FintypeCat (FiberAutGroup (x ≫ f))) :
    (classification x).functor.obj
        ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A)) ≅
      (ContAction.res FintypeCat (inducedGroupHom f x)).obj A :=
  (classificationBaseChangeIso f x).app ((classification (x ≫ f)).inverse.obj A) ≪≫
    (ContAction.res FintypeCat (inducedGroupHom f x)).mapIso
      ((classification (x ≫ f)).counitIso.app A)

/-- The pulled-back marking evaluates by projecting to the original fibre
and then applying its classification counit, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
@[simp] theorem pulledbackActionIso_hom_apply
    (A : ContAction FintypeCat (FiberAutGroup (x ≫ f)))
    (p : Fiber x ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A))) :
    (pulledbackActionIso f x A).hom.hom.hom p =
      ((classification (x ≫ f)).counitIso.hom.app A).hom.hom
        ((fiberBaseChangeEquiv f x ((classification (x ≫ f)).inverse.obj A)).symm p) := by
  change ((classification (x ≫ f)).counitIso.hom.app A).hom.hom
    (((classificationBaseChangeIso f x).hom.app
      ((classification (x ≫ f)).inverse.obj A)).hom.hom p) = _
  rw [classificationBaseChangeIso_hom_apply]

/-- The inverse pulled-back marking evaluates by the inverse counit and
the actual pullback lift, for `K2-018#prop:k2018-arithmetic-characters`, on the
module source basis. -/
@[simp] theorem pulledbackActionIso_inv_apply
    (A : ContAction FintypeCat (FiberAutGroup (x ≫ f))) (a : A.obj.V) :
    (pulledbackActionIso f x A).inv.hom.hom a =
      fiberBaseChangeEquiv f x ((classification (x ≫ f)).inverse.obj A)
        (((classification (x ≫ f)).counitIso.inv.app A).hom.hom a) := by
  change ((classificationBaseChangeIso f x).inv.app
    ((classification (x ≫ f)).inverse.obj A)).hom.hom
      (((classification (x ≫ f)).counitIso.inv.app A).hom.hom a) = _
  exact classificationBaseChangeIso_inv_apply f x
    ((classification (x ≫ f)).inverse.obj A)
    (((classification (x ≫ f)).counitIso.inv.app A).hom.hom a)

/-- A pulled-back descended cover is isomorphic to descent of the restricted
action, for the general cover functoriality of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
def descendedCoverPullbackIso (A : ContAction FintypeCat (FiberAutGroup (x ≫ f))) :
    (baseChange f).obj ((classification (x ≫ f)).inverse.obj A) ≅
      (classification x).inverse.obj
        ((ContAction.res FintypeCat (inducedGroupHom f x)).obj A) :=
  (descendedBaseChangeIso f x).app A

/-- The explicit unit/marking formula for descended-cover pullback in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem descendedCoverPullbackIso_hom (A : ContAction FintypeCat (FiberAutGroup (x ≫ f))) :
    (descendedCoverPullbackIso f x A).hom =
      (classification x).unitIso.hom.app
          ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A)) ≫
        (classification x).inverse.map (pulledbackActionIso f x A).hom := by
  simp only [descendedCoverPullbackIso, descendedBaseChangeIso, pulledbackActionIso,
    Iso.inverseCompIso, Iso.isoCompInverse, Functor.isoWhiskerLeft_trans,
    Functor.isoWhiskerLeft_twice, Iso.trans_assoc, NatIso.trans_app, Functor.comp_obj,
    Functor.id_obj, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.comp_map, ContAction.res_map, Functor.leftUnitor_hom_app, Category.comp_id,
    Category.id_comp, Functor.mapIso_hom, NatIso.cancel_natIso_hom_left]
  exact ((classification x).inverse.map_comp _ _).symm

/-- The inverse cover formula uses inverse marking and the inverse unit in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem descendedCoverPullbackIso_inv (A : ContAction FintypeCat (FiberAutGroup (x ≫ f))) :
    (descendedCoverPullbackIso f x A).inv =
      (classification x).inverse.map (pulledbackActionIso f x A).inv ≫
        (classification x).unitIso.inv.app
          ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A)) := by
  simp only [descendedCoverPullbackIso, descendedBaseChangeIso, pulledbackActionIso,
    Iso.inverseCompIso, Iso.isoCompInverse, Functor.isoWhiskerLeft_trans,
    Functor.isoWhiskerLeft_twice, Iso.trans_assoc, NatIso.trans_app, Functor.comp_obj,
    Functor.id_obj, Iso.trans_inv, Iso.app_inv, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.comp_map, ContAction.res_map,
    Category.id_comp, Iso.symm_inv, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Category.assoc, Functor.rightUnitor_hom_app, Functor.mapIso_inv]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun h => h ≫ (classification x).unitIso.inv.app
        ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A)))
      ((classification x).inverse.map_comp _ _).symm)

/-- The descended cover comparison preserves the explicitly constructed
fibre marking, by the equivalence triangle and counit naturality, for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem descendedCoverPullbackIso_marking
    (A : ContAction FintypeCat (FiberAutGroup (x ≫ f))) :
    (classification x).functor.map (descendedCoverPullbackIso f x A).hom ≫
        (classification x).counitIso.hom.app
          ((ContAction.res FintypeCat (inducedGroupHom f x)).obj A) =
      (pulledbackActionIso f x A).hom := by
  rw [descendedCoverPullbackIso_hom, (classification x).functor.map_comp, Category.assoc]
  calc
    _ = (classification x).functor.map
        ((classification x).unitIso.hom.app
          ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A))) ≫
        (classification x).counitIso.hom.app ((classification x).functor.obj
          ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A))) ≫
        (pulledbackActionIso f x A).hom := by
      exact congrArg (fun h => (classification x).functor.map
          ((classification x).unitIso.hom.app
            ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A))) ≫ h)
        ((classification x).counitIso.hom.naturality (pulledbackActionIso f x A).hom)
    _ = (pulledbackActionIso f x A).hom := by
      rw [← Category.assoc]
      exact (congrArg (fun h => h ≫ (pulledbackActionIso f x A).hom)
        ((classification x).functor_unitIso_comp
          ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A)))).trans
        (Category.id_comp _)

/-- Actual scheme-valued points transported by descended-cover pullback
have the same action marking as their canonical original-fibre projections,
for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem descendedCoverPullbackIso_point
    (A : ContAction FintypeCat (FiberAutGroup (x ≫ f)))
    (p : Fiber x ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A))) :
    ((classification x).counitIso.hom.app
        ((ContAction.res FintypeCat (inducedGroupHom f x)).obj A)).hom.hom
        (p ≫ (descendedCoverPullbackIso f x A).hom.hom) =
      ((classification (x ≫ f)).counitIso.hom.app A).hom.hom
        ((fiberBaseChangeEquiv f x ((classification (x ≫ f)).inverse.obj A)).symm p) := by
  have h := ConcreteCategory.congr_hom (C := FintypeCat)
    (congrArg (fun (g : (classification x).functor.obj
        ((baseChange f).obj ((classification (x ≫ f)).inverse.obj A)) ⟶
        (ContAction.res FintypeCat (inducedGroupHom f x)).obj A) => g.hom.hom)
      (descendedCoverPullbackIso_marking f x A)) p
  change ((classification x).counitIso.hom.app
      ((ContAction.res FintypeCat (inducedGroupHom f x)).obj A)).hom.hom
      (p ≫ (descendedCoverPullbackIso f x A).hom.hom) =
    (pulledbackActionIso f x A).hom.hom.hom p at h
  exact h.trans (pulledbackActionIso_hom_apply f x A p)

end Classification

end AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c5a81c1ddb5007a8867a601a567da181bb11d78a3e70a271477a10b3482b5c07.
Definitions, hypotheses and universes are retained modulo native names. -/
