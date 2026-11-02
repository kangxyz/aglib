/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Translation
public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange
public import Aglib.CategoryTheory.Monoidal.AdjunctionHomMulEquiv

/-!
# Base change of the original translated line-bundle family

The comparison is the existing pasted fibre-product isomorphism. First prove
its projection laws over the original base and the original adjunction's
product law; then compare the actual translated Picard classes. The group on
the scalar extension is the existing pullback group object.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

section Products

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (G : Over S) (T : Over S')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The existing pasted family isomorphism, over the original base. -/
def familyBaseChangeOverIso :
    (Over.map s).obj ((Over.pullback s).obj G ⊗ T) ≅ G ⊗ (Over.map s).obj T :=
  Over.isoMk (familyBaseChangeIso G.hom s T) (by
    change (familyBaseChangeIso G.hom s T).hom ≫
        (pullback.fst G.hom (T.hom ≫ s) ≫ G.hom) =
      (pullback.fst (pullback.snd G.hom s) T.hom ≫ pullback.snd G.hom s) ≫ s
    rw [← Category.assoc, familyBaseChangeIso_hom_fst, Category.assoc,
      pullback.condition, ← Category.assoc])

/-- The original first projection is the original pullback-adjunction image. -/
theorem familyBaseChangeOverIso_hom_fst :
    (familyBaseChangeOverIso s G T).hom ≫ fst G ((Over.map s).obj T) =
      ((Over.mapPullbackAdj s).homEquiv ((Over.pullback s).obj G ⊗ T) G).symm
        (fst ((Over.pullback s).obj G) T) :=
  Over.OverMorphism.ext (familyBaseChangeIso_hom_fst G.hom s T)

/-- The original second projection is unchanged by the same comparison. -/
theorem familyBaseChangeOverIso_hom_snd :
    (familyBaseChangeOverIso s G T).hom ≫ snd G ((Over.map s).obj T) =
      (Over.map s).map (snd ((Over.pullback s).obj G) T) :=
  Over.OverMorphism.ext (familyBaseChangeIso_hom_snd G.hom s T)

/-- The original adjunction image commutes with precomposition on the
parameter scheme. This keeps its literal underlying composite. -/
theorem mapPullbackAdj_symm_comp {T' : Over S'} (f : T' ⟶ T)
    (t : T ⟶ (Over.pullback s).obj G) :
    ((Over.mapPullbackAdj s).homEquiv T' G).symm (f ≫ t) =
      (Over.map s).map f ≫ ((Over.mapPullbackAdj s).homEquiv T G).symm t :=
  Over.OverMorphism.ext (Category.assoc f.left t.left (pullback.fst G.hom s))

end Products

variable {k K : Type u} [Field k] [Field K]
  (s : Spec (.of K) ⟶ Spec (.of k))
  (G : Over (Spec (.of k))) [GrpObj G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete translated-family morphism commutes with the actual
field-base-change comparison, before Picard pullback is evaluated. -/
theorem translationFamilyMorphism_baseChange {T : Over (Spec (.of K))}
    (t : T ⟶ (Over.pullback s).obj G) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    ((Over.mapPullbackAdj s).homEquiv ((Over.pullback s).obj G ⊗ T) G).symm
        (translationFamilyMorphism ((Over.pullback s).obj G) t) =
      (familyBaseChangeOverIso s G T).hom ≫
        translationFamilyMorphism G (((Over.mapPullbackAdj s).homEquiv T G).symm t) := by
  let : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
  have h := (Over.mapPullbackAdj s).homEquiv_symm_mul
    (fst ((Over.pullback s).obj G) T) (snd ((Over.pullback s).obj G) T ≫ t)
  change _ = (familyBaseChangeOverIso s G T).hom ≫
    (fst G ((Over.map s).obj T) *
      (snd G ((Over.map s).obj T) ≫ ((Over.mapPullbackAdj s).homEquiv T G).symm t))
  rw [MonObj.comp_mul, familyBaseChangeOverIso_hom_fst, ← Category.assoc,
    familyBaseChangeOverIso_hom_snd, ← mapPullbackAdj_symm_comp]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original translated Picard class respects field base change, using
the same pasted family isomorphism and original pullback group law. -/
theorem translationFamilyClass_baseChange {T : Over (Spec (.of K))}
    (t : T ⟶ (Over.pullback s).obj G) (a : PicardGroup G.left) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    pullbackClass (familyBaseChangeIso G.hom s T).hom
        (translationFamilyClass (T := Over.mk (T.hom ≫ s)) G
          (((Over.mapPullbackAdj s).homEquiv T G).symm t) a) =
      translationFamilyClass ((Over.pullback s).obj G) t
        (pullbackClass (pullback.fst G.hom s) a) := by
  let : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
  have hm := congrArg (fun f => f.left) (translationFamilyMorphism_baseChange s G t)
  change (translationFamilyMorphism ((Over.pullback s).obj G) t).left ≫
      pullback.fst G.hom s =
    (familyBaseChangeIso G.hom s T).hom ≫
      (translationFamilyMorphism G (((Over.mapPullbackAdj s).homEquiv T G).symm t)).left at hm
  simp only [translationFamilyClass]
  simp only [← pullbackHom_apply, map_sub]
  simp only [pullbackHom_apply, ← pullbackClass_comp]
  rw [← hm]
  congr 1
  exact congrArg (fun f : ((Over.pullback s).obj G ⊗ T).left ⟶ G.left => pullbackClass f a)
    (familyBaseChangeIso_hom_fst G.hom s T)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse original pasted comparison carries the extended translated
class to the original translated class, before native Picard evaluation. -/
theorem translationFamilyClass_baseChange_inv {T : Over (Spec (.of K))}
    (t : T ⟶ (Over.pullback s).obj G) (a : PicardGroup G.left) :
    letI : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
    pullbackClass (familyBaseChangeIso G.hom s T).inv
        (translationFamilyClass ((Over.pullback s).obj G) t
          (pullbackClass (pullback.fst G.hom s) a)) =
      translationFamilyClass (T := Over.mk (T.hom ≫ s)) G
        (((Over.mapPullbackAdj s).homEquiv T G).symm t) a := by
  let : GrpObj ((Over.pullback s).obj G) := Functor.grpObjObj
  have h := congrArg (pullbackHom (familyBaseChangeIso G.hom s T).inv)
    (translationFamilyClass_baseChange s G t a).symm
  simpa only [pullbackHom_apply, ← pullbackClass_comp,
    Iso.inv_hom_id, pullbackClass_id] using h

end AlgebraicGeometry.Scheme.RelativePicard
