/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ClosureEmbedding
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Naturality

/-!
# Literal finite coefficient points and field pullback composition

Manuscript locators: `K2-018#lem:k2018-geometric-exact-order` and
`K2-018#prop:k2018-arithmetic-characters`. Mathematical basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

All maps are genuine scheme/group pullbacks. Ordinary Over projection lemmas
and the actual compatible closure embeddings prove the finite-point tower
formulas before H1. Native tensor specialization invokes opaque ordinary
point identities; no H1 square or coefficient-isomorphism independence is an
input. The actual squared cyclotomic action stays in the native tensor group.
-/
@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory TensorProduct
open AlgebraicGeometry.Scheme.EtaleH1
open AlgebraicGeometry.Scheme.Group
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open _root_.GroupCohomology.ContinuousH1
open Field.absoluteGaloisGroup.RootsOfUnity
namespace AlgebraicGeometry.Scheme.Group.BaseChange.PointTransport
universe u w w'
attribute [local instance] Over.cartesianMonoidalCategory

/-- Opaque projection of composition of group morphisms onto literal points. -/
theorem groupPoint_comp {X : Scheme.{u}} {A B D : Grp (Over X)} {U : Over X}
    (a : U ⟶ A.X) (f : A ⟶ B) (g : B ⟶ D) :
    a ≫ (f ≫ g).hom.hom = (a ≫ f.hom.hom) ≫ g.hom.hom :=
  (congrArg (fun q => a ≫ q) (Grp.comp_hom_hom f g)).trans (Category.assoc _ _ _).symm

/-- Three group maps act by the same ordinary three point maps. -/
theorem groupPoint_comp_three {X : Scheme.{u}} {A B D E : Grp (Over X)} {U : Over X}
    (a : U ⟶ A.X) (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) :
    a ≫ (f ≫ g ≫ h).hom.hom = (a ≫ f.hom.hom ≫ g.hom.hom) ≫ h.hom.hom :=
  (groupPoint_comp a f (g ≫ h)).trans
    ((groupPoint_comp (a ≫ f.hom.hom) g h).trans
      (congrArg (fun q => q ≫ h.hom.hom) (Category.assoc _ _ _)))

/-- Canonical group-object composition of actual scheme pullback. -/
def groupPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Grp (Over Z)) :
    baseChangedGroup f (baseChangedGroup g A) ≅ baseChangedGroup (f ≫ g) A :=
  ((Functor.mapGrpCompIso (F := Over.pullback g) (G := Over.pullback f)).app A).symm ≪≫
    (Functor.mapGrpNatIso (Over.pullbackComp f g).symm).app A

/-- The actual group-object composition has the canonical underlying Over arrow. -/
theorem groupPullbackCompIso_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Grp (Over Z)) :
    (groupPullbackCompIso f g A).hom.hom.hom = (Over.pullbackComp f g).inv.app A.X := by
  simp [groupPullbackCompIso]

/-- The group pullback-composition map is the literal iterated pullback projection. -/
theorem groupPullbackCompIso_projection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Grp (Over Z)) :
    (groupPullbackCompIso f g A).hom.hom.hom =
      MultiplicativeBaseChange.pullbackComposeMap f g A.X := by
  rw [groupPullbackCompIso_hom]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h := conjugateEquiv_counit ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
      (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom A.X
    have hh := congrArg (fun q => q.left) h
    change ((Over.pullbackComp f g).inv.app A.X).left ≫ pullback.fst A.X.hom (f ≫ g) =
      (MultiplicativeBaseChange.pullbackComposeMap f g A.X).left ≫ pullback.fst A.X.hom (f ≫ g)
    simp [Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit_app,
      MultiplicativeBaseChange.pullbackComposeMap, Category.assoc]
  · exact (Over.w ((Over.pullbackComp f g).inv.app A.X)).trans
      (Over.w (MultiplicativeBaseChange.pullbackComposeMap f g A.X)).symm

/-- Pullback of actual coefficient points with an explicitly identified base point. -/
def pointedGroupPointEquiv {X S : Scheme.{u}} {C : Type u} [Field C]
    (f : S ⟶ X) (s : Spec (.of C) ⟶ S) (x : Spec (.of C) ⟶ X)
    (hx : s ≫ f = x) (A : Grp (Over X)) :
    (Over.mk x ⟶ A.X) ≃* (Over.mk s ⟶ (baseChangedGroup f A).X) := by
  subst x
  exact _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s A

@[simp] theorem pointedGroupPointEquiv_left {X S : Scheme.{u}} {C : Type u} [Field C]
    (f : S ⟶ X) (s : Spec (.of C) ⟶ S) (x : Spec (.of C) ⟶ X)
    (hx : s ≫ f = x) (A : Grp (Over X)) (a : Over.mk x ⟶ A.X) :
    (pointedGroupPointEquiv f s x hx A a).left =
      pullback.lift a.left s (by exact (Over.w a).trans hx.symm) := by
  subst x
  change (((Over.mapPullbackAdj f).homEquiv (Over.mk s) A.X) a).left = _
  simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The canonical pointed coefficient marking is inverse to the actual point pullback. -/
theorem pointedPullbackFiberMark_point {X S : Scheme.{u}} {C : Type u} [Field C]
    (f : S ⟶ X) (s : Spec (.of C) ⟶ S) (x : Spec (.of C) ⟶ X) (hx : s ≫ f = x)
    (A : Grp (Over X)) [IsCommMonObj A.X] [IsFinite A.X.hom] [Etale A.X.hom]
    (M : Type*) [AddCommGroup M] (m : (Over.mk x ⟶ A.X) ≃* Multiplicative M)
    (a : Over.mk x ⟶ A.X) :
    _root_.AlgebraicGeometry.Scheme.EtaleH1.Naturality.pointedPullbackFiberMark f s x hx A M m
      (pointedGroupPointEquiv f s x hx A a) = m a := by
  subst x
  change m ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s
    A).symm
    ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv f s A) a)) =
      m a
  rw [MulEquiv.symm_apply_apply]

/-- Canonical group pullback composition has exactly the iterated literal point map. -/
theorem groupPullbackCompIso_point {X Y Z : Scheme.{u}} {C : Type u} [Field C]
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Spec (.of C) ⟶ X)
    (y : Spec (.of C) ⟶ Y) (z : Spec (.of C) ⟶ Z)
    (hy : s ≫ f = y) (hz : y ≫ g = z) (A : Grp (Over Z))
    (a : Over.mk z ⟶ A.X) :
    pointedGroupPointEquiv f s y hy (baseChangedGroup g A)
        (pointedGroupPointEquiv g y z hz A a) ≫ (groupPullbackCompIso f g A).hom.hom.hom =
      pointedGroupPointEquiv (f ≫ g) s z (by rw [← Category.assoc, hy, hz]) A a := by
  rw [groupPullbackCompIso_projection]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, pointedGroupPointEquiv_left,
    MultiplicativeBaseChange.pullbackComposeMap]
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Actual pointed pullback of coefficient points is natural in group morphisms. -/
theorem pointedGroupPointEquiv_naturality {X S : Scheme.{u}} {C : Type u} [Field C]
    (f : S ⟶ X) (s : Spec (.of C) ⟶ S) (x : Spec (.of C) ⟶ X)
    (hx : s ≫ f = x) {A B : Grp (Over X)} (q : A ⟶ B)
    (a : Over.mk x ⟶ A.X) :
    pointedGroupPointEquiv f s x hx B (a ≫ q.hom.hom) =
      pointedGroupPointEquiv f s x hx A a ≫ ((Over.pullback f).mapGrp.map q).hom.hom := by
  subst x
  exact (Over.mapPullbackAdj f).homEquiv_naturality_right (X := Over.mk s) a q.hom.hom

/-- Equality of the actual scheme maps gives the literal corresponding point transport. -/
theorem pointedGroupPointEquiv_congr {X S : Scheme.{u}} {C : Type u} [Field C]
    {f g : S ⟶ X} (he : f = g) (s : Spec (.of C) ⟶ S)
    (x : Spec (.of C) ⟶ X) (hf : s ≫ f = x) (hg : s ≫ g = x)
    (A : Grp (Over X)) (a : Over.mk x ⟶ A.X) :
    pointedGroupPointEquiv f s x hf A a ≫
      (eqToIso (congrArg (fun k => baseChangedGroup k A) he)).hom.hom.hom =
      pointedGroupPointEquiv g s x hg A a := by
  subst g
  simp

/-- Ordinary pullback composition, tested only on underlying Over projections.
This isolates scheme pullback coherence from any group-object transport. -/
theorem pullbackComposePoint_ext {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) {h : Z ⟶ X} (e : f ≫ g = h)
    (A : Over X) {U : Over Z}
    (a : U ⟶ (Over.pullback f).obj ((Over.pullback g).obj A))
    (b : U ⟶ (Over.pullback h).obj A)
    (hp : a.left ≫ pullback.fst ((Over.pullback g).obj A).hom f ≫
        pullback.fst A.hom g = b.left ≫ pullback.fst A.hom h) :
    a ≫ MultiplicativeBaseChange.pullbackComposeMap f g A ≫
      (eqToIso (congrArg (fun k => (Over.pullback k).obj A) e)).hom = b := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.comp_left, MultiplicativeBaseChange.pullbackComposeMap,
      Over.homMk_left, Category.assoc, pullback.lift_fst] using hp
  · exact (Over.w _).trans (Over.w _).symm

section FieldPointTransport
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    (i : FieldPullbackIndependence.Embedding (K := K) (L := L))

/-- Actual finite group points transported along a displayed closure embedding
and the genuine scheme pullback adjunction. -/
def fieldGroupPointEquiv (A : Grp (Over (Spec (.of K)))) [IsFinite A.X.hom] :
    (Over.mk (geometricPoint K) ⟶ A.X) ≃*
      (Over.mk (geometricPoint L) ⟶
        (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A).X) := by
  letI := i.toAlgebra
  exact (_root_.AlgebraicGeometry.Scheme.FiniteEtale.GeometricFibres.finiteGroupPointEquiv
    (AlgebraicClosure K) (AlgebraicClosure L) (ClosureEmbedding.pointExtension i) rfl A).trans
      (_root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange.pullbackFiberMulEquiv
        (ClosureEmbedding.fieldMorphism (K := K) (L := L)) (geometricPoint L) A)

@[reassoc] theorem fieldGroupPointEquiv_fst (A : Grp (Over (Spec (.of K)))) [IsFinite A.X.hom]
    (a : Over.mk (geometricPoint K) ⟶ A.X) :
    (fieldGroupPointEquiv i A a).left ≫
      pullback.fst A.X.hom (ClosureEmbedding.fieldMorphism (K := K) (L := L)) =
      (ClosureEmbedding.pointExtension i).left ≫ a.left := by
  change (((Over.mapPullbackAdj (ClosureEmbedding.fieldMorphism (K := K) (L := L))).homEquiv
    (Over.mk (geometricPoint L)) A.X) (ClosureEmbedding.pointExtension i ≫ a)).left ≫
      pullback.fst A.X.hom (ClosureEmbedding.fieldMorphism (K := K) (L := L)) = _
  simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

/-- Ordinary point transport commutes with every actual coefficient group map. -/
theorem fieldGroupPointEquiv_naturality {A B : Grp (Over (Spec (.of K)))}
    [IsFinite A.X.hom] [IsFinite B.X.hom] (q : A ⟶ B)
    (a : Over.mk (geometricPoint K) ⟶ A.X) :
    fieldGroupPointEquiv i B (a ≫ q.hom.hom) =
      fieldGroupPointEquiv i A a ≫
        ((Over.pullback (ClosureEmbedding.fieldMorphism (K := K) (L := L))).mapGrp.map q).hom.hom :=
          by
  change ((Over.mapPullbackAdj (ClosureEmbedding.fieldMorphism (K := K) (L := L))).homEquiv
    (Over.mk (geometricPoint L)) B.X) (ClosureEmbedding.pointExtension i ≫ (a ≫ q.hom.hom)) = _
  rw [← Category.assoc]
  exact (Over.mapPullbackAdj (ClosureEmbedding.fieldMorphism (K := K) (L :=
    L))).homEquiv_naturality_right
    (X := Over.mk (geometricPoint L)) (ClosureEmbedding.pointExtension i ≫ a) q.hom.hom

end FieldPointTransport

section FieldTowerPoints
variable {K L M : Type u} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- The actual field spectrum maps compose according to the given scalar tower. -/
theorem fieldMorphism_comp :
    ClosureEmbedding.fieldMorphism (K := L) (L := M) ≫
      ClosureEmbedding.fieldMorphism (K := K) (L := L) =
    ClosureEmbedding.fieldMorphism (K := K) (L := M) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (IsScalarTower.algebraMap_apply K L M a).symm

/-- The underlying ordinary Over arrow of a group-pullback equality transport. -/
theorem groupPullbackCongr_hom {X S : Scheme.{u}} {f g : S ⟶ X} (he : f = g)
    (A : Grp (Over X)) :
    (eqToIso (congrArg (fun k => baseChangedGroup k A) he)).hom.hom.hom =
      (eqToIso (congrArg (fun k => (Over.pullback k).obj A.X) he)).hom := by
  subst g
  rfl

/-- Group pullback-composition and equality transport are controlled by one
ordinary projection equation, before specializing any actual field maps. -/
theorem groupPullbackComposePoint_ext {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) {h : Z ⟶ X} (e : f ≫ g = h)
    (A : Grp (Over X)) {U : Over Z}
    (a : U ⟶ (baseChangedGroup f (baseChangedGroup g A)).X)
    (b : U ⟶ (baseChangedGroup h A).X)
    (hp : a.left ≫ pullback.fst (baseChangedGroup g A).X.hom f ≫
        pullback.fst A.X.hom g = b.left ≫ pullback.fst A.X.hom h) :
    a ≫ (groupPullbackCompIso f g A).hom.hom.hom ≫
      (eqToIso (congrArg (fun k => baseChangedGroup k A) e)).hom.hom.hom = b := by
  rw [groupPullbackCompIso_projection, groupPullbackCongr_hom e]
  exact pullbackComposePoint_ext f g e A.X a b hp

/-- The actual closure-point extensions compose under the literal embedding composite. -/
theorem pointExtension_comp_left
    (i : FieldPullbackIndependence.Embedding (K := K) (L := L))
    (j : FieldPullbackIndependence.Embedding (K := L) (L := M)) :
    (ClosureEmbedding.pointExtension j).left ≫
      (ClosureEmbedding.pointExtension i).left =
      (ClosureEmbedding.pointExtension (FieldPullbackIndependence.embeddingComp j i)).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Transport by equality of actual base maps preserves the first pullback projection. -/
theorem groupPullbackCongr_fst {X S : Scheme.{u}} {f g : S ⟶ X} (he : f = g)
    (A : Grp (Over X)) :
    (eqToIso (congrArg (fun k => baseChangedGroup k A) he)).hom.hom.hom.left ≫
      pullback.fst A.X.hom g = pullback.fst A.X.hom f := by
  subst g
  simp

/-- The field-point composition calculation takes place only in ordinary
scheme morphisms, with no group-pullback equality transports in the proof. -/
theorem fieldGroupPointEquiv_comp_projection
    (i : FieldPullbackIndependence.Embedding (K := K) (L := L))
    (j : FieldPullbackIndependence.Embedding (K := L) (L := M))
    (A : Grp (Over (Spec (.of K)))) [IsFinite A.X.hom]
    (a : Over.mk (geometricPoint K) ⟶ A.X) :
    (fieldGroupPointEquiv j
        (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)
        (fieldGroupPointEquiv i A a)).left ≫
      pullback.fst (baseChangedGroup
        (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A).X.hom
        (ClosureEmbedding.fieldMorphism (K := L) (L := M)) ≫
      pullback.fst A.X.hom (ClosureEmbedding.fieldMorphism (K := K) (L := L)) =
    (fieldGroupPointEquiv (FieldPullbackIndependence.embeddingComp j i) A a).left ≫
      pullback.fst A.X.hom (ClosureEmbedding.fieldMorphism (K := K) (L := M)) := by
  have h₁ := fieldGroupPointEquiv_fst j
    (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)
    (fieldGroupPointEquiv i A a)
  have h₂ := fieldGroupPointEquiv_fst i A a
  have h₃ := fieldGroupPointEquiv_fst (FieldPullbackIndependence.embeddingComp j i) A a
  calc
    _ = ((fieldGroupPointEquiv j
        (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)
        (fieldGroupPointEquiv i A a)).left ≫
      pullback.fst (baseChangedGroup
        (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A).X.hom
        (ClosureEmbedding.fieldMorphism (K := L) (L := M))) ≫
      pullback.fst A.X.hom (ClosureEmbedding.fieldMorphism (K := K) (L := L)) :=
        (Category.assoc _ _ _).symm
    _ = ((ClosureEmbedding.pointExtension j).left ≫
        (fieldGroupPointEquiv i A a).left) ≫
      pullback.fst A.X.hom (ClosureEmbedding.fieldMorphism (K := K) (L := L)) :=
        congrArg (fun q => q ≫ pullback.fst A.X.hom
          (ClosureEmbedding.fieldMorphism (K := K) (L := L))) h₁
    _ = (ClosureEmbedding.pointExtension j).left ≫
        ((ClosureEmbedding.pointExtension i).left ≫ a.left) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => (ClosureEmbedding.pointExtension j).left ≫ q) h₂)
    _ = (ClosureEmbedding.pointExtension
        (FieldPullbackIndependence.embeddingComp j i)).left ≫ a.left :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ a.left) (pointExtension_comp_left i j))
    _ = _ := h₃.symm

/-- Literal finite coefficient-point extension composes with the actual group
pullback-composition iso and the actual scalar-tower equality. -/
theorem fieldGroupPointEquiv_comp
    (i : FieldPullbackIndependence.Embedding (K := K) (L := L))
    (j : FieldPullbackIndependence.Embedding (K := L) (L := M))
    (A : Grp (Over (Spec (.of K)))) [IsFinite A.X.hom]
    (a : Over.mk (geometricPoint K) ⟶ A.X) :
    fieldGroupPointEquiv j (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)
        (fieldGroupPointEquiv i A a) ≫
      (groupPullbackCompIso (ClosureEmbedding.fieldMorphism (K := L) (L := M))
        (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A).hom.hom.hom ≫
      (eqToIso (congrArg (fun f => baseChangedGroup f A)
        (fieldMorphism_comp (K := K) (L := L) (M := M)))).hom.hom.hom =
    fieldGroupPointEquiv (FieldPullbackIndependence.embeddingComp j i) A a := by
  exact groupPullbackComposePoint_ext
    (ClosureEmbedding.fieldMorphism (K := L) (L := M))
    (ClosureEmbedding.fieldMorphism (K := K) (L := L))
    (fieldMorphism_comp (K := K) (L := L) (M := M)) A _ _
    (fieldGroupPointEquiv_comp_projection i j A a)

end FieldTowerPoints

section TensorTowerCoefficients
variable {K L M : Type u} [Field K] [Field L] [Field M]
  [CharZero K] [CharZero L] [CharZero M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  (i : FieldPullbackIndependence.Embedding (K := K) (L := L))
  (j : FieldPullbackIndependence.Embedding (K := L) (L := M))
  (n : ℕ) [NeZero n]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of M)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint M))]

/- Faithfulness after two ordinary field-point extensions. Keeping the
surjectivity eliminations generic avoids expanding descended tensor objects. -/
omit [CharZero K] [CharZero L] [CharZero M] [Algebra K M] [IsScalarTower K L M]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
  [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))] in
theorem fieldTowerGroupHom_ext
    [CharZero K] [CharZero L] [CharZero M] [Algebra K M] [IsScalarTower K L M]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of K)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint K))]
    [GaloisCategory (Scheme.FiniteEtale (Spec (.of L)))]
    [PreGaloisCategory.FiberFunctor (fiberToFinite (geometricPoint L))]
    (A : Grp (Over (Spec (.of K)))) [IsFinite A.X.hom] [Etale A.X.hom]
    {B : Grp (Over (Spec (.of M)))} [IsFinite B.X.hom] [Etale B.X.hom]
    (q r : baseChangedGroup (ClosureEmbedding.fieldMorphism (K := L) (L := M))
      (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A) ⟶ B)
    (h : ∀ a : Over.mk (geometricPoint K) ⟶ A.X,
      fieldGroupPointEquiv j
          (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)
          (fieldGroupPointEquiv i A a) ≫ q.hom.hom =
        fieldGroupPointEquiv j
          (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)
          (fieldGroupPointEquiv i A a) ≫ r.hom.hom) : q = r := by
  apply Grp.hom_ext
  apply finiteEtale_hom_ext (geometricPoint M)
  intro a
  obtain ⟨aL, rfl⟩ := (fieldGroupPointEquiv j
    (baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A)).surjective a
  obtain ⟨aK, rfl⟩ := (fieldGroupPointEquiv i A).surjective aL
  exact h aK

/-- A tower square of ordinary finite-group coefficient maps follows from its
literal point square. All coefficient groups remain generic in this proof. -/
theorem fieldTowerCoefficientHom_comp
    (A : Grp (Over (Spec (.of K)))) [IsFinite A.X.hom] [Etale A.X.hom]
    (B : Grp (Over (Spec (.of L)))) [IsFinite B.X.hom] [Etale B.X.hom]
    (D : Grp (Over (Spec (.of M)))) [IsFinite D.X.hom] [Etale D.X.hom]
    (α : baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A ⟶ B)
    (β : baseChangedGroup (ClosureEmbedding.fieldMorphism (K := L) (L := M)) B ⟶ D)
    (γ : baseChangedGroup (ClosureEmbedding.fieldMorphism (K := K) (L := M)) A ⟶ D)
    (hp : ∀ a : Over.mk (geometricPoint K) ⟶ A.X,
      fieldGroupPointEquiv j B (fieldGroupPointEquiv i A a ≫ α.hom.hom) ≫ β.hom.hom =
        fieldGroupPointEquiv (FieldPullbackIndependence.embeddingComp j i) A a ≫ γ.hom.hom) :
    ((Over.pullback (ClosureEmbedding.fieldMorphism (K := L) (L := M))).mapGrp.map α) ≫ β =
      (groupPullbackCompIso (ClosureEmbedding.fieldMorphism (K := L) (L := M))
        (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A).hom ≫
      (eqToIso (congrArg (fun f => baseChangedGroup f A)
        (fieldMorphism_comp (K := K) (L := L) (M := M)))).hom ≫ γ := by
  apply fieldTowerGroupHom_ext i j A
  intro a
  have hn := fieldGroupPointEquiv_naturality j α (fieldGroupPointEquiv i A a)
  have hc := fieldGroupPointEquiv_comp i j A a
  have hleft := groupPoint_comp
    (fieldGroupPointEquiv j _ (fieldGroupPointEquiv i A a))
    ((Over.pullback (ClosureEmbedding.fieldMorphism (K := L) (L := M))).mapGrp.map α) β
  have hright := groupPoint_comp_three
    (fieldGroupPointEquiv j _ (fieldGroupPointEquiv i A a))
    (groupPullbackCompIso (ClosureEmbedding.fieldMorphism (K := L) (L := M))
      (ClosureEmbedding.fieldMorphism (K := K) (L := L)) A).hom
    (eqToIso (congrArg (fun f => baseChangedGroup f A)
      (fieldMorphism_comp (K := K) (L := L) (M := M)))).hom γ
  exact hleft.trans
    ((congrArg (fun q => q ≫ β.hom.hom) hn.symm).trans
      ((hp a).trans ((congrArg (fun q => q ≫ γ.hom.hom) hc.symm).trans hright.symm)))

end TensorTowerCoefficients
end AlgebraicGeometry.Scheme.Group.BaseChange.PointTransport
