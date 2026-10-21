/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Embedding
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
# Field-extension transport of actual scheme points

Finite point transport already native; faithfully delegate native precompose_bijective and actual
pullback equivalence, then exact chosen closurePointArrow/absoluteRestriction naturality. Do not
introduce another closure embedding.

Source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.FieldExtension`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ddaa5424e1c95a2c1d966a0a8487e460451712b33f265a42155ccab432bf0901`. Selected lines: [[23, 104]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.Group.BaseChange (scalarExtensionMap)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale
namespace AlgebraicGeometry.Scheme.RationalPoint
universe u
variable {F K : Type u} [Field F] [Field K] (i : F →+* K)
/-- Actual pullback adjunction on the selected completion geometric point. -/
def pullbackPointEquiv (X : FScheme F) :
    (Over.mk (FieldEmbeddingBaseChange.extensionPoint i) ⟶ X) ≃
      (Over.mk (FieldGalois.geometricPoint K) ⟶ (Over.pullback (scalarExtensionMap i)).obj X) :=
  (Over.mapPullbackAdj (scalarExtensionMap i)).homEquiv
    (Over.mk (FieldGalois.geometricPoint K)) X

/-- The actual point map uses Spec of the same compatible closure embedding,
then the literal scheme pullback. It is defined for arbitrary X. -/
def pointExtensionMap (X : FScheme F)
    (p : Over.mk (FieldGalois.geometricPoint F) ⟶ X) :
    Over.mk (FieldGalois.geometricPoint K) ⟶ (Over.pullback (scalarExtensionMap i)).obj X :=
  pullbackPointEquiv i X (FieldEmbeddingBaseChange.closurePointArrow i ≫ p)

theorem pullbackPointEquiv_left (X : FScheme F)
    (p : Over.mk (FieldEmbeddingBaseChange.extensionPoint i) ⟶ X) :
    (pullbackPointEquiv i X p).left =
      pullback.lift p.left (FieldGalois.geometricPoint K) (Over.w p) := by
  simp only [pullbackPointEquiv, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The first projection is exactly precomposition by native Spec(j). -/
@[reassoc (attr := simp)] theorem pointExtensionMap_fst (X : FScheme F)
    (p : Over.mk (FieldGalois.geometricPoint F) ⟶ X) :
    (pointExtensionMap i X p).left ≫ pullback.fst X.hom (scalarExtensionMap i) =
      Spec.map (CommRingCat.ofHom (FieldEmbeddingBaseChange.closureEmbedding i)) ≫ p.left := by
  rw [pointExtensionMap, pullbackPointEquiv_left, pullback.lift_fst]
  rfl

/-- For a finite actual scheme the exact point map is bijective. -/
theorem pointExtensionMap_bijective (X : FScheme F) [IsFinite X.hom] :
    Function.Bijective (pointExtensionMap i X) :=
  (pullbackPointEquiv i X).bijective.comp
    (GeometricFibres.closedPoint_precompose_bijective F (AlgebraicClosure K)
      (FieldEmbeddingBaseChange.extensionPoint i) X)

/-- The bijection on actual points of a finite scheme, with the same chosen closure arrow. -/
def pointExtensionEquiv (X : FScheme F) [IsFinite X.hom] :
    (Over.mk (FieldGalois.geometricPoint F) ⟶ X) ≃
      (Over.mk (FieldGalois.geometricPoint K) ⟶ (Over.pullback (scalarExtensionMap i)).obj X) :=
  Equiv.ofBijective (pointExtensionMap i X) (pointExtensionMap_bijective i X)

/-- Naturality also holds when the target scheme is not finite, allowing
application to the literal kernel inclusion into the elliptic curve. -/
theorem pointExtensionMap_naturality {X Y : FScheme F} (h : X ⟶ Y)
    (p : Over.mk (FieldGalois.geometricPoint F) ⟶ X) :
    pointExtensionMap i Y (p ≫ h) =
      pointExtensionMap i X p ≫ (Over.pullback (scalarExtensionMap i)).map h := by
  change pullbackPointEquiv i Y (FieldEmbeddingBaseChange.closurePointArrow i ≫ (p ≫ h)) = _
  rw [← Category.assoc]
  exact (Over.mapPullbackAdj (scalarExtensionMap i)).homEquiv_naturality_right _ h

section Galois
variable [CharZero F] [CharZero K]

/-- The actual field restriction intertwines the same chosen closure arrow. -/
theorem closurePointArrow_galois (g : Field.absoluteGaloisGroup K) :
    FieldEmbeddingBaseChange.closurePointArrow i ≫
        FieldGalois.pointEnd F (FieldEmbeddingBaseChange.absoluteRestriction i g) =
      (Over.map (scalarExtensionMap i)).map (FieldGalois.pointEnd K g) ≫
        FieldEmbeddingBaseChange.closurePointArrow i := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (FieldEmbeddingBaseChange.closureEmbedding i)) ≫
      Spec.map (CommRingCat.ofHom (FieldEmbeddingBaseChange.absoluteRestriction i g).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (FieldEmbeddingBaseChange.closureEmbedding i))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact FieldEmbeddingBaseChange.absoluteRestriction_commutes i g x

/-- Actual global and completion field actions commute with the exact point map. -/
theorem pointExtensionMap_galois (X : FScheme F) (g : Field.absoluteGaloisGroup K)
    (p : Over.mk (FieldGalois.geometricPoint F) ⟶ X) :
    pointExtensionMap i X
        (FieldGalois.pointEnd F (FieldEmbeddingBaseChange.absoluteRestriction i g) ≫ p) =
      FieldGalois.pointEnd K g ≫ pointExtensionMap i X p := by
  change pullbackPointEquiv i X (FieldEmbeddingBaseChange.closurePointArrow i ≫
    (FieldGalois.pointEnd F (FieldEmbeddingBaseChange.absoluteRestriction i g) ≫ p)) = _
  rw [← Category.assoc, closurePointArrow_galois, Category.assoc]
  exact (Over.mapPullbackAdj (scalarExtensionMap i)).homEquiv_naturality_left _ _

end Galois

end AlgebraicGeometry.Scheme.RationalPoint
