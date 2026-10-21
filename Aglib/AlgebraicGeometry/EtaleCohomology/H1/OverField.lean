/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteLocallyConstant
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Arbitrary coefficients and rational sections over a field

For an F-scheme and rational section, the origin map is actual inverse-image
H1 pullback. Its kernel is functorial in every abelian field coefficient.
The structural pullback between F-schemes carries the canonical composition
identification and commutes with coefficient maps. Positive integers are
invertible on a characteristic-zero field scheme.

These generic interfaces are extracted from the Tate coefficient and pointed
modules at R5Lab revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
The original construction basis is `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`;
mathematical source `K2-018#eq:k2018-pointed-character` and
`K2-018#eq:k2018-coefficient-compatibility`, revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, source SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
Legacy declaration namespaces are preserved, with no Tate coefficient hypothesis.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.OverField` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c950d212763c2524de11b5e117d63f40d7a179b70583a86cda2997aee14bffae`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology _root_.CategoryTheory.Functor.LargePresheaf

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TatePointed
universe u
attribute [local instance] hasSheafifyLarge hasExtStandard
variable (F : Type u) [Field F]
variable (X : FScheme F) (o : Over.mk (𝟙 (Base F)) ⟶ X)
variable (L : AbelianSheaf.{u, u + 1} (Base F))

/-- Canonical composition/identity transport along the actual rational origin. -/
abbrev originCoefficientIso :
    (inverseImage o.left).obj ((inverseImage X.hom).obj L) ≅ L :=
  Scheme.EtaleCohomology.PointedNaturality.sectionCoefficientIso X.hom o.left o.w L

/-- Actual H1 pullback to the rational origin with the original field coefficient. -/
abbrev originPullback :
    H1Etale.{u, u + 1, u + 2} X.left ((inverseImage X.hom).obj L) →+
      H1Etale.{u, u + 1, u + 2} (Base F) L :=
  Scheme.EtaleCohomology.PointedNaturality.sectionPullback X.hom o.left o.w L

/-- Origin-zero cohomology is the additive kernel, with no chosen trivialization. -/
abbrev PointedH1 := (originPullback F X o L).ker

theorem originPullback_inflation (a : H1Etale.{u, u + 1, u + 2} (Base F) L) :
    originPullback F X o L (h1Pullback X.hom L a) = a :=
  Scheme.EtaleCohomology.PointedNaturality.sectionPullback_inflation X.hom
      o.left o.w L a

theorem originPullback_coefficient {L M : AbelianSheaf.{u, u + 1} (Base F)}
    (q : L ⟶ M) (a : H1Etale.{u, u + 1, u + 2} X.left ((inverseImage X.hom).obj L)) :
    originPullback F X o M (coefficientMap ((inverseImage X.hom).map q) a) =
      coefficientMap q (originPullback F X o L a) :=
  Scheme.EtaleCohomology.PointedNaturality.sectionPullback_coefficient X.hom
      o.left o.w q a

/-- Every actual field coefficient morphism restricts to the actual origin kernel. -/
def pointedCoefficientMap {L M : AbelianSheaf.{u, u + 1} (Base F)} (q : L ⟶ M) :
    PointedH1 F X o L →+ PointedH1 F X o M where
  toFun a := ⟨coefficientMap ((inverseImage X.hom).map q) a.1, by
    change originPullback F X o M _ = 0
    rw [originPullback_coefficient, show originPullback F X o L a.1 = 0 from a.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)


@[simp] theorem pointedCoefficientMap_id :
    pointedCoefficientMap F X o (𝟙 L) = AddMonoidHom.id (PointedH1 F X o L) := by
  ext a
  change coefficientMap ((inverseImage X.hom).map (𝟙 L)) a.1 = a.1
  rw [CategoryTheory.Functor.map_id, coefficientMap_id]
  rfl

theorem pointedCoefficientMap_comp {L M N : AbelianSheaf.{u, u + 1} (Base F)}
    (q : L ⟶ M) (r : M ⟶ N) :
    pointedCoefficientMap F X o (q ≫ r) =
      (pointedCoefficientMap F X o r).comp (pointedCoefficientMap F X o q) := by
  ext a
  change coefficientMap ((inverseImage X.hom).map (q ≫ r)) a.1 =
    coefficientMap ((inverseImage X.hom).map r)
      (coefficientMap ((inverseImage X.hom).map q) a.1)
  rw [CategoryTheory.Functor.map_comp, coefficientMap_comp]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.TatePointed

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TateCoefficients
universe u
attribute [local instance] hasSheafifyLarge hasExtStandard
variable (F : Type u) [Field F]

section LevelInvertible
variable [CharZero F] (n : ℕ) [NeZero n]
/-- Every positive integer is an actual unit on Spec of this characteristic-zero field. -/
theorem levelInvertible : LevelInvertible (Base F) n := by
  have hn : IsUnit (n : F) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  simpa only [LevelInvertible, map_natCast] using hn.map (Scheme.ΓSpecIso (.of F)).inv.hom

end LevelInvertible

variable {X Y : FScheme F}
/-- Canonical structural-map coefficient identification for a morphism of F-schemes. -/
def overInverseImage (q : X ⟶ Y) :
    inverseImage Y.hom ⋙ inverseImage q.left ≅ inverseImage X.hom :=
  (inverseImageComp Y.hom q.left).symm ≪≫
    eqToIso (congrArg (fun f : X.left ⟶ Base F => inverseImage f) q.w)

/-- Actual scheme H1 pullback with the canonical coefficient identification. -/
def overH1Pullback (q : X ⟶ Y) (L : AbelianSheaf.{u, u + 1} (Base F)) :
    H1Etale.{u, u + 1, u + 2} Y.left ((inverseImage Y.hom).obj L) →+
      H1Etale.{u, u + 1, u + 2} X.left ((inverseImage X.hom).obj L) :=
  (coefficientMap ((overInverseImage F q).hom.app L)).comp
    (h1Pullback q.left ((inverseImage Y.hom).obj L))

private theorem coefficient_natural {B T : Scheme.{u}}
    {V W : AbelianSheaf.{u, u + 1} B ⥤ AbelianSheaf.{u, u + 1} T} (e : V ⟶ W)
    {L M : AbelianSheaf.{u, u + 1} B} (a : L ⟶ M)
    (x : H1Etale.{u, u + 1, u + 2} T (V.obj L)) :
    coefficientMap (e.app M) (coefficientMap (V.map a) x) =
      coefficientMap (W.map a) (coefficientMap (e.app L) x) := by
  change ((coefficientMap (e.app M)).comp (coefficientMap (V.map a))) x =
    ((coefficientMap (W.map a)).comp (coefficientMap (e.app L))) x
  rw [← coefficientMap_comp, ← coefficientMap_comp, e.naturality a]

/-- All structural pullback wrappers commute with actual coefficient morphisms. -/
theorem overH1Pullback_coefficient (q : X ⟶ Y)
    {L M : AbelianSheaf.{u, u + 1} (Base F)} (a : L ⟶ M)
    (x : H1Etale.{u, u + 1, u + 2} Y.left ((inverseImage Y.hom).obj L)) :
    overH1Pullback F q M (coefficientMap ((inverseImage Y.hom).map a) x) =
      coefficientMap ((inverseImage X.hom).map a) (overH1Pullback F q L x) := by
  let b : H1Etale.{u, u + 1, u + 2} X.left ((inverseImage q.left).obj ((inverseImage Y.hom).obj
      L)) :=
    h1Pullback q.left ((inverseImage Y.hom).obj L) x
  calc
    _ = coefficientMap ((overInverseImage F q).hom.app M)
        (coefficientMap ((inverseImage q.left).map ((inverseImage Y.hom).map a)) b) :=
      congrArg (coefficientMap ((overInverseImage F q).hom.app M))
        (h1Pullback_coefficientMap q.left ((inverseImage Y.hom).map a) x)
    _ = _ := coefficient_natural (overInverseImage F q).hom a b

end AlgebraicGeometry.Scheme.EtaleCohomology.TateCoefficients
