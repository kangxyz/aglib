/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphLineBundle
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family
public import Aglib.AlgebraicGeometry.Picard.Relative.Groups
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# The actual normalized Abel class on every test scheme

The canonical graph-ideal base-change map supplies equality of actual ideal
line-bundle classes. Tensor and dual pullback compatibility then proves
naturality of O(graph(s)-graph(o_T)). Applying the explicit origin-normalization
projection gives a natural transformation from the universe-lifted scheme
functor of points to the unchanged normalized Picard-class presheaf.
No resizing is asserted: Hom lies in Type u and actual Picard classes in
Type (u+1), so uliftYoneda is used explicitly.

At the origin this transformation is zero, using the previously constructed
dual-evaluation trivialization. Every test scheme, including nonreduced ones,
is allowed. Degree zero, a representing Picard scheme and the all-test inverse
are separate subsequent obligations. The only retained general families are
SmoothRelativeDivisorIdeal (0B9D), RelativeCartierIdealBaseChange (056Q), and
the explicitly separated ModuleTensorPullback (01CD). The Abel naturality
and origin-zero statements themselves are proved applications.

Incoming RelativePicard.Group SHA256
33ac892d639f67b0589b6842d96053e9630d054d4a46c46e7e5985eafe0e2dec;
AlgebraicGeometry.Scheme.Hom.BaseChange SHA256
248af6ad43d5b9f14a845d931a2f5637635ed95715e9da1bd975dafb6504f03b.
Application K2-018#prop:k2018-arithmetic-characters, source
e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/


/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open AlgebraicGeometry.Scheme.Hom RelativePicard
variable {S X T T' : Scheme.{u}}
variable (hdivisor : SmoothRelativeDivisorIdeal.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
variable (htensor : AlgebraicGeometry.Scheme.Modules.Invertible.ModuleTensorPullback.{u})
variable (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
variable (t : T ⟶ S) (t' : T' ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)
variable (a : T' ⟶ T) (ha : a ≫ t = t')

include hbase in
theorem graphIdealClass_baseChange :
    Invertible.pullbackClass (familyMap p t t' a ha) (Invertible.classOf _ (graphIdealLineBundle
      hdivisor p t s hs)) =
      Invertible.classOf _ (graphIdealLineBundle hdivisor p t' (a ≫ s) (by rw [Category.assoc, hs,
        ha])) := by
  apply Quotient.sound
  exact ⟨graphIdealBaseChangeIso hdivisor hbase p t t' s hs a ha⟩

include hbase htensor in
theorem positiveGraphClass_baseChange :
    Invertible.pullbackClass (familyMap p t t' a ha) (Invertible.classOf _
      (positiveGraphLineBundle hdivisor p t s hs)) =
      Invertible.classOf _ (positiveGraphLineBundle hdivisor p t' (a ≫ s) (by rw [Category.assoc,
        hs, ha])) := by
  change Invertible.pullbackClass _ (-Invertible.classOf _ (graphIdealLineBundle hdivisor p t s
    hs)) =
    -Invertible.classOf _ (graphIdealLineBundle hdivisor p t' (a ≫ s) _)
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.pullbackClass_neg htensor,
    graphIdealClass_baseChange hdivisor hbase]

include hbase in
theorem originIdealClass_baseChange :
    Invertible.pullbackClass (familyMap p t t' a ha) (Invertible.classOf _ (originIdealLineBundle
      hdivisor p o ho t)) =
      Invertible.classOf _ (originIdealLineBundle hdivisor p o ho t') := by
  have h := graphIdealClass_baseChange hdivisor hbase p t t' (t ≫ o)
    (by simp [Category.assoc, ho]) a ha
  have he : a ≫ (t ≫ o) = t' ≫ o := by rw [← Category.assoc, ha]
  simpa only [he, originIdealLineBundle] using h

include hbase htensor in
theorem abelClass_baseChange :
    Invertible.pullbackClass (familyMap p t t' a ha) (abelClass hdivisor p o ho t s hs) =
      abelClass hdivisor p o ho t' (a ≫ s) (by rw [Category.assoc, hs, ha]) := by
  rw [abelClass_eq, AlgebraicGeometry.Scheme.Modules.Invertible.pullbackClass_add htensor,
    AlgebraicGeometry.Scheme.Modules.Invertible.pullbackClass_neg htensor,
    graphIdealClass_baseChange hdivisor hbase, originIdealClass_baseChange hdivisor hbase]
  rfl

def abelClassTransformation : uliftYoneda.{u+1}.obj (Over.mk p) ⟶ familyPicardFunctor p where
  app T := ↾fun s ↦ abelClass hdivisor p o ho T.unop.hom s.down.left (Over.w s.down)
  naturality {T T'} f := by
    ext s
    exact (abelClass_baseChange hdivisor hbase htensor p o ho T.unop.hom T'.unop.hom
      s.down.left (Over.w s.down) f.unop.left (Over.w f.unop)).symm

def normalizedAbelClass (T : Over S) (s : T ⟶ Over.mk p) :
    normalizedGroup htensor p o ho T :=
  normalizeHom htensor p o ho T (abelClass hdivisor p o ho T.hom s.left (Over.w s))

set_option backward.isDefEq.respectTransparency false in
def normalizedAbelTransformation : uliftYoneda.{u+1}.obj (Over.mk p) ⟶ normalizedClassFunctor p o
  ho where
  app T := ↾fun s ↦ normalizedAbelClass hdivisor htensor p o ho T.unop s.down
  naturality {T T'} f := by
    ext s
    have hn := normalizeHom_naturality htensor p o ho f.unop
      (abelClass hdivisor p o ho T.unop.hom s.down.left (Over.w s.down))
    apply Subtype.ext
    exact congrArg Subtype.val ((congrArg (normalizeHom htensor p o ho T'.unop)
      (abelClass_baseChange hdivisor hbase htensor p o ho T.unop.hom T'.unop.hom
        s.down.left (Over.w s.down) f.unop.left (Over.w f.unop))).symm.trans hn.symm)

def originPoint (T : Over S) : T ⟶ Over.mk p :=
  Over.homMk (T.hom ≫ o) (by simp [Category.assoc, ho])

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem normalizedAbelClass_origin (T : Over S) :
    normalizedAbelClass hdivisor htensor p o ho T (originPoint p o ho T) = 0 := by
  change normalizeHom htensor p o ho T (abelClass hdivisor p o ho T.hom (T.hom ≫ o) _) = 0
  rw [abelClass_origin, map_zero]
end AlgebraicGeometry.Scheme.OverField.Curve.Abel
