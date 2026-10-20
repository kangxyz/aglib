/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Canonical pullback of relative Cartier ideal sheaves

For every commutative square, the ideal comparison is constructed from the
actual kernel universal property, pushforward preservation of kernels, and the
module pullback adjunction. Its composite with the ideal inclusion is proved
to be pullback of the original inclusion followed by the canonical map to O.
No flatness or invertibility assumption is used merely to construct this map.

`RelativeCartierIdealBaseChange` is an explicit general proof-level corollary
of Stacks Lemma 31.19.1, tag 056Q. Its two actual cartesian squares and the
flatness of D over S are essential. The source's tensor-exactness proof identifies
the canonical pulled-back ideal, not just an unrelated invertible module. It
requires no flatness of the base change or the ambient family and no reducedness.
The statement, proof and 2015 notation correction were inspected 2026-10-09;
the complete external proof dependencies remain retained standard foundations.

For graph ideals, both cartesian squares are proved in RelativeDivisors, the
Cartier condition follows from the actual smooth relative-curve application,
and flatness follows because the graph maps identically to the parameter
scheme. The resulting isomorphism is induced by the constructed canonical
ideal map on every test scheme, including nonreduced schemes. Its sign is
O(-graph); taking the dual gives the positive divisor only downstream.

Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.BaseChange` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`12b6e050d9925bf8a7aaf90ecab11b02bf5969e1e16eaeee38936585d5f48341`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X Y Z : Scheme.{u}}
/-- The theorem-family input asserting that the canonical ideal pullback map is invertible
for cartesian base change of a closed Cartier subscheme flat over the family base. -/
def RelativeCartierIdealBaseChange : Prop :=
  ∀ (S T X Y D D' : Scheme.{u}) (p : X ⟶ S) (q : T ⟶ S) (p' : Y ⟶ T)
    (b : Y ⟶ X) (i : D ⟶ X) (i' : D' ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b),
    IsPullback b p' p q → IsPullback a i' i b → IsClosedImmersion i →
      _root_.AlgebraicGeometry.Scheme.Modules.Invertible.IsLocallyRankOne X (idealModule i) →
          Flat (i ≫ p) →
        IsIso (idealPullbackMap i i' b a h)

variable {S T T' : Scheme.{u}}
/-- The canonical map from the pulled-back graph ideal to the graph ideal after base change. -/
def graphIdealPullbackMap (p : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (s : T ⟶ X) (hs : s ≫ p = t) (a : T' ⟶ T) (ha : a ≫ t = t') :
    (Scheme.Modules.pullback (familyMap p t t' a ha)).obj (idealModule (graph p t s hs)) ⟶
      idealModule (graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha])) :=
  idealPullbackMap (graph p t s hs)
    (graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha]))
    (familyMap p t t' a ha) a (graph_naturality p t t' s hs a ha).symm

theorem graphIdealPullbackMap_isIso
    (hdivisor : SmoothRelativeDivisorIdeal.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (t : T ⟶ S) (t' : T' ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)
    (a : T' ⟶ T) (ha : a ≫ t = t') : IsIso (graphIdealPullbackMap p t t' s hs a ha) := by
  apply hbase T T' (pullback p t) (pullback p t') T T'
    (pullback.snd p t) a (pullback.snd p t') (familyMap p t t' a ha)
    (graph p t s hs) (graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha]))
    a (graph_naturality p t t' s hs a ha).symm
  · exact familyMap_isPullback p t t' a ha
  · exact (graph_isPullback p t t' s hs a ha).flip
  · infer_instance
  · exact graphIdeal_isLocallyRankOne hdivisor p t s hs
  · rw [graph_snd]; infer_instance

/-- The canonical graph-ideal base-change isomorphism for a separated smooth relative curve,
using the supplied divisor and Cartier ideal base-change inputs. -/
def graphIdealBaseChangeIso
    (hdivisor : SmoothRelativeDivisorIdeal.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (t : T ⟶ S) (t' : T' ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)
    (a : T' ⟶ T) (ha : a ≫ t = t') :
    (Scheme.Modules.pullback (familyMap p t t' a ha)).obj (idealModule (graph p t s hs)) ≅
      idealModule (graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha])) := by
  haveI := graphIdealPullbackMap_isIso hdivisor hbase p t t' s hs a ha
  exact asIso (graphIdealPullbackMap p t t' s hs a ha)

@[simp] theorem graphIdealBaseChangeIso_hom
    (hdivisor : SmoothRelativeDivisorIdeal.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (t : T ⟶ S) (t' : T' ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)
    (a : T' ⟶ T) (ha : a ≫ t = t') :
    (graphIdealBaseChangeIso hdivisor hbase p t t' s hs a ha).hom =
      graphIdealPullbackMap p t t' s hs a ha := rfl

/-- The native theorem concerns the same actual ideal and the same adjunction mate. -/
theorem relativeCartierIdealBaseChange : RelativeCartierIdealBaseChange.{u} :=
  idealPullbackMap_isIso_of_relativeCartier

end AlgebraicGeometry.Scheme.Hom
