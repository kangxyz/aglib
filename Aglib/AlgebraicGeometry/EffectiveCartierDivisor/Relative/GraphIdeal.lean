/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Ideal
public import Aglib.AlgebraicGeometry.Picard.Presheaf

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual relative graph ideals over arbitrary test schemes

`idealModule i` is the actual kernel of O_X → i_*O_D. Its sections are canonically
identified with the ring-theoretic kernel of i# on every open, compatibly with the
inclusion into O_X. For a general morphism this is only a kernel sheaf; the graph
applications separately prove the relevant closed-immersion condition.

Graphs, their family base-change maps, identity/composition/naturality and the
cartesian graph square are constructed over arbitrary schemes, including
nonreduced bases. The retained family `SmoothRelativeDivisorIdeal` is the general
finite-flat divisor theorem for smooth relative curves: Stacks Lemma 44.3.1,
0B9D, implication (3) → (2), with finite implying locally quasi-finite. Effective
Cartier means the actual ideal module is invertible (Definition 31.14.1, 01WR,
in section 01WQ). These statements, proofs and visible comments were inspected
2026-10-09. Tag 0B9D has no correction comments; the September 2026 comment on
01WQ notes that the empty closed subscheme is also Cartier, which this definition
allows. The full external dependency chains remain a standard theorem input.

The graph application proves separatedness gives a closed graph, and its map to
the parameter scheme is the identity, hence finite, flat and locally of finite
presentation. Smooth relative dimension one is stable under the actual base
change. Thus the result is O(-graph), and similarly O(-diagonal); a positive Abel
divisor requires taking the actual dual later. No Picard representability or
Abel isomorphism is asserted here.

Accepted incoming C object interface: Picard.Basic, SHA256
b9570475203f86c9d1622f5762bd14b0df6e3c785ac24219fa37c0b9e0581b04.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.Basic` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`570b9ca11f8d9c206126d72a7d4d9df1eb0a0d63084a139a8639f5ca136b393b`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X Y S T T' : Scheme.{u}}
def graph (p : X ⟶ S) (t : T ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t) :
    T ⟶ pullback p t := pullback.lift s (𝟙 T) (by simpa using hs)
@[reassoc (attr := simp)] theorem graph_fst (p : X ⟶ S) (t : T ⟶ S)
    (s : T ⟶ X) (hs : s ≫ p = t) : graph p t s hs ≫ pullback.fst p t = s :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem graph_snd (p : X ⟶ S) (t : T ⟶ S)
    (s : T ⟶ X) (hs : s ≫ p = t) : graph p t s hs ≫ pullback.snd p t = 𝟙 T :=
  pullback.lift_snd _ _ _
instance graph_isClosedImmersion (p : X ⟶ S) [IsSeparated p] (t : T ⟶ S)
    (s : T ⟶ X) (hs : s ≫ p = t) : IsClosedImmersion (graph p t s hs) := by
  haveI : IsClosedImmersion (graph p t s hs ≫ pullback.snd p t) := by
    rw [graph_snd]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd p t)

def familyMap (p : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (a : T' ⟶ T) (ha : a ≫ t = t') : pullback p t' ⟶ pullback p t :=
  pullback.lift (pullback.fst p t') (pullback.snd p t' ≫ a)
    (by rw [Category.assoc, ha, pullback.condition])
@[reassoc (attr := simp)] theorem familyMap_fst (p : X ⟶ S) (t : T ⟶ S)
    (t' : T' ⟶ S) (a : T' ⟶ T) (ha : a ≫ t = t') :
    familyMap p t t' a ha ≫ pullback.fst p t = pullback.fst p t' :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem familyMap_snd (p : X ⟶ S) (t : T ⟶ S)
    (t' : T' ⟶ S) (a : T' ⟶ T) (ha : a ≫ t = t') :
    familyMap p t t' a ha ≫ pullback.snd p t = pullback.snd p t' ≫ a :=
  pullback.lift_snd _ _ _
@[simp] theorem familyMap_id (p : X ⟶ S) (t : T ⟶ S) :
    familyMap p t t (𝟙 T) (Category.id_comp t) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp
@[reassoc] theorem familyMap_comp {T'' : Scheme.{u}} (p : X ⟶ S) (t : T ⟶ S)
    (t' : T' ⟶ S) (t'' : T'' ⟶ S) (a : T' ⟶ T) (b : T'' ⟶ T')
    (ha : a ≫ t = t') (hb : b ≫ t' = t'') :
    familyMap p t' t'' b hb ≫ familyMap p t t' a ha =
      familyMap p t t'' (b ≫ a) (by rw [Category.assoc, ha, hb]) := by
  apply pullback.hom_ext <;> simp [Category.assoc]
@[reassoc] theorem graph_naturality (p : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (s : T ⟶ X) (hs : s ≫ p = t) (a : T' ⟶ T) (ha : a ≫ t = t') :
    graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha]) ≫ familyMap p t t' a ha =
      a ≫ graph p t s hs := by
  apply pullback.hom_ext <;> simp

theorem familyMap_isPullback (p : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (a : T' ⟶ T) (ha : a ≫ t = t') :
    IsPullback (familyMap p t t' a ha) (pullback.snd p t') (pullback.snd p t) a := by
  apply IsPullback.of_right (h₁₂ := pullback.fst p t) (h₂₂ := t)
    (v₁₃ := p) _ (familyMap_snd p t t' a ha) (IsPullback.of_hasPullback p t)
  simpa [ha] using (IsPullback.of_hasPullback p t')

theorem graph_isPullback (p : X ⟶ S) (t : T ⟶ S) (t' : T' ⟶ S)
    (s : T ⟶ X) (hs : s ≫ p = t) (a : T' ⟶ T) (ha : a ≫ t = t') :
    IsPullback (graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha])) a
      (familyMap p t t' a ha) (graph p t s hs) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd p t') (h₂₂ := pullback.snd p t)
    (v₁₃ := a) _ (graph_naturality p t t' s hs a ha) (familyMap_isPullback p t t' a ha).flip
  simpa using (IsPullback.of_id_fst (f := a))

def SmoothRelativeDivisorIdeal : Prop :=
  ∀ (S X D : Scheme.{u}) (p : X ⟶ S) (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsFinite (i ≫ p) → Flat (i ≫ p) → LocallyOfFinitePresentation (i ≫ p) →
        Scheme.Modules.Invertible.IsLocallyRankOne X (idealModule i)

theorem sectionIdeal_isLocallyRankOne (hstandard : SmoothRelativeDivisorIdeal.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (s : S ⟶ X) (hs : s ≫ p = 𝟙 S) :
        Scheme.Modules.Invertible.IsLocallyRankOne X (idealModule s) := by
  haveI : IsClosedImmersion (s ≫ p) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s p
  apply hstandard S X S p s inferInstance inferInstance
  all_goals rw [hs]; infer_instance

theorem graphIdeal_isLocallyRankOne (hstandard : SmoothRelativeDivisorIdeal.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (t : T ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t) :
    Scheme.Modules.Invertible.IsLocallyRankOne (pullback p t)
        (idealModule (graph p t s hs)) := by
  haveI : SmoothOfRelativeDimension 1 (pullback.snd p t) :=
    MorphismProperty.pullback_snd p t inferInstance
  exact sectionIdeal_isLocallyRankOne hstandard (pullback.snd p t) _ (graph_snd p t s hs)

def graphIdealLineBundle (hstandard : SmoothRelativeDivisorIdeal.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (t : T ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t) :
    Scheme.Modules.Invertible.LineBundle (pullback p t) :=
  ⟨idealModule (graph p t s hs), graphIdeal_isLocallyRankOne hstandard p t s hs⟩

@[simp] theorem graphIdealLineBundle_val (hstandard : SmoothRelativeDivisorIdeal.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (t : T ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t) :
    (graphIdealLineBundle hstandard p t s hs).val = idealModule (graph p t s hs) := rfl

def diagonalIdealLineBundle (hstandard : SmoothRelativeDivisorIdeal.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p] :
    Scheme.Modules.Invertible.LineBundle (pullback p p) :=
  graphIdealLineBundle hstandard p p (𝟙 X) (Category.id_comp p)

@[simp] theorem diagonalIdealLineBundle_val (hstandard : SmoothRelativeDivisorIdeal.{u})
    (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p] :
    (diagonalIdealLineBundle hstandard p).val = idealModule (pullback.diagonal p) := rfl

/-- Native smooth relative-curve geometry supplies the incoming ideal interface. -/
theorem smoothRelativeDivisorIdeal : SmoothRelativeDivisorIdeal.{u} :=
  idealModule_isLocallyRankOne_of_smooth_of_finite_flat

end AlgebraicGeometry.Scheme.Hom
