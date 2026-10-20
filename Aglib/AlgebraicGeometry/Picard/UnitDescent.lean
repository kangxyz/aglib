/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitInverse
public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.Pullback
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.UnitDescent` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`375464e4b3b5e7753363d676c74feb1209b8cbbff5c380e1ff54b8bd2528de19`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle isLocallyRankOne_iff_local_unit )
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Effective descent of literal unit transition functions

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Let `f i : U i ⟶ S` be a family of actual scheme morphisms whose generated
sieve covers S for the etale topology. Choose genuine pair and triple
fiber products. The inputs are literal global units on pair overlaps,
whose diagonal restrictions are one and whose product on triple overlaps
is the remaining transition. No curve, characteristic, or positivity
hypothesis is needed for this general descent construction.

We construct native chosen-pullback descent data for the fixed
`EtaleDescent.lineBundles` pseudofunctor: the objects are the actual
structure-module sheaves, and transitions are actual scalar multiplication
conjugated by the canonical structure-module pullback isomorphisms.
Native pullback coherence is proved from canonical unit-map composition
and scalar pullback. Its orientation is i to j followed by j to k equals
i to k; consequently the local chart to O on j is the chart on i followed
by multiplication by the prescribed overlap unit.

The sole retained general theorem family is exactly
`EtaleDescent.EtaleLineBundleDescent`, namely the stack property of that
fixed actual locally-rank-one full sub-pseudofunctor with native module
pullbacks for `Scheme.etaleTopology`. Its source boundary, Stacks Tags
023T and 05B2 and rank-one preservation/descent, is documented in
EtaleDescent. No premise returns a line bundle, Picard class, torsor or
cohomology classification. The descended actual line bundle, exact
recovery isomorphism of descent data, and O-linear local charts with their
prescribed transition equation are outputs of the proved stack equivalence.
This module makes no torsor or H1 comparison and uses no additional
application-specific descent assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite Bicategory Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent
open EtaleDescent ScalarAutomorphisms
universe u v

def unitObject (X : Scheme.{u}) : lineBundles.obj (.mk (op X)) :=
  ⟨SheafOfModules.unit X.ringCatSheaf, by
    change IsLocallyRankOne X (SheafOfModules.unit X.ringCatSheaf)
    rw [isLocallyRankOne_iff_local_unit]
    intro x
    exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩⟩


/-- Literal multiplication by a scalar in the native pullbacks of O. -/
def transition {X₁ X₂ Y : Scheme.{u}} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (a : Γ(Y, ⊤)) :
    (lineBundles.map f₁.op.toLoc).toFunctor.obj (unitObject X₁) ⟶
      (lineBundles.map f₂.op.toLoc).toFunctor.obj (unitObject X₂) :=
  ObjectProperty.homMk ((pullbackUnitIso f₁).hom ≫
    AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y
        (SheafOfModules.unit Y.ringCatSheaf) a ≫
    (pullbackUnitIso f₂).inv)

open Pseudofunctor.LocallyDiscreteOpToCat

/-- Scalar transition pullback uses the native pseudofunctor coherence. -/
theorem pullHom_transition {X₁ X₂ Y Y' : Scheme.{u}}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (a : Γ(Y, ⊤)) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (transition f₁ f₂ a) g gf₁ gf₂ h₁ h₂ =
      transition gf₁ gf₂ (g.appTop a) := by
  subst gf₁ gf₂
  apply ObjectProperty.hom_ext
  change (Scheme.Modules.pullbackComp g f₁).inv.app _ ≫
    (Scheme.Modules.pullback g).map
      ((pullbackUnitIso f₁).hom ≫
          AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y _ a ≫
        (pullbackUnitIso f₂).inv) ≫
    (Scheme.Modules.pullbackComp g f₂).hom.app _ =
      (pullbackUnitIso (g ≫ f₁)).hom ≫
          AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y' _ (g.appTop a) ≫
        (pullbackUnitIso (g ≫ f₂)).inv
  apply (cancel_mono (pullbackUnitIso (g ≫ f₂)).hom).mp
  have hlast : (Scheme.Modules.pullback g).map (pullbackUnitIso f₂).inv ≫
      (Scheme.Modules.pullbackComp g f₂).hom.app _ ≫
        (pullbackUnitIso (g ≫ f₂)).hom = (pullbackUnitIso g).hom := by
    rw [Scheme.Modules.pullbackUnitIso_comp g f₂]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hlast, pullback_scalar_unit]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y' _ (g.appTop a))
      (Scheme.Modules.pullbackUnitIso_comp_inv g f₁)

@[simp] theorem transition_self_one {A Y : Scheme.{u}} (f : Y ⟶ A) :
    transition f f 1 = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  dsimp [transition]
  rw [scalarMap_one, Category.id_comp, Iso.hom_inv_id]

@[reassoc] theorem transition_comp {A B C Y : Scheme.{u}}
    (f₁ : Y ⟶ A) (f₂ : Y ⟶ B) (f₃ : Y ⟶ C) (a b : Γ(Y, ⊤)) :
    transition f₁ f₂ a ≫ transition f₂ f₃ b = transition f₁ f₃ (a * b) := by
  apply ObjectProperty.hom_ext
  change ((pullbackUnitIso f₁).hom ≫
      AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y _ a ≫
    (pullbackUnitIso f₂).inv) ≫ ((pullbackUnitIso f₂).hom ≫
    AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y _ b ≫
        (pullbackUnitIso f₃).inv) =
      (pullbackUnitIso f₁).hom ≫
          AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y _ (a * b) ≫
        (pullbackUnitIso f₃).inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun k => (pullbackUnitIso f₁).hom ≫ k)
    (ScalarAutomorphisms.scalarMap_mul_assoc Y (SheafOfModules.unit Y.ringCatSheaf)
      a b (pullbackUnitIso f₃).inv)

/-- Actual pullback of global units along a scheme morphism. -/
def pullUnit {X Y : Scheme.{u}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ :=
  Units.map f.appTop.hom.toMonoidHom

@[simp] theorem coe_pullUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ(Y, ⊤)ˣ) :
    ↑(pullUnit f a) = f.appTop a := rfl

variable {ι : Type v} {S : Scheme.{u}} {U : ι → Scheme.{u}} {f : ∀ i, U i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

/-- The actual diagonal into the chosen overlap. -/
def diagonal (i : ι) : U i ⟶ (sq i i).pullback :=
  (sq i i).isPullback.lift (𝟙 _) (𝟙 _) (by simp)

@[simp, reassoc] theorem diagonal_p₁ (i : ι) : diagonal sq i ≫ (sq i i).p₁ = 𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

@[simp, reassoc] theorem diagonal_p₂ (i : ι) : diagonal sq i ≫ (sq i i).p₂ = 𝟙 _ :=
  IsPullback.lift_snd _ _ _ _

/-- Literal units on overlaps with the identity and multiplicative cocycle laws. -/
structure Cocycle where
  unit (i j : ι) : Γ((sq i j).pullback, ⊤)ˣ
  diagonal (i : ι) : pullUnit (diagonal sq i) (unit i i) = 1
  cocycle (i j k : ι) :
    pullUnit (sq₃ i j k).p₁₂ (unit i j) * pullUnit (sq₃ i j k).p₂₃ (unit j k) =
      pullUnit (sq₃ i j k).p₁₃ (unit i k)

namespace Cocycle
variable {sq sq₃} (c : Cocycle sq sq₃)

/-- The actual rank-one native descent datum built from unit multiplication. -/
def descentData : lineBundles.DescentData' sq sq₃ where
  obj i := unitObject (U i)
  hom i j := transition (sq i j).p₁ (sq i j).p₂ (c.unit i j)
  pullHom'_hom_self i := by
    rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _
        (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal sq i)]
    rw [pullHom_transition]
    have h := congrArg Units.val (c.diagonal i)
    change (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.diagonal sq i).appTop
        ↑(c.unit i i) = 1 at h
    rw [h, transition_self_one]
  pullHom'_hom_comp i j k := by
    rw [Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    rw [pullHom_transition, pullHom_transition, pullHom_transition, transition_comp]
    have h := congrArg Units.val (c.cocycle i j k)
    exact congrArg (transition (sq₃ i j k).p₁ (sq₃ i j k).p₃) h


variable (h : EtaleLineBundleDescent.{u})
  (hf : Sieve.ofArrows U f ∈ Scheme.etaleTopology S)

/-- The native étale stack equivalence; its only boundary is rank-one descent. -/
def stackEquivalence :
    lineBundles.obj (.mk (op S)) ≌ lineBundles.DescentData f := by
  letI : lineBundles.IsStack Scheme.etaleTopology := h
  letI := lineBundles.isEquivalence_toDescentData f hf
  exact (lineBundles.toDescentData f).asEquivalence

/-- Effective descent applied to the constructed scalar transition datum. -/
def descendedObject : lineBundles.obj (.mk (op S)) :=
  (stackEquivalence h hf).inverse.obj c.descentData.descentData

/-- The descended actual locally free rank-one module sheaf. -/
def descended : LineBundle S := toLineBundle S (c.descendedObject h hf)

/-- The actual counit recovers precisely the constructed descent datum. -/
def recoveryIso :
    (lineBundles.toDescentData f).obj (c.descendedObject h hf) ≅
      c.descentData.descentData :=
  (stackEquivalence h hf).counitIso.app c.descentData.descentData

/-- Actual O-linear trivializations on each member of the cover. -/
def chart (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (c.descended h hf).val ≅
      SheafOfModules.unit (U i).ringCatSheaf where
  hom := ((c.recoveryIso h hf).hom.hom i).hom
  inv := ((c.recoveryIso h hf).inv.hom i).hom
  hom_inv_id := congrArg (fun k => (k.hom i).hom) (c.recoveryIso h hf).hom_inv_id
  inv_hom_id := congrArg (fun k => (k.hom i).hom) (c.recoveryIso h hf).inv_hom_id

/-- Exact recovery of the scalar transitions in the native chosen overlap.
The right-hand comparison is the genuine module pullback coherence. -/
theorem chart_transition (i j : ι) :
    (Scheme.Modules.pullback (sq i j).p₁).map (c.chart h hf i).hom ≫
        (transition (sq i j).p₁ (sq i j).p₂ (c.unit i j)).hom =
      ((Pseudofunctor.DescentData.ofObj (f := f) (c.descendedObject h hf)).hom
        (sq i j).p (sq i j).p₁ (sq i j).p₂ (by simp) (by simp)).hom ≫
      (Scheme.Modules.pullback (sq i j).p₂).map (c.chart h hf j).hom := by
  have he := (c.recoveryIso h hf).hom.comm (sq i j).p (sq i j).p₁ (sq i j).p₂
    (by simp) (by simp)
  change _ ≫ Pseudofunctor.DescentData'.pullHom' c.descentData.hom
    (sq i j).p (sq i j).p₁ (sq i j).p₂ (by simp) (by simp) = _ at he
  rw [Pseudofunctor.DescentData'.pullHom'_p₁_p₂] at he
  exact congrArg (fun k => k.hom) he

end Cocycle
end AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent
