/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual

/-!
# Actual graph-difference line bundles for the Abel construction

Migrated from `R5Lab.Aglib.AlgebraicGeometry.Curves.Abel.LineBundle` at
R5Lab revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The native owner
records arbitrary scheme morphisms and tests; no field is assumed.

On X ×_S T, the positive graph bundle is the actual dual Hom(I_graph,O),
and O(graph(s)-graph(o_T)) is its actual tensor product with I_graph(o_T).
This is constructed for every test scheme T, including nonreduced schemes.
At the origin the bundle is canonically trivialized by actual dual evaluation,
not merely by an equality of numerical degrees. The diagonal case is the
actual O(diagonal - o × X) family.

This object layer has not yet descended these bundles to the relative Picard
functor, proved degree zero, or normalized by the origin restriction. Those
steps, naturality of the positive tensor bundle, Picard representability and
the all-test-scheme Abel inverse remain downstream obligations. Its only
standard theorem input is the generic graph-ideal rank theorem already
specified in AlgebraicGeometry.Scheme.Hom.

Accepted C dependencies: Picard.Dual SHA256
f982da32fc32b8e5e60b4086ee86f98635f840b81e999e37f747101d845a4d77;
Picard.HomSheaf SHA256
2e744b782488e8ad27bf61f4f4450f8ef6156b5ca884e075129e7d83a5920a27,
with its accepted tensor/associator/object closure. No new premises are added.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/


/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Hom
variable {S X T : Scheme.{u}}
variable (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (p : X ⟶ S) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
variable (t : T ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)

def positiveGraphLineBundle : Invertible.LineBundle (pullback p t) :=
  Invertible.dualLineBundle _ (graphIdealLineBundle hdivisor p t s hs)

def originIdealLineBundle : Invertible.LineBundle (pullback p t) :=
  graphIdealLineBundle hdivisor p t (t ≫ o) (by simp [Category.assoc, ho])

def abelLineBundle : Invertible.LineBundle (pullback p t) :=
  Invertible.tensorLineBundle _ (positiveGraphLineBundle hdivisor p t s hs)
    (originIdealLineBundle hdivisor p o ho t)

def abelClass : Invertible.PicardGroup (pullback p t) :=
  Invertible.classOf _ (abelLineBundle hdivisor p o ho t s hs)

theorem abelClass_eq : abelClass hdivisor p o ho t s hs =
    - Invertible.classOf _ (graphIdealLineBundle hdivisor p t s hs) +
      Invertible.classOf _ (originIdealLineBundle hdivisor p o ho t) := rfl

def abelOriginIso :
    (abelLineBundle hdivisor p o ho t (t ≫ o) (by simp [Category.assoc, ho])).val ≅
      SheafOfModules.unit (pullback p t).ringCatSheaf :=
  Invertible.dualEvaluationIso _ (originIdealLineBundle hdivisor p o ho t)

@[simp] theorem abelClass_origin :
    abelClass hdivisor p o ho t (t ≫ o) (by simp [Category.assoc, ho]) = 0 := by
  change Invertible.tensorClass _
    (Invertible.classOf _ (Invertible.dualLineBundle _ (originIdealLineBundle hdivisor p o ho t)))
    (Invertible.classOf _ (originIdealLineBundle hdivisor p o ho t)) = 0
  exact Invertible.dual_tensor_class_eq_zero _ _

def diagonalAbelLineBundle : Invertible.LineBundle (pullback p p) :=
  abelLineBundle hdivisor p o ho p (𝟙 X) (Category.id_comp p)

end AlgebraicGeometry.Scheme.Hom
