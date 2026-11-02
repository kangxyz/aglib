/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackConstantDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativePullbackCoefficient
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FieldLimit

/-! # Finite-stage descent for original cohomology under algebraic field extension

The native finite intermediate-field limit and existing class and zero descent
retain the original restriction maps. No curve or purely inseparable hypothesis
is imposed. Source, stages and apex use a common independent Ext universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.AlgebraicExtension

universe u e

attribute [local instance] hasSheafifyLarge

open FiniteEtale Stalk Curves

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The existing intermediate-field scheme system, in cohomological direction. -/
def coefficientDiagram : Finset K ⥤ Scheme.{u}ᵒᵖ :=
  (opOpEquivalence (Finset K)).inverse ⋙
    (FieldLimit.schemeDiagram k K p ⋙ Over.forget X).op

/-- The original structural maps to the unchanged source. -/
def coefficientBaseCone : Cone (coefficientDiagram k K p) :=
  (relativeCoefficientBaseCone (FieldLimit.schemeDiagram k K p)).whisker
    (opOpEquivalence (Finset K)).inverse

/-- The native field pullback is the apex, with its original projection. -/
def coefficientLimitCocone : Cocone (coefficientDiagram k K p) :=
  ((((Over.forget X).mapCone (FieldLimit.schemeCone k K p)).extend
    (pullbackSymmetry p (Spec.algebraMap k K)).hom).op).whisker
      (opOpEquivalence (Finset K)).inverse

private def coefficientLimitIsColimit : IsColimit (coefficientLimitCocone k K p) := by
  let c := (Over.forget X).mapCone (FieldLimit.schemeCone k K p)
  let e : pullback p (Spec.algebraMap k K) ≅ c.pt :=
    pullbackSymmetry p (Spec.algebraMap k K)
  have hc : IsLimit c :=
    isLimitOfPreserves (Over.forget X) (FieldLimit.schemeConeIsLimit k K p)
  exact ((IsLimit.extendIso (s := c) e.hom hc).op).whiskerEquivalence
    (opOpEquivalence (Finset K)).symm

omit [Algebra.IsAlgebraic k K] in
private theorem coefficient_cone_composite (s : Finset K) :
    (coefficientBaseCone k K p).π.app s ≫
      (coefficientLimitCocone k K p).ι.app s =
        (pullback.fst p (Spec.algebraMap k K)).op := by
  exact congrArg Quiver.Hom.op (FieldLimit.fieldProjection_base k K p (op s))

variable [CompactSpace X] [QuasiSeparatedSpace X]
  [hExt : ∀ s : Finset K, HasExt.{e} (AbelianSheaf.{u, u + 1}
    ((FieldLimit.schemeDiagram k K p).obj (op s)).left)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap k K)))]
  [HasColimitsOfShape (Finset K) AddCommGrpCat.{e}] [UnivLE.{u, e}]

local instance (s : Finset K) : CompactSpace ((coefficientDiagram k K p).obj s).unop :=
  FieldLimit.stage_compact k K p (op s)

local instance (s : Finset K) : QuasiSeparatedSpace ((coefficientDiagram k K p).obj s).unop :=
  FieldLimit.stage_quasiSeparated k K p (op s)

local instance (s : Finset K) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((coefficientDiagram k K p).obj s).unop) := hExt s

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (coefficientLimitCocone k K p).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback p (Spec.algebraMap k K))))

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (coefficientBaseCone k K p).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} X))

local instance {s t : Finset K} (a : s ⟶ t) :
    IsAffineHom ((coefficientDiagram k K p).map a).unop :=
  inferInstanceAs (IsAffineHom ((FieldLimit.schemeDiagram k K p).map a.op).left)

omit [HasExt.{e} (AbelianSheaf.{u, u + 1} X)] in
/-- An original constant class over the algebraic extension descends to an actual
finite intermediate field, with its original projection and coefficient map. -/
theorem exists_finiteField_constantCohomologyClass
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (a : Sheaf.H.{e} (coefficient A (pullback p (Spec.algebraMap k K))) q) :
    ∃ (s : Finset K) (b : Sheaf.H.{e}
      (coefficient A ((FieldLimit.schemeDiagram k K p).obj (op s)).left) q),
      constantRestriction.{u, e, e} A (FieldLimit.fieldProjection k K p (op s)) q b = a := by
  exact exists_stage_constantCohomologyClass
    (coefficientDiagram k K p) (coefficientBaseCone k K p)
    (coefficientLimitCocone k K p) (coefficientLimitIsColimit k K p)
    (pullback.fst p (Spec.algebraMap k K)).op (coefficient_cone_composite k K p) A q a

/-- If an original source class vanishes after algebraic field extension, it
already vanishes after the original finite-field stage restriction. -/
theorem exists_finiteField_constantRestriction_eq_zero
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (a : Sheaf.H.{e} (coefficient A X) q)
    (ha : constantRestriction.{u, e, e} A (pullback.fst p (Spec.algebraMap k K)) q a = 0) :
    ∃ s : Finset K, constantRestriction.{u, e, e} A
      ((FieldLimit.schemeDiagram k K p).obj (op s)).hom q a = 0 := by
  exact exists_stage_constantCohomologyZero
    (coefficientDiagram k K p) (coefficientBaseCone k K p)
    (coefficientLimitCocone k K p) (coefficientLimitIsColimit k K p)
    (pullback.fst p (Spec.algebraMap k K)).op (coefficient_cone_composite k K p) A q a ha

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.AlgebraicExtension
