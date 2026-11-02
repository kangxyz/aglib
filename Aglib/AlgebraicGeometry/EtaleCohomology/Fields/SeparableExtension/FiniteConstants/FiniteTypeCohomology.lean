/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackConstantDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativePullbackCoefficient
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.Spec.CompletionSpecialization

/-! # Original all-degree class and equality descent to coefficient subalgebras -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.FieldComparison

universe u e

attribute [local instance] hasSheafifyLarge

open Algebra.FiniteTypeSubalgebraLimit
open Stalk Continuity

local instance (K : Type u) : IsConnected (Finset K) := IsFiltered.isConnected (Finset K)

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
  {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))

/-- The original finite-type coefficient base changes, viewed as schemes over `Y`. -/
abbrev overDiagram : (Finset K)ᵒᵖ ⥤ Over Y :=
  Scheme.FiniteTypeSubalgebraLimit.baseDiagram k K ⋙ Over.pullback p

/-- The canonical functor from finite subsets to their double opposites. -/
abbrev indexEquivalence := (opOpEquivalence (Finset K)).inverse

/-- Original coefficient schemes in their filtered cohomological direction. -/
def coefficientDiagram : Finset K ⥤ Scheme.{u}ᵒᵖ :=
  indexEquivalence K ⋙ (Scheme.FiniteTypeSubalgebraLimit.schemeDiagram k K p).op

theorem coefficientDiagram_obj (s : Finset K) :
    (coefficientDiagram k K p).obj s =
      op (pullback (Spec.algebraMap k (stage k K s)) p) := rfl

theorem coefficientDiagram_map {s t : Finset K} (a : s ⟶ t) :
    ((coefficientDiagram k K p).map a).unop =
      (Scheme.FiniteTypeSubalgebraLimit.schemeDiagram k K p).map a.op := rfl

/-- Original structural arrows to the fixed source scheme. -/
def coefficientBaseCone : Cone (coefficientDiagram k K p) :=
  (relativeCoefficientBaseCone (overDiagram k K p)).whisker (indexEquivalence K)

/-- The apex is the literal original base change in standard pullback order. -/
def coefficientLimitCocone : Cocone (coefficientDiagram k K p) :=
  (((Scheme.FiniteTypeSubalgebraLimit.schemeCone k K p).extend
    (pullbackSymmetry p (Spec.algebraMap k K)).hom).op).whisker (indexEquivalence K)

private theorem coefficient_cone_composite (s : Finset K) :
    (coefficientBaseCone k K p).π.app s ≫
      (coefficientLimitCocone k K p).ι.app s =
        (pullback.fst p (Spec.algebraMap k K)).op := by
  change (pullback.snd (Spec.algebraMap k (stage k K s)) p).op ≫
      (Scheme.FiniteTypeSubalgebraLimit.projection k K p (op s)).op =
    (pullback.fst p (Spec.algebraMap k K)).op
  exact congrArg Quiver.Hom.op
    (Scheme.FiniteTypeSubalgebraLimit.projection_snd k K p (op s))

private def coefficientLimitIsColimit : IsColimit (coefficientLimitCocone k K p) :=
  ((IsLimit.extendIso (s := Scheme.FiniteTypeSubalgebraLimit.schemeCone k K p)
    (pullbackSymmetry p (Spec.algebraMap k K)).hom
    (Scheme.FiniteTypeSubalgebraLimit.schemeConeIsLimit k K p)).op).whiskerEquivalence
      (opOpEquivalence (Finset K)).symm

private theorem coefficientProjection_eq (s : Finset K) :
    Scheme.FiniteTypeSubalgebraLimit.projection k K p (op s) =
      LocalRing.coefficientBaseChangeMap p (stage k K s).val := by
  apply pullback.hom_ext
  · exact (Scheme.FiniteTypeSubalgebraLimit.projection_fst k K p (op s)).trans
      (LocalRing.coefficientBaseChangeMap_fst p (stage k K s).val).symm
  · exact (Scheme.FiniteTypeSubalgebraLimit.projection_snd k K p (op s)).trans
      (LocalRing.coefficientBaseChangeMap_snd p (stage k K s).val).symm

variable [QuasiCompact p] [QuasiSeparated p]
  [hExt : ∀ s : Finset K, HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap k (stage k K s)) p))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap k K)))]
  [HasColimitsOfShape (Finset K) AddCommGrpCat.{e}] [UnivLE.{u, e}]

local instance (s : Finset K) : CompactSpace ((coefficientDiagram k K p).obj s).unop := by
  rw [coefficientDiagram_obj]
  exact inferInstanceAs (CompactSpace
    ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram k K p).obj (op s)))

local instance (s : Finset K) : QuasiSeparatedSpace ((coefficientDiagram k K p).obj s).unop := by
  rw [coefficientDiagram_obj]
  exact inferInstanceAs (QuasiSeparatedSpace
    ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram k K p).obj (op s)))

local instance (s : Finset K) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((coefficientDiagram k K p).obj s).unop) := by
  rw [coefficientDiagram_obj]
  exact hExt s

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (coefficientLimitCocone k K p).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback p (Spec.algebraMap k K))))

local instance {s t : Finset K} (a : s ⟶ t) :
    IsAffineHom ((coefficientDiagram k K p).map a).unop := by
  rw [coefficientDiagram_map]
  exact inferInstanceAs (IsAffineHom
    ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram k K p).map a.op))

/-- Every original constant cohomology class descends to a genuine finite-type
coefficient subalgebra, with its actual inclusion and constant restriction. -/
theorem exists_cohomologyClass_over_finiteTypeSubalgebra
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{e} (coefficient A (pullback p (Spec.algebraMap k K))) q) :
    ∃ (s : Finset K) (cₛ : Sheaf.H.{e}
      (coefficient A (pullback (Spec.algebraMap k (stage k K s)) p)) q),
      Curves.constantRestriction A
        (LocalRing.coefficientBaseChangeMap p (stage k K s).val) q cₛ = c := by
  obtain ⟨s, a, ha⟩ := exists_stage_constantCohomologyClass
    (coefficientDiagram k K p) (coefficientBaseCone k K p) (coefficientLimitCocone k K p)
    (coefficientLimitIsColimit k K p) (pullback.fst p (Spec.algebraMap k K)).op
    (coefficient_cone_composite k K p) A q c
  refine ⟨s, a, ?_⟩
  rw [← coefficientProjection_eq k K p s]
  exact ha

variable [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]

/-- If an original source class becomes zero over the full coefficient algebra,
it becomes zero over one genuine finite-type subalgebra. -/
theorem exists_cohomologyZero_over_finiteTypeSubalgebra
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (a : Sheaf.H.{e} (coefficient A Y) q)
    (ha : Curves.constantRestriction A
      (pullback.fst p (Spec.algebraMap k K)) q a = 0) :
    ∃ s : Finset K, Curves.constantRestriction A
      (pullback.snd (Spec.algebraMap k (stage k K s)) p) q a = 0 := by
  let : HasExt.{e} (AbelianSheaf.{u, u + 1} (coefficientBaseCone k K p).pt.unop) :=
    inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} Y))
  exact exists_stage_constantCohomologyZero
    (coefficientDiagram k K p) (coefficientBaseCone k K p) (coefficientLimitCocone k K p)
    (coefficientLimitIsColimit k K p) (pullback.fst p (Spec.algebraMap k K)).op
    (coefficient_cone_composite k K p) A q a ha

/-- Equality of original source classes over the full coefficient algebra is
already equality over a genuine finite-type subalgebra. -/
theorem exists_cohomologyEquality_over_finiteTypeSubalgebra
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (a b : Sheaf.H.{e} (coefficient A Y) q)
    (hab : Curves.constantRestriction A (pullback.fst p (Spec.algebraMap k K)) q a =
      Curves.constantRestriction A (pullback.fst p (Spec.algebraMap k K)) q b) :
    ∃ s : Finset K, Curves.constantRestriction A
      (pullback.snd (Spec.algebraMap k (stage k K s)) p) q a =
        Curves.constantRestriction A
          (pullback.snd (Spec.algebraMap k (stage k K s)) p) q b := by
  obtain ⟨s, hs⟩ := exists_cohomologyZero_over_finiteTypeSubalgebra k K p A q (a - b)
    (by rw [map_sub, hab, sub_self])
  exact ⟨s, sub_eq_zero.mp (by simpa only [map_sub] using hs)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.FieldComparison
