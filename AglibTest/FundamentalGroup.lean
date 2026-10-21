/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineNeighborhoodRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FundamentalGroupComparison

/-! Public-interface regressions for actual fibres, receiver-namespace lookup and finite H1.
The source interfaces originate in local R5 checkpoint
c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5, which is not published by this migration.
All comparison inputs below remain explicit. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open Scheme.EtaleFundamentalGroups Scheme.EtaleCohomology
open Scheme.FiniteEtale (fiberToFinite)
open Scheme.FiniteEtale.FiberTorsorActions (coefficientCover)

universe u v w

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

example {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) :
    FiberAutGroup x = Aut (fiberToFinite x) := rfl

example {S X : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) :
    Continuous (Scheme.EtaleFundamentalGroups.map f x) :=
  Scheme.EtaleFundamentalGroups.continuous_map f x

example {B X : Scheme.{u}} {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X)
    (h : o ≫ p = 𝟙 B) :
    (projectionHom b p o h).comp (originHom b o) = MonoidHom.id (FiberAutGroup b) :=
  originHom_projectionHom b p o h

section ReceiverNamespace

variable {X S : Scheme.{u}} {F : SetSheaf X} (t : FiniteSetLocalTrivialization F)

example : X.Cover (Scheme.precoverage @Etale) := t.cover

example (f : S ⟶ X) : FiniteSetLocalTrivialization ((setInverseImage f).obj F) :=
  t.pullback f

example (i : t.index) : t.smallValue i ≃ t.value i := t.smallValueEquiv i

example (x : X) : Scheme.FiniteEtale.SheafDescent.AffineTrivializingNeighborhood F x :=
  t.affineTrivializingNeighborhood x

example (x : X) : ∃ U : X.Opens, Scheme.FiniteEtale.SheafDescent.IsGoodAffineOpen F U ∧ x ∈ U :=
  t.exists_goodAffineOpen x

end ReceiverNamespace

section FiniteCoefficientComparison

variable {X : Scheme.{u}} {K : Type u} [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ X)
variable [GaloisCategory (Scheme.FiniteEtale X)]
variable [PreGaloisCategory.FiberFunctor (fiberToFinite s)] [PreconnectedSpace X]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (L : AbelianSheaf.{u, u + 1} X) (R : CoefficientRepresentation L)
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup s) M] [ContinuousSMul (FiberAutGroup s) M]
variable (mark : (Over.mk s ⟶ R.group.X) ≃* Multiplicative M)
variable (hmark : ∀ (γ : FiberAutGroup s) a,
  mark (γ.hom.app (coefficientCover R.group) a) = Multiplicative.ofAdd (γ • (mark a).toAdd))
variable (hcoeff : FiniteCoefficient L)

example : H1Etale X L = Sheaf.H L 1 := rfl

example : Sheaf.H L 1 ≃+ GroupCohomology.ContinuousH1.H1 (FiberAutGroup s) M :=
  FundamentalGroupComparison.compareH1WithRepresentation s hA hR L R M mark hmark hcoeff

end FiniteCoefficientComparison
