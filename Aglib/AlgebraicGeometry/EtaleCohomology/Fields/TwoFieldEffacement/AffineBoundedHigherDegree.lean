/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.BoundedClassFiniteConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineHigherDegree
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CoefficientCompositeZero

/-! # Original bounded higher classes after finite field extension

The existing finite-constant representative retains the original coefficient
arrow. Finite-stage vanishing of that representative and coefficient naturality
kill the original class. Both actual field stages and the actual composite
scheme map remain in the conclusion; no source-point neighbourhood is produced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Prove finiteness of the actual finite-stage tower with its original scalar
actions before specializing either field to a packaged intermediate field. -/
private theorem finiteField_finite_over_base
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    [Module.Finite k K] [Algebra.IsAlgebraic K Ω] (s : Finset Ω) :
    Module.Finite k (FiniteEtale.FieldLimit.finiteField K Ω s) := by
  exact Module.Finite.trans K (FiniteEtale.FieldLimit.finiteField K Ω s)

/-- Construct the complete original second stage before specializing the affine
source to its finite-Galois pullback. The original class and coefficient arrow
are transported along the actual finite-field diagram projection. -/
private theorem exists_affine_finiteField_killing_coefficient_higher
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k))
    (V : Scheme.{u}) [IsAffine V] [Nonempty V]
    (r : V ⟶ Spec (.of L)) [SmoothOfRelativeDimension 1 r]
    [GeometricallyConnected r]
    {T : Scheme.{u}} (f : V ⟶ T) (M : AbelianSheaf.{u, u + 1} T)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : L)) (q : ℕ) (hq : 2 ≤ q)
    (c : Sheaf.H.{u + 2} M q)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient A V) q)
    (β : ConstantFinite.coefficient A V ⟶ (inverseImage f).obj M)
    (hd : Sheaf.H.map β q d = cohomologyPullback.{u, u + 2, u + 2} f M q c) :
    ∃ s : Finset (AlgebraicClosure L),
      Module.Finite k (FiniteEtale.FieldLimit.finiteField L (AlgebraicClosure L) s) ∧
      cohomologyPullback.{u, u + 2, u + 2}
        (((FiniteEtale.FieldLimit.schemeDiagram L (AlgebraicClosure L) r).obj
          (op s)).hom ≫ f) M q c = 0 := by
  obtain ⟨s, hs⟩ := exists_affine_finiteField_killing_higher_constant
    L V r A n hn hkill hunit q hq d
  refine ⟨s, finiteField_finite_over_base k L (AlgebraicClosure L) s, ?_⟩
  exact cohomologyPullback_zero_of_constant_coefficient_composite
    ((FiniteEtale.FieldLimit.schemeDiagram L (AlgebraicClosure L) r).obj (op s)).hom
    f M A q c d β hd hs

/-- Every original bounded higher class on a smooth affine curve becomes zero
at two actual finite field stages. This is field extension, not pointed local
effacement, and uses the original standard Ext realization throughout. -/
theorem exists_affine_finiteField_killing_bounded_higher
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of k)))
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) (hunit : IsUnit (n : k))
    (q : ℕ) (hq : 2 ≤ q)
    (c : Sheaf.H.{u + 2} ((inverseImage p).obj F) q) :
    ∃ (L : FiniteGaloisIntermediateField k (SeparableClosure k))
      (s : Finset (AlgebraicClosure L)),
      Module.Finite k (FiniteEtale.FieldLimit.finiteField L (AlgebraicClosure L) s) ∧
      cohomologyPullback.{u, u + 2, u + 2}
        (((FiniteEtale.FieldLimit.schemeDiagram L (AlgebraicClosure L)
          (pullback.snd p (Spec.algebraMap k L))).obj (op s)).hom ≫
            pullback.fst p (Spec.algebraMap k L))
        ((inverseImage p).obj F) q c = 0 := by
  have hclass := @Fields.exists_finiteGalois_constant_class.{u, u + 2, u + 2}
    k inferInstance F n hn hF U p inferInstance inferInstance inferInstance
      (fun _ => inferInstance) inferInstance q c
  obtain ⟨E, a, _, _, L, B, hB, hfiniteB, hBn, ht⟩ := hclass
  let := hB
  let := hfiniteB
  obtain ⟨t, d, hd⟩ := ht
  let f := pullback.fst p (Spec.algebraMap k L)
  let r := pullback.snd p (Spec.algebraMap k L)
  let : SmoothOfRelativeDimension 1 r :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback p (Spec.algebraMap k L)) inferInstance
  let : ConnectedSpace (pullback p (Spec.algebraMap k L) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton r
  let e := Fields.constantTrivializationAlongSquare p f r (Spec.algebraMap k L)
    pullback.condition E (ConstantFinite.value B) t
  let a' := e.inv ≫ (inverseImage f).map ((inverseImage p).map a)
  have hunitL : IsUnit (n : L) := by
    simpa only [map_natCast] using hunit.map (algebraMap k L)
  exact ⟨L, exists_affine_finiteField_killing_coefficient_higher
    k L (pullback p (Spec.algebraMap k L)) r f ((inverseImage p).obj F)
    B n hn hBn hunitL q hq c d a' hd⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
