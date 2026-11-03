/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineEtaleHigherConstant
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CoefficientCompositeZero

/-! # The actual separable field and original coefficient-class zero

The original constant-class producer selects the finite stage internally. Its
literal maximal separable subextension supplies the field in the conclusion;
no ambient separable-closure action on that finite field is requested. The
coefficient presentation is transported through the original composite map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale.FieldLimit

/-- Choose the actual finite separable field and kill the original class using
its original coefficient-image equation. No zero certificate is an input. -/
theorem exists_affine_finiteEtaleField_killing_coefficient_higher
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p]
    {T : Scheme.{u}} [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
    (f : U ⟶ T) (M : AbelianSheaf.{u, u + 1} T)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q)
    (c : Sheaf.H.{eX} M q)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient A U) q)
    (β : ConstantFinite.coefficient A U ⟶ (inverseImage f).obj M)
    (hd : Sheaf.H.map β q d = cohomologyPullback.{u, eX, u + 2} f M q c) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E),
      Module.Finite k E ∧ Algebra.IsSeparable k E ∧ Etale (Spec.algebraMap k E) ∧
      cohomologyPullback.{u, eX, u + 2}
        (pullback.fst p (Spec.algebraMap k E) ≫ f) M q c = 0 := by
  obtain ⟨s, hfinite, hetale, hzero⟩ :=
    exists_affine_finiteEtaleField_killing_higher_constant
      k U p A n hn hkill hunit q hq d
  let E := separableClosure k (finiteField k (AlgebraicClosure k) s)
  refine ⟨E, inferInstance, inferInstance, hfinite, inferInstance, hetale, ?_⟩
  exact cohomologyPullback_zero_of_constant_coefficient_composite
    (pullback.fst p (Spec.algebraMap k E)) f M A q c d β hd hzero

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
