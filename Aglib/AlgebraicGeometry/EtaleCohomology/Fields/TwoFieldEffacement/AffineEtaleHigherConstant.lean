/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineHigherDegree
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteSeparableZero

/-! # Actual finite-etale field refinement for higher affine classes

The maximal separable subextension of the produced finite field stage retains
zero of the original finite-constant class by the existing finite-pure
comparison. The literal original class and finite field stage are retained.
No pointed neighbourhood over a
higher-dimensional base and no smooth base change theorem are asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open FiniteEtale.FieldLimit

/-- The actual finite algebraic zero stage supplies zero over its literal
maximal separable subextension. No perfection assumption is imposed on k. -/
theorem exists_affine_finiteEtaleField_killing_higher_constant
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p]
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A U) q) :
    ∃ s : Finset (AlgebraicClosure k),
      let E := separableClosure k (finiteField k (AlgebraicClosure k) s)
      Module.Finite k E ∧ Etale (Spec.algebraMap k E) ∧
        Curves.constantRestriction.{u, u + 2, u + 2} A
          (pullback.fst p (Spec.algebraMap k E)) q c = 0 := by
  obtain ⟨s, hs⟩ := exists_affine_finiteField_killing_higher_constant
    k U p A n hn hkill hunit q hq c
  let L := finiteField k (AlgebraicClosure k) s
  let E := separableClosure k L
  let b := Spec.algebraMap k L
  have hs' : Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.snd b p) q c = 0 := hs
  have hL : Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p b) q c = 0 := by
    rw [← pullbackSymmetry_hom_comp_snd p b,
      Curves.constantRestriction_comp, hs', map_zero]
  have hE := ConstantFinite.finiteField_zero_at_separableClosure k L p A q c hL
  exact ⟨s, inferInstance,
    (FiniteEtale.FieldGalois.Arbitrary.finiteFieldCover k E).property.2, hE⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
