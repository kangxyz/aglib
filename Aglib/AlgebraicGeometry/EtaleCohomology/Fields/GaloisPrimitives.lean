/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.GaloisCech
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CechPrimitives

/-! # Primitives on the original small-etale free Čech resolution

The actual tuple/Amitsur complex isomorphism transports both cocycles and
primitives. The original sheafification adjunction then returns a primitive
on the literal sheafified free resolution used by the two-kernel Ext criterion.
-/

@[expose] public noncomputable section

open CategoryTheory
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

variable (E L : Type u) [Field E] [Field L] [Algebra E L]
  [FiniteDimensional E L] [IsGalois E L]
  (K : Type u) [Field K] [IsAlgClosed K] [Algebra (RatFunc K) E]
  [Algebra.IsAlgebraic (RatFunc K) E]

include K

attribute [local instance] hasSheafifyLarge

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal degree-two cocycles on the actual field-cover free resolution
have literal primitives, over an algebraic function field. -/
theorem galoisCech_exists_primitive
    (c : (Presheaf.Cech.sheafComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
      (Scheme.smallEtaleTopology (Spec (.of E)))).X 2 ⟶ gm (Spec (.of E)))
    (hc : (Presheaf.Cech.sheafComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
      (Scheme.smallEtaleTopology (Spec (.of E)))).d 3 2 ≫ c = 0) :
    ∃ b : (Presheaf.Cech.sheafComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
      (Scheme.smallEtaleTopology (Spec (.of E)))).X 1 ⟶ gm (Spec (.of E)),
      (Presheaf.Cech.sheafComplex (Presheaf.Cech.familyMap (galoisCoverFamily E L))
        (Scheme.smallEtaleTopology (Spec (.of E)))).d 2 1 ≫ b = c := by
  apply Presheaf.Cech.sheaf_primitive_of_free_primitive _ _ _ 1 _ c hc
  intro a ha
  let e := galoisCechAmitsurIso E L
  have hExact : (amitsurUnitComplex E L).ExactAt 2 := by
    rw [HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp)]
    exact (ShortComplex.ab_exact_iff _).mpr
      (amitsurUnitComplex_exists_primitive E L K)
  have hOriginal := hExact.of_iso e.symm
  rw [HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp)] at hOriginal
  exact ((ShortComplex.ab_exact_iff _).mp hOriginal) a ha

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
