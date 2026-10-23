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
  let q (n : ℕ) := (HomologicalComplex.Hom.isoApp e n).addCommGroupIsoToAddEquiv
  have ha' : (amitsurUnitComplex E L).d 2 3 (q 2 a) = 0 := by
    have h := ConcreteCategory.congr_hom (e.hom.comm 2 3) a
    change (amitsurUnitComplex E L).d 2 3 (q 2 a) =
      q 3 ((Presheaf.Cech.freeComplex
        (Presheaf.Cech.familyMap (galoisCoverFamily E L))).d 3 2 ≫ a) at h
    rw [ha, map_zero] at h
    exact h
  obtain ⟨b, hb⟩ := amitsurUnitComplex_exists_primitive E L K (q 2 a) ha'
  refine ⟨(q 1).symm b, (q 2).injective ?_⟩
  have h := ConcreteCategory.congr_hom (e.hom.comm 1 2) ((q 1).symm b)
  change (amitsurUnitComplex E L).d 1 2 (q 1 ((q 1).symm b)) =
    q 2 ((Presheaf.Cech.freeComplex
      (Presheaf.Cech.familyMap (galoisCoverFamily E L))).d 2 1 ≫ (q 1).symm b) at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm.trans hb

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
