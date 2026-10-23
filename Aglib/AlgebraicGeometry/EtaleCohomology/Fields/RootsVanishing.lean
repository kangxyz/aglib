/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteCohomologicalDimension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CyclicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant

/-! # Higher original root cohomology over separably closed constant fields

Actual cyclic short exact sequences reduce every positive invertible order
to its prime divisors. Native constant-root coordinates then identify the
original coefficient sheaves on the actual function-field spectrum. No
multiplicative-sheaf invariance over imperfect constants is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

attribute [local instance] hasSheafifyLarge

variable (K E : Type u) [Field K] [IsSepClosed K] [Field E]
  [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of E)))]

/-- All positive constant cyclic coefficients of invertible order have zero
original cohomology in degrees at least two. -/
theorem constant_cohomology_subsingleton_of_separablyClosed_ratFunc
    (n : ℕ) (hn : 0 < n) (hK : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of E))) q) := by
  apply Curves.cyclic_vanishing_of_prime_divisors (Spec (.of E)) q n hn
  intro p hp hpn
  let : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit (p : Γ(Spec (.of K), ⊤)) := by
    apply isUnit_of_dvd_unit _ hK
    obtain ⟨m, hm⟩ := hpn
    exact ⟨m, by rw [hm, Nat.cast_mul]⟩
  have hzero : p • 𝟙 (AddCommGrpCat.of (ZMod p)) = 0 := by
    ext a
    change p • a = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hk : KilledBy p
      (ConstantFinite.coefficient (ULift.{u} (ZMod p)) (Spec (.of E))) := by
    change p • 𝟙 (ConstantFinite.coefficient (ULift.{u} (ZMod p)) (Spec (.of E))) = 0
    have h := congrArg (fun f => (Curves.cyclicCoefficientFunctor (Spec (.of E))).map f) hzero
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    exact h
  exact finite_cohomology_subsingleton_of_separablyClosed_ratFunc K p hunit E _
    (ConstantFinite.isFiniteLocallyConstant _ _) hk q hq

/-- Every positive invertible root sheaf has zero original higher
cohomology over an algebraic function field with possibly imperfect
separably closed constants. -/
theorem roots_cohomology_subsingleton_of_separablyClosed_ratFunc
    (n : ℕ) (hn : 0 < n) (hK : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (GroupCohomology.Kummer.Coefficients.mu (Spec (.of E)) n) q) := by
  let : IsSepClosed (IsLocalRing.ResidueField K) :=
    Algebra.IsAlgebraic.isSepClosed (F := K) (E := IsLocalRing.ResidueField K)
  let f : Spec (.of E) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))))
  let e := Kummer.HenselianConstant.constantRootIsoOver K n hn hK f
  let : Subsingleton (Sheaf.H.{w}
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of E))) q) :=
    constant_cohomology_subsingleton_of_separablyClosed_ratFunc K E n hn hK q hq
  refine ⟨fun a b => ?_⟩
  have h := congrArg (Sheaf.H.map e.hom q)
    (Subsingleton.elim (Sheaf.H.map e.inv q a) (Sheaf.H.map e.inv q b))
  simpa only [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
