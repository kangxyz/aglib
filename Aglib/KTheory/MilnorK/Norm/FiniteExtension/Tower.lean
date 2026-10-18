/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.NestedDescent
public import Aglib.RingTheory.AdjoinRootNestedBranches

/-!
# General finite-extension norm transitivity

Actual direct and nested scalar branches are matched by tensor associativity.
Over each Sylow fixed field, every lower branch embeds into the p-group
splitting field, so proved p-group transitivity identifies the complete sums.
Joint restriction detection then proves the original tower equality.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot

universe u

local instance towerRootFinite {A : Type u} [Field A] (p : MonicIrreducible A) :
    FiniteDimensional A (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance towerRootCharZero {A : Type u} [Field A] [CharZero A]
    (p : MonicIrreducible A) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap A (AdjoinRoot p.val)).injective

attribute [local instance] AdjoinRoot.scalarBranchAlgebra

/-- Actual norm naturality retains the complete original source-field square. -/
theorem finiteExtensionNorm_map_square
    {S A B C : Type*} [Field S] [CharZero S] [Field A] [Field B] [Field C]
    [Algebra S A] [Algebra S B] [FiniteDimensional S A] [FiniteDimensional S B]
    (θ : A ≃ₐ[S] B) (f : C →+* A) (g : C →+* B)
    (hsquare : θ.toRingHom.comp f = g) (n : ℕ) (x : K C n) :
    finiteExtensionNorm S A n (map n f x) = finiteExtensionNorm S B n (map n g x) := by
  have hn := finiteExtensionNorm_map_algEquiv θ n (map n f x)
  rw [← LinearMap.comp_apply (map n θ.toRingHom), ← map_comp, hsquare] at hn
  exact hn.symm

/-- Direct base change equals the complete nested branch sum for any two
actual presentations, by the proved literal branch-field equivalences. -/
theorem finiteExtensionNorm_restrict_nested_presentation
    {k S E : Type u} [Field k] [CharZero k] [Field S] [CharZero S]
    [Field E] [Algebra k S] [Algebra k E] [FiniteDimensional k E]
    (p h : MonicIrreducible k) [Algebra (AdjoinRoot p.val) E]
    [IsScalarTower k (AdjoinRoot p.val) E]
    (q : MonicIrreducible (AdjoinRoot p.val))
    (η : AdjoinRoot h.val ≃ₐ[k] E) (ε : AdjoinRoot q.val ≃ₐ[AdjoinRoot p.val] E)
    [Fintype (NestedScalarBranch (S := S) p.val q.val)]
    (n : ℕ) (x : K E n) :
    map n (algebraMap k S) (finiteExtensionNorm k E n x) =
      ∑ u : NestedScalarBranch (S := S) p.val q.val,
        let : FiniteDimensional S (AdjoinRoot u.2.val.val) :=
          FiniteDimensional.trans S (AdjoinRoot u.1.val.val) (AdjoinRoot u.2.val.val)
        finiteExtensionNorm S (AdjoinRoot u.2.val.val) n
          (map n ((adjoinRootMap
            (algebraMap (AdjoinRoot p.val) (AdjoinRoot u.1.val.val))
            q.val u.2.val.val u.2.property).comp ε.symm.toRingHom) x) := by
  classical
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k S))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k S))) := Fintype.ofFinite _
  refine (finiteExtensionNorm_restrict_presentation (S := S) E h η n x).trans ?_
  let B := nestedBranchEquiv (S := S) p.val h.val p.property.1 q.val η ε
  refine (B.sum_comp _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro u _
  let : FiniteDimensional S (AdjoinRoot u.2.val.val) :=
    FiniteDimensional.trans S (AdjoinRoot u.1.val.val) (AdjoinRoot u.2.val.val)
  exact finiteExtensionNorm_map_square
    (nestedBranchAlgEquiv (S := S) p.val h.val p.property.1 q.val η ε u) _ _
    (nestedBranchAlgEquiv_comp_originalMap p.val h.val p.property.1 q.val η ε u) n x

/-- Restriction compares the actual original tower after p-group splitting of
its lower polynomial; all direct and nested branches occur in the proof. -/
theorem finiteExtensionNorm_restrict_tower_root_of_pGroup
    {k S E Ω : Type u} [Field k] [CharZero k] [Field S] [CharZero S]
    [Field E] [Field Ω] [Algebra k S] [Algebra k E] [Algebra k Ω]
    [Algebra S Ω] [IsScalarTower k S Ω] [FiniteDimensional S Ω] [IsGalois S Ω]
    (p : MonicIrreducible k) [Algebra (AdjoinRoot p.val) E]
    [IsScalarTower k (AdjoinRoot p.val) E]
    [FiniteDimensional (AdjoinRoot p.val) E] [FiniteDimensional k E]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[S] Ω))
    (hsplit : (p.val.map (algebraMap k Ω)).Splits) (n : ℕ) (x : K E n) :
    map n (algebraMap k S) (finiteExtensionNorm k E n x) =
      map n (algebraMap k S) (finiteExtensionNorm k (AdjoinRoot p.val) n
        (finiteExtensionNorm (AdjoinRoot p.val) E n x)) := by
  classical
  let h := finiteNormPolynomial k E
  let η := finiteNormPresentation k E
  let q := finiteNormPolynomial (AdjoinRoot p.val) E
  let ε := finiteNormPresentation (AdjoinRoot p.val) E
  let : Finite (IrreducibleBranch (p.val.map (algebraMap k S))) :=
    finite_irreducibleBranch _ (p.property.1.map _)
  let : Fintype (IrreducibleBranch (p.val.map (algebraMap k S))) := Fintype.ofFinite _
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k S))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k S))) := Fintype.ofFinite _
  let : ∀ r : IrreducibleBranch (p.val.map (algebraMap k S)),
      Finite (IrreducibleBranch
        (q.val.map (algebraMap (AdjoinRoot p.val) (AdjoinRoot r.val.val)))) :=
    fun _ => finite_irreducibleBranch _ (q.property.1.map _)
  let : ∀ r : IrreducibleBranch (p.val.map (algebraMap k S)),
      Fintype (IrreducibleBranch
        (q.val.map (algebraMap (AdjoinRoot p.val) (AdjoinRoot r.val.val)))) :=
    fun _ => Fintype.ofFinite _
  rw [finiteExtensionNorm_adjoinRoot p n]
  change map n (algebraMap k S) (finiteExtensionNorm k E n x) =
    map n (algebraMap k S) (polynomialNorm n p
      (polynomialNorm n q (map n ε.symm.toRingHom x)))
  refine (finiteExtensionNorm_restrict_nested_presentation (S := S) p h q η ε n x).trans ?_
  have hn := polynomialNorm_restrict_nested_of_pGroup (S := S) (Ω := Ω)
    p q ℓ hG hsplit n (map n ε.symm.toRingHom x)
  simpa only [map_comp, LinearMap.comp_apply] using hn.symm

/-- Sylow fixed-field restrictions jointly detect the original norm tower.
No normality or degree restriction remains on the lower root field. -/
theorem finiteExtensionNorm_tower_root
    {k E : Type u} [Field k] [CharZero k] [Field E] [Algebra k E]
    (p : MonicIrreducible k) [Algebra (AdjoinRoot p.val) E]
    [IsScalarTower k (AdjoinRoot p.val) E]
    [FiniteDimensional (AdjoinRoot p.val) E] [FiniteDimensional k E]
    (n : ℕ) (x : K E n) :
    finiteExtensionNorm k E n x = finiteExtensionNorm k (AdjoinRoot p.val) n
      (finiteExtensionNorm (AdjoinRoot p.val) E n x) := by
  classical
  let Ω := p.val.SplittingField
  let : IsGalois k Ω := ⟨⟩
  apply eq_of_sylow_restrictions k Ω n
  intro ℓ hℓ
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let T : Sylow ℓ (Ω ≃ₐ[k] Ω) := Classical.arbitrary _
  refine ⟨T, ?_⟩
  exact finiteExtensionNorm_restrict_tower_root_of_pGroup (Ω := Ω) p ℓ
    (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ T)
    (SplittingField.splits p.val) n x

/-- General transitivity of actual finite-extension norms in all Milnor degrees.
The original fields and original scalar tower are retained throughout. -/
theorem finiteExtensionNorm_tower
    {k : Type u} [Field k] [CharZero k] (L E : Type u)
    [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (n : ℕ) (x : K E n) :
    finiteExtensionNorm k E n x = finiteExtensionNorm k L n (finiteExtensionNorm L E n x) := by
  let p := finiteNormPolynomial k L
  let ε := finiteNormPresentation k L
  let : Algebra (AdjoinRoot p.val) E :=
    ((algebraMap L E).comp ε.toRingHom).toAlgebra
  let : IsScalarTower k (AdjoinRoot p.val) E := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    change algebraMap k E a = algebraMap L E (ε (algebraMap k (AdjoinRoot p.val) a))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply k L E])
  let : FiniteDimensional (AdjoinRoot p.val) E := FiniteDimensional.right k (AdjoinRoot p.val) E
  have hroot := finiteExtensionNorm_tower_root p n x
  have hbase := finiteExtensionNorm_equiv ε.toRingEquiv (RingEquiv.refl E)
    (show ∀ a : AdjoinRoot p.val,
      (RingEquiv.refl E) (algebraMap (AdjoinRoot p.val) E a) = algebraMap L E (ε a) from
      fun _ => rfl) n x
  change map n ε.toRingHom (finiteExtensionNorm (AdjoinRoot p.val) E n x) =
    finiteExtensionNorm L E n (map n (RingHom.id E) x) at hbase
  rw [map_id, LinearMap.id_apply] at hbase
  rw [hroot, ← finiteExtensionNorm_map_algEquiv ε n, hbase]

/-- General norm transitivity as equality of the actual integer-linear maps. -/
theorem finiteExtensionNorm_tower_comp
    {k : Type u} [Field k] [CharZero k] (L E : Type u)
    [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E] (n : ℕ) :
    finiteExtensionNorm k E n = (finiteExtensionNorm k L n).comp (finiteExtensionNorm L E n) := by
  apply LinearMap.ext
  exact finiteExtensionNorm_tower L E n

end MilnorK
