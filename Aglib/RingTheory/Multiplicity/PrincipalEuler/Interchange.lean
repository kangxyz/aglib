/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity

/-!
# Interchanging two principal scalar quotients

The double cokernels and the cross kernels are compared as actual modules.
The cross-kernel comparison assumes that both scalars are individually regular
on the original module; neither must be regular on the other scalar quotient.
The resulting Euler equality also applies to modules with an embedded component
after the first quotient. Finiteness needed for Euler associativity is stated
separately and is not inferred from regularity alone.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEulerInterchange` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`4272b5e8e6303deec26e073b19c1243de481d2a4907315493549841749a42285`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

theorem scalarCokernelMap_lsmul (a b : A) :
    scalarCokernelMap (LinearMap.lsmul A M a) b =
      LinearMap.lsmul A (ScalarCokernel M b) a := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

/-- Both successive quotient orders have the literal common quotient by aM+bM. -/
def scalarDoubleCokernelEquiv (a b : A) :
    ScalarCokernel (ScalarCokernel M a) b ≃ₗ[A]
      ScalarCokernel (ScalarCokernel M b) a := by
  let U := LinearMap.range (LinearMap.lsmul A M a)
  let V := LinearMap.range (LinearMap.lsmul A M b)
  have hab : V.map U.mkQ = LinearMap.range (LinearMap.lsmul A (M ⧸ U) b) := by
    rw [← LinearMap.range_comp, scalarSquare U.mkQ b, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective U), Submodule.map_top]
  have hba : U.map V.mkQ = LinearMap.range (LinearMap.lsmul A (M ⧸ V) a) := by
    rw [← LinearMap.range_comp, scalarSquare V.mkQ a, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective V), Submodule.map_top]
  let e₁ : ScalarCokernel (ScalarCokernel M a) b ≃ₗ[A] M ⧸ U ⊔ V :=
    (Submodule.quotEquivOfEq _ _ hab.symm).trans
      (Submodule.quotientQuotientEquivQuotientSup U V)
  let e₂ : ScalarCokernel (ScalarCokernel M b) a ≃ₗ[A] M ⧸ V ⊔ U :=
    (Submodule.quotEquivOfEq _ _ hba.symm).trans
      (Submodule.quotientQuotientEquivQuotientSup V U)
  exact e₁.trans ((Submodule.quotEquivOfEq _ _ (sup_comm U V)).trans e₂.symm)

/-- The connecting map is the syzygy comparison a*u=b*v. Individual regularity
on M suffices; neither scalar is required regular on the other quotient. -/
def scalarCrossKernelEquiv (a b : A) (ha : IsSMulRegular M a)
    (hb : IsSMulRegular M b) :
    ScalarKernel (ScalarCokernel M a) b ≃ₗ[A]
      ScalarKernel (ScalarCokernel M b) a := by
  let f := LinearMap.lsmul A M a
  let g := (LinearMap.range f).mkQ
  have hf : Function.Injective f := ha
  have hg : Function.Surjective g := Submodule.mkQ_surjective _
  have hex : Function.Exact f g := LinearMap.exact_map_mkQ_range f
  let δ := principalConnecting f g hf hg hex b
  have hright := principalConnecting_exact_right f g hf hg hex b
  have hleft := principalConnecting_exact_left f g hf hg hex b
  have he : scalarCokernelMap f b = LinearMap.lsmul A (ScalarCokernel M b) a :=
    scalarCokernelMap_lsmul a b
  have hker : Subsingleton (ScalarKernel M b) := by
    constructor
    intro x y
    apply Subtype.ext
    apply hb
    exact x.property.trans y.property.symm
  let := hker
  have hδ : Function.Injective δ := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    obtain ⟨z, hz⟩ := (hright x).mp hx
    have hz0 : z = 0 := Subsingleton.elim _ _
    simpa only [Submodule.mem_bot, hz0, map_zero] using hz.symm
  let d : ScalarKernel (ScalarCokernel M a) b →ₗ[A]
      ScalarKernel (ScalarCokernel M b) a :=
    δ.codRestrict _ (by
      intro x
      change LinearMap.lsmul A (ScalarCokernel M b) a (δ x) = 0
      rw [← he]
      exact (hleft (δ x)).mpr ⟨x, rfl⟩)
  apply LinearEquiv.ofBijective d
  constructor
  · intro x y hxy
    apply hδ
    exact congrArg Subtype.val hxy
  · intro y
    have hy : scalarCokernelMap f b y.val = 0 := by
      rw [he]
      exact y.property
    obtain ⟨x, hx⟩ := (hleft y.val).mp hy
    exact ⟨x, Subtype.ext hx⟩

/-- Equality of actual scalar Euler expressions in the two quotient orders.
Finite double cokernel length is needed when interpreting these expressions as
finite Euler characteristics, but not for the canonical comparison itself. -/
theorem principalEuler_interchange (a b : A) (ha : IsSMulRegular M a)
    (hb : IsSMulRegular M b) :
    principalEuler (N := ScalarCokernel M a) b =
      principalEuler (N := ScalarCokernel M b) a := by
  unfold principalEuler
  rw [(scalarDoubleCokernelEquiv (M := M) a b).length_eq,
    (scalarCrossKernelEquiv a b ha hb).length_eq]

/-- Finite double cokernel gives finite principal homology in both orders,
without scalar regularity on either intermediate quotient. -/
theorem finitePrincipal_doubleCokernel [IsNoetherianRing A] [Module.Finite A M]
    (a b : A)
    (h : Module.length A (ScalarCokernel (ScalarCokernel M a) b) ≠ ⊤) :
    FinitePrincipal (ScalarCokernel M a) b ∧ FinitePrincipal (ScalarCokernel M b) a := by
  constructor
  · exact finitePrincipal_of_support_subset (M := ScalarCokernel M a)
      (N := ScalarCokernel M a) b h (Set.Subset.refl _)
  · rw [(scalarDoubleCokernelEquiv (M := M) a b).length_eq] at h
    exact finitePrincipal_of_support_subset (M := ScalarCokernel M b)
      (N := ScalarCokernel M b) a h (Set.Subset.refl _)

/-- Euler associativity requires regularity only on the contributing prime
quotients; the intermediate module may have scalar torsion. -/
theorem principalEuler_associativity_of_minimalRegular [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤)
    (hr : ∀ p ∈ (Module.annihilator A M).minimalPrimes, IsSMulRegular (A ⧸ p) t) :
    principalEuler (N := M) t =
      ∑ p ∈ moduleMinimalPrimes (A := A) M, minimalPrimeCokernelTerm M t p := by
  classical
  rw [principalEuler_associativity t ht hM]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := (mem_moduleMinimalPrimes p).mp hp
  simp only [minimalPrimeEulerTerm, minimalPrimeCokernelTerm, dite_eq_left hm]
  rw [principalEuler_of_regular t (hr p hm)]

end Module
