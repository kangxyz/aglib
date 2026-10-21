/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Ideal.Span

/-!
# Rank-one cancellation for finite free products

An actual basis of `M × Rⁿ` with `n + 1` vectors gives a cyclic generator of
`M`. The construction uses the cofactor alternating map with values in `M`.
For a nonzero ideal of a domain, comparison with `R × Rⁿ` supplies the rank
equality. Consequently a stably free ideal is principal.
-/

@[expose] public section

noncomputable section

universe u v w

open Module

namespace AlternatingMap

/-- The determinant expansion of a top-degree alternating map also holds
when its values lie in an arbitrary module. -/
theorem eq_basis_det_smulRight
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (f : M [⋀^ι]→ₗ[R] N) :
    f = b.det.smulRight (f b) := by
  refine b.ext_alternating fun i hi => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
  change f (b ∘ σ) = b.det.smulRight (f b) (b ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self, Units.smul_def]

end AlternatingMap

namespace Module

private def cofactorAlternatingMap
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : (M × (Fin n → R)) [⋀^Fin (n + 1)]→ₗ[R] M := by
  classical
  let d := (Pi.basisFun R (Fin n)).det.compLinearMap (LinearMap.snd R M (Fin n → R))
  let f : (M × (Fin n → R)) →ₗ[R]
      (M × (Fin n → R)) [⋀^Fin n]→ₗ[R] M :=
    { toFun := fun z => d.smulRight z.1
      map_add' := fun x y => by ext v; simp [smul_add]
      map_smul' := fun r x => by ext v; simp [smul_smul, mul_comm] }
  exact AlternatingMap.alternatizeUncurryFin f

private theorem cofactorAlternatingMap_cons
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (m : M) :
    cofactorAlternatingMap R M n
      (Fin.cons (m, 0) (fun i => (0, Pi.basisFun R (Fin n) i))) = m := by
  classical
  have hb : (fun i : Fin n => Pi.single i (1 : R)) = Pi.basisFun R (Fin n) :=
    funext fun i => (Pi.basisFun_apply R (Fin n) i).symm
  have hd : Matrix.detRowAlternating (fun i : Fin n => Pi.single i (1 : R)) = 1 := by
    rw [hb, ← Pi.basisFun_det, Basis.det_self]
  simp [cofactorAlternatingMap, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, Fin.removeNth, AlternatingMap.compLinearMap_apply, hd]

/-- A basis of `M × Rⁿ` with `n + 1` elements gives an actual cyclic
generator of `M`, without any freeness assumption on `M`. -/
theorem exists_smul_eq_of_basis_prod
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ) (b : Basis (Fin (n + 1)) R (M × (Fin n → R))) :
    ∃ m : M, ∀ x : M, ∃ r : R, r • m = x := by
  classical
  let f := cofactorAlternatingMap R M n
  refine ⟨f b, fun x => ⟨b.det
    (Fin.cons (x, 0) (fun i => (0, Pi.basisFun R (Fin n) i))), ?_⟩⟩
  have h := congrArg
    (fun g : (M × (Fin n → R)) [⋀^Fin (n + 1)]→ₗ[R] M =>
      g (Fin.cons (x, 0) (fun i => (0, Pi.basisFun R (Fin n) i))))
    (f.eq_basis_det_smulRight b)
  exact h.symm.trans (cofactorAlternatingMap_cons R M n x)

end Module

namespace Ideal

/-- A nonzero ideal of a domain whose product with a finite free module is
finite free is principal. No projectivity or factoriality premise is needed. -/
theorem isPrincipal_of_free_prod
    {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (N : Type v) [AddCommGroup N] [Module R N]
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R (I × N)] [Module.Finite R (I × N)] : I.IsPrincipal := by
  classical
  let n := Module.finrank R N
  let eN : N ≃ₗ[R] (Fin n → R) := (Module.finBasis R N).equivFun
  let e := (LinearEquiv.refl R I).prodCongr eN
  have : Module.Free R (I × (Fin n → R)) := Module.Free.of_equiv e
  have : Module.Finite R (I × (Fin n → R)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  obtain ⟨a, ha, ha0⟩ := I.ne_bot_iff.mp hI
  let f : (I × (Fin n → R)) →ₗ[R] R × (Fin n → R) :=
    I.subtype.prodMap LinearMap.id
  have hf : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · simpa [f] using congrArg Prod.snd h
  let g : (R × (Fin n → R)) →ₗ[R] I × (Fin n → R) :=
    (LinearMap.toSpanSingleton R I (⟨a, ha⟩ : I)).prodMap LinearMap.id
  have hg : Function.Injective g := by
    intro x y h
    apply Prod.ext
    · have he : x.1 * a = y.1 * a := congrArg (fun z => (z.1 : R)) h
      exact mul_right_cancel₀ ha0 he
    · simpa [g] using congrArg Prod.snd h
  have hr : Module.finrank R (I × (Fin n → R)) = n + 1 := by
    have hle := f.finrank_le_finrank_of_injective hf
    have hge := g.finrank_le_finrank_of_injective hg
    simpa [Module.finrank_prod, Module.finrank_pi, Nat.add_comm] using le_antisymm hle hge
  let b : Basis (Fin (n + 1)) R (I × (Fin n → R)) :=
    (Module.finBasis R (I × (Fin n → R))).reindex (finCongr hr)
  obtain ⟨m, hm⟩ := Module.exists_smul_eq_of_basis_prod n b
  refine ⟨m.1, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr m.2)⟩
  intro x hx
  obtain ⟨r, hr⟩ := hm ⟨x, hx⟩
  exact Ideal.mem_span_singleton'.mpr ⟨r, congrArg Subtype.val hr⟩

end Ideal
