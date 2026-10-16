/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Rigidity of unramified algebra maps

Maps from an essentially finite-type formally unramified algebra to any local commutative
ring are determined by their actual residue maps, including targets with zero divisors.
For a domain target, reductions at a chosen prime also determine the maps. No Noetherian
hypothesis or nilpotence condition on the relevant ideals is imposed.

## Extraction basis

The local-target and local-subalgebra results are transferred from
`R5Lab/AlgebraicGeometry/FiniteEtale/Reduction/PointSpecialization.lean`, lines 37–82,
at R5 revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`32660e0e1f5f95505f9b41c6c52a823d30d13ed2148e39849540c18c2a825957`.
The actual residue map, tensor-product lift, diagonal ideal and codomain restrictions
are retained. Their source-proof correspondence is separate from native Lean validation.

The domain/prime result comes from
`R5Lab/AlgebraicGeometry/FiniteEtale/UnramifiedRigidity.lean` at the private R5 2f9 source,
frozen after the native-consumer refactor, SHA-256
`ae7a23021c805bedf235075e127e7cff6672cfc9548527e143b377dbef735b3e`.
Its existing native statement, context and proof remain unchanged.
-/
@[expose] public section

noncomputable section

open scoped TensorProduct
universe u v w

namespace Algebra.FormallyUnramified

section LocalTarget

variable {R : Type u} {A : Type v} {W : Type w}
  [CommRing R] [CommRing A] [CommRing W]
  [Algebra R A] [Algebra R W] [IsLocalRing W]
  [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]

/-- Maps from an essentially finite-type formally unramified algebra to any local
commutative ring are determined by their actual residue maps. The target may have
zero divisors. The evaluated diagonal idempotent vanishes because its complement is a unit. -/
theorem eq_of_comp_residue_eq (f g : A →ₐ[R] W)
    (h : ∀ a, IsLocalRing.residue W (f a) = IsLocalRing.residue W (g a)) : f = g := by
  let phi : A ⊗[R] A →ₐ[R] W := Algebra.TensorProduct.lift f g (fun a b => Commute.all _ _)
  let I := KaehlerDifferential.ideal R A
  obtain ⟨e, he, hspan⟩ : ∃ e, IsIdempotentElem e ∧ I = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg I (KaehlerDifferential.ideal_fg R A)).mp
      ((Ideal.cotangent_subsingleton_iff I).mp
        (inferInstanceAs (Subsingleton (KaehlerDifferential R A))))
  have hI : I ≤ (IsLocalRing.maximalIdeal W).comap phi.toRingHom := by
    rw [show I = _ from (KaehlerDifferential.span_range_eq_ideal (R := R) (S := A)).symm,
      Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    change phi (1 ⊗ₜ[R] a - a ⊗ₜ[R] 1) ∈ IsLocalRing.maximalIdeal W
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    simp only [phi, map_sub, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one]
    exact sub_eq_zero.mpr (h a).symm
  have hemem : phi e ∈ IsLocalRing.maximalIdeal W :=
    hI (hspan.symm ▸ Ideal.subset_span (Set.mem_singleton e))
  have hmul : phi e * (1 - phi e) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  have he0 : phi e = 0 :=
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (phi e)
      ((IsLocalRing.mem_maximalIdeal _).mp hemem)).mul_left_eq_zero.mp hmul
  have hker : I ≤ RingHom.ker phi.toRingHom := by
    rw [hspan, Ideal.span_le]
    rintro _ (rfl : _ = e)
    exact he0
  ext a
  have hz := hker (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a)
  change phi (1 ⊗ₜ[R] a - a ⊗ₜ[R] 1) = 0 at hz
  simp only [phi, map_sub, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one,
    sub_eq_zero] at hz
  exact hz.symm

/-- Maps into a common ambient algebra are determined by residue equality in a
specified local subalgebra containing their values. The restrictions use the given
membership proofs and the actual residue map of that subalgebra. -/
theorem eq_of_comp_residue_eq_of_mem_subalgebra
    {L : Type*} [CommRing L] [Algebra R L]
    (S : Subalgebra R L) [IsLocalRing S]
    (f g : A →ₐ[R] L) (hf : ∀ a, f a ∈ S) (hg : ∀ a, g a ∈ S)
    (h : ∀ a, IsLocalRing.residue S (⟨f a, hf a⟩ : S) =
      IsLocalRing.residue S (⟨g a, hg a⟩ : S)) : f = g := by
  have hi : f.codRestrict S hf = g.codRestrict S hg :=
    eq_of_comp_residue_eq (f.codRestrict S hf) (g.codRestrict S hg) h
  ext a
  exact congrArg (fun q : A →ₐ[R] S => (q a : L)) hi

end LocalTarget

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsDomain B]
  [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]

/-- Maps from an essentially finite type unramified algebra to a domain are
determined by their reduction at a prime. The tensor separator supplies the
rigidity; no separation or Noetherian assumption is placed on the domain. -/
theorem eq_of_comp_mkQ_eq (Q : Ideal B) [Q.IsPrime] (f g : A →ₐ[R] B)
    (hfg : ∀ a, (Ideal.Quotient.mk Q) (f a) = (Ideal.Quotient.mk Q) (g a)) : f = g := by
  obtain ⟨t, ht, hμ⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp
      inferInstance
  let H : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)
  have hmod (z : A ⊗[R] A) :
      (Ideal.Quotient.mk Q) (H z) =
        (Ideal.Quotient.mk Q) (f (Algebra.TensorProduct.lmul' R z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [H, Algebra.TensorProduct.lift_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
        rw [hfg b]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hH : H t ≠ 0 := by
    intro h
    have := hmod t
    rw [h, hμ, map_zero, map_one, map_one] at this
    exact zero_ne_one this
  ext a
  have ha := congrArg H (ht a)
  have hz : (g a - f a) * H t = 0 := by
    simpa only [map_mul, map_sub, H, Algebra.TensorProduct.lift_tmul,
      map_one, one_mul, mul_one, map_zero] using ha
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hH)).symm

end Algebra.FormallyUnramified
