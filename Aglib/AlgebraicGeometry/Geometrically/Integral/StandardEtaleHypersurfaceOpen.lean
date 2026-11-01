/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.RingTheory.Etale.StandardEtaleDomainOpen
public import Aglib.AlgebraicGeometry.Geometrically.Integral.StandardEtaleFactor
public import Mathlib.RingTheory.Localization.BaseChange

/-! # An original etale principal open inside an integral hypersurface

The same actual principal localization of the original algebra maps by an
open immersion to the factor hypersurface. Its field extension stays a
domain by the native tensor-localization equivalence. The hypersurface
polynomial is the one obtained from the original vanishing factor, and the
open immersion preserves the original structural scalar map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- An actual etale polynomial-coordinate algebra contains a nonzero
principal open which is also an original open of a hypersurface irreducible
over the supplied field extension. This is an affine generic common open,
not spreading over a general integral base. -/
theorem exists_standardEtale_hypersurface_open
    (K Ω B : Type u) [Field K] [Field Ω] [CommRing B] [IsDomain B]
    [Algebra K Ω] [Algebra K B] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) B]
    [IsScalarTower K (MvPolynomial (Fin n) K) B]
    [Algebra.Etale (MvPolynomial (Fin n) K) B] [IsDomain (Ω ⊗[K] B)] :
    ∃ s : B, s ≠ 0 ∧ ∃ F : MvPolynomial (Fin (n + 1)) K,
      Irreducible (MvPolynomial.map (algebraMap K Ω) F) ∧
      ∃ j : Spec (.of (Localization.Away s)) ⟶
        Spec (.of (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F})),
        IsOpenImmersion j ∧
        j ≫ Spec.algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F}) =
          Spec.algebraMap K (Localization.Away s) := by
  obtain ⟨s, hs, P, p, q, hp, hf, hx, e, _, _⟩ :=
    Algebra.exists_nonzero_standardEtale_factor_open (MvPolynomial (Fin n) K) B
  let S := Localization.Away s
  let : IsDomain S := IsLocalization.Away.isDomain S hs
  have hsΩ : (1 : Ω) ⊗ₜ[K] s ≠ 0 := by
    intro h
    apply hs
    apply Algebra.TensorProduct.includeRight_injective (algebraMap K Ω).injective
    exact h.trans (map_zero _).symm
  let : IsDomain (Localization.Away ((1 : Ω) ⊗ₜ[K] s)) :=
    IsLocalization.Away.isDomain (Localization.Away ((1 : Ω) ⊗ₜ[K] s)) hsΩ
  let : IsDomain (Ω ⊗[K] S) :=
    MulEquiv.isDomain (Localization.Away ((1 : Ω) ⊗ₜ[K] s))
      (IsLocalization.Away.tensorProductEquivTMulRight K Ω s S).toMulEquiv
  let F := (MvPolynomial.finSuccEquiv K n).symm p
  have hF : Irreducible (MvPolynomial.map (algebraMap K Ω) F) :=
    P.irreducible_map_factor_of_isDomain_tensor n p q hp hf hx
  let D := AdjoinRoot p
  let A := Localization.Away (AdjoinRoot.mk p (P.g * q))
  let T := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F}
  let eK : S ≃ₐ[K] A := e.restrictScalars K
  let eD : D ≃ₐ[K] T := MvPolynomial.adjoinRootFinSuccEquiv K n p
  let eS : Spec (.of S) ≅ Spec (.of A) :=
    Scheme.Spec.mapIso eK.symm.toRingEquiv.toCommRingCatIso.op
  let eT : Spec (.of D) ≅ Spec (.of T) :=
    Scheme.Spec.mapIso eD.symm.toRingEquiv.toCommRingCatIso.op
  let j : Spec (.of S) ⟶ Spec (.of T) :=
    eS.hom ≫ Spec.algebraMap D A ≫ eT.hom
  have hS : eS.hom ≫ Spec.algebraMap K A = Spec.algebraMap K S := by
    change Spec.map (CommRingCat.ofHom eK.symm.toRingHom) ≫
      Spec.algebraMap K A = Spec.algebraMap K S
    exact Spec.map_algHom_algebraMap eK.symm.toAlgHom
  have hT : eT.hom ≫ Spec.algebraMap K T = Spec.algebraMap K D := by
    change Spec.map (CommRingCat.ofHom eD.symm.toRingHom) ≫
      Spec.algebraMap K T = Spec.algebraMap K D
    exact Spec.map_algHom_algebraMap eD.symm.toAlgHom
  have hA : Spec.algebraMap D A ≫ Spec.algebraMap K D = Spec.algebraMap K A :=
    Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom K D A)
  refine ⟨s, hs, F, hF, j, ?_, ?_⟩
  · dsimp only [j]
    infer_instance
  · dsimp only [j]
    rw [Category.assoc, Category.assoc, hT, hA, hS]

end AlgebraicGeometry.Scheme
