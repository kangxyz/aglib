/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.FieldCoordinates
public import Aglib.AlgebraicGeometry.Geometrically.Integral.StandardEtaleHypersurfaceOpen

/-! # An original common open for a smooth geometrically integral field scheme

The affine coordinate ring and its principal localization belong to the
original scheme. Geometric integrality of the original scheme supplies the
domain property after scalar extension through the original open immersion.
The resulting hypersurface open retains the original structural triangle.
This is a field construction, not spreading over an integral base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- Scalar extension of the ring of an original nonempty affine open in a
geometrically integral field scheme is a domain. The comparison uses the
actual tensor-product square and the original open immersion. -/
theorem isDomain_tensor_of_geometricallyIntegral_open
    (K Ω B : Type u) [Field K] [Field Ω] [CommRing B] [Nontrivial B]
    [Algebra K Ω] [Algebra K B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (i : Spec (.of B) ⟶ X) [IsOpenImmersion i]
    (hi : Spec.algebraMap K B = i ≫ f) : IsDomain (Ω ⊗[K] B) := by
  let g := Spec.algebraMap K Ω
  let b := Spec.algebraMap K B
  let : Nontrivial (Ω ⊗[K] B) := Function.Injective.nontrivial
    (Algebra.TensorProduct.includeRight_injective (algebraMap K Ω).injective)
  let : IsIntegral (pullback g f) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst g f)
  let m : pullback g b ⟶ pullback g f :=
    pullback.map g b g f (𝟙 _) i (𝟙 _)
      (by simp only [Category.comp_id, Category.id_comp])
      (by simpa only [Category.comp_id] using hi)
  let : IsIntegral (Spec (.of (Ω ⊗[K] B))) :=
    isIntegral_of_isOpenImmersion ((pullbackSpecIso K Ω B).inv ≫ m)
  exact (affine_isIntegral_iff (.of (Ω ⊗[K] B))).mp inferInstance

/-- A smooth geometrically integral field scheme has an original nonempty
affine principal open which is also an open of a hypersurface irreducible
over the supplied field extension. The original map to the original field
is retained. -/
theorem exists_smooth_hypersurface_common_open
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [GeometricallyIntegral f] :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), Nonempty U ∧
      ∃ s : Γ(X, U), s ≠ 0 ∧ ∃ F : MvPolynomial (Fin (n + 1)) K,
        Irreducible (MvPolynomial.map (algebraMap K Ω) F) ∧
        ∃ j : Spec (.of (Localization.Away s)) ⟶
          Spec (.of (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F})),
          Nonempty (Spec (.of (Localization.Away s))) ∧ IsOpenImmersion j ∧
          j ≫ Spec.algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F}) =
            Spec.algebraMap Γ(X, U) (Localization.Away s) ≫ hU.fromSpec ≫ f := by
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, hx, γ, hγe, hγ⟩ :=
    SmoothLocalCoordinates.exists_field_coordinates K f n x
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let B := Γ(X, U)
  let : Algebra K B := (γ.comp MvPolynomial.C).toAlgebra
  let : Algebra (MvPolynomial (Fin n) K) B := γ.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.Etale (MvPolynomial (Fin n) K) B := hγe.toAlgebra
  have hB : Spec.algebraMap K B = hU.fromSpec ≫ f := hγ
  let : IsDomain (Ω ⊗[K] B) :=
    isDomain_tensor_of_geometricallyIntegral_open K Ω B f hU.fromSpec hB
  obtain ⟨s, hs, F, hF, j, hjopen, hj⟩ :=
    exists_standardEtale_hypersurface_open K Ω B n
  let : IsDomain (Localization.Away s) :=
    IsLocalization.Away.isDomain (Localization.Away s) hs
  refine ⟨U, hU, inferInstance, s, hs, F, hF, j, inferInstance, hjopen, ?_⟩
  calc
    j ≫ Spec.algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F}) =
        Spec.algebraMap K (Localization.Away s) := hj
    _ = Spec.algebraMap B (Localization.Away s) ≫ Spec.algebraMap K B :=
      (Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom K B (Localization.Away s))).symm
    _ = Spec.algebraMap B (Localization.Away s) ≫ hU.fromSpec ≫ f := by rw [hB]

end AlgebraicGeometry.Scheme
