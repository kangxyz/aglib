/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.FieldExtensionFiniteType
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber

/-! # Dimension after field extension for arbitrary finite-type schemes

The actual tensor-product calculation for affine charts and an arbitrary
open cover show that extension of the ground field does not increase the
dimension of any scheme locally of finite type over a field.
Quasi-compactness is not needed. The base field need not be algebraically
closed or perfect, and the base-changed scheme need not remain integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- A nonempty affine finite-type field scheme has no larger dimension
after any extension of its ground field. The pullback is the actual scheme
pullback along the displayed field-valued morphism. -/
theorem Scheme.Hom.topologicalKrullDim_fieldBaseChange_le_of_isAffine_of_nonempty
    {k K : Type u} [Field k] [Field K]
    {X : Scheme.{u}} [IsAffine X] [Nonempty X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (η : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback (C := Scheme) f η) ≤ topologicalKrullDim X := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice ‹Nonempty X›, trivial⟩⟩
  let S := Spec (.of k)
  let : Field Γ(S, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (η ≫ S.isoSpec.hom)
  let : Algebra Γ(S, ⊤) K := φ.hom.toAlgebra
  let e₁ : pullback f η ≅ pullback (Spec.map f.appTop) (Spec.map φ) :=
    asIso (pullback.map _ _ _ _ X.isoSpec.hom (𝟙 _) S.isoSpec.hom
      (Scheme.isoSpec_hom_naturality f).symm (by simpa using hφ.symm))
  let e₂ : pullback (Spec.map f.appTop) (Spec.map φ) ≅
      Spec (.of (K ⊗[Γ(S, ⊤)] Γ(X, ⊤))) :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso Γ(S, ⊤) K Γ(X, ⊤)
  calc
    topologicalKrullDim (pullback (C := Scheme) f η) =
        topologicalKrullDim (Spec (.of (K ⊗[Γ(S, ⊤)] Γ(X, ⊤)))) :=
      IsHomeomorph.topologicalKrullDim_eq _ (e₁ ≪≫ e₂).hom.homeomorph.isHomeomorph
    _ = ringKrullDim (K ⊗[Γ(S, ⊤)] Γ(X, ⊤)) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ ringKrullDim Γ(X, ⊤) :=
      Algebra.ringKrullDim_tensorProduct_le_of_finiteType Γ(S, ⊤) Γ(X, ⊤) K
    _ = topologicalKrullDim (Spec Γ(X, ⊤)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ = topologicalKrullDim X :=
      (IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph).symm

/-- Extension of the ground field does not increase dimension for any
scheme locally of finite type over a field. No properness, quasi-compactness,
normality or geometric-integrality hypothesis is imposed. -/
theorem Scheme.Hom.topologicalKrullDim_fieldBaseChange_le_of_finiteType
    {k K : Type u} [Field k] [Field K]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (η : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback (C := Scheme) f η) ≤ topologicalKrullDim X := by
  apply Scheme.topologicalKrullDim_le_of_openCover
    (Scheme.Pullback.openCoverOfLeft X.affineCover f η)
  intro i
  let : IsAffine (X.affineCover.X i) := Scheme.isAffine_affineCover X i
  let : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  by_cases hi : Nonempty (X.affineCover.X i)
  · let : Nonempty (X.affineCover.X i) := hi
    exact (Scheme.Hom.topologicalKrullDim_fieldBaseChange_le_of_isAffine_of_nonempty
      (X.affineCover.f i ≫ f) η).trans
      (X.affineCover.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le
  · let : IsEmpty (X.affineCover.X i) := not_nonempty_iff.mp hi
    let : IsEmpty (pullback (C := Scheme) (X.affineCover.f i ≫ f) η) :=
      Function.isEmpty (pullback.fst (X.affineCover.f i ≫ f) η)
    exact (Topology.IsOpenEmbedding.of_isEmpty
      (pullback.fst (X.affineCover.f i ≫ f) η ≫
        X.affineCover.f i)).isInducing.topologicalKrullDim_le

end AlgebraicGeometry
