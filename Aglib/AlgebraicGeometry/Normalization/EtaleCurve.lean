/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Nagata
public import Aglib.AlgebraicGeometry.Normalization.FiniteFromDenseSource
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Aglib.RingTheory.Nagata.FieldCurve

/-! # Finite relative normalization of etale morphisms to field curves

The generic fibre is the literal pullback to the original function field.
Its projection is schematically dominant by flat base change, so finiteness
of its generic normalization descends to the actual relative normalization.
Neither the base curve nor the etale source is assumed normal. The source
need not be integral, connected or nonempty.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Every actual affine section ring of a finite-type field curve is Nagata.
The structural field map is the supplied original scheme morphism. -/
theorem isNagataRing_sections_of_fieldCurve
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : IsAffineOpen U) :
    IsNagataRing.{u, 0} Γ(X, U) := by
  let α : k →+* Γ(X, U) :=
    (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(X, U) := α.toAlgebra
  let : Algebra.FiniteType k Γ(X, U) :=
    (p.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  apply IsNagataRing.of_finiteType_field_dimLE_one k Γ(X, U)
  calc
    ringKrullDim Γ(X, U) = topologicalKrullDim (Spec Γ(X, U)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ = topologicalKrullDim U.toScheme :=
      (IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph).symm
    _ ≤ topologicalKrullDim X := U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
    _ ≤ 1 := hdim

/-- A qcqs etale morphism to an integral finite-type field curve has finite
actual relative normalization. This allows arbitrary fields and arbitrary
etale sources, including split or empty sources. -/
theorem Hom.isFinite_fromNormalization_of_etale_fieldCurve
    {k : Type u} [Field k] {V X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1)
    (f : V ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f] :
    IsFinite f.fromNormalization := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let γ := X.fromSpecStalk (genericPoint X)
  let g := pullback.snd f γ
  let : IsFinite g := IsFinite.of_locallyQuasiFinite g
  let C : Scheme.FiniteEtale (Spec X.functionField) := Scheme.FiniteEtale.mk g
  have hfinite : IsFinite (g ≫ γ).fromNormalization :=
    FiniteEtale.GenericNormalization.isFinite_of_isNagataRing X C
      (fun U _ => isNagataRing_sections_of_fieldCurve p hdim U.1 U.2)
  let : IsSchemeTheoreticallyDominant γ :=
    IsSchemeTheoreticallyDominant.of_isDominant γ
  have htransport (a : pullback f γ ⟶ X) [QuasiCompact a] [QuasiSeparated a]
      (ha : a = g ≫ γ) : IsFinite a.fromNormalization := by
    subst a
    exact hfinite
  let : IsFinite (pullback.fst f γ ≫ f).fromNormalization := by
    exact htransport _ (pullback.condition (f := f) (g := γ))
  exact f.isFinite_fromNormalization_of_comp (pullback.fst f γ)

end AlgebraicGeometry.Scheme
