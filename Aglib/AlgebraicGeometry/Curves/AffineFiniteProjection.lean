/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NoetherNormalization.DimensionOne
public import Aglib.AlgebraicGeometry.Morphisms.Dominant.Spec
public import Aglib.AlgebraicGeometry.Geometrically.Integral.Smooth
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite projections of whole affine curves

Noether normalization supplies an integral polynomial coordinate on the entire
original affine curve. Exact dimension one excludes the zero-variable case;
no open subset is removed, and no perfectness assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace NoetherNormalization

/-- A one-dimensional finite-type domain is finite over an injected polynomial
algebra in exactly one variable. -/
theorem exists_finite_inj_polynomial_algHom
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) :
    ∃ g : Polynomial k →ₐ[k] A, Function.Injective g ∧ g.toRingHom.Finite := by
  obtain ⟨n, hn, g, hg, hint⟩ :=
    exists_integral_inj_algHom_dim_le_one k A hdim.le
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · let e := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm
    have he : e.toRingHom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ e.surjective
    have hf : (algebraMap k A).IsIntegral := by
      have hcomp := he.trans e.toRingHom g.toRingHom hint
      have hmap : g.toRingHom.comp e.toRingHom = algebraMap k A := by
        ext x
        exact (g.comp e.toAlgHom).commutes x
      rwa [hmap] at hcomp
    let : Algebra.IsIntegral k A := ⟨hf⟩
    have hzero : ringKrullDim A = 0 :=
      ringKrullDim_eq_zero_of_isField (isField_of_isIntegral_of_isField' (Field.toIsField k))
    exact False.elim (zero_ne_one (hzero.symm.trans hdim))
  · let e := (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm
    let f : Polynomial k →ₐ[k] A := g.comp e.toAlgHom
    have he : e.toRingHom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ e.surjective
    have hf : f.toRingHom.IsIntegral := he.trans e.toRingHom g.toRingHom hint
    let : Algebra (Polynomial k) A := f.toRingHom.toAlgebra
    let : IsScalarTower k (Polynomial k) A := IsScalarTower.of_algHom f
    let : Algebra.FiniteType (Polynomial k) A :=
      Algebra.FiniteType.of_restrictScalars_finiteType k (Polynomial k) A
    exact ⟨f, hg.comp e.injective, hf.to_finite
      (show Algebra.FiniteType (Polynomial k) A from inferInstance)⟩

end NoetherNormalization

namespace AlgebraicGeometry.Scheme

/-- An affine integral curve of exact dimension one admits a finite map to the
affine line over its original field, defined on the whole source. -/
theorem exists_finite_dominant_affineLine_projection
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [IsIntegral U]
    (p : U ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim U = 1) :
    ∃ q : U ⟶ Spec (.of (Polynomial k)), IsFinite q ∧ IsDominant q ∧
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = p := by
  let φ : k →+* Γ(U, ⊤) := ((ΓSpecIso (.of k)).inv ≫ p.appTop).hom
  let : Algebra k Γ(U, ⊤) := φ.toAlgebra
  have hp : p.appTop.hom.FiniteType := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact p.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  have hφ : φ.FiniteType := hp.comp
    (RingHom.FiniteType.of_surjective _
      (ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let : Algebra.FiniteType k Γ(U, ⊤) := hφ
  have hA : ringKrullDim Γ(U, ⊤) = 1 := by
    calc
      ringKrullDim Γ(U, ⊤) = topologicalKrullDim (Spec Γ(U, ⊤)) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
      _ = topologicalKrullDim U :=
        (IsHomeomorph.topologicalKrullDim_eq _
          U.isoSpec.hom.homeomorph.isHomeomorph).symm
      _ = 1 := hdim
  obtain ⟨g, hinj, hg⟩ :=
    NoetherNormalization.exists_finite_inj_polynomial_algHom k Γ(U, ⊤) hA
  let q := U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom)
  have : IsFinite (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr hg
  let : IsDominant (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    specMap_dominant_of_injective g.toRingHom hinj
  refine ⟨q, inferInstance, inferInstance, ?_⟩
  have hmap : g.toRingHom.comp Polynomial.C = φ := by
    ext x
    exact g.commutes x
  change U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom Polynomial.C) = p
  rw [← Spec.map_comp]
  change U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (g.toRingHom.comp Polynomial.C)) = p
  rw [hmap]
  change U.toSpecΓ ≫ Spec.map ((ΓSpecIso (.of k)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The preceding finite projection applies to every nonempty geometrically
connected smooth affine curve, over arbitrary fields. -/
theorem exists_finite_dominant_affineLine_projection_of_smooth
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ q : U ⟶ Spec (.of (Polynomial k)), IsFinite q ∧ IsDominant q ∧
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = p := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton p
  let : IsIntegral U := isIntegral_of_connected_of_smooth p
  exact exists_finite_dominant_affineLine_projection k U p
    (smoothFieldDimension k U p 1 inferInstance inferInstance)

/-- The finite projection, forgetting only its already proved dominance. -/
theorem exists_finite_affineLine_projection
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [IsIntegral U]
    (p : U ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim U = 1) :
    ∃ q : U ⟶ Spec (.of (Polynomial k)), IsFinite q ∧
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = p := by
  obtain ⟨q, hq, _, hqp⟩ := exists_finite_dominant_affineLine_projection k U p hdim
  exact ⟨q, hq, hqp⟩

/-- The original smooth-affine projection interface is retained unchanged. -/
theorem exists_finite_affineLine_projection_of_smooth
    (k : Type u) [Field k] (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ q : U ⟶ Spec (.of (Polynomial k)), IsFinite q ∧
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = p := by
  obtain ⟨q, hq, _, hqp⟩ := exists_finite_dominant_affineLine_projection_of_smooth k U p
  exact ⟨q, hq, hqp⟩

end AlgebraicGeometry.Scheme
