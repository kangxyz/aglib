/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.NilpotentLift
public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeCoordinates
public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Nilpotent affine stages of proper-residue object existence

The actual finite étale pullback along Spec(R/I) → Spec(R) is essentially
surjective when I is nilpotent. The lifted cover is the spectrum of the
constructed finite étale algebra, with an actual pullback square retaining
the prescribed cover and structural map.

This affine object-existence step uses no locality, Henselianity, Noetherianity
or completeness. Gluing the nilpotent lifts on an arbitrary scheme, proper
formal algebraization and incomplete-base approximation remain separate.
There is no proper-residue EssSurj or IsEquivalence assertion in this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.Nilpotent

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- Every actual finite étale cover of a nilpotent affine closed subscheme
occurs in a pullback square from a constructed finite étale algebra. -/
theorem exists_spec_quotient_pullback (hI : IsNilpotent I)
    (Y : FiniteEtale (Spec (.of (R ⧸ I)))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        ∃ g : Y.obj.left ⟶ Spec (.of A),
          IsPullback g Y.obj.hom (Spec.algebraMap R A)
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let B : Type u := Γ(Y.obj.left, ⊤)
  let : CommRing B := inferInstanceAs (CommRing Γ(Y.obj.left, ⊤))
  let : Algebra (R ⧸ I) B := AffineBaseChange.coordinateAlgebra (R ⧸ I) Y.obj
  have hcoord : Y.obj.left.isoSpec.inv ≫ Y.obj.hom =
      Spec.algebraMap (R ⧸ I) B := AffineBaseChange.isoSpec_inv_over (R ⧸ I) Y.obj
  have hcoord' : Y.obj.left.isoSpec.hom ≫ Spec.algebraMap (R ⧸ I) B = Y.obj.hom := by
    rw [← hcoord]
    simp
  let : Algebra.Etale (R ⧸ I) B := by
    have he : Etale (Spec.algebraMap (R ⧸ I) B) := by rw [← hcoord]; infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  let : Module.Finite (R ⧸ I) B := by
    have hfin : IsFinite (Spec.algebraMap (R ⧸ I) B) := by
      rw [← hcoord]
      infer_instance
    exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)
  obtain ⟨A, hA, hAlg, hfin, het, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_nilpotent_lift R I hI B
  let : CommRing A := hA
  let : Algebra R A := hAlg
  let a : A →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] (R ⧸ I) ⊗[R] A).toRingHom
  have hp : IsPullback (Spec.map (CommRingCat.ofHom a))
      (Spec.algebraMap (R ⧸ I) B) (Spec.algebraMap R A)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    Spec.isPullback_of_tensorEquiv e a rfl
  refine ⟨A, hA, hAlg, hfin, het,
    Y.obj.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom a), ?_⟩
  exact hp.of_iso' Y.obj.left.isoSpec (.refl _) (.refl _) (.refl _)
    (by simp) (by simpa using hcoord') (by simp) (by simp)

/-- The prescribed cover is isomorphic over the actual quotient spectrum to
the literal pullback of a constructed finite étale cover. -/
theorem exists_quotient_baseChange_iso (hI : IsNilpotent I)
    (Y : FiniteEtale (Spec (.of (R ⧸ I)))) :
    ∃ X : FiniteEtale (Spec (.of R)),
      Nonempty ((baseChange (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj X ≅ Y) := by
  obtain ⟨A, hA, hAlg, hfin, het, g, hg⟩ := exists_spec_quotient_pullback R I hI Y
  let : CommRing A := hA
  let : Algebra R A := hAlg
  let : IsFinite (Spec.algebraMap R A) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
  let : Etale (Spec.algebraMap R A) :=
    (HasRingHomProperty.Spec_iff (P := @Etale.{u})).mpr (RingHom.etale_algebraMap.mpr het)
  exact ⟨mk (Spec.algebraMap R A),
    ⟨ObjectProperty.isoMk _ (Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd)⟩⟩

/-- Nilpotent affine closed restriction is essentially surjective on actual
finite étale covers. No object-lifting family is assumed. -/
theorem quotient_baseChange_essSurj (hI : IsNilpotent I) :
    (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).EssSurj where
  mem_essImage Y := exists_quotient_baseChange_iso R I hI Y

/-- The forward cover retains the original categorical second projection. -/
@[simp]
theorem quotient_baseChange_obj_hom (Y : FiniteEtale (Spec (.of R))) :
    ((baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj Y).obj.hom =
      pullback.snd Y.obj.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := rfl

/-- The original first-projection equation for a pulled-back cover morphism. -/
@[reassoc]
theorem quotient_baseChange_map_fst {Y Z : FiniteEtale (Spec (.of R))} (f : Y ⟶ Z) :
    ((baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f).hom.left ≫
        pullback.fst Z.obj.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      pullback.fst Y.obj.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ f.hom.left :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale.Nilpotent
