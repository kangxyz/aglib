/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Field
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Aglib.RingTheory.LocalRing.ResidueTensor
public import Aglib.RingTheory.Localization.ModulePresentation
public import Aglib.AlgebraicGeometry.Modules.Invertible.Field
public import Aglib.RingTheory.Flat.IdealBaseChange
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Field fibres and lifted generators of smooth divisor ideals

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open TensorProduct
open LinearMap
open Module
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

/-- Every field-valued pullback of a finite flat divisor ideal is a line,
without assuming beforehand that the original ideal is invertible. -/
theorem fieldPoint_idealPullback_rankOne
    {S X D : Scheme.{u}} (p : X ⟶ S) [SmoothOfRelativeDimension 1 p]
    (i : D ⟶ X) [IsClosedImmersion i] [LocallyQuasiFinite (i ≫ p)] [Flat (i ≫ p)]
    (K : Type u) [Field K] (x : Spec (.of K) ⟶ X) :
    IsLocallyRankOne (Spec (.of K))
      ((Scheme.Modules.pullback x).obj (idealModule i)) := by
  let t := x ≫ p
  let b := pullback.fst p t
  let p' := pullback.snd p t
  let i' := fibreInclusion p i t
  have : SmoothOfRelativeDimension 1 p' := MorphismProperty.pullback_snd p t inferInstance
  have : LocallyQuasiFinite (i' ≫ p') := by
    dsimp [i', p']
    rw [fibreInclusion_snd]
    infer_instance
  have : IsLocallyArtinian (pullback (i ≫ p) t) := IsLocallyArtinian.of_locallyQuasiFinite (i' ≫ p')
  have hI' := smoothField_artinian_ideal K p' i'
  have : IsIso (idealPullbackMap i i' b (pullback.fst (i ≫ p) t)
      (fibreInclusion_fst p i t).symm) :=
    flatQuotient_idealPullbackMap_isIso p t p' b i i' _ _
      (IsPullback.of_hasPullback p t) (fibreInclusion_isPullback p i t)
  have hb : IsLocallyRankOne (pullback p t)
      ((Scheme.Modules.pullback b).obj (idealModule i)) :=
    isLocallyRankOne_of_iso _
      (asIso (idealPullbackMap i i' b (pullback.fst (i ≫ p) t)
        (fibreInclusion_fst p i t).symm)).symm hI'
  let j : Spec (.of K) ⟶ pullback p t := pullback.lift x (𝟙 _) (by simp [t])
  have hj : j ≫ b = x := pullback.lift_fst _ _ _
  exact isLocallyRankOne_of_iso _
    (((Scheme.Modules.pullbackComp j b).app (idealModule i)) ≪≫
      (Scheme.Modules.pullbackCongr hj).app (idealModule i))
    (pullback_locallyRankOne j _ hb)

/-- Spectral field fibres of a finite flat divisor's actual ring ideal have
one-dimensional bases. -/
def fieldTensorIdealBasis
    {S : Scheme.{u}} {A B : CommRingCat.{u}}
    (p : Spec A ⟶ S) [SmoothOfRelativeDimension 1 p]
    (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)]
    [LocallyQuasiFinite (Spec.map φ ≫ p)] [Flat (Spec.map φ ≫ p)]
    (K : Type u) [Field K] [Algebra A K] :
    Basis PUnit.{u + 1} K (K ⊗[A] RingHom.ker φ.hom) := by
  let x : Spec (.of K) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have hx := fieldPoint_idealPullback_rankOne p (Spec.map φ) K x
  let I := ModuleCat.of A (RingHom.ker φ.hom)
  let e : (Scheme.Modules.pullback x).obj (idealModule (Spec.map φ)) ≅
      tilde (ModuleCat.of K (K ⊗[A] RingHom.ker φ.hom)) :=
    (Scheme.Modules.pullback x).mapIso (affineIdealIso φ).symm ≪≫
      ((tildePullbackIso (CommRingCat.ofHom (algebraMap A K))).app I) ≪≫
        (tilde.functor (.of K)).mapIso (ModuleCat.extendScalarsAlgebraIso A K I)
  exact basisOfTildeRankOne K _ (isLocallyRankOne_of_iso _ e hx)

/-- A finite spectral divisor ideal is cyclic on a principal neighborhood of
each prime. Its fibre basis is derived from the actual field ideal comparison. -/
theorem exists_away_surjective_idealGenerator
    {S : Scheme.{u}} {A B : CommRingCat.{u}}
    (p : Spec A ⟶ S) [SmoothOfRelativeDimension 1 p]
    (φ : A ⟶ B) [IsClosedImmersion (Spec.map φ)]
    [LocallyQuasiFinite (Spec.map φ ≫ p)] [Flat (Spec.map φ ≫ p)]
    (hfg : (RingHom.ker φ.hom).FG) (P : Ideal A) [P.IsPrime] :
    ∃ s : A, s ∉ P ∧ ∃ a : RingHom.ker φ.hom,
      Function.Surjective (LocalizedModule.map (Submonoid.powers s)
        (LinearMap.toSpanSingleton A (RingHom.ker φ.hom) a)) := by
  let I := RingHom.ker φ.hom
  let Aₚ := Localization.AtPrime P
  let K := IsLocalRing.ResidueField Aₚ
  let M := LocalizedModule P.primeCompl I
  have : Module.Finite A I := Module.Finite.of_fg hfg
  have : Module.Finite Aₚ M := inferInstance
  let b := fieldTensorIdealBasis p φ K
  let e : K ⊗[Aₚ] M ≃ₗ[K] K ⊗[A] I :=
    (AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (LocalizedModule.equivTensorProduct P.primeCompl I)).trans
      (AlgebraTensorModule.cancelBaseChange A Aₚ K K I)
  obtain ⟨f, hf⟩ := _root_.IsLocalRing.exists_surjective_unit_of_residue_basis Aₚ M (b.map e.symm)
  exact _root_.Module.exists_away_surjective_unit_of_localized_surjective_unit A I P f hf

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A principal closed subscheme flat and locally quasi-finite over the base of
a smooth relative curve has regular defining element after every field base change. -/
theorem smoothQuasiFiniteFlat_principal_fieldBaseChange_isSMulRegular
    (R A B K : Type u) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R K]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (hsurj : Function.Surjective (algebraMap A B)) (a : A)
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {a}) :
    IsSMulRegular (K ⊗[R] A) ((1 : K) ⊗ₜ[R] a) := by
  let : Module.Flat R B := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R B))).mp inferInstance)
  let : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A)))) :=
    MorphismProperty.of_isPullback (_root_.AlgebraicGeometry.Scheme.tensorSpecProjection_isPullback
      R A K).flip inferInstance
  let : LocallyQuasiFinite
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))) :=
    MorphismProperty.of_isPullback (_root_.AlgebraicGeometry.Scheme.tensorSpecProjection_isPullback
      R B K).flip inferInstance
  let : IsLocallyArtinian (Spec (.of (K ⊗[R] B))) :=
    IsLocallyArtinian.of_locallyQuasiFinite
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B))))
  let : IsArtinianRing (K ⊗[R] B) := (Scheme.isLocallyArtinianScheme_Spec (R := .of (K ⊗[R] B))).mp
    inferInstance
  exact smoothField_artinian_principalKernel_isSMulRegular K
    (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))))
    (CommRingCat.ofHom (_root_.Algebra.tensorQuotientMap R A B K))
    (Algebra.TensorProduct.map_surjective _ _ (fun x ↦ ⟨x, rfl⟩) hsurj)
    ((1 : K) ⊗ₜ[R] a) (_root_.Algebra.flatQuotient_principal_tensorKernel R A B K hsurj a hker)

/-- Residue-field fibre form, with the actual composite divisor structure map. -/
theorem smoothQuasiFiniteFlat_principal_fibre_isSMulRegular
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (hsurj : Function.Surjective (algebraMap A B)) (a : A)
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {a})
    (P : Ideal R) [P.IsPrime] :
    IsSMulRegular (P.ResidueField ⊗[R] A) ((1 : P.ResidueField) ⊗ₜ[R] a) := by
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact IsScalarTower.algebraMap_apply R A B x
  let : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := hcomp.symm ▸ inferInstance
  let : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    hcomp.symm ▸ inferInstance
  exact smoothQuasiFiniteFlat_principal_fieldBaseChange_isSMulRegular
    R A B P.ResidueField hsurj a hker

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

/-- Conditional interface wiring only: the general fibrewise regularity
criterion is not asserted by this theorem. -/
theorem smoothPrincipalKernel_regular_of_residueCriterion
    (hreg : ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
      [Module.Flat R A] [Algebra.FinitePresentation R A] (a : A),
      (∀ (P : Ideal R) [P.IsPrime],
        IsSMulRegular (P.ResidueField ⊗[R] A) ((1 : P.ResidueField) ⊗ₜ[R] a)) →
        IsSMulRegular A a)
    {R A B : CommRingCat.{u}} (ψ : R ⟶ A) (φ : A ⟶ B)
    [SmoothOfRelativeDimension 1 (Spec.map ψ)] [IsClosedImmersion (Spec.map φ)]
    [LocallyQuasiFinite (Spec.map φ ≫ Spec.map ψ)]
    [Flat (Spec.map φ ≫ Spec.map ψ)] (a : A)
    (hker : RingHom.ker φ.hom = Ideal.span {a}) : IsSMulRegular A a := by
  have : Smooth (Spec.map ψ) := SmoothOfRelativeDimension.smooth 1 _
  have hflat : ψ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hfp := (LocallyOfFinitePresentation.SpecMap_iff ψ).mp inferInstance
  algebraize [ψ.hom, φ.hom, (ψ ≫ φ).hom]
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat R A := hflat
  let : Algebra.FinitePresentation R A := hfp
  exact hreg R A a (fun P _ ↦
    smoothQuasiFiniteFlat_principal_fibre_isSMulRegular R A B
      (IsClosedImmersion.surjective_of_specMap φ) a hker P)

end AlgebraicGeometry.Scheme.Hom
end
