/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Global sections of proper geometrically integral field schemes

The actual constants map factors the structure morphism through the actual
affinization. Properness makes that map integral. Flat field base change
preserves scheme-theoretic dominance, so the affinization is geometrically
integral. Tensoring its actual ring with an algebraic closure gives the field;
the resulting one-dimensional scalar map is bijective over the original field.

All dimensions and fields, the original universe and the actual canonical
constants map are retained. No cohomology-finiteness or cohomological base-change
family is assumed. The final linear argument is the original Gamma argument
with its redundant H0 transport omitted.

Source: `R5Lab/AlgebraicGeometry/Curves/Genus/ProperConstants.lean` at frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `4d933d594f9d8c8c0435b74ee6c41ee98ecd94af518e24a5213afff7affa6d08`.
Only the direct proof at source lines 152–250 is extracted. The older general
H0/cohomological alternatives remain separately inventoried for their consumers.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.Scheme.OverField (FScheme)
namespace AlgebraicGeometry.Scheme
universe u
variable {F : Type u} [Field F]

theorem structureMap_factorsThroughAffinization (X : FScheme F) :
    X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (constants X)) = X.hom := by
  change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of F)).inv ≫ X.hom.appTop) = X.hom
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Properness alone makes the actual structural constants ring homomorphism integral.
The proof uses proper surjective affinization, without coherent-cohomology finiteness. -/
theorem constants_isIntegral_of_proper (X : FScheme F) [IsProper X.hom] :
    (constants X).IsIntegral := by
  let g := Spec.map (CommRingCat.ofHom (constants X))
  have hfac : X.left.toSpecΓ ≫ g = X.hom := structureMap_factorsThroughAffinization X
  let : IsProper (X.left.toSpecΓ ≫ g) := hfac.symm ▸ inferInstance
  let : IsProper X.left.toSpecΓ := IsProper.of_comp X.left.toSpecΓ g
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : Surjective X.left.toSpecΓ := inferInstance
  have hgc : UniversallyClosed g := UniversallyClosed.of_comp_surjective X.left.toSpecΓ g
  have hgi : IsIntegralHom g := IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨hgc, inferInstance⟩
  exact IsIntegralHom.SpecMap_iff.mp hgi

/-- Over an algebraically closed field, proper integral schemes have exactly the
structural constants, with no coherent-cohomology family premise. -/
theorem constants_bijective_of_proper_of_isAlgClosed [IsAlgClosed F]
    (X : FScheme F) [IsProper X.hom] [IsIntegral X.left] :
    Function.Bijective (constants X) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral (constants X) (constants_isIntegral_of_proper X)

/-- A proper geometrically integral field scheme has geometrically integral
affinization. Flat field base change preserves scheme-theoretic dominance; reducedness
and irreducibility then descend from each actual integral geometric fibre. -/
theorem affinization_geometricallyIntegral (X : FScheme F)
    [IsProper X.hom] [GeometricallyIntegral X.hom] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (constants X))) := by
  let g := Spec.map (CommRingCat.ofHom (constants X))
  have hfac : X.left.toSpecΓ ≫ g = X.hom := structureMap_factorsThroughAffinization X
  let : IsProper (X.left.toSpecΓ ≫ g) := hfac.symm ▸ inferInstance
  let : IsProper X.left.toSpecΓ := IsProper.of_comp X.left.toSpecΓ g
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : Surjective X.left.toSpecΓ := inferInstance
  let : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  let : IsSchemeTheoreticallyDominant X.left.toSpecΓ :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  refine ⟨?_⟩
  intro K _ s T fst snd hT
  let U := pullback X.left.toSpecΓ fst
  let a : U ⟶ X.left := pullback.fst _ _
  let b : U ⟶ T := pullback.snd _ _
  let : Flat fst := MorphismProperty.of_isPullback hT.flip (inferInstance : Flat s)
  let : IsSchemeTheoreticallyDominant b := inferInstanceAs
    (IsSchemeTheoreticallyDominant (pullback.snd X.left.toSpecΓ fst))
  let : QuasiCompact b := inferInstanceAs (QuasiCompact (pullback.snd X.left.toSpecΓ fst))
  have hpaste : IsPullback a (b ≫ snd) X.hom s := by
    have hpaste' : IsPullback a (b ≫ snd) (X.left.toSpecΓ ≫ g) s :=
      (IsPullback.of_hasPullback X.left.toSpecΓ fst).paste_vert hT
    rwa [hfac] at hpaste'
  let : IsIntegral U := GeometricallyIntegral.geometrically_isIntegral (f := X.hom)
    s a (b ≫ snd) hpaste
  let : IsReduced T := IsSchemeTheoreticallyDominant.isReduced b
  have hb : Function.Surjective b := Scheme.Hom.surjective b
  let : IrreducibleSpace T := hb.irreducibleSpace b.continuous
  exact (isIntegral_iff_irreducibleSpace_and_isReduced (X := T)).mpr ⟨inferInstance, inferInstance⟩

/-- The actual constants map of every proper geometrically integral field scheme is
bijective. The proof uses integral geometric affinization and algebraic-closure tensor
dimension, without proper-cohomology finiteness or cohomological base change. -/
theorem constants_bijective_of_proper_geometricallyIntegral (X : FScheme F)
    [IsProper X.hom] [GeometricallyIntegral X.hom] :
    Function.Bijective (constants X) := by
  let A := Γ(X.left, ⊤)
  let : Algebra F A := (constants X).toAlgebra
  let K := AlgebraicClosure F
  let g := Spec.map (CommRingCat.ofHom (algebraMap F A))
  let s := Spec.map (CommRingCat.ofHom (algebraMap F K))
  let : IsIntegralHom g := IsIntegralHom.SpecMap_iff.mpr (constants_isIntegral_of_proper X)
  let : GeometricallyIntegral g := affinization_geometricallyIntegral X
  let : GeometricallyIntegral (pullback.fst s g) := inferInstance
  let : IsIntegral (pullback s g) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst s g)
  let : IsIntegral (Spec (.of (K ⊗[F] A))) :=
    IsIntegral.of_isIso (pullbackSpecIso F K A).hom
  let : IsDomain (K ⊗[F] A) := (affine_isIntegral_iff (.of (K ⊗[F] A))).mp inferInstance
  have hti : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[F] A)))) := by
    rw [← pullbackSpecIso_inv_fst' F K A]
    infer_instance
  have hbij : Function.Bijective (algebraMap K (K ⊗[F] A)) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral _ (IsIntegralHom.SpecMap_iff.mp hti)
  let e := LinearEquiv.ofBijective (Algebra.linearMap K (K ⊗[F] A)) hbij
  have hdimA : Module.finrank F A = 1 := by
    calc
      Module.finrank F A = Module.finrank K (K ⊗[F] A) :=
        (Module.finrank_baseChange (R := K) (S := F)).symm
      _ = Module.finrank K K := e.finrank_eq.symm
      _ = 1 := Module.finrank_self K
  let : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  let : Module.Finite F A := Module.finite_of_finrank_eq_succ hdimA
  have hinj : Function.Injective (Algebra.linearMap F A) := RingHom.injective (constants X)
  refine ⟨RingHom.injective (constants X), ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdimA.symm) (f := Algebra.linearMap F A)).mp hinj

end AlgebraicGeometry.Scheme
