/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineEffectiveDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedRestriction
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Aglib.RingTheory.Descent.Basic

/-! Extract algebra descent data from an actual locally represented set sheaf. -/

@[expose] public section

open _root_.Algebra.Descent (Datum counit)

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open TensorProduct
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.AffineSheafAlgebraDatum

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Etale R S]

/-- The affine chart map `Spec S ⟶ Spec R` induced by the algebra structure. -/
def chart : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))

instance chart_etale : Etale (chart R S) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)

variable {R S}

/-- The etale test object `Spec A` over `Spec S` supplied by the etale `S`-algebra structure. -/
def test (S A : Type u) [CommRing S] [CommRing A] [Algebra S A] [Algebra.Etale S A] :
    (Spec (.of S)).Etale := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap S A))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)
  exact Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap S A)))

section Sections
variable (F : Scheme.EtaleCohomology.SetSheaf (Spec (.of R)))
variable (A A' A'' : Type u) [CommRing A] [CommRing A'] [CommRing A'']
variable [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra.Etale S A]
variable [Algebra R A'] [Algebra S A'] [IsScalarTower R S A'] [Algebra.Etale S A']
variable [Algebra R A''] [Algebra S A''] [IsScalarTower R S A''] [Algebra.Etale S A'']

/-- The sections of `F` on the affine test scheme `Spec A`, viewed over `Spec R` through the
chart. -/
abbrev sections : Type (u + 1) :=
  F.obj.obj (op ((Scheme.EtaleCohomology.siteEtalePostcompose (chart R S)).obj (test S A)))

variable {A A' A''}

/-- An R-algebra map induces a map of the affine test schemes over Spec R,
even when it does not respect their chosen S-algebra structures. -/
def testMap (φ : A →ₐ[R] A') :
    (Scheme.EtaleCohomology.siteEtalePostcompose (chart R S)).obj (test S A') ⟶
      (Scheme.EtaleCohomology.siteEtalePostcompose (chart R S)).obj (test S A) :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ chart R S) =
        Spec.map (CommRingCat.ofHom (algebraMap S A')) ≫ chart R S
    simp only [chart, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    change φ.toRingHom.comp ((algebraMap S A).comp (algebraMap R S)) =
      (algebraMap S A').comp (algebraMap R S)
    rw [← IsScalarTower.algebraMap_eq R S A, ← IsScalarTower.algebraMap_eq R S A']
    exact φ.comp_algebraMap) (by trivial)

/-- The restriction map on test-scheme sections given by pullback along the spectrum map of `φ`. -/
def map (φ : A →ₐ[R] A') : sections (S := S) F A → sections (S := S) F A' :=
  F.obj.map (testMap (S := S) φ).op

lemma testMap_id : testMap (S := S) (AlgHom.id R A) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
  exact Spec.map_id _

lemma testMap_comp (φ : A →ₐ[R] A') (ψ : A' →ₐ[R] A'') :
    testMap (S := S) (ψ.comp φ) = testMap (S := S) ψ ≫ testMap (S := S) φ := by
  apply MorphismProperty.Over.Hom.ext
  exact Spec.map_comp (CommRingCat.ofHom φ.toRingHom) (CommRingCat.ofHom ψ.toRingHom)

@[simp] lemma map_id (s : sections (S := S) F A) : map F (AlgHom.id R A) s = s := by
  simp [map, testMap_id]

lemma map_comp (φ : A →ₐ[R] A') (ψ : A' →ₐ[R] A'') (s : sections (S := S) F A) :
    map F (ψ.comp φ) s = map F ψ (map F φ s) := by
  simp [map, testMap_comp]

end Sections

section AlgebraHom
variable (K B A A' : Type u) [CommRing K] [CommRing B] [CommRing A] [CommRing A']
variable [Algebra K B] [Algebra K A] [Algebra K A']

/-- Full faithfulness of the actual affine Spec functor, in algebra-map form. -/
def algHomOverEquiv : (B →ₐ[K] A) ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))) :=
  (ConcreteCategory.homEquiv (C := CommAlgCat K)
    (X := CommAlgCat.of K B) (Y := CommAlgCat.of K A)).symm.trans
    ((opEquiv (op (CommAlgCat.of K A)) (op (CommAlgCat.of K B))).symm.trans
      (algSpec.fullyFaithful (R := .of K)).homEquiv)

@[simp] lemma algHomOverEquiv_left (φ : B →ₐ[K] A) :
    (algHomOverEquiv K B A φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

lemma algHomOverEquiv_comp (φ : B →ₐ[K] A) (ψ : A →ₐ[K] A') :
    algHomOverEquiv K B A' (ψ.comp φ) =
      algHomOverEquiv K A A' ψ ≫ algHomOverEquiv K B A φ := by
  apply Over.OverMorphism.ext
  exact Spec.map_comp (CommRingCat.ofHom φ.toRingHom) (CommRingCat.ofHom ψ.toRingHom)

end AlgebraHom

section Representation
variable (F : Scheme.EtaleCohomology.SetSheaf (Spec (.of R)))
variable (B A A' : Type u) [CommRing B] [CommRing A] [CommRing A']
variable [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Module.Finite S B] [Algebra.Etale S B]
variable [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra.Etale S A]
variable [Algebra R A'] [Algebra S A'] [IsScalarTower R S A'] [Algebra.Etale S A']
variable (e : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.specCover S B) ≅
  (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).obj F)

/-- The local sheaf representative gives an equivalence on every etale affine
S-algebra test object. -/
def representationEquiv : (B →ₐ[S] A) ≃ sections (S := S) F A :=
  ((algHomOverEquiv S B A).trans Equiv.ulift.symm).trans
    (((sheafToPresheaf _ _).mapIso e).app (op (test S A))).toEquiv

variable {A A'}

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
lemma representationEquiv_naturality (φ : B →ₐ[S] A) (ψ : A →ₐ[S] A') :
    representationEquiv F B A' e (ψ.comp φ) =
      map F (ψ.restrictScalars R) (representationEquiv F B A e φ) := by
  let k := algHomOverEquiv S A A' ψ
  let α : test S A' ⟶ test S A :=
    MorphismProperty.Over.homMk k.left (Over.w k) (by trivial)
  have h := congrArg (fun q => q (ULift.up (algHomOverEquiv S B A φ)))
    (e.hom.hom.naturality α.op)
  change e.hom.hom.app (op (test S A'))
    (ULift.up (algHomOverEquiv S B A' (ψ.comp φ))) =
      map F (ψ.restrictScalars R)
        (e.hom.hom.app (op (test S A)) (ULift.up (algHomOverEquiv S B A φ)))
  rw [algHomOverEquiv_comp]
  exact h

end Representation

section Coaction
variable (F : Scheme.EtaleCohomology.SetSheaf (Spec (.of R)))
variable (B : Type u) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Module.Finite S B] [Algebra.Etale S B]
variable (e : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.specCover S B) ≅
  (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).obj F)

local instance etaleTensor : Algebra.Etale S (S ⊗[R] B) := by
  have : Algebra.Etale R B := Algebra.Etale.comp R S B
  infer_instance

/-- The section of `F` corresponding to the identity of the representing `S`-algebra `B` under
`e`. -/
def identitySection : sections (S := S) F B :=
  representationEquiv F B B e (AlgHom.id S B)

/-- The coaction is recovered from the restriction of the identity section
along the second tensor embedding, using the actual local representing iso. -/
def coaction : B →ₐ[S] S ⊗[R] B :=
  (representationEquiv F B (S ⊗[R] B) e).symm
    (map F (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)
      (identitySection F B e))

lemma representationEquiv_coaction :
    representationEquiv F B (S ⊗[R] B) e (coaction F B e) =
      map F (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)
        (identitySection F B e) :=
  Equiv.apply_symm_apply _ _

lemma representationEquiv_eq {A : Type u} [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Algebra.Etale S A] (φ : B →ₐ[S] A) :
    representationEquiv F B A e φ =
      map F (φ.restrictScalars R) (identitySection F B e) := by
  simpa [identitySection] using
    representationEquiv_naturality F B e (AlgHom.id S B) φ

lemma coaction_counit : (counit R S B).comp (coaction F B e) = AlgHom.id S B := by
  apply (representationEquiv F B B e).injective
  rw [representationEquiv_naturality, representationEquiv_coaction]
  rw [← map_comp]
  have h : ((counit R S B).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) = AlgHom.id R B := by
    ext b
    simp
  rw [h, map_id]
  rfl

lemma coaction_coassoc :
    (Algebra.TensorProduct.map (AlgHom.id S S)
      ((coaction F B e).restrictScalars R)).comp (coaction F B e) =
    (Algebra.TensorProduct.map (AlgHom.id S S)
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)).comp (coaction F B e) := by
  apply (representationEquiv F B (S ⊗[R] (S ⊗[R] B)) e).injective
  rw [representationEquiv_naturality, representationEquiv_naturality]
  simp only [representationEquiv_coaction]
  rw [← map_comp, ← map_comp]
  have h₁ : ((Algebra.TensorProduct.map (AlgHom.id S S)
      ((coaction F B e).restrictScalars R)).restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) =
      (Algebra.TensorProduct.includeRight : S ⊗[R] B →ₐ[R] S ⊗[R] (S ⊗[R] B)).comp
        ((coaction F B e).restrictScalars R) := by ext b; simp
  have h₂ : ((Algebra.TensorProduct.map (AlgHom.id S S)
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)).restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) =
      (Algebra.TensorProduct.includeRight : S ⊗[R] B →ₐ[R] S ⊗[R] (S ⊗[R] B)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) := by ext b; simp
  rw [h₁, h₂, map_comp, map_comp]
  congr 1
  exact (representationEquiv_eq F B e (coaction F B e)).symm.trans
    (representationEquiv_coaction F B e)

/-- An actual local sheaf representation produces the full algebra descent
datum, with both laws proved rather than supplied as additional inputs. -/
def datum : Datum R S B where
  coaction := coaction F B e
  counit_coaction := coaction_counit F B e
  coassoc := coaction_coassoc F B e

end Coaction

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.AffineSheafAlgebraDatum

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 0efd4ae5193bd1293fea485f19c8afbdb84448cf93a6e6cc1e0cba9ce848c477.
Definitions, hypotheses and universes are retained modulo native names. -/
