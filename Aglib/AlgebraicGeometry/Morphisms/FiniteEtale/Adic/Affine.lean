/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.AdicCompletion
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine tensor fibres and closed-fibre morphism lifting
-/

@[expose] public section


noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic
universe u
variable (R T B : Type u) [CommRing R] [CommRing T] [CommRing B]
  [Algebra R T] [Algebra R B]

/-- Actual affine scheme fibre identified with the scalar-extension tensor algebra. -/
def fibreIso :
    pullback (Spec.algebraMap R B) (Spec.algebraMap R T) ≅ Spec (.of (T ⊗[R] B)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso R T B

@[reassoc (attr := simp)] theorem fibreIso_inv_base :
    (fibreIso R T B).inv ≫ pullback.snd _ _ = Spec.algebraMap T (T ⊗[R] B) := by
  dsimp only [fibreIso, Iso.trans_inv]
  rw [Category.assoc, pullbackSymmetry_inv_comp_snd, pullbackSpecIso_inv_fst']

@[reassoc (attr := simp)] theorem fibreIso_inv_fst :
    (fibreIso R T B).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom) := by
  dsimp only [fibreIso, Iso.trans_inv]
  rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd]
  simp only [AlgHom.toRingHom_eq_coe]

@[reassoc (attr := simp)] theorem fibreIso_hom_base :
    (fibreIso R T B).hom ≫ Spec.algebraMap T (T ⊗[R] B) = pullback.snd _ _ := by
  rw [← fibreIso_inv_base, Iso.hom_inv_id_assoc]

variable {R T B} {A : Type u} [CommRing A] [Algebra R A]

/-- The actual pullback morphism attached to an algebra map. -/
def fibreMap (g : A →ₐ[R] B) :
    pullback (Spec.algebraMap R B) (Spec.algebraMap R T) ⟶
      pullback (Spec.algebraMap R A) (Spec.algebraMap R T) :=
  pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (pullback.snd _ _) (by
      rw [Category.assoc, Spec.map_algHom_algebraMap]
      exact pullback.condition)

@[reassoc (attr := simp)] theorem fibreMap_fst (g : A →ₐ[R] B) :
    fibreMap (T := T) g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  simp [fibreMap]

@[reassoc (attr := simp)] theorem fibreMap_snd (g : A →ₐ[R] B) :
    fibreMap (T := T) g ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [fibreMap]

/-- Affine pullback really acts by tensor base change on algebra maps. -/
theorem fibreIso_inv_fibreMap (g : A →ₐ[R] B) :
    (fibreIso R T B).inv ≫ fibreMap (T := T) g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id T T) g).toRingHom) ≫
          (fibreIso R T A).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreMap_fst, fibreIso_inv_fst_assoc, fibreIso_inv_fst]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · simp only [Category.assoc, fibreMap_snd, fibreIso_inv_base]
    exact (Spec.map_algHom_algebraMap (Algebra.TensorProduct.map (AlgHom.id T T) g)).symm


variable [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
  [Module.Finite R B] [Algebra.FormallySmooth R A]

/-- A morphism of the actual closed affine fibres lifts over the complete base. -/
theorem affine_fibre_hom_lift
    (φ : pullback (Spec.algebraMap R B) (Spec.algebraMap R (R ⧸ I)) ⟶
      pullback (Spec.algebraMap R A) (Spec.algebraMap R (R ⧸ I)))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ g : A →ₐ[R] B, fibreMap (T := R ⧸ I) g = φ := by
  let ψ := (fibreIso R (R ⧸ I) B).inv ≫ φ ≫ (fibreIso R (R ⧸ I) A).hom
  have hψ : ψ ≫ Spec.algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] A) =
      Spec.algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] B) := by
    simp only [ψ, Category.assoc, fibreIso_hom_base, hφ, fibreIso_inv_base]
  let f : (R ⧸ I) ⊗[R] A →ₐ[R ⧸ I] (R ⧸ I) ⊗[R] B :=
    Spec.homEquivAlgHom ⟨ψ, hψ⟩
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = ψ := by
    exact congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨ψ, hψ⟩)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.tensorProduct_map_surjective_of_finite R I f
  dsimp only at hg
  refine ⟨g, ?_⟩
  apply (cancel_epi (fibreIso R (R ⧸ I) B).inv).mp
  rw [fibreIso_inv_fibreMap, hg, hf]
  simp [ψ]

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/Adic/Affine.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 1bbf7b246c59ebda332cbf3b1fa4588d2124e433d43943cc8354b81a01303c63.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
