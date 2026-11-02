/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.Affine

/-!
# The original Frobenius square on all section tensors

The additive component is the original coefficient endomorphism, with only its
value-universe lift removed. Its whole tensor square extends the pure-tensor
formula without introducing another section module or sheaf.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
    moduleSpecΓFunctor.obj F)
  (B : CommAlgCat.{u} A) [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/-- Remove only the original value lift from the original additive component. -/
def affineFrobeniusSectionsAddHom :
    Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F, ⊤) →+
      Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F, ⊤) :=
  AddEquiv.ulift.toAddMonoidHom.comp
    (((affineFrobenius A F p hp hA Φ).hom.app
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))).hom.comp
      AddEquiv.ulift.symm.toAddMonoidHom)

/-- The complete original additive tensor square, before evaluating any section. -/
theorem affineFrobeniusSectionsAddHom_tensor :
    (affineFrobeniusSectionsAddHom A F p hp hA Φ B).comp
        (tensorSectionsAddHom A F B) =
      (tensorSectionsAddHom A F B).comp
        (LinearMap.frobeniusBaseChange p hp hA Φ B).toAddMonoidHom := by
  apply TensorProduct.addHom_ext
  intro r m
  exact affineFrobenius_specTensor A F p hp hA Φ B r m

/-- Every original tensor section satisfies the same Frobenius formula. -/
theorem affineFrobenius_specTensor_apply (z : B ⊗[A] moduleSpecΓFunctor.obj F) :
    @Eq Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F, ⊤)
      (((affineFrobenius A F p hp hA Φ).hom.app
        (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
        (ULift.up ((specTensorSectionsIso A F B).hom z))).down)
      ((specTensorSectionsIso A F B).hom
        (LinearMap.frobeniusBaseChange p hp hA Φ B z)) :=
  DFunLike.congr_fun (affineFrobeniusSectionsAddHom_tensor A F p hp hA Φ B) z

/-- Subtraction is preserved on the original section module as well as on tensors. -/
theorem affineFrobenius_sub_id_specTensor (z : B ⊗[A] moduleSpecΓFunctor.obj F) :
    @Eq Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F, ⊤)
      ((((affineFrobenius A F p hp hA Φ) - 𝟙 _).hom.app
        (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
        (ULift.up ((specTensorSectionsIso A F B).hom z))).down)
      ((specTensorSectionsIso A F B).hom
        (LinearMap.frobeniusBaseChange p hp hA Φ B z - z)) := by
  have h := affineFrobenius_specTensor_apply A F p hp hA Φ B z
  have hs := (tensorSectionsAddHom A F B).map_sub
    (LinearMap.frobeniusBaseChange p hp hA Φ B z) z
  exact (congrArg (fun s => s - (tensorSectionsAddHom A F B) z) h).trans hs.symm

omit [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))] in
/-- An inhomogeneous solution on the original tensors is a solution on the
original sections, with restriction along the same algebra morphism. -/
theorem affineFrobenius_solution_specTensor (C : CommAlgCat.{u} A)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A C)))] (f : B ⟶ C)
    (y : B ⊗[A] moduleSpecΓFunctor.obj F) (z : C ⊗[A] moduleSpecΓFunctor.obj F)
    (hz : LinearMap.frobeniusBaseChange p hp hA Φ C z - z =
      f.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F) y) :
    @Eq Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj F, ⊤)
      (affineFrobeniusSectionsAddHom A F p hp hA Φ C
        ((tensorSectionsAddHom A F C) z) - (tensorSectionsAddHom A F C) z)
      (sectionsAddHom (Spec A) F ((algSpec A).map f.op)
        ((tensorSectionsAddHom A F B) y)) := by
  have hΦ := DFunLike.congr_fun
    (affineFrobeniusSectionsAddHom_tensor A F p hp hA Φ C) z
  have hsub := (tensorSectionsAddHom A F C).map_sub
    (LinearMap.frobeniusBaseChange p hp hA Φ C z) z
  have hroot := congrArg (tensorSectionsAddHom A F C) hz
  have hres := DFunLike.congr_fun (tensorSectionsAddHom_naturality A F f) y
  exact (congrArg (fun t => t - (tensorSectionsAddHom A F C) z) hΦ).trans
    (hsub.symm.trans (hroot.trans hres))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
