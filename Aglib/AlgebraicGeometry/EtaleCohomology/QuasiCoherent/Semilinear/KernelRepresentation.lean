/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.Semilinear.Tensor
public import Aglib.CategoryTheory.Sites.SheafKernelComponents

/-!
# Representation of the original semilinear categorical kernel

Tensor coordinates evaluate the actual categorical sheaf kernel through its
original inclusion. No fixed-point presheaf or replacement coefficient is
introduced.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (A : CommRingCat.{u}) (F : (Spec A).Modules) [F.IsQuasicoherent]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : moduleSpecΓFunctor.obj F →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA]
    moduleSpecΓFunctor.obj F)
  (B : CommAlgCat.{u} A) [Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/-- The original tensor-section isomorphism with only the native value lift added. -/
def tensorCoefficientAddEquiv :
    B ⊗[A] moduleSpecΓFunctor.obj F ≃+
      (additiveCoefficient (Spec A) F).obj.obj
        (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))) :=
  (specTensorSectionsIso A F B).toLinearEquiv.toAddEquiv.trans AddEquiv.ulift.symm

/-- Fixed tensors are exactly zero values of the original additive coefficient difference. -/
theorem fixed_iff_tensorCoefficient_mem_kernel
    (z : B ⊗[A] moduleSpecΓFunctor.obj F) :
    LinearMap.frobeniusBaseChange p hp hA Φ B z = z ↔
      ((affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F)).hom.app
        (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))).hom
        (tensorCoefficientAddEquiv A F B z) = 0 := by
  have hd := affineFrobenius_sub_id_specTensor A F p hp hA Φ B z
  constructor
  · intro hz
    apply ULift.ext
    exact hd.trans (by rw [hz, sub_self]; exact (specTensorSectionsIso A F B).hom.hom.map_zero)
  · intro hz
    have hv := congrArg ULift.down hz
    have he : (specTensorSectionsIso A F B).hom
        (LinearMap.frobeniusBaseChange p hp hA Φ B z - z) =
        (specTensorSectionsIso A F B).hom 0 :=
      hd.symm.trans (hv.trans (specTensorSectionsIso A F B).hom.hom.map_zero.symm)
    exact sub_eq_zero.mp ((specTensorSectionsIso A F B).toLinearEquiv.injective he)

/-- Fixed tensors are the values of the original categorical kernel on the
actual spectrum test, via its unchanged coefficient inclusion. -/
def affineFrobeniusKernelTensorEquiv :
    {z : B ⊗[A] moduleSpecΓFunctor.obj F //
      LinearMap.frobeniusBaseChange p hp hA Φ B z = z} ≃
    (kernel (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))).obj.obj
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))) :=
  (Equiv.subtypeEquiv (tensorCoefficientAddEquiv A F B).toEquiv
      (fixed_iff_tensorCoefficient_mem_kernel A F p hp hA Φ B)).trans
    (Sheaf.kernelComponentEquiv
      (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))).symm.toEquiv

/-- The forward equivalence is the original section tensor comparison under
the original categorical kernel inclusion. -/
theorem affineFrobeniusKernelTensorEquiv_ι
    (z : {z : B ⊗[A] moduleSpecΓFunctor.obj F //
      LinearMap.frobeniusBaseChange p hp hA Φ B z = z}) :
    (kernel.ι (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))).hom.app
        (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
        (affineFrobeniusKernelTensorEquiv A F p hp hA Φ B z) =
      ULift.up ((tensorSectionsAddHom A F B) z.val) :=
  Sheaf.kernelComponentEquiv_symm_ι _ _ _

/-- The original categorical kernel comparison reads the same forward tensor value. -/
theorem affineFrobeniusKernelTensorEquiv_component_val
    (z : {z : B ⊗[A] moduleSpecΓFunctor.obj F //
      LinearMap.frobeniusBaseChange p hp hA Φ B z = z}) :
    (Sheaf.kernelComponentEquiv
      (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))
      (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
      (affineFrobeniusKernelTensorEquiv A F p hp hA Φ B z)).val =
        tensorCoefficientAddEquiv A F B z.val :=
  congrArg Subtype.val (AddEquiv.apply_symm_apply _ _)

/-- The actual lifted coefficient restriction preserves the entire tensor map. -/
theorem tensorCoefficientAddEquiv_naturality (C : CommAlgCat.{u} A)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A C)))] (f : B ⟶ C)
    (z : B ⊗[A] moduleSpecΓFunctor.obj F) :
    let q : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C))) ⟶
        Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
      MorphismProperty.Over.homMk ((algSpec A).map f.op).left ((algSpec A).map f.op).w
    (additiveCoefficient (Spec A) F).obj.map q.op (tensorCoefficientAddEquiv A F B z) =
      tensorCoefficientAddEquiv A F C
        (f.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F) z) := by
  intro q
  apply ULift.ext
  exact (DFunLike.congr_fun (tensorSectionsAddHom_naturality A F f) z).symm

/-- Original kernel restriction agrees with the actual tensor map. The two
fixed points are supplied with their actual tensor equality, as in algebraic
representability naturality; no new fixed-point functor is introduced. -/
theorem affineFrobeniusKernelTensorEquiv_naturality (C : CommAlgCat.{u} A)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A C)))] (f : B ⟶ C)
    (z : {z : B ⊗[A] moduleSpecΓFunctor.obj F //
      LinearMap.frobeniusBaseChange p hp hA Φ B z = z})
    (w : {w : C ⊗[A] moduleSpecΓFunctor.obj F //
      LinearMap.frobeniusBaseChange p hp hA Φ C w = w})
    (hw : w.val = f.hom.toLinearMap.rTensor (moduleSpecΓFunctor.obj F) z.val) :
    let q : Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C))) ⟶
        Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
      MorphismProperty.Over.homMk ((algSpec A).map f.op).left ((algSpec A).map f.op).w
    (kernel (affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F))).obj.map
        q.op (affineFrobeniusKernelTensorEquiv A F p hp hA Φ B z) =
      affineFrobeniusKernelTensorEquiv A F p hp hA Φ C w := by
  intro q
  let δ := affineFrobenius A F p hp hA Φ - 𝟙 (additiveCoefficient (Spec A) F)
  apply (Sheaf.kernelComponentEquiv δ
    (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A C)))))).injective
  apply Subtype.ext
  rw [Sheaf.kernelComponentEquiv_naturality,
    affineFrobeniusKernelTensorEquiv_component_val,
    affineFrobeniusKernelTensorEquiv_component_val]
  exact (tensorCoefficientAddEquiv_naturality A F B C f z.val).trans
    (congrArg (tensorCoefficientAddEquiv A F C) hw.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
