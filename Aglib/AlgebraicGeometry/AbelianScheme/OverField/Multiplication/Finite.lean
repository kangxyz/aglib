/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Symmetric
public import Aglib.AlgebraicGeometry.Group.Multiplication.FiniteKernel
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Ample
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Proper

/-!
# Positive multiplication has finite native kernel

Symmetrization of an actual projective ample line bundle, followed by the
original square-exponent pullback law, makes a positive tensor power ample
and trivial on the existing native multiplication kernel. That kernel is
proper, hence finite. No invertibility or smoothness assumption is needed.

The resulting finite point fibres give finite multiplication after extension
to the algebraic closure. Descent gives finiteness over the original field;
the fixed identity gives surjectivity. Generic flatness and group translations
then supply flatness in every characteristic.
The numerical locally free rank is a separate Hilbert-polynomial obligation.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- Projectivity supplies a symmetric ample line bundle on the same group
scheme. The bundle is the tensor product of one ample bundle with its
pullback along the original inversion morphism. -/
theorem exists_symmetric_isAmple (G : Over (Spec (.of k))) [GrpObj G]
    [IsHProjective G.hom] :
    ∃ L : LineBundle G.left, L.IsAmple ∧
      pullbackClass ((𝟙 G)⁻¹).left (classOf G.left L) = classOf G.left L := by
  let : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  let j : G ⟶ G := (𝟙 G)⁻¹
  have hj : j ≫ j = 𝟙 G := by
    simp only [j, GrpObj.comp_inv, Category.comp_id, inv_inv]
  let : IsIso j := by
    change IsIso ((𝟙 G)⁻¹)
    rw [← GrpObj.inv_eq_inv]
    infer_instance
  let : IsIso j.left := (Over.forget (Spec (.of k))).map_isIso j
  obtain ⟨L, hL⟩ := IsHProjective.exists_isAmple G.hom
  let N := tensorLineBundle G.left L (pullbackLineBundle j.left L)
  have hN : N.IsAmple := hL.tensor (hL.pullback_of_isAffineHom j.left)
  refine ⟨N, hN, ?_⟩
  have hinv : pullbackClass j.left (pullbackClass j.left (classOf G.left L)) =
      classOf G.left L := by
    rw [← pullbackClass_comp, ← Over.comp_left, hj, Over.id_left, pullbackClass_id]
  change pullbackClass j.left (classOf G.left N) = classOf G.left N
  simp only [N, classOf_tensor, ← pullbackClass_classOf, pullbackClass_add]
  rw [hinv, add_comm]

/-- At every positive level the existing scheme-theoretic multiplication
kernel is finite over the original field, including inseparable levels. -/
theorem kernelGroup_isFinite_of_pos
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom]
    (n : ℕ) (hn : 0 < n) : IsFinite (MultiplicationKernel.kernelGroup G n).X.hom := by
  let K := MultiplicationKernel.kernelGroup G n
  let i := (Kernel.inclusion (MultiplicationKernel.multiplicationHom G n)).hom.hom
  let : IsClosedImmersion η[G.X].left :=
    isClosedImmersion_of_comp_eq_id G.X.hom η[G.X].left (Over.w _)
  let : IsClosedImmersion i.left :=
    MorphismProperty.of_isPullback (MultiplicationKernel.kernelSquare G n).flip inferInstance
  let : IsProper K.X.hom := by
    rw [← Over.w i]
    infer_instance
  let : G.X.left.IsSeparated := ⟨by rw [← terminal.comp_from G.X.hom]; infer_instance⟩
  obtain ⟨L, hL, hsym⟩ := exists_symmetric_isAmple G.X
  let M := tensorPowerLineBundle G.X.left L (n ^ 2)
  have hM : M.IsAmple := hL.tensorPower (n ^ 2) (pow_pos hn 2)
  have hpower : pullbackClass ((𝟙 G.X) ^ n).left (classOf G.X.left L) =
      classOf G.X.left M := by
    change pullbackClass ((𝟙 G.X) ^ n).left (classOf G.X.left L) =
      classOf G.X.left (tensorPowerLineBundle G.X.left L (n ^ 2))
    rw [classOf_tensorPower]
    exact LineBundleCube.pullbackClass_multiplication_of_symmetric G.X _ hsym n
  have hconst : i ≫ (𝟙 G.X) ^ n = 1 := by
    have h : (Kernel.inclusion (MultiplicationKernel.multiplicationHom G n)).hom.hom ≫
        (MultiplicationKernel.multiplicationHom G n).hom.hom = 1 :=
      (Kernel.square (MultiplicationKernel.multiplicationHom G n)).w
    simpa only [i, MultiplicationKernel.multiplicationHom_hom,
      MultiplicationKernel.multiplication] using h
  have hzero : classOf K.X.left (pullbackLineBundle i.left M) = 0 := by
    rw [← pullbackClass_classOf, ← hpower, ← pullbackClass_comp, ← Over.comp_left, hconst]
    exact LineBundleCube.pullbackClass_one _
  exact (hM.pullback_of_isAffineHom i.left).isFinite_of_isProper_of_classOf_eq_zero K.X.hom hzero

/-- Actual multiplication by every positive integer is finite, flat, and
surjective over every field. Its locally free rank is a separate theorem. -/
theorem multiplication_finite_flat_surjective_of_isHProjective
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left := by
  let : IsFinite (MultiplicationKernel.kernelGroup G n).X.hom := kernelGroup_isFinite_of_pos G n hn
  exact multiplication_finite_flat_surjective_of_finite_kernelGroup G n

end AlgebraicGeometry.Scheme.Group.Multiplication
