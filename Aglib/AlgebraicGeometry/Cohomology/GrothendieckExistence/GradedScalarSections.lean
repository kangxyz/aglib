/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedStageIndependence
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections

/-! # Original finite-stage section lifts of homogeneous scalar multiplication -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The original common-stage layer of a graded section is represented by
any actual lift to that finite stage. No surjectivity on arbitrary open
sections is asserted. -/
theorem gradedPieceCommonStageIso_inv_section {n m : ℕ} (h : n + 1 ≤ m)
    (U : X.Opens) (x : Γ(F.obj.obj (op m), U)) (y : Γ(F.gradedPiece n, U))
    (hy : (kernel.ι (F.transition n)).app U y = (F.obj.map (homOfLE h).op).app U x) :
    (kernel.ι (idealQuotientMap X (idealThickeningBaseScalar f)
      (F.obj.obj (op m)) (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n))).app U
      ((gradedPieceCommonStageIso f I F h).inv.app U y) =
    (idealQuotientπ X (idealThickeningBaseScalar f) (F.obj.obj (op m)) (I ^ (n + 1))).app U x := by
  let e := gradedPieceCommonStageIso f I F h
  let b := baseIdealReductionIso f I F h
  apply moduleHom_app_injective b.hom U
  have he := congrArg (fun k => k.app U (e.inv.app U y))
    (gradedPieceCommonStageIso_hom_ι f I F h)
  have hei : e.hom.app U (e.inv.app U y) = y :=
    congrArg (fun k => k.app U y) e.inv_hom_id
  change (kernel.ι (F.transition n)).app U (e.hom.app U (e.inv.app U y)) = _ at he
  rw [hei] at he
  have hb := congrArg (fun k => k.app U x)
    (idealQuotientπ_baseIdealReductionIso_hom f I F h)
  exact he.symm.trans (hy.trans hb.symm)

/-- Multiplying an original finite-stage lift computes the original formal
homogeneous action. This keeps the original coefficient reduction map and
original scalar endomorphism, rather than a chosen quotient-module model. -/
theorem formalGradedScalarMap_section_lift (r n m : ℕ) (h : r + n + 1 ≤ m)
    (a : ↥(I ^ r)) (U : X.Opens) (x : Γ(F.obj.obj (op m), U))
    (y : Γ(F.gradedPiece n, U))
    (hy : (kernel.ι (F.transition n)).app U y =
      (F.obj.map (homOfLE ((Nat.add_le_add_right (Nat.le_add_left n r) 1).trans h)).op).app U x) :
    (kernel.ι (F.transition (r + n))).app U ((formalGradedScalarMap f I F r n a).app U y) =
      (F.obj.map (homOfLE h).op).app U
        ((globalScalarEndomorphism X (F.obj.obj (op m))
          (idealThickeningBaseScalar f a)).app U x) := by
  let hn : n + 1 ≤ m := (Nat.add_le_add_right (Nat.le_add_left n r) 1).trans h
  let en := gradedPieceCommonStageIso f I F hn
  let ej := gradedPieceCommonStageIso f I F h
  let μ := idealPowerQuotientLayerMul X (idealThickeningBaseScalar f)
    (F.obj.obj (op m)) I r n a
  have hy' := gradedPieceCommonStageIso_inv_section f I F hn U x y hy
  rw [← formalGradedScalarMapAtStage_eq f I F r n m h a]
  change (kernel.ι (F.transition (r + n))).app U
      (ej.hom.app U (μ.app U (en.inv.app U y))) = _
  have he := congrArg (fun k => k.app U (μ.app U (en.inv.app U y)))
    (gradedPieceCommonStageIso_hom_ι f I F h)
  change (kernel.ι (F.transition (r + n))).app U
      (ej.hom.app U (μ.app U (en.inv.app U y))) = _ at he
  rw [he]
  have hm := congrArg (fun k => k.app U (en.inv.app U y))
    (idealQuotientLayerMul_ι X (idealThickeningBaseScalar f)
      (F.obj.obj (op m))
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ (r + n)) : I ^ (r + n + 1) ≤ I ^ (r + n))
      a
      (fun b hb => by
        rw [show r + n + 1 = r + (n + 1) from Nat.add_assoc r n 1, pow_add]
        exact Ideal.mul_mem_mul a.property hb)
      (fun b hb => by rw [pow_add]; exact Ideal.mul_mem_mul a.property hb))
  change (kernel.ι (idealQuotientMap X (idealThickeningBaseScalar f)
      (F.obj.obj (op m))
      (Ideal.pow_le_pow_right (Nat.le_succ (r + n)) : I ^ (r + n + 1) ≤ I ^ (r + n)))).app U
      (μ.app U (en.inv.app U y)) = _ at hm
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hm ⊢
  rw [hm, hy']
  have hq := congrArg (fun k => k.app U x)
    (idealQuotientπ_mul X (idealThickeningBaseScalar f) (F.obj.obj (op m))
      (J := I ^ (n + 1)) (K := I ^ (r + n + 1)) a
      (fun b (hb : b ∈ I ^ (n + 1)) => by
        rw [show r + n + 1 = r + (n + 1) from Nat.add_assoc r n 1, pow_add]
        exact Ideal.mul_mem_mul a.property hb))
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hq
  rw [hq]
  exact congrArg (fun k => k.app U
      ((globalScalarEndomorphism X (F.obj.obj (op m))
        (idealThickeningBaseScalar f a)).app U x))
    (idealQuotientπ_baseIdealReductionIso_hom f I F h)

end AlgebraicGeometry.Scheme.Cohomology
