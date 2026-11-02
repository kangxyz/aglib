/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.ThickeningTransitions
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-! # Original section coordinates and their adic retraction

The compatible maps are formed from the original geometric units and scalar
isomorphisms on literal ideal thickenings. The resulting map lands in the
original complete ring, not in a new completion realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
variable {B C : Type u} [CommRing B] [CommRing C] {X Y : Scheme.{u}}

/-- The original scalar map of an affine-base scheme. -/
abbrev affineScalarMap (f : X ⟶ Spec (.of B)) : B →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom

/-- The whole scalar triangle on original global sections. -/
theorem affineScalarMap_square (p : Y ⟶ X) (q : Y ⟶ Spec (.of C))
    (f : X ⟶ Spec (.of B)) (σ : B →+* C)
    (h : p ≫ f = q ≫ Spec.map (CommRingCat.ofHom σ)) :
    p.appTop.hom.comp (affineScalarMap f) = (affineScalarMap q).comp σ := by
  change (((ΓSpecIso (.of B)).inv ≫ f.appTop) ≫ p.appTop).hom =
    ((CommRingCat.ofHom σ ≫ (ΓSpecIso (.of C)).inv) ≫ q.appTop).hom
  rw [Category.assoc, ← Hom.comp_appTop, h, Hom.comp_appTop,
    ΓSpecIso_inv_naturality, Category.assoc]

open Modules
variable (f : X ⟶ Spec (.of B)) (I : Ideal B)

/-- Original quotient scalars on the literal thickening. -/
abbrev adicSectionScalar (n : ℕ) := affineScalarMap (idealThickeningStructure f (I ^ n))

variable (hb : ∀ n, Function.Bijective (adicSectionScalar f I n))

/-- The inverse of the original quotient scalar map. -/
def adicSectionScalarEquiv (n : ℕ) :
    (B ⧸ I ^ n) ≃+* Γ(idealThickeningSpace f (I ^ n), ⊤) :=
  RingEquiv.ofBijective (adicSectionScalar f I n) (hb n)

/-- Original sections reduced to original quotient-ring coordinates. -/
def adicSectionCoordinate (n : ℕ) : Γ(X, ⊤) →+* B ⧸ I ^ n :=
  (adicSectionScalarEquiv f I hb n).symm.toRingHom.comp
    (idealThickeningι f (I ^ n)).appTop.hom

/-- The original unit in quotient coordinates. -/
theorem adicSectionCoordinate_scalar (n : ℕ) :
    (adicSectionCoordinate f I hb n).comp (affineScalarMap f) =
      Ideal.Quotient.mk (I ^ n) := by
  have h := affineScalarMap_square (idealThickeningι f (I ^ n))
    (idealThickeningStructure f (I ^ n)) f (Ideal.Quotient.mk (I ^ n))
    pullback.condition
  ext b
  change (adicSectionScalarEquiv f I hb n).symm
    ((idealThickeningι f (I ^ n)).appTop.hom (affineScalarMap f b)) = _
  have he : (idealThickeningι f (I ^ n)).appTop.hom (affineScalarMap f b) =
      adicSectionScalar f I n (Ideal.Quotient.mk (I ^ n) b) := RingHom.congr_fun h b
  rw [he]
  exact (adicSectionScalarEquiv f I hb n).symm_apply_apply _

/-- Whole compatibility with the original quotient reductions. -/
theorem adicSectionCoordinate_transition {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (adicSectionCoordinate f I hb n) =
      adicSectionCoordinate f I hb m := by
  let t := idealThickeningMap f (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m)
  have ht : t ≫ idealThickeningStructure f (I ^ n) =
      idealThickeningStructure f (I ^ m) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)) := pullback.lift_snd ..
  have hs := affineScalarMap_square t (idealThickeningStructure f (I ^ m))
    (idealThickeningStructure f (I ^ n)) (Ideal.Quotient.factorPow I h) ht
  have hu : (idealThickeningι f (I ^ n)).appTop ≫ t.appTop =
      (idealThickeningι f (I ^ m)).appTop := by
    rw [← Hom.comp_appTop, idealThickeningMap_ι]
  ext s
  apply (hb m).injective
  change adicSectionScalar f I m
    (Ideal.Quotient.factorPow I h ((adicSectionScalarEquiv f I hb n).symm
      ((idealThickeningι f (I ^ n)).appTop.hom s))) = _
  have hse (b : B ⧸ I ^ n) : t.appTop.hom (adicSectionScalar f I n b) =
      adicSectionScalar f I m (Ideal.Quotient.factorPow I h b) := RingHom.congr_fun hs b
  rw [← hse]
  change t.appTop.hom ((adicSectionScalarEquiv f I hb n)
    ((adicSectionScalarEquiv f I hb n).symm _)) =
      (adicSectionScalarEquiv f I hb m) ((adicSectionScalarEquiv f I hb m).symm _)
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom hu s

variable [IsAdicComplete I B]

/-- The direct compatible lift into the original complete base ring. -/
def adicSectionRetraction : Γ(X, ⊤) →+* B :=
  IsAdicComplete.liftRingHom I (adicSectionCoordinate f I hb)
    (fun {_ _} h => adicSectionCoordinate_transition f I hb h)

/-- Every original quotient of the lift is the original unit coordinate. -/
theorem adicSectionRetraction_quotient (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n)).comp (adicSectionRetraction f I hb) =
      adicSectionCoordinate f I hb n :=
  IsAdicComplete.mk_comp_liftRingHom ..

/-- The scalar composite is the identity, by native adic separatedness. -/
theorem adicSectionRetraction_scalar :
    (adicSectionRetraction f I hb).comp (affineScalarMap f) = RingHom.id B := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n b
  have h := RingHom.congr_fun (adicSectionRetraction_quotient f I hb n)
    (affineScalarMap f b)
  exact h.trans (RingHom.congr_fun (adicSectionCoordinate_scalar f I hb n) b)

end AlgebraicGeometry.Scheme
