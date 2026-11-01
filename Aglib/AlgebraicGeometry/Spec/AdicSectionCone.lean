/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AdicSectionRetraction
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf

/-! # The original ring-section cone of actual ideal thickenings -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open Modules
universe u
variable {B : Type u} [CommRing B] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of B)) (I : Ideal B)

/-- The original thickening transition is the identity for equal ideals. -/
theorem adicThickeningMap_refl (J : Ideal B) :
    idealThickeningMap f (le_refl J) = 𝟙 _ := by
  apply (cancel_mono (idealThickeningι f J)).mp
  simp

/-- The original thickening transitions compose on the original projections. -/
theorem adicThickeningMap_comp {J K L : Ideal B} (h : J ≤ K) (k : K ≤ L) :
    idealThickeningMap f k ≫ idealThickeningMap f h = idealThickeningMap f (h.trans k) := by
  apply (cancel_mono (idealThickeningι f J)).mp
  simp

/-- Literal structure-ring sections, with the original geometric restriction arrows. -/
def adicRingSectionDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := Γ(idealThickeningSpace f (I ^ n.unop), ⊤)
  map {m n} h := (idealThickeningMap f
    (Ideal.pow_le_pow_right (leOfHom h.unop) : I ^ m.unop ≤ I ^ n.unop)).appTop
  map_id n := by rw [adicThickeningMap_refl, Hom.id_appTop]
  map_comp h k := by rw [← Hom.comp_appTop, adicThickeningMap_comp]

/-- The vertex and all legs are the original global sections and actual units. -/
def adicRingSectionCone : Cone (adicRingSectionDiagram f I) where
  pt := Γ(X, ⊤)
  π :=
    { app := fun n => (idealThickeningι f (I ^ n.unop)).appTop
      naturality := by
        intro m n h
        change (𝟙 Γ(X, ⊤)) ≫ (idealThickeningι f (I ^ n.unop)).appTop =
          (idealThickeningι f (I ^ m.unop)).appTop ≫
            (idealThickeningMap f (Ideal.pow_le_pow_right (leOfHom h.unop) :
              I ^ m.unop ≤ I ^ n.unop)).appTop
        rw [Category.id_comp, ← Hom.comp_appTop, idealThickeningMap_ι] }

/-- The whole quotient-scalar triangle for the original transition. -/
theorem adicRingSectionScalar_transition {m n : ℕ} (h : m ≤ n) :
    (idealThickeningMap f (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m)).appTop.hom.comp
        (adicSectionScalar f I n) =
      (adicSectionScalar f I m).comp (Ideal.Quotient.factorPow I h) :=
  affineScalarMap_square _ _ _ _ (pullback.lift_snd ..)

variable (hb : ∀ n, Function.Bijective (adicSectionScalar f I n))

/-- Original ring-cone legs in the canonical quotient coordinates. -/
def adicRingConeCoordinate (s : Cone (adicRingSectionDiagram f I)) (n : ℕ) :
    s.pt →+* B ⧸ I ^ n :=
  (adicSectionScalarEquiv f I hb n).symm.toRingHom.comp (s.π.app (op n)).hom

/-- Every original ring cone gives the required whole compatible quotient family. -/
theorem adicRingConeCoordinate_transition (s : Cone (adicRingSectionDiagram f I))
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (adicRingConeCoordinate f I hb s n) =
      adicRingConeCoordinate f I hb s m := by
  have hs := adicRingSectionScalar_transition f I h
  have hn := s.w (homOfLE h).op
  ext x
  apply (hb m).injective
  have he (b : B ⧸ I ^ n) :
      (idealThickeningMap f (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m)).appTop.hom
        (adicSectionScalar f I n b) =
      adicSectionScalar f I m (Ideal.Quotient.factorPow I h b) := RingHom.congr_fun hs b
  change adicSectionScalar f I m
    (Ideal.Quotient.factorPow I h ((adicSectionScalarEquiv f I hb n).symm
      ((s.π.app (op n)).hom x))) =
    (adicSectionScalarEquiv f I hb m) ((adicSectionScalarEquiv f I hb m).symm _)
  rw [← he]
  change (idealThickeningMap f (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m)).appTop.hom
    ((adicSectionScalarEquiv f I hb n) ((adicSectionScalarEquiv f I hb n).symm _)) = _
  erw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom hn x

variable [IsAdicComplete I B]

/-- Native compatible lifting directly into the unchanged complete ring. -/
def adicRingConeLift (s : Cone (adicRingSectionDiagram f I)) : s.pt ⟶ Γ(X, ⊤) :=
  CommRingCat.ofHom ((affineScalarMap f).comp (IsAdicComplete.liftRingHom I
    (adicRingConeCoordinate f I hb s)
    (fun {_ _} h => adicRingConeCoordinate_transition f I hb s h)))

/-- The lift retains every original geometric unit. -/
theorem adicRingConeLift_fac (s : Cone (adicRingSectionDiagram f I)) (n : ℕᵒᵖ) :
    adicRingConeLift f I hb s ≫ (adicRingSectionCone f I).π.app n = s.π.app n := by
  have hu := affineScalarMap_square (idealThickeningι f (I ^ n.unop))
    (idealThickeningStructure f (I ^ n.unop)) f (Ideal.Quotient.mk (I ^ n.unop))
    pullback.condition
  ext x
  change (idealThickeningι f (I ^ n.unop)).appTop.hom
    (affineScalarMap f (IsAdicComplete.liftRingHom I
      (adicRingConeCoordinate f I hb s) _ x)) = _
  have he (b : B) : (idealThickeningι f (I ^ n.unop)).appTop.hom
      (affineScalarMap f b) = adicSectionScalar f I n.unop
      (Ideal.Quotient.mk (I ^ n.unop) b) := RingHom.congr_fun hu b
  rw [he, IsAdicComplete.mk_liftRingHom]
  exact (adicSectionScalarEquiv f I hb n.unop).apply_symm_apply _

/-- The original ring-section cone is limiting once its original scalar map is
bijective. Applications derive this scalar fact, rather than assume a limit. -/
def adicRingSectionConeIsLimit (hB : Function.Bijective (affineScalarMap f)) :
    IsLimit (adicRingSectionCone f I) where
  lift := adicRingConeLift f I hb
  fac := adicRingConeLift_fac f I hb
  uniq s m hm := by
    let E := RingEquiv.ofBijective (affineScalarMap f) hB
    have hinj : Function.Injective E.symm := E.symm.injective
    ext x
    apply hinj
    apply congrFun (IsHausdorff.funext' I (f := fun _ : Unit => E.symm (m x))
      (g := fun _ : Unit => E.symm (adicRingConeLift f I hb s x)) ?_) ()
    intro n _
    apply (hb n).injective
    have he (b : B) : (idealThickeningι f (I ^ n)).appTop.hom (E b) =
        adicSectionScalar f I n (Ideal.Quotient.mk (I ^ n) b) :=
      RingHom.congr_fun (affineScalarMap_square (idealThickeningι f (I ^ n))
        (idealThickeningStructure f (I ^ n)) f (Ideal.Quotient.mk (I ^ n))
        pullback.condition) b
    rw [← he, ← he]
    erw [E.apply_symm_apply, E.apply_symm_apply]
    exact (ConcreteCategory.congr_hom (hm (op n)) x).trans
      (ConcreteCategory.congr_hom (adicRingConeLift_fac f I hb s (op n)) x).symm

end AlgebraicGeometry.Scheme
