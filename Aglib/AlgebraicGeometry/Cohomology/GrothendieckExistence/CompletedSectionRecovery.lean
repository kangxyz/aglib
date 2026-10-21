/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineSectionRecovery
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientNaturality

/-! # Global recovery from compatible completed affine sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F : X.Modules) [F.IsQuasicoherent]
  (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F)

local notation "α" => Modules.idealThickeningBaseScalar f

include hF in
/-- Compatible completed affine sections determine an original global section
with exactly their prescribed affine quotient coordinates. -/
theorem existsUnique_section_of_completedAffineSections
    (s : ∀ U : X.affineOpens,
      letI := Modules.idealSectionModule X α F U.val
      AdicCompletion I Γ(F, U))
    (hres : ∀ (U V : X.affineOpens) (i : V.val ⟶ U.val),
      letI := Modules.idealSectionModule X α F U.val
      letI := Modules.idealSectionModule X α F V.val
      AdicCompletion.map I ((moduleSectionsPresheaf X α F).map i.op).hom (s U) = s V) :
    ∃! t : Γ(F, ⊤), ∀ (n : ℕ) (U : X.affineOpens),
      letI := Modules.idealSectionModule X α F U.val
      (Modules.idealQuotient X α F (I ^ n)).val.map
        (homOfLE le_top : U.val ⟶ ⊤).op
          ((Modules.idealQuotientπ X α F (I ^ n)).app ⊤ t) =
        Modules.idealQuotientAffineSectionsEquiv f F (I ^ n) U
          (AdicCompletion.eval I Γ(F, U) n (s U)) := by
  let q (n : ℕ) (U : X.affineOpens) :
      Γ(Modules.idealQuotient X α F (I ^ n), U) :=
    letI := Modules.idealSectionModule X α F U.val
    Modules.idealQuotientAffineSectionsEquiv f F (I ^ n) U
      (AdicCompletion.eval I Γ(F, U) n (s U))
  apply existsUnique_section_of_affineQuotientSections I f F hF q
  · intro n U V i
    let := Modules.idealSectionModule X α F U.val
    let := Modules.idealSectionModule X α F V.val
    have hr := congrArg (AdicCompletion.eval I Γ(F, V) n) (hres U V i)
    exact (Modules.idealQuotientAffineSectionsEquiv_restrict f F (I ^ n) U V i
      (AdicCompletion.eval I Γ(F, U) n (s U))).symm.trans
        (congrArg (Modules.idealQuotientAffineSectionsEquiv f F (I ^ n) V) hr)
  · intro m n h U
    let := Modules.idealSectionModule X α F U.val
    exact (Modules.idealQuotientAffineSectionsEquiv_factor f F
      (Ideal.pow_le_pow_right h) U (AdicCompletion.eval I Γ(F, U) n (s U))).symm.trans
        (congrArg (Modules.idealQuotientAffineSectionsEquiv f F (I ^ m) U)
          (AdicCompletion.transitionMap_comp_eval_apply I Γ(F, U) h (s U)))

end AlgebraicGeometry.Scheme.Cohomology
