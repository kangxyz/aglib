/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletedSectionRecovery

/-! # Original global sections realizing compatible completed affine sections -/

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
/-- A restriction-compatible family of completed affine sections is the actual
completion of the restrictions of a unique original global section. -/
theorem existsUnique_section_of_completedAffineSections_eq
    (s : ∀ U : X.affineOpens,
      letI := Modules.idealSectionModule X α F U.val
      AdicCompletion I Γ(F, U))
    (hres : ∀ (U V : X.affineOpens) (i : V.val ⟶ U.val),
      letI := Modules.idealSectionModule X α F U.val
      letI := Modules.idealSectionModule X α F V.val
      AdicCompletion.map I ((moduleSectionsPresheaf X α F).map i.op).hom (s U) = s V) :
    ∃! t : Γ(F, ⊤), ∀ U : X.affineOpens,
      letI := Modules.idealSectionModule X α F U.val
      AdicCompletion.of I Γ(F, U) (F.val.map (homOfLE le_top : U.val ⟶ ⊤).op t) = s U := by
  have hcoord (t : Γ(F, ⊤)) (n : ℕ) (U : X.affineOpens) :
      letI := Modules.idealSectionModule X α F U.val
      Modules.idealQuotientAffineSectionsEquiv f F (I ^ n) U
          (AdicCompletion.eval I Γ(F, U) n
            (AdicCompletion.of I Γ(F, U)
              (F.val.map (homOfLE le_top : U.val ⟶ ⊤).op t))) =
        (Modules.idealQuotient X α F (I ^ n)).val.map
          (homOfLE le_top : U.val ⟶ ⊤).op
            ((Modules.idealQuotientπ X α F (I ^ n)).app ⊤ t) := by
    let := Modules.idealSectionModule X α F U.val
    change (Modules.idealQuotientπ X α F (I ^ n)).app U.val
      (F.val.map (homOfLE le_top : U.val ⟶ ⊤).op t) = _
    exact PresheafOfModules.naturality_apply
      (Modules.idealQuotientπ X α F (I ^ n)).val
        (homOfLE le_top : U.val ⟶ ⊤).op t
  obtain ⟨t, ht, huniq⟩ := existsUnique_section_of_completedAffineSections I f F hF s hres
  refine ⟨t, ?_, ?_⟩
  · intro U
    let := Modules.idealSectionModule X α F U.val
    apply AdicCompletion.ext
    intro n
    apply (Modules.idealQuotientAffineSectionsEquiv f F (I ^ n) U).injective
    exact (hcoord t n U).trans (ht n U)
  · intro t' ht'
    apply huniq t'
    intro n U
    let := Modules.idealSectionModule X α F U.val
    exact (hcoord t' n U).symm.trans
      (congrArg (fun z => Modules.idealQuotientAffineSectionsEquiv f F (I ^ n) U
        (AdicCompletion.eval I Γ(F, U) n z)) (ht' U))

end AlgebraicGeometry.Scheme.Cohomology
