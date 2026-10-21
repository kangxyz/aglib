/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.CompletedEvaluation

/-! # Restriction naturality of actual completed evaluation -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤)) (I : Ideal A)
variable (F G : X.Modules)
variable (hF : QuasiCoherent.affineLocallyFiniteType X F)
variable (hG : QuasiCoherent.affineLocallyFiniteType X G)

/-- Completed affine evaluation preserves actual restrictions. Only the
structural ideal must be finitely generated; chart rings need not be complete. -/
theorem affineCompletedEvaluation_restrict (hI : I.FG)
    (U V : X.affineOpens) (i : V.val ⟶ U.val) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    letI := idealSectionModule X α (sheaf X F G) V.val
    letI := idealSectionModule X α F U.val
    letI := idealSectionModule X α F V.val
    letI := idealSectionModule X α G U.val
    letI := idealSectionModule X α G V.val
    ∀ (s : AdicCompletion I Γ(sheaf X F G, U)) (m : AdicCompletion I Γ(F, U)),
      affineCompletedEvaluation α I V F G hF hG
        (AdicCompletion.map I
          ((Cohomology.moduleSectionsPresheaf X α (sheaf X F G)).map i.op).hom s)
        (AdicCompletion.map I ((Cohomology.moduleSectionsPresheaf X α F).map i.op).hom m) =
      AdicCompletion.map I ((Cohomology.moduleSectionsPresheaf X α G).map i.op).hom
        (affineCompletedEvaluation α I U F G hF hG s m) := by
  let := idealSectionModule X α (sheaf X F G) U.val
  let := idealSectionModule X α (sheaf X F G) V.val
  let := idealSectionModule X α F U.val
  let := idealSectionModule X α F V.val
  let := idealSectionModule X α G U.val
  let := idealSectionModule X α G V.val
  let : IsAdicComplete I (AdicCompletion I Γ(G, V)) := AdicCompletion.isAdicComplete hI
  let rH := (AdicCompletion.map I
    ((Cohomology.moduleSectionsPresheaf X α (sheaf X F G)).map i.op).hom).restrictScalars A
  let rF := (AdicCompletion.map I
    ((Cohomology.moduleSectionsPresheaf X α F).map i.op).hom).restrictScalars A
  let rG := (AdicCompletion.map I
    ((Cohomology.moduleSectionsPresheaf X α G).map i.op).hom).restrictScalars A
  let eU := affineCompletedEvaluation α I U F G hF hG
  let eV := affineCompletedEvaluation α I V F G hF hG
  let L := (LinearMap.lcomp A (AdicCompletion I Γ(G, V)) rF).comp (eV.comp rH)
  let R := (LinearMap.compRight A rG).comp eU
  have heq : L = R := by
    apply AdicCompletion.bilinear_ext_of I hI
    intro s m
    change eV (rH (AdicCompletion.of I _ s)) (rF (AdicCompletion.of I _ m)) =
      rG (eU (AdicCompletion.of I _ s) (AdicCompletion.of I _ m))
    simp only [eU, eV, rH, rF, rG, LinearMap.restrictScalars_apply,
      AdicCompletion.map_of, affineCompletedEvaluation_of_of]
    change affineCompletedEvaluation α I V F G hF hG
      (AdicCompletion.of I Γ(sheaf X F G, V) ((sheaf X F G).val.map i.op s))
      (AdicCompletion.of I Γ(F, V) (F.val.map i.op m)) =
        AdicCompletion.map I ((Cohomology.moduleSectionsPresheaf X α G).map i.op).hom
          (AdicCompletion.of I Γ(G, U) (sectionEvaluation X F G U s m))
    erw [affineCompletedEvaluation_of_of, AdicCompletion.map_of]
    exact congrArg (AdicCompletion.of I Γ(G, V))
      (sectionEvaluation_restrict X F G i s m)
  intro s m
  exact LinearMap.congr_fun (LinearMap.congr_fun heq s) m

end AlgebraicGeometry.Scheme.Modules.InternalHom
