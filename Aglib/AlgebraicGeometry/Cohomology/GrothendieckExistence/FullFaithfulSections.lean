/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.LocalCompletedRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletedSectionGluing
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Coherent

/-! # Global original Hom sections associated with formal morphisms -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.InternalHom

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F G : X.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent]
  (hF : QuasiCoherent.affineLocallyFiniteType X F)
  (hG : QuasiCoherent.affineLocallyFiniteType X G)

local notation "α" => idealThickeningBaseScalar f

/-- A formal morphism determines a unique original global Hom section, whose
affine restrictions have exactly the prescribed completed local Hom elements. -/
theorem existsUnique_internalHomSection
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I) :
    ∃! t : Γ(sheaf X F G, ⊤), ∀ U : X.affineOpens,
      letI := idealSectionModule X α (sheaf X F G) U.val
      AdicCompletion.of I Γ(sheaf X F G, U)
          ((sheaf X F G).val.map (homOfLE le_top : U.val ⟶ ⊤).op t) =
        localCompletedHom f F G hF hG I η U := by
  have hH := affineLocallyFiniteType_internalHom F G hF hG
  let : (sheaf X F G).IsFinitePresentation :=
    QuasiCoherent.affineLocallyFiniteType_finitePresentation hH
  exact existsUnique_section_of_completedAffineSections_eq I f (sheaf X F G) hH
    (localCompletedHom f F G hF hG I η)
      (localCompletedHom_restrict f F G hF hG I (IsNoetherian.noetherian I) η)

/-- The original global Hom section algebraizing a formal morphism. -/
def formalHomSection
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I) :
    Γ(sheaf X F G, ⊤) :=
  (existsUnique_internalHomSection I f F G hF hG η).choose

/-- The chosen global Hom section retains the uniquely specified local completions. -/
theorem formalHomSection_completion
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I)
    (U : X.affineOpens) :
    letI := idealSectionModule X α (sheaf X F G) U.val
    AdicCompletion.of I Γ(sheaf X F G, U)
        ((sheaf X F G).val.map (homOfLE le_top : U.val ⟶ ⊤).op
          (formalHomSection I f F G hF hG η)) =
      localCompletedHom f F G hF hG I η U :=
  (existsUnique_internalHomSection I f F G hF hG η).choose_spec.1 U

/-- The original module morphism represented by the recovered global Hom section. -/
def formalHomLift
    (η : idealPowerQuotientFunctor X α F I ⟶ idealPowerQuotientFunctor X α G I) :
    F ⟶ G :=
  (globalHomEquiv X F G).symm (formalHomSection I f F G hF hG η)

end AlgebraicGeometry.Scheme.Cohomology
