/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.CompletedCoordinates
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionGeneration

/-! # Detection of completed Hom sections by restricted original sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤)) (I : Ideal A)
variable (F G : X.Modules) [F.IsQuasicoherent]
variable (hF : QuasiCoherent.affineLocallyFiniteType X F)
variable (hG : QuasiCoherent.affineLocallyFiniteType X G)

/-- On a smaller affine open, completed Hom sections are determined by their
evaluations on restrictions of original source sections from the larger open. -/
theorem affineCompletedEvaluation_ext_restriction
    (U V : X.affineOpens) (i : V.val ⟶ U.val) :
    letI := idealSectionModule X α (sheaf X F G) V.val
    letI := idealSectionModule X α F V.val
    letI := idealSectionModule X α G V.val
    ∀ (h k : AdicCompletion I Γ(sheaf X F G, V)),
      (∀ m : Γ(F, U), affineCompletedEvaluation α I V F G hF hG h
          (AdicCompletion.of I _ (F.val.map i.op m)) =
        affineCompletedEvaluation α I V F G hF hG k
          (AdicCompletion.of I _ (F.val.map i.op m))) → h = k := by
  let := idealSectionModule X α (sheaf X F G) V.val
  let := idealSectionModule X α F V.val
  let := idealSectionModule X α G V.val
  let : Algebra A Γ(X, V) := (idealSectionRingHom X α V.val).toAlgebra
  let : IsScalarTower A Γ(X, V) Γ(G, V) := IsScalarTower.of_compHom A Γ(X, V) _
  intro h k heval
  let e := affineStructuralCompletedHomEquiv V F G hF hG α I
  apply e.injective
  apply Subtype.ext
  funext n
  let J := I.map (idealSectionRingHom X α V.val)
  let q := (J ^ n • ⊤ : Submodule Γ(X, V) Γ(F, V)).mkQ
  have hstage : ((e h).val n).comp q = ((e k).val n).comp q := by
    apply affineOpenRestriction_linearMap_ext U V i F
    intro m
    exact (affineCompletedEvaluation_coordinate α I V F G hF hG n h
      (F.val.map i.op m)).trans
        ((congrArg (fun z => AdicCompletion.mapIdealQuotientEquiv (S := Γ(X, V))
          I Γ(G, V) n (AdicCompletion.eval I Γ(G, V) n z)) (heval m)).trans
            (affineCompletedEvaluation_coordinate α I V F G hF hG n k
              (F.val.map i.op m)).symm)
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact LinearMap.congr_fun hstage x

end AlgebraicGeometry.Scheme.Modules.InternalHom
