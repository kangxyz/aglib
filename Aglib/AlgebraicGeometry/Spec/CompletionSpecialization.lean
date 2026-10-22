/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.CompletionResidueFiber

/-!
# Specialization of an actual coefficient model along a precision-one map

The arrows here use the original algebra maps into the local ring and its
completion. Their equality on the literal closed fibres follows from equality
modulo the first maximal-ideal power, with no equality after completion assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.LocalRing

universe u

section AlgebraMaps

variable {R C S : Type u} [CommRing R] [CommRing C] [CommRing S]
  [Algebra R C] [Algebra R S]

/-- The triangle on spectra retains the original coefficient algebra map. -/
@[reassoc]
theorem specMap_algHom_triangle (a : C →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.algebraMap R C = Spec.algebraMap R S := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ : R →+* S => Spec.map (CommRingCat.ofHom φ)) a.comp_algebraMap

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Specialize the original coefficient model by a map back to its base ring. -/
def algebraSpecialization (a : C →ₐ[R] R) : X ⟶ pullback (Spec.algebraMap R C) f :=
  pullback.lift (f ≫ Spec.map (CommRingCat.ofHom a.toRingHom)) (𝟙 X) (by
    rw [Category.assoc, specMap_algHom_triangle]
    simp [Spec.algebraMap])

@[reassoc (attr := simp)]
theorem algebraSpecialization_fst (a : C →ₐ[R] R) :
    algebraSpecialization f a ≫ pullback.fst (Spec.algebraMap R C) f =
      f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem algebraSpecialization_snd (a : C →ₐ[R] R) :
    algebraSpecialization f a ≫ pullback.snd (Spec.algebraMap R C) f = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- Pull the original coefficient model back along an original coefficient map. -/
def coefficientBaseChangeMap (b : C →ₐ[R] S) :
    pullback f (Spec.algebraMap R S) ⟶ pullback (Spec.algebraMap R C) f :=
  pullback.lift
    (pullback.snd f (Spec.algebraMap R S) ≫ Spec.map (CommRingCat.ofHom b.toRingHom))
    (pullback.fst f (Spec.algebraMap R S)) (by
      rw [Category.assoc, specMap_algHom_triangle]
      exact pullback.condition.symm)

@[reassoc (attr := simp)]
theorem coefficientBaseChangeMap_fst (b : C →ₐ[R] S) :
    coefficientBaseChangeMap f b ≫ pullback.fst (Spec.algebraMap R C) f =
      pullback.snd f (Spec.algebraMap R S) ≫ Spec.map (CommRingCat.ofHom b.toRingHom) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem coefficientBaseChangeMap_snd (b : C →ₐ[R] S) :
    coefficientBaseChangeMap f b ≫ pullback.snd (Spec.algebraMap R C) f =
      pullback.fst f (Spec.algebraMap R S) := pullback.lift_snd _ _ _

end AlgebraMaps

/-- The canonical fibre comparison also retains its original residue-base map. -/
@[reassoc (attr := simp)]
theorem residueFiberBaseChangeIso_hom_snd {S T K L X : Scheme.{u}}
    (f : X ⟶ S) (c : T ⟶ S) (r : K ⟶ S) (t : L ⟶ T)
    (e : L ≅ K) (h : t ≫ c = e.hom ≫ r) :
    (residueFiberBaseChangeIso f c r t e h).hom ≫ pullback.snd f r =
      pullback.snd (pullback.snd f c) t ≫ e.hom := by
  simp only [residueFiberBaseChangeIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [pullback.condition]
  simp [pullback.map, pullback.lift_snd_assoc]

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {C : Type u} [CommRing C] [Algebra R C]

/-- The exact precision-one equation gives the square of the original
coefficient maps on spectra of residue fields. -/
@[reassoc]
theorem completionResidueCoefficientSquare
    (a : C →ₐ[R] R) (b : C →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (h : (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R ^ 1)).comp a =
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) 1).comp b) :
    residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R) ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      (completionResidueSpecIso R).hom ≫ residueSpecMap R ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (AdicCompletion.residueField_map_comp_eq_of_precision R a b h).symm

variable {R} {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

@[reassoc (attr := simp)]
theorem completionResidueFiberIso_hom_snd :
    (completionResidueFiberIso f).hom ≫ pullback.snd f (residueSpecMap R) =
      pullback.snd (pullback.snd f (completionSpecMap R))
        (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ≫
          (completionResidueSpecIso R).hom :=
  residueFiberBaseChangeIso_hom_snd _ _ _ _ _ _

/-- Precision one identifies the two maps from the literal completed fibre
into the original descended coefficient model. -/
theorem completionSpecialization_square
    (a : C →ₐ[R] R) (b : C →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (h : (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R ^ 1)).comp a =
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) 1).comp b) :
    pullback.fst (pullback.snd f (completionSpecMap R))
        (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ≫
      coefficientBaseChangeMap f b =
    (completionResidueFiberIso f).hom ≫ pullback.fst f (residueSpecMap R) ≫
      algebraSpecialization f a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientBaseChangeMap_fst, algebraSpecialization_fst]
    rw [← Category.assoc, pullback.condition, Category.assoc,
      completionResidueCoefficientSquare R a b h]
    simpa only [Category.assoc, pullback.condition_assoc] using
      congrArg (fun z => z ≫ residueSpecMap R ≫ Spec.map (CommRingCat.ofHom a.toRingHom))
        (completionResidueFiberIso_hom_snd f).symm
  · simpa only [Category.assoc, coefficientBaseChangeMap_snd,
      algebraSpecialization_snd, Category.comp_id] using
        (completionResidueFiberIso_hom_fst f).symm

end AlgebraicGeometry.Scheme.LocalRing
