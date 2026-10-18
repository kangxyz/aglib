/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Determinant.Overlap

/-!
# The actual global projective differential determinant isomorphism

The original compatible determinant chart arrows give matching sections of the original
structure-linear Hom sheaf. Native sheaf gluing produces the unique actual global morphism
with those original restrictions. Native open-cover detection of isomorphisms then gives
an isomorphism from the actual top relative exterior sheaf to the original inverse twist
tensor the pulled-back actual coefficient determinant.

The native over-site and scheme-restriction equations are exact, and the original signed
ratio-differential wedge formula survives globally. The coefficient determinant remains
explicit. Any commutative ring is allowed, including the zero ring; the supplied coordinate
order includes dimension zero. Comparison with the original Laurent trace is a later gate.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveSpace

private theorem determinantHomSection_restrict (X : Scheme.{u}) (M N : X.Modules)
    (U T : X.Opens) (h : T ≤ U) (f : M.over U ⟶ N.over U) :
    InternalHom.sectionHomEquiv X M N T
      ((InternalHom.sheaf X M N).val.map (homOfLE h).op
        ((InternalHom.sectionHomEquiv X M N U).symm f)) =
      ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app M).inv ≫
        (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).map f ≫
          ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app N).hom := by
  ext V m
  rfl

private theorem determinantGlobalHomSection_over (X : Scheme.{u}) (M N : X.Modules)
    (f : M ⟶ N) (U : X.Opens) :
    InternalHom.sectionHomEquiv X M N U
      ((InternalHom.sheaf X M N).val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (InternalHom.globalHomEquiv X M N f)) =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map f := by
  ext V m
  rfl

private theorem determinantHom_restrict_of_over (X : Scheme.{u}) (M N : X.Modules)
    (f : M ⟶ N) (U : X.Opens) (a : M.over U ≅ N.over U)
    (hf : (SheafOfModules.overFunctor X.ringCatSheaf U).map f = a.hom) :
    (Scheme.Modules.restrictFunctor U.ι).map f =
      ((Scheme.Modules.overFunctorEquiv U).app M).inv ≫
        (Scheme.Modules.overEquiv U).functor.map a.hom ≫
          ((Scheme.Modules.overFunctorEquiv U).app N).hom := by
  let F := (Scheme.Modules.overEquiv U).functor
  let q := Scheme.Modules.overFunctorEquiv U
  have hn := q.hom.naturality f
  apply (cancel_epi (q.app M).hom).mp
  change (q.app M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
    (q.app M).hom ≫ (q.app M).inv ≫ F.map a.hom ≫ (q.app N).hom
  rw [Iso.hom_inv_id_assoc]
  exact hn.symm.trans (congrArg (fun g => F.map g ≫ (q.app N).hom) hf)

variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
local notation "P" => ProjectiveSpace R ι
local notation "Ω" => Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
local notation "K" => moduleExteriorPower P Ω n
local notation "D" => differentialDeterminantTarget R ι n

/-- The original chart arrow as a section of the actual structure-linear Hom sheaf. -/
def differentialDeterminantChartHomSection (i : ι) :
    Γ(InternalHom.sheaf P K D, coordinateOpen R ι i) :=
  (InternalHom.sectionHomEquiv P K D (coordinateOpen R ι i)).symm
    (differentialDeterminantChartIso R ι n e i).hom

/-- Native original overlap equality gives a matching family in the original Hom sheaf. -/
theorem differentialDeterminantChartHomSection_compatible :
    TopCat.Presheaf.IsCompatible (InternalHom.sheaf P K D).val.presheaf
      (coordinateOpen R ι) (differentialDeterminantChartHomSection R ι n e) := by
  intro i k
  apply (InternalHom.sectionHomEquiv P K D
    (coordinateOpen R ι i ⊓ coordinateOpen R ι k)).injective
  exact (determinantHomSection_restrict P K D (coordinateOpen R ι i)
    (coordinateOpen R ι i ⊓ coordinateOpen R ι k) inf_le_left
    (differentialDeterminantChartIso R ι n e i).hom).trans
      ((congrArg Iso.hom (differentialDeterminantChartIsoOn_eq R ι n e i k
        inf_le_left inf_le_right)).trans
          (determinantHomSection_restrict P K D (coordinateOpen R ι k)
            (coordinateOpen R ι i ⊓ coordinateOpen R ι k) inf_le_right
            (differentialDeterminantChartIso R ι n e k).hom).symm)

/-- The original Hom section glued from the original actual determinant chart arrows. -/
def differentialDeterminantHomSection : Γ(InternalHom.sheaf P K D, (⊤ : (P).Opens)) := by
  let H := InternalHom.sheaf P K D
  let A : TopCat.Sheaf Ab P := ⟨H.val.presheaf, H.isSheaf⟩
  exact (A.existsUnique_gluing' (coordinateOpen R ι) (⊤ : (P).Opens)
    (fun _ => homOfLE le_top) (iSup_coordinateOpen_eq_top R ι).ge
    (differentialDeterminantChartHomSection R ι n e)
    (differentialDeterminantChartHomSection_compatible R ι n e)).choose

/-- The glued original Hom section restricts to its original chart section. -/
theorem differentialDeterminantHomSection_restrict (i : ι) :
    (InternalHom.sheaf P K D).val.map
      (homOfLE (show coordinateOpen R ι i ≤ ⊤ from le_top)).op
      (differentialDeterminantHomSection R ι n e) =
        differentialDeterminantChartHomSection R ι n e i := by
  let H := InternalHom.sheaf P K D
  let A : TopCat.Sheaf Ab P := ⟨H.val.presheaf, H.isSheaf⟩
  exact (A.existsUnique_gluing' (coordinateOpen R ι) (⊤ : (P).Opens)
    (fun _ => homOfLE le_top) (iSup_coordinateOpen_eq_top R ι).ge
    (differentialDeterminantChartHomSection R ι n e)
    (differentialDeterminantChartHomSection_compatible R ι n e)).choose_spec.1 i

/-- The actual global morphism characterized by the original determinant chart maps. -/
def differentialDeterminantHom : K ⟶ D :=
  (InternalHom.globalHomEquiv P K D).symm (differentialDeterminantHomSection R ι n e)

/-- Native over-restriction recovers exactly the original actual chart arrow. -/
theorem differentialDeterminantHom_over (i : ι) :
    (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).map
      (differentialDeterminantHom R ι n e) =
        (differentialDeterminantChartIso R ι n e i).hom := by
  have hh : (InternalHom.sheaf P K D).val.map
      (homOfLE (show coordinateOpen R ι i ≤ ⊤ from le_top)).op
      (InternalHom.globalHomEquiv P K D (differentialDeterminantHom R ι n e)) =
        differentialDeterminantChartHomSection R ι n e i := by
    dsimp only [differentialDeterminantHom]
    rw [Equiv.apply_symm_apply]
    exact differentialDeterminantHomSection_restrict R ι n e i
  exact (determinantGlobalHomSection_over P K D
    (differentialDeterminantHom R ι n e) (coordinateOpen R ι i)).symm.trans
      ((congrArg (InternalHom.sectionHomEquiv P K D (coordinateOpen R ι i)) hh).trans
        ((InternalHom.sectionHomEquiv P K D (coordinateOpen R ι i)).apply_symm_apply _))

/-- The original over-chart isomorphism through the native scheme-restriction equivalence. -/
def differentialDeterminantChartRestrictIso (i : ι) :
    (K).restrict (coordinateOpen R ι i).ι ≅ (D).restrict (coordinateOpen R ι i).ι :=
  ((Scheme.Modules.overFunctorEquiv (coordinateOpen R ι i)).app K).symm ≪≫
    (Scheme.Modules.overEquiv (coordinateOpen R ι i)).functor.mapIso
      (differentialDeterminantChartIso R ι n e i) ≪≫
    ((Scheme.Modules.overFunctorEquiv (coordinateOpen R ι i)).app D)

/-- Native scheme restriction recovers the same original transported chart isomorphism. -/
theorem differentialDeterminantHom_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (coordinateOpen R ι i).ι).map
      (differentialDeterminantHom R ι n e) =
        (differentialDeterminantChartRestrictIso R ι n e i).hom :=
  determinantHom_restrict_of_over P K D (differentialDeterminantHom R ι n e)
    (coordinateOpen R ι i) (differentialDeterminantChartIso R ι n e i)
    (differentialDeterminantHom_over R ι n e i)

private theorem determinant_coordinateCover :
    ∀ x : P, ∃ (i : ι) (y : (coordinateOpen R ι i).toScheme),
      (coordinateOpen R ι i).ι y = x := by
  intro x
  obtain ⟨i, hix⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ iSup (coordinateOpen R ι) by rw [iSup_coordinateOpen_eq_top]; trivial)
  exact ⟨i, ⟨x, hix⟩, rfl⟩

/-- The actual global map is an isomorphism by the original coordinate-open cover. -/
theorem differentialDeterminantHom_isIso : IsIso (differentialDeterminantHom R ι n e) := by
  apply isIso_of_restrict_openCover
    (fun i : ι => (coordinateOpen R ι i).toScheme)
    (fun i => (coordinateOpen R ι i).ι) (determinant_coordinateCover R ι)
  intro i
  rw [differentialDeterminantHom_restrict]
  infer_instance

/-- The actual relative differential determinant, retaining the coefficient determinant. -/
def differentialDeterminantIso : K ≅ D := by
  letI := differentialDeterminantHom_isIso R ι n e
  exact asIso (differentialDeterminantHom R ι n e)

/-- The actual global isomorphism has exactly the original over-chart homomorphism. -/
theorem differentialDeterminantIso_over (i : ι) :
    (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).map
      (differentialDeterminantIso R ι n e).hom =
        (differentialDeterminantChartIso R ι n e i).hom :=
  differentialDeterminantHom_over R ι n e i

/-- The actual global isomorphism has exactly the original native scheme restriction. -/
theorem differentialDeterminantIso_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (coordinateOpen R ι i).ι).map
      (differentialDeterminantIso R ι n e).hom =
        (differentialDeterminantChartRestrictIso R ι n e i).hom :=
  differentialDeterminantHom_restrict R ι n e i

/-- The original actual chart maps uniquely characterize the global morphism. -/
theorem differentialDeterminantHom_unique (f : K ⟶ D)
    (hf : ∀ i, (SheafOfModules.overFunctor (P).ringCatSheaf
      (coordinateOpen R ι i)).map f = (differentialDeterminantChartIso R ι n e i).hom) :
    f = differentialDeterminantHom R ι n e := by
  apply hom_ext_of_coordinateSubopens R ι
  intro i T hi s
  let V := op (Over.mk (homOfLE hi))
  exact (congrArg (fun a => a.val.app V s) (hf i)).trans
    (congrArg (fun a => a.val.app V s) (differentialDeterminantHom_over R ι n e i)).symm

/-- The actual global map retains the original pivot-first ratio-differential wedge formula. -/
theorem differentialDeterminantIso_wedge (i : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (differentialDeterminantIso R ι n e).hom.val.app
      (op ((coordinateOpen R ι i).ι ''ᵁ W))
      ((SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app
        (op ((coordinateOpen R ι i).ι ''ᵁ W))
        (fun a => (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a))
            ((coordinateOpen R ι i).ι_image_le W)))) =
      (-1 : Γ(P, (coordinateOpen R ι i).ι ''ᵁ W)) ^ (e i).val •
        differentialDeterminantTargetGenerator R ι n e i
          ((coordinateOpen R ι i).ι_image_le W) := by
  let U := coordinateOpen R ι i
  let V := op (U.overEquivalence.inverse.obj W)
  let w := (SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app
    (op (U.ι ''ᵁ W))
    (fun a => (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
      (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) (U.ι_image_le W)))
  exact (congrArg (fun f => f.val.app V w)
    (differentialDeterminantIso_over R ι n e i)).trans
      (differentialDeterminantChartIso_wedge R ι n e i W)


end AlgebraicGeometry.ProjectiveSpace
