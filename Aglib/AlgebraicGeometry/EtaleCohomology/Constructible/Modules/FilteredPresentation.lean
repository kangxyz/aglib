/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FreeFinitePresentation
public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentableGenerators
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction

/-! # Native fixed-ring filtered presentations

Original affine étale free module sheaves form compact strong generators.
Their native finite-colimit closure therefore presents every module sheaf by
an actual filtered diagram over the same coefficient ring. Constructibility
of these stages, and finite generation of a constructible apex, are separate
geometric obligations rather than assumptions hidden in this presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation

universe u

variable (R : Type (u + 1)) [Ring R] (X : Scheme.{u})

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

/-- Original affine étale free generators over the unchanged ring. -/
abbrev generators : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  ModuleCat.Sheaf.freeGenerators.{u + 1, u, u + 1, 0} X.smallEtaleTopology R
    (Scheme.AffineEtale.Spec X)

private instance coefficientColimits : HasColimitsOfSize.{u + 1, u + 1}
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) where
  has_colimits_of_shape I _ := by
    let : HasColimitsOfShape I AddCommGrpCat.{u + 1} := AddCommGrpCat.hasColimitsOfShape
    let : HasColimitsOfShape I (ModuleCat.{u + 1} R) := ModuleCat.hasColimitsOfShape R I
    exact CategoryTheory.Sheaf.instHasColimitsOfShape
      (J := X.smallEtaleTopology) (K := I)

instance generators_small : ObjectProperty.Small.{u + 1} (generators R X) := by
  unfold generators ModuleCat.Sheaf.freeGenerators
  infer_instance

/-- The original affine restriction, without choosing a second sheaf model. -/
private abbrev restriction :=
  (Scheme.AffineEtale.Spec X).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology

private instance restriction_faithful : (restriction R X).Faithful := by
  let V := ModuleCat.Sheaf.underlying R (Scheme.AffineEtale.topology X)
  let : (restriction R X ⋙ V).Faithful :=
    inferInstanceAs (ModuleCat.Sheaf.underlying R X.smallEtaleTopology ⋙
      EtaleAffineBasis.abelianRestriction X).Faithful
  exact Functor.Faithful.of_comp (restriction R X) V

private instance restriction_reflectsIsomorphisms : (restriction R X).ReflectsIsomorphisms := by
  let V := ModuleCat.Sheaf.underlying R (Scheme.AffineEtale.topology X)
  let : (restriction R X ⋙ V).ReflectsIsomorphisms :=
    inferInstanceAs (ModuleCat.Sheaf.underlying R X.smallEtaleTopology ⋙
      EtaleAffineBasis.abelianRestriction X).ReflectsIsomorphisms
  exact CategoryTheory.reflectsIsomorphisms_of_comp (restriction R X) V

/-- The actual affine generators detect original arrows and subobjects. -/
theorem generators_isStrongGenerator : (generators R X).IsStrongGenerator :=
  ModuleCat.Sheaf.freeGenerators_isStrongGenerator.{u + 1, u, u + 1, 0} X.smallEtaleTopology R
    (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)

/-- Every selected original affine generator is finitely presentable. -/
theorem generators_presentable : generators R X ≤
    isCardinalPresentable (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      Cardinal.aleph0.{u + 1} := by
  rintro F ⟨U⟩
  have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  exact qcqs_freeModule_isFinitelyPresentable R ((Scheme.AffineEtale.Spec X).obj U)

/-- The native finite-colimit closure, not a replacement constructibility predicate. -/
def finiteColimitStages : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (generators R X).colimitsCardinalClosure Cardinal.aleph0.{u + 1}

/-- Native density and finite-colimit closure supply genuine filtered generation. -/
theorem finiteColimitStages_filteredGenerator :
    (finiteColimitStages R X).IsCardinalFilteredGenerator Cardinal.aleph0.{u + 1} := by
  change ((generators R X).colimitsCardinalClosure
    Cardinal.aleph0.{u + 1}).IsCardinalFilteredGenerator Cardinal.aleph0.{u + 1}
  have : ((generators R X).colimitsCardinalClosure Cardinal.aleph0.{u + 1}).ι.IsDense :=
    ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι.{u + 1, u + 1, u + 2}
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (κ := Cardinal.aleph0.{u + 1}) (generators_isStrongGenerator R X)
      (generators_presentable R X)
  let (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      IsCardinalFiltered (CostructuredArrow
        ((generators R X).colimitsCardinalClosure Cardinal.aleph0.{u + 1}).ι F)
        Cardinal.aleph0.{u + 1} :=
    ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
      (generators R X) Cardinal.aleph0.{u + 1} F
  exact IsCardinalFilteredGenerator.of_isDense_ι.{u + 1, u + 1, u + 2}
    ((generators R X).colimitsCardinalClosure Cardinal.aleph0.{u + 1})
    Cardinal.aleph0.{u + 1}
    ((generators R X).colimitsCardinalClosure_le_isCardinalPresentable
      (κ := Cardinal.aleph0.{u + 1}) (generators_presentable R X))

/-- Native finite presentation places the original coefficient in the same
actual finite-colimit closure; no object model is supplied as a certificate. -/
theorem finiteColimitStages_of_isFinitelyPresentable
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    [IsFinitelyPresentable.{u + 1} F] : finiteColimitStages R X F := by
  have h := CategoryTheory.IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
    (κ := Cardinal.aleph0.{u + 1}) (generators_isStrongGenerator R X)
    (generators_presentable R X)
  change (generators R X).colimitsCardinalClosure Cardinal.aleph0.{u + 1} F
  rw [← h]
  infer_instance

/-- Every actual module sheaf admits an actual filtered finite-colimit
presentation over its original ring, with the original cocone and arrows. -/
theorem exists_filtered_presentation
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (c : Cocone D), c.pt = F ∧ Nonempty (IsColimit c) ∧
        ∀ i, finiteColimitStages R X (D.obj i) := by
  obtain ⟨I, hI, hfiltered, ⟨p⟩⟩ :=
    (finiteColimitStages_filteredGenerator R X).exists_colimitsOfShape F
  have : IsFiltered I := isFiltered_of_isCardinalFiltered I Cardinal.aleph0.{u + 1}
  exact ⟨I, hI, inferInstance, p.diag, ⟨F, p.ι⟩, rfl, ⟨p.isColimit⟩, p.prop_diag_obj⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation
