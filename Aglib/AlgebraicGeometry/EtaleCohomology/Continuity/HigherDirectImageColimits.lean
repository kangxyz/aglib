/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartStrictLocalNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.QcqsComparison
public import Aglib.CategoryTheory.Limits.Preserves.JointConservativity
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.Grp.Ulift

/-! # Sequential coefficient colimits for the original higher direct image

The coefficient-natural original marked-stalk comparison transports fixed-
scheme cohomology continuity to every original higher-image stalk. The actual
geometric stalks preserve colimits and jointly reflect their colimit property.
The comparison retains the stalk and Ext universe lifts explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

section MarkedChart

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η)
  (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)

/-- The actual original stalk comparison is natural in every coefficient,
with a common lift of the original stalk and the standard Ext universe. -/
def higherDirectImageChartStalkUliftIso :
    (higherDirectImage f q ⋙
      (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ⋙
        AddCommGrpCat.uliftFunctor.{u + 2, u + 1} ≅
      (inverseImage (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f) ⋙
        cohomologyFunctor.{u, u + 2}
          (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f) q) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u + 2} := by
  let (U : S.Etale) : HasExt.{u + 2}
      (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
        AddCommGrpCat.{u + 1}) := HasExt.standard _
  let (U : S.Etale) : HasExt.{u + 2}
      (AbelianSheaf.{u, u + 1} (pullback U.hom f)) := HasExt.standard _
  exact NatIso.ofComponents
    (fun F => Stalk.chartStrictLocalComparisonUliftIso.{u, u + 2, u + 2, u + 2}
      R Ω j η hη f F q)
    (fun g => (Stalk.chartStrictLocalComparisonUliftIso_naturality.{u, u + 2, u + 2, u + 2}
      R Ω j η hη f g q).symm)

include R j hη in
/-- Sequential continuity after an original geometric stalk, using a specified
actual affine chart and its original marked-point factorization. -/
theorem higherDirectImage_chartStalk_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ
      (higherDirectImage f q ⋙ (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) := by
  let Z := pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f
  let π : Z ⟶ X := pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f
  let : CompactSpace Z := inferInstance
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)
  let : PreservesColimitsOfShape ℕ (cohomologyFunctor.{u, u + 2} Z q) :=
    qcqsCohomologyFunctor_preservesSequentialColimits Z q
  let L := higherDirectImage f q ⋙
    (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let U := AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let V := AddCommGrpCat.uliftFunctor.{u + 1, u + 2}
  let : PreservesColimitsOfShape ℕ ((inverseImage π ⋙ cohomologyFunctor.{u, u + 2} Z q) ⋙ V) :=
    inferInstance
  let : PreservesColimitsOfShape ℕ (L ⋙ U) :=
    preservesColimitsOfShape_of_natIso (higherDirectImageChartStalkUliftIso R Ω j η hη f q).symm
  let : ReflectsColimitsOfShape ℕ U := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves L U

end MarkedChart

/-- Every original geometric point admits an actual affine open chart with the
literal spectrum factorization used by the marked-stalk comparison. -/
private theorem higherDirectImage_geometricStalk_preservesSequentialColimits
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S) :
    PreservesColimitsOfShape ℕ
      (higherDirectImage f q ⋙ (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) := by
  classical
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq (η default)
  let : IsOpenImmersion j := hj
  have hRange : Set.range η ⊆ Set.range j := by
    rintro z ⟨x, rfl⟩
    have hx : x = default := Subsingleton.elim _ _
    subst x
    exact ⟨y, hy⟩
  let k := IsOpenImmersion.lift j η hRange
  let φ : R →+* Ω := (Spec.preimage k).hom
  let : Algebra R Ω := φ.toAlgebra
  have hk : Spec.algebraMap R Ω = k := Spec.map_preimage k
  have hη : Spec.algebraMap R Ω ≫ j = η :=
    (congrArg (fun l => l ≫ j) hk).trans (IsOpenImmersion.lift_fac j η hRange)
  exact higherDirectImage_chartStalk_preservesSequentialColimits R Ω j η hη f q

/-- The original sheaf-valued higher direct image of a qcqs morphism preserves
sequential coefficient colimits over an arbitrary target scheme. -/
theorem higherDirectImage_preservesSequentialColimits
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ) :
    PreservesColimitsOfShape ℕ (higherDirectImage f q) := by
  let P (x : FibrewiseClosed.Index (𝟙 S)) :
      AbelianSheaf.{u, u + 1} S ⥤ AddCommGrpCat.{u + 1} :=
    (pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
  let (x : FibrewiseClosed.Index (𝟙 S)) : PreservesColimitsOfShape ℕ (P x) :=
    inferInstanceAs (PreservesColimitsOfShape ℕ
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})))
  let (x : FibrewiseClosed.Index (𝟙 S)) :
      PreservesColimitsOfShape ℕ (higherDirectImage f q ⋙ P x) :=
    higherDirectImage_geometricStalk_preservesSequentialColimits f q
      (FibrewiseClosed.pointField x.val) (FibrewiseClosed.geometricPoint x.val)
  exact preservesColimitsOfShape_of_jointlyReflectIsomorphisms (higherDirectImage f q) P
    (StalkUniverse.originalStalks_jointlyReflectIsomorphisms (𝟙 S))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
