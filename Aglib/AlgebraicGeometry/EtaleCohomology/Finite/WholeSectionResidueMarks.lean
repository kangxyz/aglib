/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Pullback.SectionPointLift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFiniteModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStageLift
public import Aglib.RingTheory.Henselian.StrictHenselization.BasePoint

/-! # A whole lifted section supplies every finite-source residue mark

Each canonical maximal-localization residue point of the actual finite
Henselian model maps to the original prescribed target point. If that point
lies on the original section, its X-coordinate factors through the section
as a scheme morphism. The unchanged whole lifted section therefore gives
all actual residue-field marks, with their exact original over equations.
No choice of geometric point above a residue point or new residue field is
introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open GeometricNeighborhood

universe u

/-- A finite algebra's canonical component residue point maps to the closed
point of the original local base. This does not require a separably closed
residue field or an extension to an algebraically closed point field. -/
theorem finiteSourceResiduePoint_basePoint
    (S A : Type u) [CommRing S] [IsLocalRing S] [CommRing A]
    [Algebra S A] [Module.Finite S A] (i : MaximalSpectrum A) :
    (finiteSourceResiduePoint A i ≫ Spec.algebraMap S A)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) =
        IsLocalRing.closedPoint S := by
  let : IsLocalHom
      (CommRingCat.ofHom (IsLocalRing.residue (Localization.AtPrime i.asIdeal))).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue (Localization.AtPrime i.asIdeal)))
  change (Spec.algebraMap S A)
    ((Spec.algebraMap A (Localization.AtPrime i.asIdeal))
      ((LocalRing.residueSpecMap (Localization.AtPrime i.asIdeal))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))))) = _
  rw [show LocalRing.residueSpecMap (Localization.AtPrime i.asIdeal)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) =
        IsLocalRing.closedPoint (Localization.AtPrime i.asIdeal) from Spec_closedPoint]
  apply PrimeSpectrum.ext
  change ((IsLocalRing.maximalIdeal (Localization.AtPrime i.asIdeal)).under A).under S =
    IsLocalRing.maximalIdeal S
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime i.asIdeal) i.asIdeal]
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S) i.asIdeal)

/-- The actual neighborhood-ring closed point is the originally selected
field-valued point on the base, on underlying points. -/
theorem geometricColimit_closedPoint_base
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] :
    (Spec.algebraMap R (GeometricEtaleColimit R Ω))
      (IsLocalRing.closedPoint (GeometricEtaleColimit R Ω)) =
        (Spec.algebraMap R Ω) (IsLocalRing.closedPoint Ω) := by
  apply PrimeSpectrum.ext
  change (IsLocalRing.maximalIdeal (GeometricEtaleColimit R Ω)).under R =
    (IsLocalRing.maximalIdeal Ω).under R
  rw [GeometricEtaleColimit.maximalIdeal_under_base, IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- The original residue-field map into the original finite source, using
its actual Henselian model and its native affine reconstruction. -/
def limitResidueMap
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (i : MaximalSpectrum (limitSourceRing R Ω f)) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ X :=
  finiteSourceResiduePoint (limitSourceRing R Ω f) i ≫ limitSourceTargetMap R Ω f

/-- Every original finite-model residue map lies above the same prescribed
target point, not merely some point specializing to it. -/
theorem limitResidueMap_basepoint
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (i : MaximalSpectrum (limitSourceRing R Ω f)) :
    (limitResidueMap R Ω f i ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) =
        (Spec.algebraMap R Ω) (IsLocalRing.closedPoint Ω) := by
  let := limitSourceAlgebra R Ω f
  let : Module.Finite (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) :=
    limitSource_moduleFinite R Ω f
  have hcomm : (baseChangedCone R Ω f).pt.hom ≫ f =
      limitFiniteProjection R Ω f ≫ Spec.algebraMap R (GeometricEtaleColimit R Ω) :=
    (pullback.condition (f := Spec.algebraMap R (GeometricEtaleColimit R Ω))
      (g := f)).symm
  have hbase : limitSourceTargetMap R Ω f ≫ f =
      Spec.algebraMap (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) ≫
        Spec.algebraMap R (GeometricEtaleColimit R Ω) := by
    change ((limitSourceIso R Ω f).hom ≫ (baseChangedCone R Ω f).pt.hom) ≫ f = _
    rw [Category.assoc, hcomm, ← Category.assoc]
    exact congrArg (fun k => k ≫ Spec.algebraMap R (GeometricEtaleColimit R Ω))
      (limitSourceIso_projection R Ω f)
  have hmap : limitResidueMap R Ω f i ≫ f =
      (finiteSourceResiduePoint (limitSourceRing R Ω f) i ≫
        Spec.algebraMap (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f)) ≫
          Spec.algebraMap R (GeometricEtaleColimit R Ω) := by
    dsimp only [limitResidueMap]
    rw [Category.assoc, hbase, Category.assoc]
  calc
    (limitResidueMap R Ω f i ≫ f)
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) =
      (Spec.algebraMap R (GeometricEtaleColimit R Ω))
        ((finiteSourceResiduePoint (limitSourceRing R Ω f) i ≫
            Spec.algebraMap (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f))
          (IsLocalRing.closedPoint
            (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)))) :=
      congrArg (fun k :
        Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
          Spec (.of R) =>
        k (IsLocalRing.closedPoint
          (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)))) hmap
    _ = (Spec.algebraMap R (GeometricEtaleColimit R Ω))
        (IsLocalRing.closedPoint (GeometricEtaleColimit R Ω)) :=
      congrArg (Spec.algebraMap R (GeometricEtaleColimit R Ω))
        (finiteSourceResiduePoint_basePoint
          (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) i)
    _ = _ := geometricColimit_closedPoint_base R Ω

/-- The exact mark supplied by the original whole lifted section on each
canonical residue-field source of the actual finite Henselian model. -/
def wholeSectionResidueMark
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {S V G : Scheme.{u}} (p : Spec (.of R) ⟶ S) (r : V ⟶ S) [IsFinite r]
    (ρ : V ⟶ G)
    (i : MaximalSpectrum (limitSourceRing R Ω (pullback.fst p r))) :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ G :=
  pullback.sectionLiftPoint p r ρ (limitResidueMap R Ω (pullback.fst p r) i)

/-- A whole section lift supplies every actual finite-source residue mark
from the single original target-point condition. The base-changed section,
cover, residue fields and original source maps are all retained. -/
@[reassoc]
theorem wholeSectionResidueMark_over
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {S V G : Scheme.{u}} (p : Spec (.of R) ⟶ S) [IsSeparated p]
    (σ : S ⟶ Spec (.of R)) (hσ : σ ≫ p = 𝟙 S)
    (r : V ⟶ S) [IsFinite r]
    (g : G ⟶ pullback p r) (ρ : V ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (hpoint : (Spec.algebraMap R Ω) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (i : MaximalSpectrum (limitSourceRing R Ω (pullback.fst p r))) :
    wholeSectionResidueMark R Ω p r ρ i ≫ g =
      limitResidueMap R Ω (pullback.fst p r) i := by
  apply pullback.sectionLiftPoint_over p r σ hσ g ρ hρ
  apply pullback_section_condition_of_range_subset p r σ hσ
  rintro _ ⟨x, rfl⟩
  have hx : x = IsLocalRing.closedPoint
      (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)) := Subsingleton.elim _ _
  rw [hx, limitResidueMap_basepoint]
  exact hpoint

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
