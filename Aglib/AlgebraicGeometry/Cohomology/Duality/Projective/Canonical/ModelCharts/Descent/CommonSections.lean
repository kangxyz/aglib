/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Descent.ChartSections
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.CommonData

/-!
# Equality of the original Hom sections near a common source point

Actual base and ambient principal refinements give charts with the same
native data and ideal. Their original normalized maps agree. Restriction
of the Hom sheaf transports this equality back to both original charts.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem sectionRestrictTrans {X : Scheme.{u}}
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : F.obj (op U)) (t : F.obj (op V)) (w : F.obj (op W))
    (hs : F.map (homOfLE hVU).op s = t) (ht : F.map (homOfLE hWV).op t = w) :
    F.map (homOfLE (hWV.trans hVU)).op s = w := by
  have hh := (congrArg (fun z => F.map (homOfLE hWV).op z) hs).trans ht
  have hPath : (homOfLE hVU).op ≫ (homOfLE hWV).op =
      (homOfLE (hWV.trans hVU)).op := Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hPath] using hh

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance commonSectionsStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X}
  (C D : SmoothClosedImmersionLocalChart i p n d x)
  (J : InjectiveResolution (relativeCanonicalModule p n))

local notation "M" => Functor.obj
  (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d))
  (closedImmersionCanonicalValue i p n)
local notation "N" => moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
local notation "H" => InternalHom.sheaf X M N

/-- Original normalized Hom sections agree on an actual common open containing the point. -/
theorem canonicalChartHomSection_common :
    ∃ V : X.Opens, x ∈ V ∧
      ∃ (hVC : V ≤ C.quotientSource.opensRange) (hVD : V ≤ D.quotientSource.opensRange),
        (H).val.presheaf.map (homOfLE hVC).op (canonicalChartHomSection C J) =
          (H).val.presheaf.map (homOfLE hVD).op (canonicalChartHomSection D J) := by
  obtain ⟨r, s, hr, hs, eR, _hBase, hRest⟩ :=
    SmoothClosedImmersionLocalChart.exists_canonicalCommonRefinementData C D
  let C₀ := C.basePrincipalChart r hr
  let Db := D.basePrincipalChart s hs
  let D₀ := Db.baseIsoChart eR
  obtain ⟨a, b, ha, hb, eA, _hAmbient, hData⟩ := hRest
  let C₁ := C₀.principalChart a ha
  let D₁ := D₀.principalChart b hb
  let D₂ := D₁.ambientIsoChart eA
  obtain ⟨hR, hA, hα, hY, hP, hI⟩ := hData
  have hC₀ : C₀.quotientSource.opensRange ≤ C.quotientSource.opensRange :=
    canonicalPrincipalChart_range_le C (C.α r) hr
  have hD₀ : D₀.quotientSource.opensRange ≤ D.quotientSource.opensRange :=
    canonicalPrincipalChart_range_le D (D.α s) hs
  have hC₁ : C₁.quotientSource.opensRange ≤ C₀.quotientSource.opensRange :=
    canonicalPrincipalChart_range_le C₀ a ha
  have hD₁ : D₁.quotientSource.opensRange ≤ D₀.quotientSource.opensRange :=
    canonicalPrincipalChart_range_le D₀ b hb
  have hD₂ : D₂.quotientSource.opensRange ≤ D₁.quotientSource.opensRange :=
    canonicalAmbientIsoChart_range_le D₁ eA
  obtain ⟨hCD, hSame⟩ := canonicalChartHomSection_sameData C₁ J D₂ hR hA hα hY hP hI
  have hsC₀ : (H).val.presheaf.map (homOfLE hC₀).op (canonicalChartHomSection C J) =
      canonicalChartHomSection C₀ J :=
    (canonicalChartHomSection_principal C J (C.α r) hr).trans
      (canonicalChartHomSection_basePrincipal C J r hr)
  have hsD₀ : (H).val.presheaf.map (homOfLE hD₀).op (canonicalChartHomSection D J) =
      canonicalChartHomSection D₀ J :=
    (canonicalChartHomSection_principal D J (D.α s) hs).trans
      ((canonicalChartHomSection_basePrincipal D J s hs).trans
        (canonicalChartHomSection_baseIso Db J eR))
  have hsC₁ := sectionRestrictTrans (H).val.presheaf hC₀ hC₁
    (canonicalChartHomSection C J) (canonicalChartHomSection C₀ J)
    (canonicalChartHomSection C₁ J) hsC₀ (canonicalChartHomSection_principal C₀ J a ha)
  have hsD₁ := sectionRestrictTrans (H).val.presheaf hD₀ hD₁
    (canonicalChartHomSection D J) (canonicalChartHomSection D₀ J)
    (canonicalChartHomSection D₁ J) hsD₀ (canonicalChartHomSection_principal D₀ J b hb)
  have hsD₂ := sectionRestrictTrans (H).val.presheaf (hD₁.trans hD₀) hD₂
    (canonicalChartHomSection D J) (canonicalChartHomSection D₁ J)
    (canonicalChartHomSection D₂ J) hsD₁ (canonicalChartHomSection_ambientIso D₁ J eA)
  have hsDC := sectionRestrictTrans (H).val.presheaf (hD₂.trans (hD₁.trans hD₀)) hCD
    (canonicalChartHomSection D J) (canonicalChartHomSection D₂ J)
    (canonicalChartHomSection C₁ J) hsD₂ hSame
  refine ⟨C₁.quotientSource.opensRange, ?_, hC₁.trans hC₀,
    hCD.trans (hD₂.trans (hD₁.trans hD₀)), hsC₁.trans hsDC.symm⟩
  exact ⟨C₁.quotientChart.point, C₁.quotientChart.point_eq⟩

end AlgebraicGeometry.Scheme.Modules
