/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Descent.CommonSections
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Ordinary Hom descent for the original normalized chart arrows

The actual common principal source ranges cover every point of each
range intersection. Locality of the original Hom sheaf gives matching
sections, and the native section comparison gives the original overlap
equation required for ordinary Hom gluing. No scheme separation is used.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance chartCompatibilityStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] (J : InjectiveResolution (relativeCanonicalModule p n))

local notation "M" => Functor.obj
  (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d))
  (closedImmersionCanonicalValue i p n)
local notation "N" => moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
local notation "H" => InternalHom.sheaf X M N

/-- The original chart Hom sections match on their actual range intersection. -/
theorem canonicalChartHomSection_matching {x y : X}
    (C : SmoothClosedImmersionLocalChart i p n d x)
    (D : SmoothClosedImmersionLocalChart i p n d y) :
    (H).val.presheaf.map (homOfLE
        (inf_le_left : C.quotientSource.opensRange ⊓ D.quotientSource.opensRange ≤
          C.quotientSource.opensRange)).op (canonicalChartHomSection C J) =
      (H).val.presheaf.map (homOfLE
        (inf_le_right : C.quotientSource.opensRange ⊓ D.quotientSource.opensRange ≤
          D.quotientSource.opensRange)).op (canonicalChartHomSection D J) := by
  apply TopCat.Presheaf.IsSheaf.section_ext (H).isSheaf
  intro z hz
  obtain ⟨qC, hqC⟩ := hz.1
  obtain ⟨qD, hqD⟩ := hz.2
  let eC : CommRingCat.of (C.A ⧸ Ideal.ofList C.regularList) ≅ C.B :=
    C.quotientRingEquiv.toCommRingCatIso
  let eD : CommRingCat.of (D.A ⧸ Ideal.ofList D.regularList) ≅ D.B :=
    D.quotientRingEquiv.toCommRingCatIso
  let c : Spec C.B := (Spec.map eC.inv) qC
  let e : Spec D.B := (Spec.map eD.inv) qD
  have hc : C.jX c = z := hqC
  have he : D.jX e = z := hqD
  let C' := C.repoint z c hc
  let D' := D.repoint z e he
  obtain ⟨V, hzV, hVC, hVD, hLocal⟩ := canonicalChartHomSection_common C' D' J
  have hVC₀ : V ≤ C.quotientSource.opensRange := hVC
  have hVD₀ : V ≤ D.quotientSource.opensRange := hVD
  have hV : V ≤ C.quotientSource.opensRange ⊓ D.quotientSource.opensRange :=
    le_inf hVC₀ hVD₀
  have hC : canonicalChartHomSection C J = canonicalChartHomSection C' J :=
    canonicalChartHomSection_repoint C J z c hc
  have hD : canonicalChartHomSection D J = canonicalChartHomSection D' J :=
    canonicalChartHomSection_repoint D J z e he
  have hLocal₀ : (H).val.presheaf.map (homOfLE hVC₀).op (canonicalChartHomSection C J) =
      (H).val.presheaf.map (homOfLE hVD₀).op (canonicalChartHomSection D J) := by
    rw [hC, hD]
    exact hLocal
  refine ⟨V, hV, hzV, ?_⟩
  have hCP : (homOfLE (inf_le_left :
        C.quotientSource.opensRange ⊓ D.quotientSource.opensRange ≤
          C.quotientSource.opensRange)).op ≫ (homOfLE hV).op =
      (homOfLE hVC₀).op := Subsingleton.elim _ _
  have hDP : (homOfLE (inf_le_right :
        C.quotientSource.opensRange ⊓ D.quotientSource.opensRange ≤
          D.quotientSource.opensRange)).op ≫ (homOfLE hV).op =
      (homOfLE hVD₀).op := Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hCP, hDP] using hLocal₀

/-- Any original point-indexed chart choice has the original native overlap compatibility. -/
theorem canonicalChartHomologyIso_compatible
    (C : ∀ x : X, SmoothClosedImmersionLocalChart i p n d x) :
    RestrictionHomCompatible (fun x => (C x).quotientSource) M N
      (fun x => (canonicalCommonModelChartHomologyIso i p n d J (C x)).hom) := by
  apply canonicalRestrictionHomCompatible_of_sections
    (fun x => Spec (regularListQuotientRing (C x).regularList))
    (fun x => (C x).quotientSource) M N
    (fun x => (canonicalCommonModelChartHomologyIso i p n d J (C x)).hom)
  intro x y
  exact canonicalChartHomSection_matching J (C x) (C y)

end AlgebraicGeometry.Scheme.Modules
