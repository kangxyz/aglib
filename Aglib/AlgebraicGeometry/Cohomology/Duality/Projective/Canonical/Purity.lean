/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Charts
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers

/-!
# Concentration of the installed smooth closed right adjoint

The actual regular charts and the actual derived restriction comparison
prove concentration of the independently installed right-adjoint object in
the integer degree `n - d`. No regular-list, frame, comparison-family,
Noetherianity, or global dimension-inequality premise is added.

The native homology comparisons also give the original local ordinary
homology arrows to the restricted tangent determinant. Their overlap
equality remains the condition to prove before gluing the canonical map.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance canonicalPurityStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The ordinary local top-homology arrow of the installed global right-adjoint object. -/
@[no_expose] def smoothClosedImmersionChartTopHomologyIso :
    let Q := C.quotientChart
    ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)).restrict Q.jX ≅
        (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict Q.jX := by
  let Q := C.quotientChart
  let c : ℤ := (n : ℤ) - d
  let K := closedImmersionCanonicalValue i p n
  let T := (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict Q.jX
  exact ((restrictFunctor Q.jX).rightDerivedFunctorPlusHomologyIso c).symm.app K ≪≫
    (DerivedCategory.Plus.homologyFunctor (Spec Q.B).Modules c).mapIso
      (smoothClosedImmersionChartCanonicalIso i p n d C) ≪≫
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := (Spec Q.B).Modules) c).app T

section Smooth
variable [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension d (i ≫ p)]

/-- The installed native right adjoint has no homology below the geometric codimension. -/
theorem smoothClosedImmersionCanonical_isGE :
    (closedImmersionCanonicalValue i p n).IsGE ((n : ℤ) - d) := by
  let C (x : X) := smoothClosedImmersionLocalChart i p n d x
  let Q (x : X) := (C x).quotientChart
  let V (x : X) := Spec (Q x).B
  let a (x : X) : V x ⟶ X := (Q x).jX
  let : ∀ x, IsOpenImmersion (a x) := fun x => (Q x).openX
  have hc : ∀ x : X, ∃ (k : X) (y : V k), a k y = x :=
    fun x => ⟨x, (Q x).point, (Q x).point_eq⟩
  apply canonical_isGE_of_derivedRestriction V a hc
  intro x
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (smoothClosedImmersionChartCanonicalIso i p n d (C x)).symm ((n : ℤ) - d)

/-- The installed native right adjoint has no homology above the geometric codimension. -/
theorem smoothClosedImmersionCanonical_isLE :
    (closedImmersionCanonicalValue i p n).IsLE ((n : ℤ) - d) := by
  let C (x : X) := smoothClosedImmersionLocalChart i p n d x
  let Q (x : X) := (C x).quotientChart
  let V (x : X) := Spec (Q x).B
  let a (x : X) : V x ⟶ X := (Q x).jX
  let : ∀ x, IsOpenImmersion (a x) := fun x => (Q x).openX
  have hc : ∀ x : X, ∃ (k : X) (y : V k), a k y = x :=
    fun x => ⟨x, (Q x).point, (Q x).point_eq⟩
  apply canonical_isLE_of_derivedRestriction V a hc
  intro x
  exact DerivedCategory.Plus.TStructure.t.isLE_of_iso
    (smoothClosedImmersionChartCanonicalIso i p n d (C x)).symm ((n : ℤ) - d)

end Smooth
end AlgebraicGeometry.Scheme.Modules
