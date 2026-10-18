/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Descent.Compatibility
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Purity
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Gluing
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Smooth

/-!
# The canonical bundle of a smooth closed subscheme

The original normalized local homology arrows descend in the ordinary
module-Hom sheaf. Native concentration then reconstructs the independently
installed right-adjoint object as the cotangent determinant in the integer
degree `n - d`. The reconstruction retains the original local maps.

All commutative bases, zero rings, empty sources and relative dimension
zero are included. No Noetherian or global dimension-inequality premise
is imposed. A supplied projective-space square supplies ambient smoothness.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u v w
namespace AlgebraicGeometry.Scheme.Modules

private theorem reconstructedHomology {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : DerivedCategory.Plus C) (c : ℤ)
    [K.IsGE c] [K.IsLE c] (N : C)
    (e : (DerivedCategory.Plus.homologyFunctor C c).obj K ≅ N) :
    (DerivedCategory.Plus.homologyFunctor C c).map
        (DerivedCategory.Plus.isoSingleHomology K c ≪≫
          (DerivedCategory.Plus.singleFunctor C c).mapIso e).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso c).hom.app N = e.hom := by
  let H := DerivedCategory.Plus.homologyFunctor C c
  let S := DerivedCategory.Plus.singleFunctor C c
  let E := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) c
  have hK : H.map (DerivedCategory.Plus.isoSingleHomology K c).hom ≫
      E.hom.app (H.obj K) = 𝟙 _ := by
    change (DerivedCategory.homologyFunctor C c).map
        ((DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C).map
          (DerivedCategory.Plus.isoSingleHomology K c).hom) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C c).hom.app
        ((DerivedCategory.homologyFunctor C c).obj
          ((DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C).obj K)) = 𝟙 _
    rw [DerivedCategory.Plus.ι_map_isoSingleHomology_hom]
    exact DerivedCategory.isoSingleHomology_homology _ c
  have he := E.hom.naturality e.hom
  change H.map (S.map e.hom) ≫ E.hom.app N = E.hom.app (H.obj K) ≫ e.hom at he
  change H.map ((DerivedCategory.Plus.isoSingleHomology K c).hom ≫ S.map e.hom) ≫
    E.hom.app N = e.hom
  rw [H.map_comp, Category.assoc, he, ← Category.assoc, hK, Category.id_comp]

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance globalCanonicalStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ)

section Smooth
variable [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension d (i ≫ p)]

/-- The actual ordinary homology isomorphism obtained by descending the original local arrows. -/
def smoothClosedImmersionCanonicalHomologyIso :
    (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
        (closedImmersionCanonicalValue i p n) ≅
      moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d := by
  let J := injectiveResolution (relativeCanonicalModule p n)
  let C (x : X) := smoothClosedImmersionLocalChart i p n d x
  let V (x : X) := Spec (regularListQuotientRing (C x).regularList)
  let a (x : X) : V x ⟶ X := (C x).quotientSource
  let : ∀ x, IsOpenImmersion (a x) := fun _ => inferInstance
  have hcover : ∀ x : X, ∃ (y : X) (z : V y), a y z = x :=
    fun x => ⟨x, (C x).quotientChart.point, (C x).quotientChart.point_eq⟩
  exact canonicalHomologyGlueIso V a hcover _ _
    (fun x => canonicalCommonModelChartHomologyIso i p n d J (C x))
    (canonicalChartHomologyIso_compatible J C)

/-- The descended map restricts to the same original class-normalized chart isomorphism. -/
theorem smoothClosedImmersionCanonicalHomologyIso_restrict (x : X) :
    let C := smoothClosedImmersionLocalChart i p n d x
    (restrictFunctor C.quotientSource).mapIso
        (smoothClosedImmersionCanonicalHomologyIso i p n d) =
      canonicalCommonModelChartHomologyIso i p n d
        (injectiveResolution (relativeCanonicalModule p n)) C := by
  let J := injectiveResolution (relativeCanonicalModule p n)
  let C (x : X) := smoothClosedImmersionLocalChart i p n d x
  let V (x : X) := Spec (regularListQuotientRing (C x).regularList)
  let a (x : X) : V x ⟶ X := (C x).quotientSource
  let : ∀ x, IsOpenImmersion (a x) := fun _ => inferInstance
  have hcover : ∀ x : X, ∃ (y : X) (z : V y), a y z = x :=
    fun x => ⟨x, (C x).quotientChart.point, (C x).quotientChart.point_eq⟩
  exact canonicalHomologyGlueIso_restrict V a hcover _ _
    (fun x => canonicalCommonModelChartHomologyIso i p n d J (C x))
    (canonicalChartHomologyIso_compatible J C) x

/-- The installed native right adjoint at the ambient canonical single is the actual
cotangent canonical sheaf in the integer codimension. -/
def smoothClosedImmersionCanonicalIso :
    closedImmersionCanonicalValue i p n ≅
      (DerivedCategory.Plus.singleFunctor X.Modules ((n : ℤ) - d)).obj
        (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d) := by
  let := smoothClosedImmersionCanonical_isGE i p n d
  let := smoothClosedImmersionCanonical_isLE i p n d
  exact canonicalIsoOfHomology (closedImmersionCanonicalValue i p n) ((n : ℤ) - d) _
    (smoothClosedImmersionCanonicalHomologyIso i p n d)

/-- Native single reconstruction induces exactly the descended original homology map. -/
theorem smoothClosedImmersionCanonicalIso_homology :
    (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).map
        (smoothClosedImmersionCanonicalIso i p n d).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso ((n : ℤ) - d)).hom.app
        (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d) =
      (smoothClosedImmersionCanonicalHomologyIso i p n d).hom := by
  let := smoothClosedImmersionCanonical_isGE i p n d
  let := smoothClosedImmersionCanonical_isLE i p n d
  exact reconstructedHomology (closedImmersionCanonicalValue i p n) ((n : ℤ) - d) _
    (smoothClosedImmersionCanonicalHomologyIso i p n d)

/-- The actual derived comparison carries the original local evaluation-one map. -/
theorem smoothClosedImmersionCanonicalIso_homology_restrict (x : X) :
    let C := smoothClosedImmersionLocalChart i p n d x
    (restrictFunctor C.quotientSource).map
      ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).map
          (smoothClosedImmersionCanonicalIso i p n d).hom ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso ((n : ℤ) - d)).hom.app
          (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d)) =
    (canonicalCommonModelChartHomologyIso i p n d
      (injectiveResolution (relativeCanonicalModule p n)) C).hom := by
  have h := congrArg
    ((restrictFunctor (smoothClosedImmersionLocalChart i p n d x).quotientSource).map)
    (smoothClosedImmersionCanonicalIso_homology i p n d)
  have hr := congrArg Iso.hom (smoothClosedImmersionCanonicalHomologyIso_restrict i p n d x)
  exact h.trans hr

end Smooth

section Projective
variable (R : Type u) [CommRing R] (ι : Type u) (e : ι ≃ Fin (n + 1))
  (a : P ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (CommRingCat.of R))
  (h : IsPullback a p (ProjectiveSpace.toSpec R ι) f)
  [SmoothOfRelativeDimension d (i ≫ p)]

/-- A supplied projective-space realization gives the same actual canonical comparison,
with ambient smoothness derived from the original polynomial coordinate charts. -/
def projectiveClosedImmersionCanonicalIso :
    closedImmersionCanonicalValue i p n ≅
      (DerivedCategory.Plus.singleFunctor X.Modules ((n : ℤ) - d)).obj
        (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d) := by
  let : SmoothOfRelativeDimension n p :=
    ProjectiveSpace.smoothOfRelativeDimension_of_isPullback R ι n e a p f h
  exact smoothClosedImmersionCanonicalIso i p n d

end Projective
end AlgebraicGeometry.Scheme.Modules
