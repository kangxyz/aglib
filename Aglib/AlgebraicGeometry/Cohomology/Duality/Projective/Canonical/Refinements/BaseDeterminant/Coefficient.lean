/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.GeneratorOverlap
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseDeterminant
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseCoefficient

/-!
# Base covariance of the actual canonical determinant

The original conormal determinant square and the actual ambient coefficient
bridge square compose. Thus the determinant used by the installed native
canonical map, including its pulled-back ambient coefficient, has the same
base covariance.
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

private theorem composeDeterminantSquares {C : Type*} [Category C]
    {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g') :
    (f ≫ g) ≫ c = a ≫ (f' ≫ g') := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private theorem composeCanonicalSquares {C : Type*} [Category C]
    {X Y Z X' Y' Z' : C}
    {D : X ⟶ Z} {D' : X' ⟶ Z'}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X ⟶ X'} {b : Y ⟶ Y'} {c : Z ⟶ Z'}
    (hD : D = f ≫ g) (hD' : D' = f' ≫ g')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g') :
    D ≫ c = a ≫ D' := by
  rw [hD, hD']
  exact composeDeterminantSquares f g f' g' a b c hf hg

private theorem isoHom_composite {C : Type*} [Category C] {X Y Z : C}
    (D : X ≅ Z) (Δ : X ≅ Y) (E : Y ≅ Z) (h : D = Δ ≪≫ E) :
    D.hom = Δ.hom ≫ E.hom := congrArg Iso.hom h

private theorem canonicalDeterminant_hom
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth) {d : ℕ}
    (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s))) :
    (regularListCanonicalDeterminantAt α (Ideal.ofList s) s.length d
      hA hB bA bQ s hs rfl rfl).hom =
      (regularListConormalDeterminantAt α (Ideal.ofList s) s.length d
        hA hB bQ s hs rfl rfl).hom ≫
      (affineConormalAmbientCoefficientIso α s (s.length + d) bA).hom :=
  isoHom_composite _ _ _ (affineRegularListCanonicalDeterminant_eq α s hs hA hB bA bQ)

private theorem mappedDeterminantSquare {C D E : Type*}
    [Category C] [Category D] [Category E] (P : D ⥤ C) (T : E ⥤ C)
    {X X' : D} {Y Y' : E} (f : T.obj Y ⟶ P.obj X) (g : T.obj Y' ⟶ P.obj X')
    {a a' : X ⟶ X'} {b b' : Y ⟶ Y'} (ha : a = a') (hb : b = b')
    (h : f ≫ P.map a' = T.map b' ≫ g) : f ≫ P.map a = T.map b ≫ g := by
  rw [ha, hb]
  exact h

/-- The actual canonical determinant, including its original ambient coefficient bridge,
commutes with the original base differential arrows. -/
def CanonicalBaseDeterminantSquare
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hA : (ρ ≫ β).hom.FormallySmooth)
    (hB : ((ρ ≫ β) ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : β.hom.FormallySmooth) (hB' : (β ≫ regularListQuotientMap s).hom.FormallySmooth)
    {d : ℕ}
    (bA : Module.Basis (Fin (s.length + d)) A
      (CommRingCat.KaehlerDifferential (ρ ≫ β)))
    (bA' : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential β))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential ((ρ ≫ β) ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s))) : Prop :=
    let B := regularListQuotientRing s
    let q := regularListQuotientMap s
    let α := ρ ≫ β
    let τA := (relativeDifferentialAffineIso α).hom ≫
      (tilde.functor A).map (canonicalBaseDifferentialMap ρ β) ≫
        (relativeDifferentialAffineIso β).inv
    let τQ := (relativeDifferentialAffineIso (α ≫ q)).hom ≫
      (tilde.functor B).map (canonicalBaseDifferentialMap ρ (β ≫ q)) ≫
        (relativeDifferentialAffineIso (β ≫ q)).inv
    (regularListCanonicalDeterminantAt α (Ideal.ofList s) s.length d
      hA hB bA bQ s hs rfl rfl).hom ≫
        (pullback (Spec.map q)).map
          ((moduleExteriorPowerFunctor (Spec A) (s.length + d)).map τA) =
      (moduleTensorLeftFunctor (Spec B)
        (regularListNormalAt (Ideal.ofList s) s.length)).map
          ((moduleExteriorPowerFunctor (Spec B) d).map τQ) ≫
        (regularListCanonicalDeterminantAt β (Ideal.ofList s) s.length d
          hA' hB' bA' bQ' s hs rfl rfl).hom

/-- The actual canonical determinant, including its original ambient coefficient bridge,
commutes with the original base differential arrows. -/
theorem canonicalBaseCanonicalDeterminant
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hA : (ρ ≫ β).hom.FormallySmooth)
    (hB : ((ρ ≫ β) ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : β.hom.FormallySmooth) (hB' : (β ≫ regularListQuotientMap s).hom.FormallySmooth)
    {d : ℕ}
    (bA : Module.Basis (Fin (s.length + d)) A
      (CommRingCat.KaehlerDifferential (ρ ≫ β)))
    (bA' : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential β))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential ((ρ ≫ β) ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s))) :
    CanonicalBaseDeterminantSquare ρ β s hs hA hB hA' hB' bA bA' bQ bQ' := by
  exact composeCanonicalSquares
    (canonicalDeterminant_hom (ρ ≫ β) s hs hA hB bA bQ)
    (canonicalDeterminant_hom β s hs hA' hB' bA' bQ')
    (canonicalBaseConormalDeterminant ρ β s hs hA hB hA' hB' bQ bQ')
    (canonicalBaseAmbientCoefficient ρ β s (s.length + d) bA bA')

/-- The same actual canonical determinant square uses both original geometric
base-open differential comparisons. -/
def CanonicalBaseDeterminantGeometrySquare
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A)
    [IsOpenImmersion (Spec.map ρ)]
    (hα : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ)
    (hβ : 𝟙 (Spec (regularListQuotientRing s)) ≫
      Spec.map (ρ ≫ (β ≫ regularListQuotientMap s)) =
        Spec.map (β ≫ regularListQuotientMap s) ≫ Spec.map ρ)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hA : (ρ ≫ β).hom.FormallySmooth)
    (hB : ((ρ ≫ β) ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : β.hom.FormallySmooth) (hB' : (β ≫ regularListQuotientMap s).hom.FormallySmooth)
    {d : ℕ}
    (bA : Module.Basis (Fin (s.length + d)) A
      (CommRingCat.KaehlerDifferential (ρ ≫ β)))
    (bA' : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential β))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential ((ρ ≫ β) ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s))) : Prop :=
    let B := regularListQuotientRing s
    let q := regularListQuotientMap s
    let α := ρ ≫ β
    (regularListCanonicalDeterminantAt α (Ideal.ofList s) s.length d
      hA hB bA bQ s hs rfl rfl).hom ≫
        (pullback (Spec.map q)).map
          ((moduleExteriorPowerFunctor (Spec A) (s.length + d)).map
            (canonicalBaseDifferentialSheafMap ρ β hα)) =
      (moduleTensorLeftFunctor (Spec B)
        (regularListNormalAt (Ideal.ofList s) s.length)).map
          ((moduleExteriorPowerFunctor (Spec B) d).map
            (canonicalBaseDifferentialSheafMap ρ (β ≫ q) hβ)) ≫
        (regularListCanonicalDeterminantAt β (Ideal.ofList s) s.length d
          hA' hB' bA' bQ' s hs rfl rfl).hom

/-- The same actual canonical determinant square uses both original geometric
base-open differential comparisons. -/
theorem canonicalBaseCanonicalDeterminant_geometry
    {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A)
    [IsOpenImmersion (Spec.map ρ)]
    (hα : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ)
    (hβ : 𝟙 (Spec (regularListQuotientRing s)) ≫
      Spec.map (ρ ≫ (β ≫ regularListQuotientMap s)) =
        Spec.map (β ≫ regularListQuotientMap s) ≫ Spec.map ρ)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hA : (ρ ≫ β).hom.FormallySmooth)
    (hB : ((ρ ≫ β) ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : β.hom.FormallySmooth) (hB' : (β ≫ regularListQuotientMap s).hom.FormallySmooth)
    {d : ℕ}
    (bA : Module.Basis (Fin (s.length + d)) A
      (CommRingCat.KaehlerDifferential (ρ ≫ β)))
    (bA' : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential β))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential ((ρ ≫ β) ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s))) :
    CanonicalBaseDeterminantGeometrySquare ρ β s hα hβ hs hA hB hA' hB' bA bA' bQ bQ' := by
  let P := moduleExteriorPowerFunctor (Spec A) (s.length + d) ⋙
    pullback (Spec.map (regularListQuotientMap s))
  let T := moduleExteriorPowerFunctor (Spec (regularListQuotientRing s)) d ⋙
    moduleTensorLeftFunctor (Spec (regularListQuotientRing s))
      (regularListNormalAt (Ideal.ofList s) s.length)
  exact mappedDeterminantSquare P T _ _
    (canonicalBaseDifferentialMap_geometry ρ β hα)
    (canonicalBaseDifferentialMap_geometry ρ (β ≫ regularListQuotientMap s) hβ)
    (canonicalBaseCanonicalDeterminant ρ β s hs hA hB hA' hB' bA bA' bQ bQ')

end AlgebraicGeometry.Scheme.Modules
