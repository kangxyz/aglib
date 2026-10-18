/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseDeterminant.Coefficient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Coefficient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.GeneratorOverlap

/-!
# Actual ordinary canonical arrows under an open change of affine base

The original base determinant square is transported through the actual
coefficient isomorphism. The same inverse-normal contraction and the original
fixed model give the canonical square, independently of both sections frames.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- The original identity-source/base-open differential isomorphism. -/
def canonicalBaseDifferentialIso {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A)
    [IsOpenImmersion (Spec.map ρ)]
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ) :
    relativeDifferentialSheaf (Spec.map (ρ ≫ β)) ≅ relativeDifferentialSheaf (Spec.map β) :=
  restrictFunctorId.symm.app (relativeDifferentialSheaf (Spec.map (ρ ≫ β))) ≪≫
    relativeDifferentialOpenSquareIso (Spec.map (ρ ≫ β)) (𝟙 (Spec A))
      (Spec.map β) (Spec.map ρ) h

/-- This is exactly the previously normalized original geometric base map. -/
theorem canonicalBaseDifferentialIso_hom {R S A : CommRingCat.{u}}
    (ρ : R ⟶ S) (β : S ⟶ A) [IsOpenImmersion (Spec.map ρ)]
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ) :
    (canonicalBaseDifferentialIso ρ β h).hom = canonicalBaseDifferentialSheafMap ρ β h := rfl

private theorem determinantThroughCoefficient {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {L Ω Ω' : C} {X X' : D}
    (E : L ≅ Ω) (u : Ω ≅ Ω') (D₁ : X ≅ P.obj Ω) (D₂ : X' ≅ P.obj Ω')
    (a : X ⟶ X') (h : (D₁).hom ≫ P.map u.hom = a ≫ (D₂).hom) :
    (D₁ ≪≫ P.mapIso E.symm).hom = a ≫ (D₂ ≪≫ P.mapIso (E ≪≫ u).symm).hom := by
  change (D₁).hom ≫ P.map E.inv = a ≫ (D₂).hom ≫ P.map (E ≪≫ u).inv
  have hh := congrArg (fun t => t ≫ P.map (E ≪≫ u).inv) h
  have hc : P.map u.hom ≫ P.map (E ≪≫ u).inv = P.map E.inv := by
    change P.map u.hom ≫ P.map (u.inv ≫ E.inv) = P.map E.inv
    rw [← P.map_comp, u.hom_inv_id_assoc]
  have h₀ := congrArg (fun t => (D₁).hom ≫ t) hc
  exact h₀.symm.trans (by simpa only [Category.assoc] using hh)

section Base
variable {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (s : List A)
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
  (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential (ρ ≫ β)))
  (bA' : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential β))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential ((ρ ≫ β) ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s)))
  {L : (Spec A).Modules}
  (E : L ≅ moduleExteriorPower (Spec A)
    (relativeDifferentialSheaf (Spec.map (ρ ≫ β))) (s.length + d))

local notation "q" => regularListQuotientMap s
local notation "B" => regularListQuotientRing s
local notation "τA" => Functor.mapIso (moduleExteriorPowerFunctor (Spec A) (s.length + d))
  (canonicalBaseDifferentialIso ρ β hα)
local notation "τQ" => Functor.mapIso (moduleExteriorPowerFunctor (Spec B) d)
  (canonicalBaseDifferentialIso ρ (β ≫ q) hβ)
local notation "D₁" => regularListCanonicalCoefficientDeterminantAt (ρ ≫ β) s hs s.length d
  hA hB bA bQ rfl E
local notation "D₂" => regularListCanonicalCoefficientDeterminantAt β s hs s.length d
  hA' hB' bA' bQ' rfl (E ≪≫ τA)

/-- The actual normal-first determinant with the original coefficient sheaf commutes
with the original base-open tangent map. -/
theorem canonicalBaseCoefficientDeterminant :
    (D₁).hom = (moduleTensorLeftFunctor (Spec B)
      (regularListNormalAt (Ideal.ofList s) s.length)).map (τQ).hom ≫ (D₂).hom := by
  have h := canonicalBaseCanonicalDeterminant_geometry ρ β s hα hβ hs
    hA hB hA' hB' bA bA' bQ bQ'
  change (regularListCanonicalDeterminantAt (ρ ≫ β) (Ideal.ofList s) s.length d
      hA hB bA bQ s hs rfl rfl).hom ≫ (pullback (Spec.map q)).map (τA).hom =
    (moduleTensorLeftFunctor (Spec B) (regularListNormalAt (Ideal.ofList s) s.length)).map
      (τQ).hom ≫ (regularListCanonicalDeterminantAt β (Ideal.ofList s) s.length d
        hA' hB' bA' bQ' s hs rfl rfl).hom at h
  exact determinantThroughCoefficient (pullback (Spec.map q)) E τA _ _ _ h

variable [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e f : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]

/-- The actual ordinary canonical maps have base covariance with arbitrary original frames. -/
theorem regularListCanonicalModelMapAt_base :
    regularListCanonicalModelMapAt (ρ ≫ β) (Ideal.ofList s) s.length J e D₁ s hs rfl rfl ≫
      (τQ).hom =
    regularListCanonicalModelMapAt β (Ideal.ofList s) s.length J f D₂ s hs rfl rfl := by
  have hD := canonicalBaseCoefficientDeterminant ρ β s hα hβ hs hA hB hA' hB'
    bA bA' bQ bQ' E
  have h := regularListCanonicalModelTopHomologyIso_baseSquare (ρ ≫ β) β s hs e J
    D₁ D₂ (τQ).hom hD
  have hf := regularListCanonicalModelTopHomologyIso_coefficient_independent β s hs e f J D₂
  exact h.trans hf

end Base
end AlgebraicGeometry.Scheme.Modules
