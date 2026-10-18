/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.GeneratorOverlap
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion.Degree

/-!
# The fixed-ideal arrow and the same common-normal model

On the literal list quotient, the original genuine ideal and degree
transport gives the same common-normal arrow. The normal determinant is
transported through the same original exterior-degree isomorphism.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- The original fixed-ideal model arrow is the same original common-normal map. -/
theorem regularListCanonicalModelMapAt_eq_commonNormal
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    [HasExt.{w} (ModuleCat.{u} A)] (c : ℕ) (hc : s.length = c)
    {Q : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalLineInDegree α s hs c hc).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    regularListCanonicalModelMapAt α (Ideal.ofList s) c J e Δ s hs rfl hc =
      (regularListCanonicalModelTopHomologyIsoCommonNormal α s hs J e c hc Δ).hom := by
  subst c
  have hΔ : regularListDeterminantFromCommonNormal α s hs s.length rfl Δ = Δ := by
    apply Iso.ext
    change ((SheafOfModulesOfCommRing.tensorFunctor
      (Spec (regularListQuotientRing s)).sheaf).map (𝟙 _)).app Q ≫ Δ.hom = Δ.hom
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  have hCommon : regularListCanonicalModelTopHomologyIsoCommonNormal α s hs J e
      s.length rfl Δ = regularListCanonicalModelTopHomologyIso s hs e α J Δ := by
    apply Iso.ext
    change (𝟙 _) ≫ (regularListCanonicalModelTopHomologyIso s hs e α J
      (regularListDeterminantFromCommonNormal α s hs s.length rfl Δ)).hom = _
    exact (Category.id_comp _).trans
      (congrArg (fun D => (regularListCanonicalModelTopHomologyIso s hs e α J D).hom) hΔ)
  exact (congrArg Iso.hom hCommon).symm

end AlgebraicGeometry.Scheme.Modules
