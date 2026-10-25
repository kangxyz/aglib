/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.ModelClosure
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.AffineEtaleModels
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-! # Original free-generator models from actual affine chart models

A free generator whose original affine etale source lies on the pullback
of one fixed affine open chart has a native canonical stage model. The
comparison uses the actual cartesian scheme model, the original site base
change, and the already proved original free-generator inverse-image iso.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

/-- The actual model property is closed under finite colimits in the small
native shapes used by the original two-chart cokernel presentation. -/
theorem hasStageModel_closedFiniteColimits
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
    [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop]
    (hc : IsColimit c) (n : ℕ) :
    (HasStageModel X c n).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ := by
    let K := ULiftHom.{u + 1} (ULift.{u + 1} J)
    let e : J ≌ K := ULiftHomULiftCategory.equiv J
    rw [(HasStageModel X c n).isClosedUnderColimitsOfShape_iff_of_equivalence e]
    exact ⟨fun _ ⟨p⟩ => hasStageModel_of_finiteColimit X c n hc p⟩

/-- An actual single model supplies actual models above every specified
stage by affine base change and the original cone-composition comparison. -/
theorem hasStageModel_of_oneModel
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
    [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop]
    (n : ℕ) (i : I) (M : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hM : BoundedPresentation.finiteColimitStages (X.obj i).unop n M)
    {A : BoundedPresentation.Coefficient c.pt.unop n}
    (e : (boundedInverseImage (c.ι.app i).unop n).obj M ≅ A) :
    HasStageModel X c n A := by
  intro i₀
  let j := IsFiltered.max i₀ i
  let q : i ⟶ j := IsFiltered.rightToMax i₀ i
  let N := (boundedInverseImage (X.map q).unop n).obj M
  have hN : BoundedPresentation.finiteColimitStages (X.obj j).unop n N :=
    finiteColimitStage_inverseImage (X.map q).unop n M hM
  exact ⟨j, IsFiltered.leftToMax i₀ i, N, hN,
    ⟨((boundedConeCompIso X c n q).app M).symm ≪≫ e⟩⟩

/-- A free generator on an original affine etale source lying in one fixed
affine chart pullback has an actual canonical stage model. The factorization
and etaleness are on its original chart map. -/
theorem free_hasStageModel_of_chart_factorization
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ D.obj i) [IsOpenImmersion j]
    (U : c.pt.Etale) [IsAffine U.left]
    (f : U.left ⟶ pullback (c.π.app i) j) [Etale f]
    (hf : f ≫ pullback.fst (c.π.app i) j = U.hom) (n : ℕ) :
    HasStageModel D.op c.op n (BoundedPresentation.free c.pt n U) := by
  obtain ⟨a, Z, g, p, hZ, hg, H⟩ :=
    exists_affineEtaleModel_onChart D c hc i j f
  let : IsAffine Z := hZ
  let : Etale g := hg
  have H' : IsPullback p U.hom g (c.π.app a.left) := by
    simpa only [hf] using H
  let G : (D.obj a.left).Etale := Scheme.Etale.mk g
  have : IsAffine G.left := hZ
  let Vᵢ := EtaleAffineBasis.affineModel G
  let E := siteBaseChange (c.π.app a.left)
  let e₀ : E.obj G ≅ U :=
    MorphismProperty.Over.isoMk H'.isoPullback.symm H'.isoPullback_inv_snd
  let e : E.obj ((Scheme.AffineEtale.Spec (D.obj a.left)).obj Vᵢ) ≅ U :=
    E.mapIso (EtaleAffineBasis.affineModelIso G) ≪≫ e₀
  let M := BoundedPresentation.free (D.obj a.left) n
    ((Scheme.AffineEtale.Spec (D.obj a.left)).obj Vᵢ)
  have hM : BoundedPresentation.finiteColimitStages (D.obj a.left) n M :=
    (BoundedPresentation.generators (D.obj a.left) n).le_colimitsCardinalClosure
      Cardinal.aleph0.{u + 1} _ ⟨Vᵢ⟩
  have {k l : Iᵒᵖ} (q : k ⟶ l) : IsAffineHom (D.op.map q).unop :=
    inferInstanceAs (IsAffineHom (D.map q.unop))
  apply hasStageModel_of_oneModel D.op c.op n (op a.left) M hM
  exact boundedIso
    (freeZModRepresentableInverseImageIso (c.π.app a.left) n
      ((Scheme.AffineEtale.Spec (D.obj a.left)).obj Vᵢ) ≪≫
        freeZModRepresentableIsoOfEtaleIso n e)

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
