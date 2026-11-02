/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineModelDescent
public import Aglib.CategoryTheory.Over.SitePullbackPasting

/-! # Actual affine etale models over original affine chart systems

The native global-section cocone of a cofiltered affine scheme limit is an
actual filtered ring colimit. The affine etale ring-model theorem therefore
applies on this affine base. The original affine/spectrum isomorphisms then
retain the actual source and cartesian comparison.

Applied to the native base-change system of a fixed affine open chart, this
gives affine etale models over the original scheme stages by cartesian
pasting. No etale model theorem over a nonaffine base is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

/-- An affine etale object over a cofiltered limit of affine schemes has
an actual affine etale model, retaining the original structural map and
native cartesian comparison. -/
theorem exists_affineEtaleModel_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ c.pt) [Etale f] :
    ∃ (i : I) (M : Scheme.FinitePresentationDescent.Model (c.π.app i) f),
      IsAffine M.X ∧ Etale M.f := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have (i : I) : IsAffine (((Functor.const I).obj c.pt).obj i) :=
    inferInstanceAs (IsAffine c.pt)
  have {i j : I} (q : i ⟶ j) : IsAffineHom (D.map q) := inferInstance
  let F := D.op ⋙ Scheme.Γ
  let C := Scheme.Γ.mapCocone c.op
  have hC : IsColimit C := (nonempty_isColimit_Γ_mapCocone D c hc).some
  let Y' := Over.mk (f ≫ c.pt.isoSpec.hom)
  have hY' : IsAffine Y'.left := inferInstanceAs (IsAffine Y)
  have hEtale : Etale Y'.hom := by
    change Etale (f ≫ c.pt.isoSpec.hom)
    infer_instance
  obtain ⟨i, Z, hZ, hf, ⟨e⟩⟩ :=
    @EtaleAffineBasis.exists_affine_etale_model_of_isColimit _ _ _ F C hC Y' hY' hEtale
  let : IsAffine Z.left := hZ
  let : Etale Z.hom := hf
  let eD : Spec (F.obj i) ≅ D.obj i.unop := (D.obj i.unop).isoSpec.symm
  let fZ : Z.left ⟶ D.obj i.unop := Z.hom ≫ eD.hom
  have hfZ : Etale fZ :=
    @Etale.etale_comp _ _ Z.hom _ eD.hom hf inferInstance
  let M := Scheme.FinitePresentationDescent.Model.ofOverIso Z.hom e
  let M' : Scheme.FinitePresentationDescent.Model (c.π.app i.unop) f := {
    X := Z.left
    f := fZ
    locallyOfFinitePresentation := (Etale.iff_flat_and_formallyUnramified.mp hfZ).2.2
    quasiCompact := inferInstance
    quasiSeparated := inferInstance
    p := M.p
    square := by
      refine M.square.of_iso' (.refl _) (.refl _) c.pt.isoSpec
        (D.obj i.unop).isoSpec ?_ ?_ ?_ ?_
      · exact (Category.comp_id _).symm
      · exact Category.id_comp _
      · change Z.hom = (Z.hom ≫ eD.hom) ≫ (D.obj i.unop).isoSpec.hom
        rw [Category.assoc, show eD.hom ≫ (D.obj i.unop).isoSpec.hom = 𝟙 _ from
          (D.obj i.unop).isoSpec.inv_hom_id]
        exact (Category.comp_id _).symm
      · simpa [F, C] using Scheme.isoSpec_hom_naturality (c.π.app i.unop) }
  exact ⟨i.unop, M', hZ, hfZ⟩

/-- The original chart-cone leg and original base-cone leg form the actual
cartesian chart square at each original stage. -/
theorem chartCone_isPullback
    {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) {V : Scheme.{u}} (j : V ⟶ D.obj i) (a : Over i) :
    IsPullback ((Scheme.baseChangeCone D c i j).π.app a)
      (pullback.fst (c.π.app i) j) (pullback.fst (D.map a.hom) j) (c.π.app a.left) := by
  let p := (Scheme.baseChangeCone D c i j).π.app a
  have hfst : p ≫ pullback.fst (D.map a.hom) j =
      pullback.fst (c.π.app i) j ≫ c.π.app a.left := by
    change pullback.lift (pullback.fst (c.π.app i) j ≫ c.π.app a.left)
      (pullback.snd (c.π.app i) j) _ ≫ pullback.fst (D.map a.hom) j = _
    exact pullback.lift_fst _ _ _
  have hsnd : p ≫ pullback.snd (D.map a.hom) j = pullback.snd (c.π.app i) j := by
    change pullback.lift (pullback.fst (c.π.app i) j ≫ c.π.app a.left)
      (pullback.snd (c.π.app i) j) _ ≫ pullback.snd (D.map a.hom) j = _
    exact pullback.lift_snd _ _ _
  exact IsPullback.of_two_pullback_projections
    (IsPullback.of_hasPullback (c.π.app i) j)
    (IsPullback.of_hasPullback (D.map a.hom) j)
    p (c.π.app a.left) (c.w a.hom) hfst hsnd

/-- Affine etale objects on the actual pullback of a fixed affine open chart
have affine etale models over an original scheme stage. The returned square
uses the literal original global map, not a replacement coefficient map. -/
theorem exists_affineEtaleModel_onChart
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ D.obj i) [IsOpenImmersion j]
    {Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ pullback (c.π.app i) j) [Etale f] :
    ∃ (a : Over i) (Z : Scheme.{u}) (g : Z ⟶ D.obj a.left) (p : Y ⟶ Z),
      IsAffine Z ∧ Etale g ∧
      IsPullback p (f ≫ pullback.fst (c.π.app i) j) g (c.π.app a.left) := by
  let E := Scheme.baseChangeDiagram D i j
  let C := Scheme.baseChangeCone D c i j
  have hE (a : Over i) : IsAffine (E.obj a) := by
    change IsAffine (pullback (D.map a.hom) j)
    let P : MorphismProperty Scheme.{u} := @IsAffineHom
    let : P.IsStableUnderBaseChange := isAffineHom_isStableUnderBaseChange
    have hsnd : IsAffineHom (pullback.snd (D.map a.hom) j) :=
      MorphismProperty.pullback_snd (P := P) _ _
        (inferInstanceAs (IsAffineHom (D.map a.hom)))
    exact @isAffine_of_isAffineHom _ V _ hsnd inferInstance
  obtain ⟨a, M, hM, hf⟩ := @exists_affineEtaleModel_of_isLimit _ _ _ E hE C
    (Scheme.isLimitBaseChangeCone D c hc i j) Y inferInstance f
      (inferInstanceAs (Etale f))
  let : Etale M.f := hf
  let g := M.f ≫ pullback.fst (D.map a.hom) j
  let P : MorphismProperty Scheme.{u} := @Etale
  let : P.IsStableUnderBaseChange := Etale.etale_isStableUnderBaseChange
  have hfst : Etale (pullback.fst (D.map a.hom) j) :=
    MorphismProperty.pullback_fst (P := P) _ _ (inferInstanceAs (Etale j))
  have hg : Etale g := @Etale.etale_comp _ _ M.f _
    (pullback.fst (D.map a.hom) j) hf hfst
  exact ⟨a, M.X, g, M.p, hM, hg,
    M.square.paste_vert (chartCone_isPullback D c i j a)⟩

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
