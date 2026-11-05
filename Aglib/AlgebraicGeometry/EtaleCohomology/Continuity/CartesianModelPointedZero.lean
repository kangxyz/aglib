/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PointedTransferZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.IsoTriangleClassTransport

/-! # Retaining pointed local zeros through actual Cartesian models

An isomorphism of source schemes over the original coefficient base determines
the isomorphism of the original Cartesian families. The coefficient triangle
and cohomology class are transported by their canonical comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- A source reconstruction over the unchanged base transports a model's
pointed zero to the original Cartesian family and original class. -/
theorem exists_pointed_zero_of_cartesian_model
    {S T X Xm Y Ym P : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Ym)]
    (a : Y ⟶ X) (b : Y ⟶ T) (g : X ⟶ S) (f : T ⟶ S)
    (H : IsPullback a b g f)
    (am : Ym ⟶ Xm) (bm : Ym ⟶ T) (gm : Xm ⟶ S)
    (Hm : IsPullback am bm gm f)
    (E : X ≅ Xm) (hE : E.hom ≫ gm = g)
    (F : AbelianSheaf.{u, u + 1} T) (q : ℕ)
    (c : Sheaf.H.{e} ((inverseImage b).obj F) q) (x : P ⟶ X)
    (hzero : ∀ d : Sheaf.H.{e} ((inverseImage bm).obj F) q,
      ∃ (U : Xm.Etale) (xU : P ⟶ U.left), xU ≫ U.hom = x ≫ E.hom ∧
        cohomologyPullback.{u, e, u + 2} (pullback.snd U.hom am) _ q d = 0) :
    ∃ (U : X.Etale) (xU : P ⟶ U.left), xU ≫ U.hom = x ∧
      cohomologyPullback.{u, e, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  have H' : IsPullback (a ≫ E.hom) b gm f :=
    H.of_iso (Iso.refl Y) E (Iso.refl T) (Iso.refl S)
      (by simp) (by simp) (by simpa using hE.symm) (by simp)
  let EY : Y ≅ Ym := H'.isoPullback ≪≫ Hm.isoPullback.symm
  have hY : EY.hom ≫ bm = b := by
    simp only [EY, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Hm.isoPullback_inv_snd, H'.isoPullback_hom_snd]
  have hsq : a ≫ E.hom = EY.hom ≫ am := by
    simp only [EY, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Hm.isoPullback_inv_fst, H'.isoPullback_hom_fst]
  obtain ⟨d, hd⟩ := exists_isoTriangle_class bm b EY hY F q c
  obtain ⟨U, xU, hxU, hU⟩ := hzero d
  obtain ⟨V, xV, hxV, hV⟩ := exists_pointed_etale_zero_of_stage_transfer
    E.hom a am EY.hom hsq ((inverseImage bm).obj F) ((inverseImage b).obj F)
    (isoTriangleCoefficientIso bm b EY hY F).hom q d x U xU hxU hU
  refine ⟨V, xV, hxV, ?_⟩
  exact (congrArg
    (cohomologyPullback.{u, e, u + 2} (pullback.snd V.hom a)
      ((inverseImage b).obj F) q) hd).symm.trans hV

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
