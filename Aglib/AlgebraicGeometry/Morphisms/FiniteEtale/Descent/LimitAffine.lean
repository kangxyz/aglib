/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.FiniteEtale
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineCoverBaseChange
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite-etale objects over limits of affine schemes

The models are actual finite-etale covers. Their specified comparisons use
the original cone projection and the native finite-etale base-change functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

open AffineDescent

/-- A finite-etale cover of the spectrum of a filtered ring colimit descends
to the spectrum of one actual ring stage. -/
theorem exists_spec_cover_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (Y : FiniteEtale (Spec c.pt)) :
    ∃ i, ∃ Yi : FiniteEtale (Spec (F.obj i)),
      Nonempty ((baseChange (Spec.map (c.ι.app i))).obj Yi ≅ Y) := by
  let M := algebraModel Y
  obtain ⟨i, B, _, _, het, hfin, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_model_of_isColimit F c hc M.algebra
  let : Algebra.Etale (F.obj i) B := het
  let : Module.Finite (F.obj i) B := hfin
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  refine ⟨i, specCover (F.obj i) B, ⟨?_⟩⟩
  exact specBaseChangeIso (F.obj i) c.pt B ≪≫ specCoverIso e ≪≫ M.coverIso

/-- A finite-etale cover of a limit of affine schemes has an actual affine-stage
model and a comparison along the specified original cone projection. -/
theorem exists_affine_cover_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Y : FiniteEtale c.pt) :
    ∃ i, ∃ Yi : FiniteEtale (D.obj i),
      Nonempty ((baseChange (c.π.app i)).obj Yi ≅ Y) := by
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f) := inferInstance
  let C := Scheme.Γ.mapCocone c.op
  have hC : IsColimit C :=
    (AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone D c hc).some
  obtain ⟨i, Yi, ⟨e⟩⟩ := exists_spec_cover_of_isColimit (D.op ⋙ Scheme.Γ) C hC
    ((baseChange c.pt.isoSpec.inv).obj Y)
  let Zi := (baseChange (D.obj i.unop).isoSpec.hom).obj Yi
  have h : c.π.app i.unop ≫ (D.obj i.unop).isoSpec.hom =
      c.pt.isoSpec.hom ≫ Spec.map ((c.π.app i.unop).appTop) :=
    (Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj i.unop)
      (c.π.app i.unop)).symm
  refine ⟨i.unop, Zi, ⟨?_⟩⟩
  exact (baseChangeComp (D.obj i.unop).isoSpec.hom (c.π.app i.unop)).symm.app Yi ≪≫
    (eqToIso (congrArg baseChange h)).app Yi ≪≫
    (baseChangeComp (Spec.map ((c.π.app i.unop).appTop)) c.pt.isoSpec.hom).app Yi ≪≫
    (baseChange c.pt.isoSpec.hom).mapIso e ≪≫
    (baseChangeComp c.pt.isoSpec.inv c.pt.isoSpec.hom).symm.app Y ≪≫
    (eqToIso (congrArg baseChange c.pt.isoSpec.hom_inv_id)).app Y ≪≫
    (baseChangeId c.pt).app Y

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
