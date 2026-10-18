/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace

/-! # The original affine trace as the composite coefficient residue -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

private theorem cohomologyIsoTrans_apply {X : Scheme.{u}} {M N K : X.Modules}
    (e : M ≅ N) (f : N ≅ K) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (e ≪≫ f).hom) n x =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f.hom) n
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n x) := by
  erw [Iso.trans_hom, Functor.map_comp, Sheaf.H.map_comp_apply]

private theorem cohomologyIsoInvHom_apply {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X N) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n x) = x := by
  erw [← Sheaf.H.map_comp_apply, ← Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id]
  exact Sheaf.H.map_id_apply x

private theorem moduleTriangle_apply {S : Type*} [Ring S] {M N : ModuleCat S}
    (f : M ⟶ N) (g : N ⟶ M) (h : f ≫ g = 𝟙 M) (x : M) :
    (ConcreteCategory.hom g) ((ConcreteCategory.hom f) x) = x := by
  exact congrArg (fun a : M ⟶ M => a.hom x) h

variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The original affine tilde counit followed by the original determinant/twist map. -/
def affineTraceCoefficientComparisonIso
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N ≅
      projectiveResidueTwistTensorCoefficients R ι (moduleSpecΓFunctor.obj N) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).mapIso
      (asIso N.fromTildeΓ).symm ≪≫
    projectiveDifferentialCoefficientsTwistingIso R ι n e (moduleSpecΓFunctor.obj N)

private theorem affineTrace_iterated
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveAffineDifferentialTraceLinearEquiv R ι n e N x =
      projectiveTraceCoefficientsLinearEquiv R ι n e (moduleSpecΓFunctor.obj N)
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (projectiveDifferentialCoefficientsTwistingIso R ι n e
            (moduleSpecΓFunctor.obj N)).hom) n
          (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
            ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map
              (asIso N.fromTildeΓ).inv)) n x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let E := asIso N.fromTildeΓ
  let F := relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n
  let y := Sheaf.H.map
    ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map (F.map E.inv)) n x
  have hc := cohomologyIsoInvHom_apply (F.mapIso E) n x
  have hn := projectiveAffineDifferentialTraceLinearEquiv_naturality R ι n e E.hom y
  have hn' := (congrArg
    (fun z => projectiveAffineDifferentialTraceLinearEquiv R ι n e N z) hc.symm).trans hn
  have ht := projectiveAffineDifferentialTraceLinearEquiv_tilde_residue R ι n e
    (moduleSpecΓFunctor.obj N) y
  have hη : (tilde.toTildeΓNatIso (R := .of R)).hom.app (moduleSpecΓFunctor.obj N) ≫
      moduleSpecΓFunctor.map E.hom = 𝟙 (moduleSpecΓFunctor.obj N) :=
    (tilde.adjunction (R := .of R)).right_triangle_components N
  let z := projectiveTraceCoefficientsLinearEquiv R ι n e (moduleSpecΓFunctor.obj N)
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      (projectiveDifferentialCoefficientsTwistingIso R ι n e
        (moduleSpecΓFunctor.obj N)).hom) n y)
  have hz : moduleSpecΓFunctor.map E.hom
      ((tilde.toTildeΓNatIso (R := .of R)).hom.app (moduleSpecΓFunctor.obj N) z) = z := by
    exact moduleTriangle_apply _ _ hη z
  exact hn'.trans ((congrArg (fun z => moduleSpecΓFunctor.map E.hom z) ht).trans hz)

/-- The actual coefficient trace retains the same original combined residue formula. -/
theorem affineTrace_residue
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveAffineDifferentialTraceLinearEquiv R ι n e N x =
      projectiveTraceCoefficientsLinearEquiv R ι n e (moduleSpecΓFunctor.obj N)
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (affineTraceCoefficientComparisonIso R ι n e N).hom) n x) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have h := cohomologyIsoTrans_apply
    ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).mapIso
      (asIso N.fromTildeΓ).symm)
    (projectiveDifferentialCoefficientsTwistingIso R ι n e (moduleSpecΓFunctor.obj N)) n x
  exact (affineTrace_iterated R ι n e N x).trans
    (congrArg (projectiveTraceCoefficientsLinearEquiv R ι n e (moduleSpecΓFunctor.obj N)) h.symm)

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
