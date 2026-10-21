/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductSections
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.Naturality
public import Aglib.Algebra.Homology.ModuleCat.Coproduct

/-!
# Finite affine Cech complexes and quasicoherent coproducts

Every term is a finite product of actual affine-intersection section modules.
Finite products are finite biproducts, so they preserve the coproduct cocone.
There is no assertion that these section modules are finite over the base.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type (max u v)} [CommRing R] (X : Scheme.{max u v}) (α : R →+* Γ(X, ⊤))
  {ι : Type (max u v)} (U : ι → X.Opens)

/-- The section diagram whose product is one term of the original Cech complex. -/
def moduleCechTermDiagramFunctor {R : Type u} [CommRing R]
    (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    X.Modules ⥤ (Discrete (Fin (n + 1) → ι) ⥤ ModuleCat.{u} R) where
  obj M := Discrete.functor (fun a =>
    (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k => U (a k))))
  map f := Discrete.natTrans (fun a =>
    ((moduleSectionsPresheafFunctor X α).map f).app (op (∏ᶜ fun k => U (a.as k))))

/-- A finite affine Cech complex preserves actual quasicoherent colimiting cocones. -/
def moduleCechIsColimit [Finite ι] [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) {J : Type v} [Category.{v} J]
    {F : J ⥤ X.Modules} (hF : ∀ j, (F.obj j).IsQuasicoherent)
    {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((moduleSectionsPresheafFunctor X α ⋙ cechComplexFunctor U).mapCocone c) := by
  classical
  apply HomologicalComplex.isColimitOfEval
  intro n
  let T := moduleCechTermDiagramFunctor.{max u v} X α U n
  have ht : IsColimit (T.mapCocone c) := by
    apply evaluationJointlyReflectsColimits
    intro a
    exact moduleAffineSectionsIsColimit.{u, v} X α (∏ᶜ fun k => U (a.as k))
      (by
        have he : (∏ᶜ fun k => U (a.as k)) = ⨅ k, U (a.as k) := by
          apply le_antisymm
          · exact le_iInf fun k => leOfHom (Limits.Pi.π _ k)
          · exact leOfHom (Limits.Pi.lift fun k => homOfLE (iInf_le _ k))
        rw [he]
        exact IsAffineOpen.iInf (fun k => hU (a.as k))) hF hc
  letI : HasFiniteBiproducts (ModuleCat.{max u v} R) := Abelian.hasFiniteBiproducts
  let : PreservesColimitsOfSize.{max u v, max u v}
      (lim : (Discrete (Fin (n + 1) → ι) ⥤ ModuleCat.{max u v} R) ⥤ _) :=
    preservesColimits_of_natIso HasBiproductsOfShape.colimIsoLim
  let : PreservesColimitsOfSize.{v, v}
      (lim : (Discrete (Fin (n + 1) → ι) ⥤ ModuleCat.{max u v} R) ⥤ _) :=
    preservesColimitsOfSize_shrink.{v, u, v, u} _
  exact isColimitOfPreserves lim ht

/-- The Cech cofan induced by the actual module-sheaf coproduct inclusions. -/
def moduleCechCoproductCofan {δ : Type v} (M : δ → X.Modules) :
    Cofan (fun i => moduleCechComplex X α (M i) U) :=
  Cofan.mk (moduleCechComplex X α (∐ M) U)
    (fun i => moduleCechMap X α U (Sigma.ι M i))

/-- The original Cech inclusion cofan is colimiting on a finite affine family. -/
def moduleCechCoproductIsColimit [Finite ι] [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) {δ : Type v}
    (M : δ → X.Modules) [∀ i, (M i).IsQuasicoherent] :
    IsColimit (moduleCechCoproductCofan.{u, v} X α U M) := by
  let T := moduleSectionsPresheafFunctor X α ⋙ cechComplexFunctor U
  let e : Discrete.functor (fun i => moduleCechComplex X α (M i) U) ≅
      Discrete.functor M ⋙ T := Discrete.natIso (fun _ => Iso.refl _)
  have h := (IsColimit.precomposeHomEquiv e _).symm
    (moduleCechIsColimit.{u, v} X α U hU
      (fun i => inferInstanceAs (M i.as).IsQuasicoherent) (coproductIsCoproduct M))
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  simp [e, T, moduleCechCoproductCofan, moduleCechMap]

/-- The finite affine Cech comparison with the termwise direct-sum complex. -/
def moduleCechCoproductIso [Finite ι] [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) {δ : Type v}
    (M : δ → X.Modules) [∀ i, (M i).IsQuasicoherent] :
    ModuleCat.coproductComplex.{u, v, 0} (fun i => moduleCechComplex X α (M i) U) ≅
      moduleCechComplex X α (∐ M) U :=
  (ModuleCat.coproductComplexIsColimit.{u, v, 0} _).coconePointUniqueUpToIso
    (moduleCechCoproductIsColimit.{u, v} X α U hU M)

/-- The comparison preserves each original coefficient inclusion. -/
@[reassoc]
theorem moduleCechCoproductIso_ι [Finite ι] [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) {δ : Type v}
    (M : δ → X.Modules) [∀ i, (M i).IsQuasicoherent] (i : δ) :
    ModuleCat.coproductComplexι.{u, v, 0} (fun i => moduleCechComplex X α (M i) U) i ≫
        (moduleCechCoproductIso.{u, v} X α U hU M).hom =
      moduleCechMap X α U (Sigma.ι M i) :=
  (ModuleCat.coproductComplexIsColimit.{u, v, 0} _).comp_coconePointUniqueUpToIso_hom
    (moduleCechCoproductIsColimit.{u, v} X α U hU M) (Discrete.mk i)

end AlgebraicGeometry.Scheme.Cohomology
