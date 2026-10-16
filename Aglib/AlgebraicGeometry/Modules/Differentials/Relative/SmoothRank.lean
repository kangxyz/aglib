/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.RingTheory.Kaehler.StandardSmooth
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth rank of actual relative differentials over arbitrary bases

Native standard-smooth affine charts and the original open-square differential
comparison give local free presentations of the actual relative differential
sheaf. Their bases have the specified native relative dimension. No field,
Noetherian, finite-type, family, or cohomological premise is added. Empty
sources and relative dimension zero are included.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- A standard-smooth affine morphism has a free presentation of its actual relative
module sheaf of the stated rank. -/
def relativeDifferentialStandardSmoothAffineFreeIso {R S : CommRingCat.{u}}
    (σ : R ⟶ S) (n : ℕ)
    (hσ : RingHom.IsStandardSmoothOfRelativeDimension n σ.hom) :
    SheafOfModules.free (R := (Spec S).ringCatSheaf) (ULift.{u} (Fin n)) ≅
      relativeDifferentialSheaf (Spec.map σ) := by
  letI : Algebra R S := σ.hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n R S := hσ.toAlgebra
  let b : Module.Basis (ULift.{u} (Fin n)) S (CommRingCat.KaehlerDifferential σ) :=
    (KaehlerDifferential.standardSmoothBasis R S n).reindex Equiv.ulift.symm
  exact (Scheme.Modules.tildeBasisIso _ b).symm ≪≫ (relativeDifferentialAffineIso σ).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original actual relative differential sheaf is free on every native standard-smooth
source/base affine chart. -/
def relativeDifferentialStandardSmoothChartFreeIso (n : ℕ)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U)
    (hσ : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ≅
      (relativeDifferentialSheaf f).restrict V.ι := by
  let c : SheafOfModules.free (R := (Spec Γ(X, V)).ringCatSheaf)
      (ULift.{u} (Fin n)) ≅ (relativeDifferentialSheaf f).restrict hV.fromSpec :=
    relativeDifferentialStandardSmoothAffineFreeIso (f.appLE U V e) n hσ ≪≫
      (relativeDifferentialOpenSquareIso f hV.fromSpec (Spec.map (f.appLE U V e))
        hU.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm).symm
  exact Scheme.Modules.freeIsoOfRestrictIso hV.isoSpec.symm
    ((relativeDifferentialSheaf f).restrict V.ι)
    (c ≪≫ (Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app
      (relativeDifferentialSheaf f))

/-- Actual differentials of every smooth morphism have its native relative rank, over any base. -/
theorem relativeDifferentialSheaf_hasRank_of_smooth (n : ℕ)
    (hf : SmoothOfRelativeDimension n f) :
    Scheme.Modules.SheafHasRank (relativeDifferentialSheaf f) n := by
  classical
  choose U hU V hV hx e hσ using hf.exists_isStandardSmoothOfRelativeDimension
  have hcov : IsOpenCover V := by
    change (⨆ x : X, V x) = ⊤
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact Scheme.Modules.sheafHasRank_of_coverFreeIso V hcov
    (fun x => relativeDifferentialStandardSmoothChartFreeIso f n
      (hU x) (hV x) (e x) (hσ x))

/-- Actual differentials of a smooth morphism are finite locally free over every scheme base. -/
theorem relativeDifferentialSheaf_finiteLocallyFree_of_smooth (n : ℕ)
    (hf : SmoothOfRelativeDimension n f) :
    Scheme.Modules.SheafFiniteLocallyFree (relativeDifferentialSheaf f) :=
  (relativeDifferentialSheaf_hasRank_of_smooth f n hf).isFiniteLocallyFree

end AlgebraicGeometry.Scheme.Modules.Differentials
