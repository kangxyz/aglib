/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Top
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle

/-!
# Degree-zero relative projective Serre duality in full derived Hom

Quasicoherent projective cohomological dimension bounds the actual installed derived
global sections by the projective dimension. The native top-Hom equivalence, the original
resolution/cohomology comparison, and native Ext in degree zero then transport the exact
canonical derived Serre comparison to the existing top Serre map.

Consequently the original degree-zero derived comparison is bijective for coherent
coefficients over every Noetherian base ring. No flatness or perfectness is assumed,
and dimension zero is included. Higher relative duality is a separate induction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

local instance projectiveDerivedTopSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
local instance projectiveDerivedTopTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

omit [Fintype ι] in
/-- The actual installed derived global sections of every quasicoherent coefficient are
bounded above by the projective dimension, over an arbitrary commutative base ring. -/
theorem projectiveDerivedGlobalSectionsSingle_isLE (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent] :
    (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj M)).IsLE
        (n : ℤ) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hi0 : 0 ≤ i := by omega
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α
    (injectiveResolution M) q
  let := projectiveCohomology_subsingleton_of_gt R ι n e M q (by exact_mod_cast hi)
  exact ModuleCat.isZero_iff_subsingleton.mpr E.injective.subsingleton

/-- The original degree-zero derived comparison is bijective for actual coherent modules
over a Noetherian base, through the existing canonical top Serre duality map. -/
theorem projectiveDerivedSerreMap_zero_bijective [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    Function.Bijective (projectiveDerivedSerreMap R ι n e M 0) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom P α
  let := moduleCohomologyModuleOfHom P α M n
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let K := F.obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj M)
  let := projectiveDerivedGlobalSectionsSingle_isLE R ι n e M
  let I := injectiveResolution M
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv P α I n
  let Q := ((ShiftedHom.homEquiv (X := K)
    (Y := (DerivedCategory.singleFunctor (ModuleCat.{u} R) (n : ℤ)).obj (ModuleCat.of R R))
      (0 : ℤ) rfl).symm.trans
        (DerivedCategory.homToSingleAddEquiv K (n : ℤ) (ModuleCat.of R R)).toEquiv).trans
    (ModuleCat.homEquiv.trans (LinearEquiv.arrowCongr E (LinearEquiv.refl R R)).toEquiv)
  have hQ (f : M ⟶ ω) :
      Q (projectiveDerivedSerreMap R ι n e M 0 (Ext.mk₀ f)) =
        projectiveTopSerreMap R ι n e M f := by
    ext z
    change (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R)
      (n : ℤ)).hom.app (ModuleCat.of R R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm
          (projectiveDerivedSerreMap R ι n e M 0 (Ext.mk₀ f))) (E.symm z)) =
        projectiveTopSerreMap R ι n e M f z
    exact (projectiveDerivedSerreMap_mk₀_homology_apply R ι n e M I f (E.symm z)).trans
      (congrArg (projectiveTopSerreMap R ι n e M f) (E.apply_symm_apply z))
  have htop := projectiveTopSerreMap_bijective R ι n e M hM
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective M ω).surjective x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective M ω).surjective y
    apply congrArg Ext.mk₀
    apply htop.injective
    exact (hQ f).symm.trans ((congrArg Q hxy).trans (hQ g))
  · intro z
    obtain ⟨f, hf⟩ := htop.surjective (Q z)
    exact ⟨Ext.mk₀ f, Q.injective ((hQ f).trans hf)⟩

end AlgebraicGeometry.Scheme.Cohomology
