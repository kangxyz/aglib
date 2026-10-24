/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureSums
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureKernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureCokernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureExtensionCharts
public import Aglib.CategoryTheory.Abelian.ExtensionPresentation

/-! # Extensions of finite-type locally constant module coefficients

The original middle term of a short exact sequence is finite-type locally
constant when its endpoints are, over a Noetherian coefficient ring. Finite
quotient generators are lifted on actual etale charts; the actual middle term
is then the cokernel of a map between finite-type local systems. We do not
assume that the extension splits locally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] [IsNoetherianRing R]

local instance {X S : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage R f).IsLeftAdjoint :=
  (moduleImageAdjunction R f).isLeftAdjoint

/-- Finite-type local systems over a Noetherian coefficient ring are closed
under extensions in the original module-sheaf abelian category. -/
theorem isFiniteTypeLocallyConstant_extension {X : Scheme.{u}}
    (S : ShortComplex (ModuleSheaf R X)) (hS : S.ShortExact)
    (h₁ : IsFiniteTypeLocallyConstant S.X₁) (h₃ : IsFiniteTypeLocallyConstant S.X₃) :
    IsFiniteTypeLocallyConstant S.X₂ := by
  classical
  obtain ⟨t⟩ := h₃
  apply isFiniteTypeLocallyConstant_of_etaleCover t.chart t.covers S.X₂
  intro i
  let P := moduleInverseImage R (t.chart i).hom
  have hSP := hS.map_of_exact P
  let hPg : Epi (P.map S.g) := hSP.epi_g
  let := t.finite_value i
  let p := P.map S.g ≫ (t.trivialization i).hom
  let : Epi p := epi_comp' hPg (IsIso.epi_of_iso (t.trivialization i).hom)
  choose U y hy M hM a ha using exists_constant_generating_chart (P.obj S.X₂) p
  apply isFiniteTypeLocallyConstant_of_etaleCover U
    (fun x => ⟨x, y x, hy x⟩) (P.obj S.X₂)
  intro x
  let Q := moduleInverseImage R (U x).hom
  let := hM x
  let v := a x
  let := ha x
  have hv : (v ≫ Q.map (P.map S.g)) ≫ Q.map (t.trivialization i).hom =
      v ≫ Q.map p := by simp [p, Functor.map_comp, Category.assoc]
  let hvg : Epi (v ≫ Q.map (P.map S.g)) :=
    (epi_comp_iff_of_isIso _ (Q.map (t.trivialization i).hom)).mp (by
      rw [hv]
      infer_instance)
  have hSPQ : ((S.map P).map Q).ShortExact := hSP.map_of_exact Q
  let : Epi (v ≫ ((S.map P).map Q).g) := hvg
  obtain ⟨rel, ⟨e⟩⟩ := hSPQ.exists_cokernel_presentation v
  apply (isFiniteTypeLocallyConstant_iff_of_iso e).mp
  apply isFiniteTypeLocallyConstant_cokernel rel
  · apply isFiniteTypeLocallyConstant_kernel (v ≫ Q.map (P.map S.g))
    · exact isFiniteTypeLocallyConstant_constant (U x).left (M x)
    · exact (isFiniteTypeLocallyConstant_iff_of_iso
        (Q.mapIso (t.trivialization i) ≪≫
          (moduleInverseImageConstantIso R (U x).hom).app (t.value i))).mpr
        (isFiniteTypeLocallyConstant_constant (U x).left (t.value i))
  · exact isFiniteTypeLocallyConstant_biprod
      (isFiniteTypeLocallyConstant_pullback (U x).hom
        (isFiniteTypeLocallyConstant_pullback (t.chart i).hom h₁))
      (isFiniteTypeLocallyConstant_constant (U x).left (M x))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
