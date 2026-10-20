/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation

/-!
# Finite pushforward chart algebras

These are the actual section ring maps and unit-pushforward chart
equivalences for arbitrary affine open charts. Finiteness follows from
finiteness of the morphism, injectivity from schematic dominance and
quasi-compactness, and projectivity from the displayed integral-source
and PID-chart hypotheses. The unit pushforward is quasicoherent over a
locally Noetherian target.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing declaration
namespaces, hypotheses, universes, objects, maps, and proofs are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Coherent.FinitePushforward.Charts` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5f97a09d2db071a3bf6ca94e961e42af952359823f74be83a39344c9dc642d4b`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order
universe u v
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (R : CommRingCat.{u})
  (j : Spec R ⟶ X) [IsOpenImmersion j]
/-- The original polynomial-chart scalar map to sections of the finite preimage. -/
def chartSectionRingMap : R →+* Γ(Y, f ⁻¹ᵁ (j ''ᵁ ⊤)) :=
  ((Scheme.ΓSpecIso R).inv ≫ (j.appIso ⊤).inv ≫ f.app (j ''ᵁ ⊤)).hom

/-- The chart-linear identification of the pushed-forward unit module with sections on the
preimage. -/
def unitPushforwardChartEquiv :
    letI := (chartSectionRingMap f R j).toAlgebra
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit Y.ringCatSheaf)).restrict j) ≃ₗ[R]
      Γ(Y, f ⁻¹ᵁ (j ''ᵁ ⊤)) := by
  letI := (chartSectionRingMap f R j).toAlgebra
  exact {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem chartSectionRingMap_finite [IsFinite f] : (chartSectionRingMap f R j).Finite := by
  let e := (Scheme.ΓSpecIso R).symm ≪≫ (j.appIso ⊤).symm
  have he : e.hom.hom.Finite := RingHom.Finite.of_surjective _
    e.commRingCatIsoToRingEquiv.surjective
  have hU : IsAffineOpen (j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j
  exact (f.finite_app _ hU).comp he

theorem unitPushforwardChart_finite [IsFinite f] :
    Module.Finite R (moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit Y.ringCatSheaf)).restrict j)) := by
  let := (chartSectionRingMap f R j).toAlgebra
  let : Module.Finite R Γ(Y, f ⁻¹ᵁ (j ''ᵁ ⊤)) := chartSectionRingMap_finite f R j
  exact Module.Finite.equiv (unitPushforwardChartEquiv f R j).symm

theorem chartSectionRingMap_injective [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
    Function.Injective (chartSectionRingMap f R j) := by
  let e := (Scheme.ΓSpecIso R).symm ≪≫ (j.appIso ⊤).symm
  exact (f.app_injective _).comp e.commRingCatIsoToRingEquiv.injective

theorem unitPushforwardChart_projective [IsFinite f] [IsSchemeTheoreticallyDominant f]
    [IsIntegral Y] [IsDomain R] [IsPrincipalIdealRing R] :
    Module.Projective R (moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit Y.ringCatSheaf)).restrict j)) := by
  have hn : ((j ''ᵁ ⊤ : X.Opens) : Set X).Nonempty := by
    simpa only [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange] using
      Set.range_nonempty j
  obtain ⟨y, hy⟩ := f.denseRange.exists_mem_open (j ''ᵁ ⊤).isOpen hn
  let : Nonempty (f ⁻¹ᵁ (j ''ᵁ ⊤)) := ⟨⟨y, hy⟩⟩
  let := (chartSectionRingMap f R j).toAlgebra
  let : Module.Finite R Γ(Y, f ⁻¹ᵁ (j ''ᵁ ⊤)) := chartSectionRingMap_finite f R j
  let : Module.IsTorsionFree R Γ(Y, f ⁻¹ᵁ (j ''ᵁ ⊤)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (chartSectionRingMap_injective f R j)
  let : Module.Projective R Γ(Y, f ⁻¹ᵁ (j ''ᵁ ⊤)) := inferInstance
  exact Module.Projective.of_equiv' (unitPushforwardChartEquiv f R j).symm


/-- Finite direct image of the unit is quasicoherent on a locally noetherian target. -/
theorem finitePushforward_unit_isQuasicoherent
    {Y X : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f] :
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent := by
  let e : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit Y.ringCatSheaf := coproductUniqueIso _
  have hO : _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType Y
      (SheafOfModules.unit Y.ringCatSheaf) :=
    (_root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType Y).prop_of_iso e
      (_root_.AlgebraicGeometry.Scheme.Modules.coherent_of_finiteLocallyFree _)
  let C : _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X :=
    ⟨_, Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward f hO⟩
  exact _root_.AlgebraicGeometry.Scheme.Modules.Coherent.coherent_obj_quasicoherent C


end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
