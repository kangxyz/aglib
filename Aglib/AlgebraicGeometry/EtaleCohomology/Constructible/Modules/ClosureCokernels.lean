/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureMorphisms

/-! # Cocokernels of finite-type locally constant module morphisms

Over a Noetherian coefficient ring, actual morphisms between finite-type
locally constant module sheaves have finite-type locally constant cocokernels.
Finite presentation makes the morphism constant on a refinement of actual
trivializing charts. This is closure for maps between local systems, not
closure under arbitrary ambient quotients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

local instance {X S : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage R f).IsLeftAdjoint :=
  (moduleImageAdjunction R f).isLeftAdjoint

/-- Even between two globally constant sheaves, the morphism itself may vary
on connected components. Its cokernel is obtained on genuinely refined charts. -/
theorem isFiniteTypeLocallyConstant_cokernel_between_constants {X : Scheme.{u}}
    {M N : ModuleCat.{u + 1} R} [Module.FinitePresentation R M] [Module.Finite R N]
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N) :
    IsFiniteTypeLocallyConstant (cokernel φ) := by
  classical
  choose U y hy a he using exists_constantMap_chart φ
  apply isFiniteTypeLocallyConstant_of_etaleCover U
    (fun x => ⟨x, y x, hy x⟩) (cokernel φ)
  intro x
  let e := (he x).some
  let ek := cokernel.mapIso
    ((constantSheaf (U x).left.smallEtaleTopology (ModuleCat.{u + 1} R)).map (a x))
    ((moduleInverseImage R (U x).hom).map φ)
    (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) e.hom.w.symm
  exact (isFiniteTypeLocallyConstant_iff_of_iso
    ((PreservesCokernel.iso (moduleInverseImage R (U x).hom) φ) ≪≫ ek.symm)).mpr
      (isFiniteTypeLocallyConstant_cokernel_constantMap (U x).left (a x))

/-- Constant presentations of the source and target suffice; the original
morphism need not be globally induced by any module map. -/
theorem isFiniteTypeLocallyConstant_cokernel_of_constant_isos {X : Scheme.{u}}
    {F G : ModuleSheaf R X} {M N : ModuleCat.{u + 1} R}
    [Module.FinitePresentation R M] [Module.Finite R N]
    (eF : F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    (eG : G ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N)
    (φ : F ⟶ G) : IsFiniteTypeLocallyConstant (cokernel φ) := by
  let ψ := eF.inv ≫ φ ≫ eG.hom
  let e := cokernel.mapIso φ ψ eF eG (by simp [ψ])
  exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (isFiniteTypeLocallyConstant_cokernel_between_constants ψ)

/-- The cokernel of a morphism between actual finite-type local systems is an
actual finite-type local system over a Noetherian coefficient ring. -/
theorem isFiniteTypeLocallyConstant_cokernel [IsNoetherianRing R] {X : Scheme.{u}}
    {F G : ModuleSheaf R X} (φ : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstant F) (hG : IsFiniteTypeLocallyConstant G) :
    IsFiniteTypeLocallyConstant (cokernel φ) := by
  obtain ⟨t⟩ := hF
  apply isFiniteTypeLocallyConstant_of_etaleCover t.chart t.covers (cokernel φ)
  intro i
  let P := moduleInverseImage R (t.chart i).hom
  apply (isFiniteTypeLocallyConstant_iff_of_iso (PreservesCokernel.iso P φ)).mpr
  obtain ⟨s⟩ := isFiniteTypeLocallyConstant_pullback (t.chart i).hom hG
  apply isFiniteTypeLocallyConstant_of_etaleCover s.chart s.covers (cokernel (P.map φ))
  intro j
  let Q := moduleInverseImage R (s.chart j).hom
  apply (isFiniteTypeLocallyConstant_iff_of_iso (PreservesCokernel.iso Q (P.map φ))).mpr
  let := t.finite_value i
  let := Module.finitePresentation_of_finite R (t.value i)
  let := s.finite_value j
  exact isFiniteTypeLocallyConstant_cokernel_of_constant_isos
    (Q.mapIso (t.trivialization i) ≪≫
      (moduleInverseImageConstantIso R (s.chart j).hom).app (t.value i))
    (s.trivialization j) (Q.map (P.map φ))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
