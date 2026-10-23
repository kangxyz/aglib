/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Coherent.StalkFinite
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Nakayama
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper closed-support detection on the original local source

Finite local Nakayama detects vanishing at the actual closed fibre. Proper closed support then
detects global vanishing and epimorphy of the original two-section row. The source is derived
Noetherian from the original Noetherian base and proper map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u v w t

section FiniteClosedDetection

private theorem isZero_of_extendScalars_zero
    {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) (hr : Function.Surjective r)
    (hJ : RingHom.ker r ≤ (⊥ : Ideal R).jacobson)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : IsZero ((ModuleCat.extendScalars r).obj M)) : IsZero M := by
  let I := RingHom.ker r
  let P : Submodule R M := I • ⊤
  let Q : ModuleCat.{u} R := ModuleCat.of R (M ⧸ P)
  have hQ : RingHom.ker r ≤ Module.annihilator R Q := by
    intro a ha
    rw [Module.mem_annihilator]
    intro q
    exact Module.isTorsionBySet_quotient_ideal_smul M I (x := q) (a := ⟨a, ha⟩)
  obtain ⟨Q', ⟨e⟩⟩ :=
    (ModuleCat.mem_essImage_restrictScalars_iff_ker_le_annihilator r hr Q).mpr hQ
  let q : M ⟶ (ModuleCat.restrictScalars r).obj Q' := ModuleCat.ofHom P.mkQ ≫ e.inv
  let _ : Epi (ModuleCat.ofHom P.mkQ) :=
    (ModuleCat.epi_iff_surjective _).mpr P.mkQ_surjective
  let _ : Epi q := by dsimp only [q]; infer_instance
  let adj := ModuleCat.extendRestrictScalarsAdj r
  let q' := (adj.homEquiv M Q').symm q
  have hq : adj.unit.app M ≫ (ModuleCat.restrictScalars r).map q' = q :=
    (adj.homEquiv M Q').apply_symm_apply q
  have hq' : q' = 0 := hM.eq_of_src _ _
  have hqzero : q = 0 := by rw [← hq, hq', Functor.map_zero, comp_zero]
  have hzQ' : IsZero ((ModuleCat.restrictScalars r).obj Q') :=
    IsZero.of_epi_eq_zero q hqzero
  have hzQ : IsZero Q := hzQ'.of_iso e.symm
  have hsQ : Subsingleton (M ⧸ P) := ModuleCat.subsingleton_of_isZero hzQ
  have hP : P = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsQ
  have htop : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top
      (by change ⊤ ≤ P; rw [hP]) hJ
  have hz (m : M) : m = 0 := by
    have hm : m ∈ (⊥ : Submodule R M) := htop ▸ (show m ∈ (⊤ : Submodule R M) from trivial)
    exact hm
  exact (ModuleCat.isZero_iff_subsingleton).mpr ⟨fun x y => (hz x).trans (hz y).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing of the actual pulled finite target implies vanishing of its
ORIGINAL stalk at every point of the original closed immersion. -/
theorem closed_pullback_zero_stalk
    {E X : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i] (M : X.Modules)
    (hM : ∀ y : E, Module.Finite (X.presheaf.stalk (i y))
      ((moduleStalk X (i y)).obj M))
    (hz : IsZero ((Scheme.Modules.pullback i).obj M)) (y : E) :
    IsZero ((moduleStalk X (i y)).obj M) := by
  let _ : Module.Finite (X.presheaf.stalk (i y))
      ((moduleStalk X (i y)).obj M) := hM y
  have hp : IsZero ((moduleStalk E y).obj ((Scheme.Modules.pullback i).obj M)) :=
    (moduleStalk E y).map_isZero hz
  have hs : IsZero ((ModuleCat.extendScalars (i.stalkMap y).hom).obj
      ((moduleStalk X (i y)).obj M)) :=
    hp.of_iso ((pullbackModuleStalkIso i y).app M).symm
  apply isZero_of_extendScalars_zero (i.stalkMap y).hom (i.stalkMap_surjective y) ?_
    ((moduleStalk X (i y)).obj M) hs
  exact (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)).trans
    (IsLocalRing.maximalIdeal_le_jacobson _)

end FiniteClosedDetection

section ProperLocalFiniteDetection

open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the ORIGINAL proper local source, a finite quasicoherent module
vanishing on the ORIGINAL residue fibre vanishes everywhere. Proper closed
support, not an off-fibre epimorphy assumption, supplies the global conclusion. -/
theorem properLocal_zero_of_closedFibre_pullback_zero
    {R k : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field k]
    (β : R →+* k) [IsLocalHom β] {E X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (i : E ⟶ X) [IsClosedImmersion i] (a : E ⟶ Spec (.of k))
    (hpb : IsPullback i a f (Spec.map (CommRingCat.ofHom β)))
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (hz : IsZero ((Scheme.Modules.pullback i).obj M)) : IsZero M := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  apply (support_eq_empty_iff M).mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hclosed : IsClosed (f '' support M) :=
    f.isClosedMap _ (isClosed_support_of_affineLocallyFiniteType hM)
  have hpt : IsLocalRing.closedPoint R ∈ f '' support M :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hclosed ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hfy⟩ := hpt
  obtain ⟨z, hzfst, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Spec.map (CommRingCat.ofHom β)) y (IsLocalRing.closedPoint k)
      (hfy.trans (by
        simpa using (AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom β)).symm))
  let e := hpb.isoPullback
  let q := e.inv z
  have hiq : i q = y := by
    have h := congrArg (fun g : pullback f (Spec.map (CommRingCat.ofHom β)) ⟶ X => g z)
      hpb.isoPullback_inv_fst
    exact h.trans hzfst
  have hs : IsZero ((moduleStalk X (i q)).obj M) :=
    closed_pullback_zero_stalk i M (fun p =>
      Stalk.coherent_stalk_finite X (⟨M, hM⟩ : FiniteTypeSheaves X) (i p)) hz q
  have hs' : IsZero ((stalkFunctor X (i q)).obj M) :=
    (((forget₂ (ModuleCat (X.presheaf.stalk (i q))) AddCommGrpCat.{u}).map_isZero hs).of_iso
      ((moduleStalkForgetIso X (i q)).app M).symm)
  exact hy (hiq ▸ hs')

end ProperLocalFiniteDetection

section ProperLocalActualRows

open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Modules.QuasiCoherent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper closed support upgrades epimorphy of the ORIGINAL fibre row to
epimorphy of the ORIGINAL global row. Only its actual cokernel is finite. -/
theorem properLocal_epi_of_closedFibre_pullback_epi
    {R k : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field k]
    (β : R →+* k) [IsLocalHom β] {E X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (i : E ⟶ X) [IsClosedImmersion i] (a : E ⟶ Spec (.of k))
    (hpb : IsPullback i a f (Spec.map (CommRingCat.ofHom β)))
    {M N : X.Modules} (φ : M ⟶ N)
    (hQ : affineLocallyFiniteType X (cokernel φ))
    [Epi ((Scheme.Modules.pullback i).map φ)] : Epi φ := by
  apply Preadditive.epi_of_isZero_cokernel
  apply properLocal_zero_of_closedFibre_pullback_zero β f i a hpb (cokernel φ) hQ
  exact (isZero_cokernel_of_epi ((Scheme.Modules.pullback i).map φ)).of_iso
    (PreservesCokernel.iso (Scheme.Modules.pullback i) φ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For the actual two-section line row, coherence is derived rather than
assumed. The original pair and its literal coproduct map are preserved. -/
theorem properLocal_twoSections_epi
    {R k : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field k]
    (β : R →+* k) [IsLocalHom β] {E X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (i : E ⟶ X) [IsClosedImmersion i] (a : E ⟶ Spec (.of k))
    (hpb : IsPullback i a f (Spec.map (CommRingCat.ofHom β)))
    (L : LineBundle X)
    (s : ULift.{u} (Fin 2) → (SheafOfModules.unit X.ringCatSheaf ⟶ L.val))
    [Epi ((Scheme.Modules.pullback i).map (Sigma.desc s))] : Epi (Sigma.desc s) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : L.val.IsFinitePresentation := lineBundle_isFinitePresentation X L
  have hP : affineLocallyFiniteType X
      (∐ fun _ : ULift.{u} (Fin 2) => SheafOfModules.unit X.ringCatSheaf) :=
    (affineLocallyFiniteType X).prop_coproduct (fun _ => affineLocallyFiniteType_unit X)
  have hQ : affineLocallyFiniteType X (cokernel (Sigma.desc s)) :=
    (affineLocallyFiniteType X).prop_cokernel (Sigma.desc s) hP
      (affineLocallyFiniteType_of_finitePresentation L.val)
  exact properLocal_epi_of_closedFibre_pullback_epi β f i a hpb (Sigma.desc s) hQ

end ProperLocalActualRows

end AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood
