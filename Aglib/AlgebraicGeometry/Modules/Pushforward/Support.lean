/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkStrata
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension

/-!
# Support of the original closed pushforward and structure module

The native closed-immersion stalk comparison identifies direct-image
support with the image of the original support. The original unit stalk
is the existing rank-one free module, so the structure module has full
support. Consequently the support of its original closed pushforward is
the original closed image and has the original source dimension.

No coherence, finite-type, Noetherianity or reducedness assumption is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The native unit module has the whole original scheme as its stalk support. -/
theorem support_unit (X : Scheme.{u}) :
    support (show X.Modules from SheafOfModules.unit X.ringCatSheaf) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let J := ULift.{u} (PLift (x ∈ (⊤ : X.Opens)))
  let : Nonempty J := ⟨⟨⟨trivial⟩⟩⟩
  let : Nontrivial ((ModuleCat.free (X.presheaf.stalk x)).obj J) :=
    inferInstanceAs (Nontrivial (J →₀ X.presheaf.stalk x))
  let : Nontrivial ((moduleStalk X x).obj O) := (unitStalkIso X x).toLinearEquiv.nontrivial
  intro hz
  have hzero : IsZero ((moduleStalk X x).obj O) :=
    (Coherent.Support.moduleStalk_isZero_iff X O x).mpr hz
  exact (not_subsingleton_iff_nontrivial.mpr
    (inferInstanceAs (Nontrivial ((moduleStalk X x).obj O))))
      (ModuleCat.isZero_iff_subsingleton.mp hzero)

/-- Closed direct image has support exactly the image of the original
support, with no finiteness or quasicoherence hypothesis on the module. -/
theorem support_pushforward_of_isClosedImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (M : X.Modules) :
    support ((Scheme.Modules.pushforward i).obj M) = i '' support M := by
  apply Set.Subset.antisymm
  · intro y hy
    by_cases hyrange : y ∈ Set.range i
    · obtain ⟨x, rfl⟩ := hyrange
      refine ⟨x, ?_, rfl⟩
      intro hx
      have hz : IsZero ((moduleStalk X x).obj M) :=
        (Coherent.Support.moduleStalk_isZero_iff X M x).mpr hx
      have hpush : IsZero ((moduleStalk Y (i x)).obj ((Scheme.Modules.pushforward i).obj M)) :=
        ((ModuleCat.restrictScalars (i.stalkMap x).hom).map_isZero hz).of_iso
          ((closedImmersionModuleStalkIso i x).app M)
      exact hy ((Coherent.Support.moduleStalk_isZero_iff Y _ (i x)).mp hpush)
    · exact False.elim (hy ((Coherent.Support.moduleStalk_isZero_iff Y _ y).mp
        (isZero_closedImmersion_moduleStalk_of_not_mem i y hyrange M)))
  · rintro y ⟨x, hx, rfl⟩ hz
    have hpush : IsZero ((moduleStalk Y (i x)).obj ((Scheme.Modules.pushforward i).obj M)) :=
      (Coherent.Support.moduleStalk_isZero_iff Y _ (i x)).mpr hz
    have hr : IsZero ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
        ((moduleStalk X x).obj M)) :=
      hpush.of_iso ((closedImmersionModuleStalkIso i x).app M).symm
    have hs' : Subsingleton ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
        ((moduleStalk X x).obj M)) := ModuleCat.isZero_iff_subsingleton.mp hr
    have hs : Subsingleton ((moduleStalk X x).obj M) := hs'
    exact hx ((Coherent.Support.moduleStalk_isZero_iff X M x).mp
      (ModuleCat.isZero_iff_subsingleton.mpr hs))

/-- The original closed pushforward of the unit module has the original
closed image as its actual support. -/
theorem support_pushforward_unit {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] :
    support ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) =
      Set.range i := by
  exact (support_pushforward_of_isClosedImmersion i
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).trans
      ((congrArg (fun S : Set X => i '' S) (support_unit X)).trans Set.image_univ)

/-- The actual closed-image homeomorphism identifies the support
dimension of the original direct-image unit with the source dimension. -/
theorem topologicalKrullDim_support_pushforward_unit {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] :
    topologicalKrullDim (support ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf))) = topologicalKrullDim X := by
  rw [support_pushforward_unit]
  let e := i.isClosedEmbedding.isEmbedding.toHomeomorph
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

/-- A nonempty original source has nonzero direct-image unit under an
actual closed embedding. -/
theorem not_isZero_pushforward_unit {X Y : Scheme.{u}} [Nonempty X]
    (i : X ⟶ Y) [IsClosedImmersion i] :
    ¬ IsZero ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  intro hz
  have hs := (support_eq_empty_iff _).mpr hz
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : i x ∈ support ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
    rw [support_pushforward_unit]
    exact ⟨x, rfl⟩
  exact (Set.eq_empty_iff_forall_notMem.mp hs) (i x) hx

end AlgebraicGeometry.Scheme.Modules
