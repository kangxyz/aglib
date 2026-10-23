/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteSupportDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.SectionSupportGeometry
public import Aglib.AlgebraicGeometry.Sites.AffineSheafification

/-! # Actual finite closed support exhaustion on the small etale site -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}}

/-- Every finite set of closed points occurs in the chosen small filtered index. -/
theorem exists_finiteSupportIndex (Z : Set X) (hZ : Z.Finite)
    (hc : ∀ x ∈ Z, IsClosed ({x} : Set X)) :
    ∃ W : FiniteSupportIndex X, finiteSupportSet X W = Z := by
  classical
  let f : ULift.{u + 1} {x : X // IsClosed ({x} : Set X)} → X := fun x => x.down.val
  have hi : Function.Injective f := fun a b h => ULift.ext _ _ (Subtype.ext h)
  have hf : (f ⁻¹' Z).Finite := hZ.preimage hi.injOn
  refine ⟨hf.toFinset, ?_⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hf.mem_toFinset.mp hz
  · intro hx
    exact ⟨ULift.up ⟨x, hc x hx⟩, hf.mem_toFinset.mpr hx, rfl⟩

variable [IsNoetherian X] (F : AbelianSheaf.{u, u + 1} X)

/-- If actual sections are locally zero at generic points, the canonical filtered
finite-support colimit map is an isomorphism. Only affine tests are used; no claim
about sectionwise colimits on arbitrary non-quasicompact tests is made. -/
theorem finiteSupportColimitMap_isIso (hdim : topologicalKrullDim X ≤ 1)
    (hF : ∀ (U : X.Etale), IsAffine U.left → ∀ a : F.obj.obj (op U),
      genericPoints U.left ⊆ Etale.sectionZeroLocus F.obj a) :
    IsIso (finiteSupportColimitMap F) := by
  let : Mono (finiteSupportColimitMap F) := finiteSupportColimitMap_mono F
  have hs : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (finiteSupportColimitMap F).hom := by
    apply Etale.locallySurjective_of_affine
    intro U hU a
    let : IsAffine U.left := hU
    let : IsLocallyNoetherian U.left :=
      LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
    let : IsNoetherian U.left := {
      toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
    let : QuasiCompact U.hom :=
      quasiCompact_of_noetherianSpace_source (X := U.left) (Y := X) U.hom
    obtain ⟨Z, hZ, hc, b, hb⟩ := exists_finite_closed_support_section F hdim a (hF U hU a)
    obtain ⟨W, hW⟩ := exists_finiteSupportIndex Z hZ hc
    subst Z
    refine ⟨(colimit.ι (finiteSupportDiagram F) W).hom.app (op U) b, ?_⟩
    have he := congrArg (fun k :
        (pointSupportedSubobject F (finiteSupportSet X W) : AbelianSheaf.{u, u + 1} X) ⟶ F =>
        k.hom.app (op U)) (finiteSupportColimitMap_ι F W)
    exact (ConcreteCategory.congr_hom he b).trans hb
  let : Sheaf.IsLocallySurjective (finiteSupportColimitMap F) := hs
  let : Epi (finiteSupportColimitMap F) :=
    (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} (finiteSupportColimitMap F)).mp inferInstance
  exact isIso_of_mono_of_epi (finiteSupportColimitMap F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
