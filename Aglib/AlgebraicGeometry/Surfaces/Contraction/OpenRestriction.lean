/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The original exceptional curve inside an actual open neighbourhood

The native open-immersion lift factors the original curve through the specified
open scheme. Its cartesian square identifies the original kernel ideal after
pullback. The canonical ideal module map is an isomorphism, preserving local
rank one and the conormal comparison on the unchanged original curve.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.OpenRestriction

variable {D X U : Scheme.{u}} (i : D ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
  (h : Set.range i ⊆ Set.range j)

/-- The original curve map, factored through the specified open immersion. -/
def map : D ⟶ U := IsOpenImmersion.lift j i h

/-- The factored curve retains its original map to the ambient scheme. -/
@[reassoc (attr := simp)]
theorem map_comp : map i j h ≫ j = i := IsOpenImmersion.lift_fac j i h

/-- The displayed square is cartesian with identity on the original curve. -/
theorem isPullback : IsPullback (𝟙 D) (map i j h) i j :=
  (IsOpenImmersion.isPullback_lift_id i j h).flip

/-- The same curve remains closed in the specified open scheme. -/
instance isClosedImmersion_map [IsClosedImmersion i] : IsClosedImmersion (map i j h) :=
  MorphismProperty.of_isPullback (isPullback i j h) inferInstance

/-- The actual points of the factored curve have the original ambient image. -/
@[simp]
theorem comp_apply (d : D) : j (map i j h d) = i d :=
  congrArg (fun f : D ⟶ X => f d) (map_comp i j h)

/-- The curve in the specified open has precisely the inverse image of the
original curve as its range. -/
theorem range_map : Set.range (map i j h) = j ⁻¹' Set.range i := by
  ext u
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, (comp_apply i j h d).symm⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, j.isOpenEmbedding.injective ((comp_apply i j h d).trans hd)⟩

/-- Removing the original curve commutes with this actual open restriction. -/
theorem preimage_complement :
    j ⁻¹' (Set.range i)ᶜ = (Set.range (map i j h))ᶜ := by
  rw [Set.preimage_compl, range_map]

/-- The full original kernel ideal, not only its support, restricts to the
kernel of the factored immersion. -/
theorem ker_comap [IsClosedImmersion i] : i.ker.comap j = (map i j h).ker := by
  calc
    i.ker.comap j = (pullback.fst j i).ker :=
      (IdealSheafData.ker_fst_of_isClosedImmersion i j).symm
    _ = ((isPullback i j h).flip.isoPullback.hom ≫ pullback.fst j i).ker :=
      (Hom.ker_comp_of_isIso _ _).symm
    _ = (map i j h).ker := by rw [(isPullback i j h).flip.isoPullback_hom_fst]

/-- The existing canonical ideal pullback map is invertible for this actual
cartesian square, whose curve map is the identity. -/
instance idealPullbackMap_isIso :
    IsIso (Hom.idealPullbackMap i (map i j h) j (𝟙 D) (isPullback i j h).w) :=
  Hom.idealPullbackMap_isIso_of_isOpenImmersion i (map i j h) j (𝟙 D)
    (isPullback i j h).w (isPullback i j h)

/-- The canonical comparison of the actual original ideal modules. -/
def idealIso :
    (Scheme.Modules.pullback j).obj (Hom.idealModule i) ≅ Hom.idealModule (map i j h) :=
  asIso (Hom.idealPullbackMap i (map i j h) j (𝟙 D) (isPullback i j h).w)

/-- The forward comparison is exactly the native ideal pullback map. -/
@[simp]
theorem idealIso_hom :
    (idealIso i j h).hom =
      Hom.idealPullbackMap i (map i j h) j (𝟙 D) (isPullback i j h).w := rfl

/-- The comparison preserves the original ideal inclusions and the native
pullback map on structure modules. -/
@[reassoc]
theorem idealIso_hom_inclusion :
    (idealIso i j h).hom ≫ Hom.idealInclusion (map i j h) =
      (Scheme.Modules.pullback j).map (Hom.idealInclusion i) ≫
        SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom :=
  Hom.idealPullbackMap_inclusion i (map i j h) j (𝟙 D) (isPullback i j h).w

/-- The original invertible ideal remains invertible in this open scheme. -/
theorem isLocallyRankOne_ideal (hI : IsLocallyRankOne X (Hom.idealModule i)) :
    IsLocallyRankOne U (Hom.idealModule (map i j h)) :=
  isLocallyRankOne_of_iso U (idealIso i j h)
    (pullback_locallyRankOne j (Hom.idealModule i) hI)

/-- The ideal line on the original open, with its actual kernel module. -/
def idealLine (hI : IsLocallyRankOne X (Hom.idealModule i)) : LineBundle U :=
  ⟨Hom.idealModule (map i j h), isLocallyRankOne_ideal i j h hI⟩

/-- The actual conormal modules are compared on the unchanged original curve.
The comparison is induced by the canonical ideal map and the original triangle. -/
def conormalIso :
    (Scheme.Modules.pullback (map i j h)).obj (Hom.idealModule (map i j h)) ≅
      (Scheme.Modules.pullback i).obj (Hom.idealModule i) :=
  (Scheme.Modules.pullback (map i j h)).mapIso (idealIso i j h).symm ≪≫
    (pullbackComp (map i j h) j).app (Hom.idealModule i) ≪≫
    (pullbackCongr (map_comp i j h)).app (Hom.idealModule i)

end AlgebraicGeometry.Scheme.Surfaces.Contraction.OpenRestriction

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

variable {k : Type u} [Field k] {X U : Scheme.{u}}
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X)
  (j : U ⟶ X) [IsOpenImmersion j] (h : Set.range i ⊆ Set.range j)

/-- The original `O(1)` conormal is retained on the same projective line after
factoring its immersion through the specified open neighbourhood. -/
def OpenRestriction.conormalTwistIso
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1) :
    (Scheme.Modules.pullback (OpenRestriction.map i j h)).obj
        (Hom.idealModule (OpenRestriction.map i j h)) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1 :=
  OpenRestriction.conormalIso i j h ≪≫ eI

include h in
/-- The same closed exceptional projective line, with its original invertible
ideal and `O(1)` conormal, lies in the specified open scheme. No properness,
projectivity, base-field identification or replacement of the curve is assumed. -/
theorem exists_exceptional_in_open [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1) :
    ∃ iU : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ U,
      IsClosedImmersion iU ∧ iU ≫ j = i ∧ IsPullback (𝟙 _) iU i j ∧
      IsLocallyRankOne U (Hom.idealModule iU) ∧
      Nonempty ((Scheme.Modules.pullback iU).obj (Hom.idealModule iU) ≅
        twistingSheaf k (ULift.{u} (Fin 2)) 1) :=
  ⟨OpenRestriction.map i j h, inferInstance, OpenRestriction.map_comp i j h,
    OpenRestriction.isPullback i j h, OpenRestriction.isLocallyRankOne_ideal i j h hI,
    ⟨OpenRestriction.conormalTwistIso i j h eI⟩⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
