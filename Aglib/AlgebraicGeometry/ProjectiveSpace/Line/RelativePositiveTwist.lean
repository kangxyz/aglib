/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalFunctions
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.PositiveTwist
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The original coefficient field of a projective-line embedding

The actual global-functions coefficient equivalence determines the original
ring map to the SAME source field. Its exact affine-base triangle gives the
canonical coefficient-base-change lift. Separatedness, not flatness, makes
that lift closed when the original map is closed. Native arbitrary-ring
base change identifies the original pulled twist on the SAME source P1.
The actual field positivity theorem then supplies a strictly positive twist
for every original closed embedding over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Line

variable {A κ I : Type u} [CommRing A] [Field κ]

/-- The canonical original coefficient homomorphism, obtained from the
actual structural map and the original source-field coefficient map on Γ. -/
def coefficientHom (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    A →+* κ :=
  (globalFunctionsRingEquiv κ (ULift.{u} (Fin 2))).symm.toRingHom.comp
    ((t ≫ toSpec A I).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)

/-- Applying the ORIGINAL source structural coefficient map recovers exactly
the original A-valued structural pullback; no κ-algebra structure is supplied. -/
theorem coefficientHom_coefficient
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) (a : A) :
    globalFunctionsRingEquiv κ (ULift.{u} (Fin 2)) (coefficientHom t a) =
      (t ≫ toSpec A I).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a) :=
  (globalFunctionsRingEquiv κ (ULift.{u} (Fin 2))).apply_symm_apply _

/-- The original morphism lies over its canonical original coefficient map. -/
theorem coefficientHom_base
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    t ≫ toSpec A I = toSpec κ (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (coefficientHom t)) := by
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of A)).inv).mp
  calc
    (Scheme.ΓSpecIso (.of A)).inv ≫ (t ≫ toSpec A I).appTop =
        CommRingCat.ofHom (coefficientHom t) ≫ (Scheme.ΓSpecIso (.of κ)).inv ≫
          (toSpec κ (ULift.{u} (Fin 2))).appTop := by
      apply CommRingCat.hom_ext
      ext a
      exact (coefficientHom_coefficient t a).symm
    _ = (Scheme.ΓSpecIso (.of A)).inv ≫
        (Spec.map (CommRingCat.ofHom (coefficientHom t))).appTop ≫
          (toSpec κ (ULift.{u} (Fin 2))).appTop := by
      simpa only [Category.assoc] using
        congrArg (fun h ↦ h ≫ (toSpec κ (ULift.{u} (Fin 2))).appTop)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (coefficientHom t)))
    _ = (Scheme.ΓSpecIso (.of A)).inv ≫
        (toSpec κ (ULift.{u} (Fin 2)) ≫
          Spec.map (CommRingCat.ofHom (coefficientHom t))).appTop :=
      congrArg (fun h ↦ (Scheme.ΓSpecIso (.of A)).inv ≫ h)
        (Scheme.Hom.comp_appTop (toSpec κ (ULift.{u} (Fin 2)))
          (Spec.map (CommRingCat.ofHom (coefficientHom t)))).symm

/-- The original map lifted to the projective space over the SAME original κ,
using the proved native Cartesian coefficient square. -/
def coefficientLift
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace κ I :=
  (isPullback_map (coefficientHom t) I).lift t (toSpec κ (ULift.{u} (Fin 2)))
    (coefficientHom_base t)

@[reassoc (attr := simp)]
theorem coefficientLift_comp
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    coefficientLift t ≫ map (coefficientHom t) I = t :=
  (isPullback_map (coefficientHom t) I).lift_fst t (toSpec κ (ULift.{u} (Fin 2)))
    (coefficientHom_base t)

@[reassoc (attr := simp)]
theorem coefficientLift_toSpec
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    coefficientLift t ≫ toSpec κ I = toSpec κ (ULift.{u} (Fin 2)) :=
  (isPullback_map (coefficientHom t) I).lift_snd t (toSpec κ (ULift.{u} (Fin 2)))
    (coefficientHom_base t)

/-- The same lift is the literal native pair map to the actual base change,
followed by the original canonical projective base-change comparison. -/
theorem coefficientLift_baseChangeIso
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    coefficientLift t ≫ (baseChangeIso (coefficientHom t) I).hom =
      pullback.lift t (toSpec κ (ULift.{u} (Fin 2))) (coefficientHom_base t) := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeIso_hom_fst, coefficientLift_comp, pullback.lift_fst]
  · rw [Category.assoc, baseChangeIso_hom_snd, coefficientLift_toSpec, pullback.lift_snd]

/-- The actual lift is a morphism over the ORIGINAL source field, with its
original structural map as the literal base triangle. -/
def coefficientLiftOver
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) :
    Over.mk (toSpec κ (ULift.{u} (Fin 2))) ⟶ Over.mk (toSpec κ I) :=
  Over.homMk (coefficientLift t) (coefficientLift_toSpec t)

/-- Original closedness descends to the coefficient lift through the separated
coefficient morphism. No flatness or finiteness of A→κ is assumed. -/
theorem coefficientLift_isClosedImmersion
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I)
    [IsClosedImmersion t] : IsClosedImmersion (coefficientLift t) := by
  let : IsSeparated (Spec.map (CommRingCat.ofHom (coefficientHom t))) := inferInstance
  let : IsSeparated (map (coefficientHom t) I) :=
    MorphismProperty.of_isPullback (isPullback_map (coefficientHom t) I).flip inferInstance
  let : IsClosedImmersion (coefficientLift t ≫ map (coefficientHom t) I) := by
    rw [coefficientLift_comp]
    infer_instance
  exact IsClosedImmersion.of_comp (coefficientLift t) (map (coefficientHom t) I)

/-- Arbitrary-ring native twist base change gives the actual pulled twist on
the SAME original projective line, for every integer twist. -/
def coefficientLiftTwistingIso
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I) (d : ℤ) :
    (Scheme.Modules.pullback t).obj (twistingSheaf A I d) ≅
      (Scheme.Modules.pullback (coefficientLift t)).obj (twistingSheaf κ I d) :=
  (Scheme.Modules.pullbackCongr (coefficientLift_comp t).symm).app (twistingSheaf A I d) ≪≫
    ((Scheme.Modules.pullbackComp (coefficientLift t) (map (coefficientHom t) I)).symm.app
      (twistingSheaf A I d)) ≪≫
    (Scheme.Modules.pullback (coefficientLift t)).mapIso
      (twistingPullbackIso (coefficientHom t) I d)

/-- An original closed embedding of native P1 into projective space over any
commutative coefficient ring has an actual positive twist on the same P1. -/
theorem exists_positiveTwist_of_isClosedImmersion_over_ring [Finite I]
    (t : ProjectiveSpace κ (ULift.{u} (Fin 2)) ⟶ ProjectiveSpace A I)
    [IsClosedImmersion t] :
    ∃ d : ℕ, 0 < d ∧ Nonempty ((Scheme.Modules.pullback t).obj (twistingSheaf A I 1) ≅
      twistingSheaf κ (ULift.{u} (Fin 2)) (d : ℤ)) := by
  let : IsClosedImmersion (coefficientLiftOver t).left := coefficientLift_isClosedImmersion t
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_positiveTwist κ (coefficientLiftOver t)
  exact ⟨d, hd, ⟨coefficientLiftTwistingIso t 1 ≪≫ e⟩⟩

end AlgebraicGeometry.ProjectiveSpace.Line
