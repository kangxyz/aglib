/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootComplementBaseChange
public import Aglib.AlgebraicGeometry.Spec.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # The original parameter-complement square at a genuine stage

The native coefficient-localization square uses the same map appearing in
the root-complement triangle. Genuine etaleness transfers to that map, and
its nonempty source over an integral complement makes it dominant.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (f : R)

local notation "U" => Localization.Away f
local notation "V" => Localization.Away (algebraMap R B f)
local notation "g" => Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual parameter-complement square, without replacement localization maps. -/
theorem parameterComplementBaseChange_isPullback :
    IsPullback g (Spec.algebraMap B V) (Spec.algebraMap R U) (Spec.algebraMap R B) := by
  apply IsOpenImmersion.isPullback
  · simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (parameterComplementBaseChangeHom_comp B f).symm
  · have hR : (Spec.algebraMap R U).opensRange = PrimeSpectrum.basicOpen f :=
      Scheme.Hom.opensRange_localizationAway (R := .of R) f
    have hB : (Spec.algebraMap B V).opensRange =
        PrimeSpectrum.basicOpen (algebraMap R B f) :=
      Scheme.Hom.opensRange_localizationAway (R := .of B) (algebraMap R B f)
    rw [hR, hB]
    exact SpecMap_preimage_basicOpen (CommRingCat.ofHom (algebraMap R B)) f

/-- The original complement coefficient map is etale at a genuine etale stage. -/
theorem parameterComplementBaseChange_etale [Algebra.Etale R B] : Etale g := by
  let : Etale (Spec.algebraMap R B) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  exact MorphismProperty.of_isPullback (parameterComplementBaseChange_isPullback R B f).flip
    inferInstance

/-- The unchanged nonempty etale complement map is dominant over the original
integral complement. This does not assume the whole pulled-back cover connected. -/
theorem parameterComplementBaseChange_dominant [IsDomain R] [Algebra.Etale R B]
    (hf : f ≠ 0) [Nonempty (Spec (.of V))] : IsDominant g := by
  let : IsDomain U := Localization.Away.isDomain hf
  let : Etale g := parameterComplementBaseChange_etale R B f
  constructor
  exact (g).isOpenMap.isOpen_range.dense (Set.range_nonempty g)

end AlgebraicGeometry.Scheme.Kummer
