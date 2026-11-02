/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual closed-immersion kernels on stalks and under base change

The original ideal stalk is the kernel of the original stalk map. In an
arbitrary cartesian square of a closed immersion, the original kernel ideal
is the actual inverse-image ideal. These general constructions are lowered
from the Cartier regular-quotient and avoidance consumers, with their existing
names and hypotheses preserved. No Cartier, flatness, regularity, or
Noetherian condition is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X D Y D' : Scheme.{u}}

/-- The stalk of the actual kernel ideal sheaf at an image point is the kernel
of the original closed-immersion stalk map. -/
theorem ker_stalkIdeal_eq_ker_stalkMap (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    i.ker.stalkIdeal (i z) = RingHom.ker (i.stalkMap z).hom := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show i z ∈ (⊤ : X.Opens) from trivial)
  rw [i.ker.stalkIdeal_eq_map ⟨U, hU⟩ (i z) hxU, i.ker_apply ⟨U, hU⟩,
    ker_stalkMap_eq_map_ker_app i U hU z hxU]

/-- The kernel ideal data in an actual cartesian square of a closed immersion is
the native inverse-image ideal data. -/
theorem ker_eq_comap_of_isPullback_of_isClosedImmersion
    (i : D ⟶ X) (i' : D' ⟶ Y) (f : Y ⟶ X) (a : D' ⟶ D)
    (H : IsPullback a i' i f) [IsClosedImmersion i] : i'.ker = i.ker.comap f := by
  have hsnd : (pullback.snd i f).ker = i.ker.comap f := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f,
      ← Hom.ker_comp_of_isIso (pullbackSymmetry i f).hom (pullback.fst f i)]
    simp
  rw [← hsnd, ← Hom.ker_comp_of_isIso H.isoPullback.hom (pullback.snd i f)]
  simp

end AlgebraicGeometry.Scheme.Hom
