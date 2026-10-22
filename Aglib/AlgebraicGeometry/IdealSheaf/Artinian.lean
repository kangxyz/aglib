/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Length

/-!
# Artinian quotient subschemes from the original stalk quotients

The actual stalk ideal is the kernel of the original closed-immersion stalk
map. Finite length of these original quotient modules gives a locally Artinian
quotient subscheme. Finite support supplies compactness and hence Artinianness.
No blowup, surface, regularity or integrality condition is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The actual ideal stalk at a point of its quotient subscheme is the kernel
of the original closed-immersion stalk map. -/
theorem stalkIdeal_subschemeι_eq_ker_stalkMap {X : Scheme.{u}}
    (J : X.IdealSheafData) (c : J.subscheme) :
    J.stalkIdeal (J.subschemeι c) = RingHom.ker (J.subschemeι.stalkMap c).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (J.subschemeι c)) isOpen_univ
  rw [J.stalkIdeal_eq_map ⟨U, hU⟩ (J.subschemeι c) hcU,
    Scheme.Hom.ker_stalkMap_eq_map_ker_app J.subschemeι U hU c hcU,
    J.ker_subschemeι_app ⟨U, hU⟩]

/-- Finite length of every original stalk quotient makes the actual quotient
subscheme locally Artinian, using its original closed-immersion stalk maps. -/
theorem isLocallyArtinian_subscheme_of_stalkQuotient_finiteLength
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (h : ∀ x, IsFiniteLength (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x)) :
    IsLocallyArtinian J.subscheme := by
  let : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  apply IsLocallyArtinian.of_topologicalKrullDim_le_zero
  rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
  apply iSup_le
  intro c
  let A := X.presheaf.stalk (J.subschemeι c)
  let φ := (J.subschemeι.stalkMap c).hom
  let : IsArtinian A (A ⧸ J.stalkIdeal (J.subschemeι c)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (h (J.subschemeι c))).2
  let : IsArtinianRing (A ⧸ J.stalkIdeal (J.subschemeι c)) := isArtinian_of_tower A inferInstance
  let : IsArtinianRing (A ⧸ RingHom.ker φ) := by
    rw [← stalkIdeal_subschemeι_eq_ker_stalkMap J c]
    infer_instance
  let e := φ.quotientKerEquivOfSurjective (J.subschemeι.stalkMap_surjective c)
  let : IsArtinianRing (J.subscheme.presheaf.stalk c) := e.isArtinianRing
  exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (J.subscheme.presheaf.stalk c))

/-- Finite support together with finite original local colengths gives an
actual Artinian quotient subscheme. -/
theorem isArtinian_subscheme_of_finite_support_of_stalkQuotient_finiteLength
    {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (hs : (J.support : Set X).Finite)
    (h : ∀ x, IsFiniteLength (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x)) :
    IsArtinianScheme J.subscheme := by
  let : Finite (J.support : Set X) := hs.to_subtype
  let e : J.subscheme ↪ (J.support : Set X) :=
    { toFun := fun c ↦ ⟨J.subschemeι c, by rw [← J.range_subschemeι]; exact Set.mem_range_self c⟩
      inj' := fun c d he ↦ J.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val he) }
  let : Finite J.subscheme := Finite.of_injective e e.injective
  let : IsLocallyArtinian J.subscheme :=
    isLocallyArtinian_subscheme_of_stalkQuotient_finiteLength J h
  exact ⟨⟩

end AlgebraicGeometry.Scheme.IdealSheafData
