/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FiniteDimension
public import Aglib.AlgebraicGeometry.Dimension.FiniteTypeFibres

/-! # Actual finite relative torsion bounds for proper morphisms

The proved auxiliary geometric-field bound and original proper geometric-stalk
comparison give a finite relative bound on all internally torsion coefficients.
For a quasi-compact target, the original finite-type generator bound supplies
one bound valid for the original morphism and every further actual base change.
The new target need not be quasi-compact. Neither Noetherianity nor absolute
cohomological dimension of any base is assumed.

The explicit auxiliary bound is `3 * d - 1`, not the sharper `2 * d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- A supplied finite bound on the actual geometric fibre dimensions gives
an actual original higher-image bound on every internally torsion coefficient,
over an arbitrary base. The numeric bound is auxiliary, not sharp. -/
theorem isZero_higherDirectImage_obj_of_geometricFibres_dimension_le
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (d : ℕ)
    (hdim : ∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      topologicalKrullDim (pullback (C := Scheme) f η) ≤ (d : ℕ))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 3 * d - 1 < q) : IsZero ((higherDirectImage f q).obj F) := by
  apply isZero_higherDirectImage_obj_of_geometricFiber_H_standard f F hF q
  intro K _ _ η
  exact subsingleton_H_of_isTorsion_of_proper_finite_dimension
    (pullback.snd f η) d (hdim K η) ((inverseImage (pullback.fst f η)).obj F)
      (hF.inverseImage (pullback.fst f η)) q hq

/-- A proper morphism with quasi-compact target has one actual all-torsion
bound valid for itself and every further original scheme base change.
No quasi-separatedness, Noetherianity or absolute cohomological bound on the
target is imposed, and the further target need not be quasi-compact. -/
theorem exists_universal_higherDirectImage_torsion_bound
    {X S : Scheme.{u}} [CompactSpace S] (f : X ⟶ S) [IsProper f] :
    ∃ D : ℕ,
      (∀ F : AbelianSheaf.{u, u + 1} X, IsTorsion X F →
        ∀ q : ℕ, D < q → IsZero ((higherDirectImage f q).obj F)) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S)
        (F : AbelianSheaf.{u, u + 1} (pullback f g)), IsTorsion (pullback f g) F →
          ∀ q : ℕ, D < q → IsZero ((higherDirectImage (pullback.snd f g) q).obj F) := by
  obtain ⟨d, hd⟩ := f.exists_geometricFiber_dimension_le
  refine ⟨3 * d - 1, ?_, ?_⟩
  · intro F hF q hq
    exact isZero_higherDirectImage_obj_of_geometricFibres_dimension_le f d
      (fun K _ _ η => hd K η) F hF q hq
  · intro T g F hF q hq
    apply isZero_higherDirectImage_obj_of_geometricFibres_dimension_le
      (pullback.snd f g) d ?_ F hF q hq
    intro K _ _ η
    have he := IsHomeomorph.topologicalKrullDim_eq _
      (pullbackLeftPullbackSndIso f g η).hom.homeomorph.isHomeomorph
    exact he.le.trans (hd K (η ≫ g))

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
