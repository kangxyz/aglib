/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Gluing
public import Aglib.RingTheory.Grassmannian.ChartPolynomial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness and flatness of the Grassmannian

The structure morphism `toBase R k n : scheme R k n ⟶ Spec R` of the glued Grassmannian is smooth
(`smooth_toBase`), hence flat (`flat_toBase`). Smoothness is local on the source, and on the
coordinate chart at `I : Fin k → Fin n` it is the smoothness of the chart ring
`ChartRing R (coordinateTuple R I)` over `R` (`Module.Grassmannian.smooth_chartRing`): a
polynomial ring in the `k (n - k)` free coordinates when `I` is injective, and the zero ring
otherwise. The same instances are stated for `(schemeOver R k n).hom`.

Sources: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 8
("`Grass(r, d) → Spec Z` is smooth of relative dimension `d(r - d)`", stated there without a
separate proof); Stacks, Tag 089T (proof of Lemma 27.22.1: the open subfunctors `F_i` are affine
spaces `A^{k(n-k)}`). Stacks, Section 27.22 (Tag 089R) states no smoothness or flatness of the
Grassmannian. The relative dimension is not recorded here. Premise: `BaseChangeMkQFormula`, the
instance argument of the gluing.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) (k n : ℕ)
  [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- **The Grassmannian is smooth over its base**: on each coordinate chart the structure morphism
is the spectrum of `R → R[Φ_{aj} : j ∉ range I]`, or the empty scheme. -/
instance smooth_toBase : Smooth (toBase R k n) := by
  -- Instance search does not find `IsZariskiLocalAtSource @Smooth` here.
  have : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (glueData R k n).openCover (fun I ↦ ?_)
  have h := ι_toBase (R := R) (k := k) (n := n) I
  change Smooth ((glueData R k n).ι I ≫ toBase R k n)
  rw [h, algSpec_obj_hom]
  exact HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr (Module.Grassmannian.smooth_chartRing R I.down))

/-- **The Grassmannian is flat over its base.** -/
instance flat_toBase : Flat (toBase R k n) :=
  inferInstance

instance smooth_schemeOver_hom : Smooth (schemeOver R k n).hom :=
  inferInstanceAs (Smooth (toBase R k n))

instance flat_schemeOver_hom : Flat (schemeOver R k n).hom :=
  inferInstanceAs (Flat (toBase R k n))

end AlgebraicGeometry.Grassmannian
