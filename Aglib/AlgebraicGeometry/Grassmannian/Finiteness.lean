/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Gluing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finiteness of the Grassmannian

The glued Grassmannian `scheme R k n` is covered by the finitely many coordinate charts
`Spec (ChartRing R x)`, indexed by the tuples `ULift (Fin k → Fin n)`, and each chart ring is a
quotient of the polynomial ring `R[Φ_{aj}]` in the `k n` variables `Φ_{aj}`. Hence:

- `scheme R k n` is quasi-compact (`compactSpace_scheme`), so its structure morphism
  `toBase R k n` to `Spec R` is quasi-compact (`quasiCompact_toBase`);
- `toBase R k n` is locally of finite type (`locallyOfFiniteType_toBase`);
- for a Noetherian ring `R`, `scheme R k n` is locally Noetherian and Noetherian
  (`isLocallyNoetherian_scheme`, `isNoetherian_scheme`).

These are instances, also stated for `(schemeOver R k n).left` and `(schemeOver R k n).hom`, which
are `scheme R k n` and `toBase R k n` by definition.

Sources: Stacks, Tag 089T (Lemma 27.22.1, TeX snapshot `a04446e5`), whose proof covers `G(k, n)`
by finitely many open subfunctors `F_i`, each an affine space `A^{k(n-k)}_Z`; since `k` here is the
rank of the quotient, `scheme R k n` is Stacks' `G(n − k, n)` over `Spec R`. Stacks states no
separate finiteness lemma for the Grassmannian. A Noetherian scheme is by definition locally
Noetherian and quasi-compact (Stacks, Tag 01OV, Definition 28.5.1); Tag 01T6 (locally of finite
type over a locally Noetherian base is locally Noetherian) is not used, since the chart rings are
Noetherian directly. Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §1, "Construction of Grassmannian", pp. 7–8 (the scheme is glued from the
affine charts `U^I ≅ A^{d(r-d)}_Z` over `Spec Z`, finitely many). Encoded subset: the glued scheme
`scheme R k n` over `Spec R` for every commutative ring `R` and all `k`, `n` (the Noetherian
statements for Noetherian `R`). Charts at non-injective tuples are empty (zero chart ring), which
does not affect finiteness. Premise: `BaseChangeMkQFormula`, the instance argument of the gluing,
supplied by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) (k n : ℕ)

/-- The chart rings of the Grassmannian are of finite type over `R`. -/
theorem finiteType_chartRing (x : Fin k → Fin n → R) :
    Algebra.FiniteType R (Module.Grassmannian.ChartRing R x) :=
  inferInstanceAs (Algebra.FiniteType R (MvPolynomial (Fin k × Fin n) R ⧸ _))

variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

instance finite_glueData_J : Finite (glueData R k n).J :=
  inferInstanceAs (Finite (ULift.{u} (Fin k → Fin n)))

/-- The Grassmannian is quasi-compact: it is covered by finitely many affine charts. -/
instance compactSpace_scheme : CompactSpace (scheme R k n) :=
  have : ∀ i, CompactSpace ((glueData R k n).openCover.X i) := fun i ↦
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of
      (Module.Grassmannian.ChartRing R (Module.Grassmannian.coordinateTuple R i.down)))))
  have : Finite (glueData R k n).openCover.I₀ := inferInstanceAs (Finite (glueData R k n).J)
  (glueData R k n).openCover.compactSpace

/-- The structure morphism of the Grassmannian is quasi-compact. -/
instance quasiCompact_toBase : QuasiCompact (toBase R k n) :=
  quasiCompact_of_compactSpace _

/-- The structure morphism of the Grassmannian is locally of finite type. -/
instance locallyOfFiniteType_toBase : LocallyOfFiniteType (toBase R k n) := by
  -- Instance search does not find `IsZariskiLocalAtSource @LocallyOfFiniteType` here.
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (glueData R k n).openCover (fun I ↦ ?_)
  have h := ι_toBase (R := R) (k := k) (n := n) I
  change LocallyOfFiniteType ((glueData R k n).ι I ≫ toBase R k n)
  rw [h, algSpec_obj_hom]
  exact HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr (finiteType_chartRing R k n _))

/-- Over a Noetherian ring, the Grassmannian is locally Noetherian. -/
instance isLocallyNoetherian_scheme [IsNoetherianRing R] : IsLocallyNoetherian (scheme R k n) :=
  (isLocallyNoetherian_iff_openCover (glueData R k n).openCover).mpr (fun i ↦
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of
      (Module.Grassmannian.ChartRing R (Module.Grassmannian.coordinateTuple R i.down))))))

/-- **Over a Noetherian ring, the Grassmannian is Noetherian.** -/
instance isNoetherian_scheme [IsNoetherianRing R] : IsNoetherian (scheme R k n) where

/-! The same instances for the Grassmannian as a scheme over `Spec R`. -/

instance compactSpace_schemeOver_left : CompactSpace (schemeOver R k n).left :=
  inferInstanceAs (CompactSpace (scheme R k n))

instance quasiCompact_schemeOver_hom : QuasiCompact (schemeOver R k n).hom :=
  inferInstanceAs (QuasiCompact (toBase R k n))

instance locallyOfFiniteType_schemeOver_hom : LocallyOfFiniteType (schemeOver R k n).hom :=
  inferInstanceAs (LocallyOfFiniteType (toBase R k n))

instance isLocallyNoetherian_schemeOver_left [IsNoetherianRing R] :
    IsLocallyNoetherian (schemeOver R k n).left :=
  inferInstanceAs (IsLocallyNoetherian (scheme R k n))

instance isNoetherian_schemeOver_left [IsNoetherianRing R] :
    IsNoetherian (schemeOver R k n).left :=
  inferInstanceAs (IsNoetherian (scheme R k n))

end AlgebraicGeometry.Grassmannian
