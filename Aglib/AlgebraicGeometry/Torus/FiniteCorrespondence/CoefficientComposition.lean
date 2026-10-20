/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FlatPrincipalComposition
public import Mathlib.RingTheory.RingHom.Flat

/-!
# CoefficientComposition for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `CoefficientComposition.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`09eb70c3d37933479b03eff26f1cc435e7d8e7081c1878a0aa25a8e437205a2e`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
section ExplicitMaps
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The extended local length at `q` after successively extending the prime ideal along `f` and
`g`. -/
def compositeLength (f : R →+* S) (g : S →+* T) (p : FiniteDominantPrime R) (q :
    FiniteDominantPrime T) : ℕ∞ :=
  Module.length (Localization.AtPrime q.val)
    (Localization.AtPrime q.val ⊗[Laurent T]
      (Laurent T ⧸ (p.val.map (coefficientMap f)).map (coefficientMap g)))

theorem flat_principal_coeffFor
    [IsDomain R] [IsDomain S] [IsNoetherianRing S] [IsNoetherianRing T]
    (f : R →+* S) (hf : f.Flat) (g : S →+* T) (b : S) (hb0 : b ≠ 0)
    (hg : Function.Surjective g) (hb : RingHom.ker g = Ideal.span ({b} : Set S))
    (p : FiniteDominantPrime R) (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMapFor g
      (quotientFibreCycleMapFor f (FreeAbelianGroup.of p))) =
        ((compositeLength f g p q).toNat : ℤ) := by
  let := f.toAlgebra
  let := g.toAlgebra
  let : Module.Flat R S := hf
  exact flat_then_principal_coeff p b hb0 hg hb q

theorem flat_second_coeffFor
    [IsNoetherianRing S] [IsNoetherianRing T]
    (f : R →+* S) (g : S →+* T) (hg : g.Flat)
    (p : FiniteDominantPrime R) (hdom : ∀ Q ∈ (p.val.map (coefficientMap f)).minimalPrimes,
      Q.under S = ⊥)
    (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMapFor g
      (quotientFibreCycleMapFor f (FreeAbelianGroup.of p))) =
        ((compositeLength f g p q).toNat : ℤ) := by
  let := f.toAlgebra
  let := g.toAlgebra
  let : Module.Flat S T := hg
  exact then_flat_coeff p hdom q

theorem mappedIdeal_comp (f : R →+* S) (g : S →+* T) (I : Ideal (Laurent R)) :
    (I.map (coefficientMap f)).map (coefficientMap g) = I.map (coefficientMap (g.comp f)) := by
  rw [Ideal.map_map]
  congr 1
  exact (MonoidAlgebra.mapRingHom_comp (M := Character) g f).symm
end ExplicitMaps

end AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
