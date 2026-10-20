/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Graph
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Conditional canonical Cartier ideal comparisons

Extracted from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, mathematical hypotheses, and source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Cartier.Interfaces` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3f48fc9676ee2e94f74f4eeec8c0540a42d1af21717581d48a3d1c3cca20460e`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (IsLocallyRankOne)
open _root_.AlgebraicGeometry.Scheme.Modules (tensorSheaf tensorSheafLeftUnit tensorSheafMap)
open AlgebraicGeometry.Scheme.Hom
  (idealModule idealInclusion idealPullbackMap)
universe u

open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom.Cartier
/-- The previously source-reviewed general codimension-one Cartier family.
It refers to the actual closed-immersion ideal module. -/
def RegularCodimOneIdealInvertible : Prop :=
  ∀ (X C : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral C] (i : C ⟶ X),
    IsClosedImmersion i →
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
    (∀ c : C, (RingHom.ker (i.stalkMap c).hom).height = 1) →
      IsLocallyRankOne X (idealModule i)


end AlgebraicGeometry.Scheme.Hom.Cartier

/-!
The four below are separately source-reviewed universal derived corollaries,
not verbatim source statements and not global axioms. Retained translation
bridges identify locally rank-one actual kernel modules with effective Cartier
ideals, and the negative ideals with the dual of the usual positive divisor
bundles. The pullback is the constructed canonical kernel comparison; tensor
multiplication is the displayed actual map and its commuting inclusion triangle.

Sources inspected 2026-10-10:
* IntegralAvoidanceCartierPullback: Stacks 02OO (31.14.13(3)) and 0C4U (31.15.5).
* CartierSumIdealEqualsUnion: Stacks 0C4R (31.14.10).
* CartierIdealTensorProduct: Stacks 02OP (31.15.4), 31.14.6 (sum definition).
* FlatDVRFibreIdealTrivial: the first proof paragraph/part (4) of Stacks 0C5Z,
  0AUW, and the general principal-Cartier description 01WQ. The retained bridge
  identifies R/(an actual uniformizer) with the actual residue field, and its
  flat pullback ideal with multiplication by that uniformizer. No regular
  model, elliptic curve, reduced fibre, or intersection conclusion is an input.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.Hom.Cartier

/-- Source-reviewed general canonical Cartier pullback comparison. The source is
integral and its image is not contained in the divisor. -/
def IntegralAvoidanceCartierPullback : Prop :=
  ∀ (X D Y : Scheme.{u}) [IsIntegral Y] (i : D ⟶ X) (f : Y ⟶ X),
    IsClosedImmersion i → IsLocallyRankOne X (idealModule i) →
    ¬ Set.range f ⊆ Set.range i →
    IsIso (idealPullbackMap i (pullback.snd i f) f (pullback.fst i f)
      (pullback.condition (f := i) (g := f)))

/-- Source-reviewed general sum-equals-union identity. Cartierness of the actual
intersection on the second divisor is essential, and is not presumed from
topological distinctness. -/
def CartierSumIdealEqualsUnion : Prop :=
  ∀ (X C D : Scheme.{u}) (i : C ⟶ X) (j : D ⟶ X),
    IsClosedImmersion i → IsClosedImmersion j →
    IsLocallyRankOne X (idealModule i) → IsLocallyRankOne X (idealModule j) →
    IsLocallyRankOne D (idealModule (pullback.snd i j)) →
      i.ker * j.ker = i.ker ⊓ j.ker

/-- The actual multiplication of the two kernel ideal inclusions. -/
def idealMultiplication {X C D : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) :
    tensorSheaf X (idealModule i) (idealModule j) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  tensorSheafMap X (idealInclusion i) (idealInclusion j) ≫
    (tensorSheafLeftUnit X (SheafOfModules.unit X.ringCatSheaf)).hom

/-- Source-reviewed intrinsic tensor/ideal multiplication comparison, on arbitrary
schemes and arbitrary actual Cartier ideals. The target is the subscheme of
the native product of their actual ideal-sheaf data. -/
def CartierIdealTensorProduct : Prop :=
  ∀ (X C D : Scheme.{u}) (i : C ⟶ X) (j : D ⟶ X),
    IsClosedImmersion i → IsClosedImmersion j →
    IsLocallyRankOne X (idealModule i) → IsLocallyRankOne X (idealModule j) →
      ∃ e : tensorSheaf X (idealModule i) (idealModule j) ≅
        idealModule (i.ker * j.ker).subschemeι,
      e.hom ≫ idealInclusion (i.ker * j.ker).subschemeι = idealMultiplication i j

/-- Source-reviewed intrinsic principal-fibre ideal trivialization over any DVR.
This requires only flatness; regular models, elliptic curves, fibre reduction,
component geometry and numerical intersection conclusions do not occur. -/
def FlatDVRFibreIdealTrivial : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (π : X ⟶ Spec (.of R)), Flat π →
    Nonempty (idealModule
      (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≅
        SheafOfModules.unit X.ringCatSheaf)

end AlgebraicGeometry.Scheme.Hom.Cartier
end -- noncomputable section
