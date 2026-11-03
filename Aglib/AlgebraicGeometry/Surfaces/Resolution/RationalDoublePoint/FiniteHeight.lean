/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Height
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.FinitePrefixGeometry
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalMixedPath

/-!
# Finite original singular height from genuine mixed-path geometry

Finite fibres are derived on the actual rational model. A compatible sequence
would be the original infinite path, contradicting the constructed mixed-case
marking over an earlier complete base. No empty-level or path-termination
hypothesis is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away
open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
open AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint

/-- An actual full cone over an earlier complete base has finite original
singular-prefix height. The rational model base and selected stalk need not
be complete. -/
theorem exists_empty_singularPrefix_level_of_initial_cone_of_complete_base
    (S : Type u) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    (hS : IsNagataRing.{u, 0} S) (hdS : ringKrullDim S = 2)
    (hRat : NormalModificationH1Vanishing S)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of S)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (t : maximalIdeal (X.presheaf.stalk x))
    (g : Fin 2 → maximalIdeal (X.presheaf.stalk x))
    (hgen : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t g i : X.presheaf.stalk x)) =
        maximalIdeal (X.presheaf.stalk x))
    (q : MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x)))
    (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (hdA : ringKrullDim A = 2)
    (a : A →+* X.presheaf.stalk x) [IsLocalHom a]
    (hinj : Function.Injective a) (hres : (ResidueField.map a).Finite) :
    ∃ n : ℕ, IsEmpty (SingularPrefix X x n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨_, hn, _, hN, hd, hclosed, hne, _, _, hR⟩ :=
    singular_stalk_properties_of_rational_model S hS hdS hRat f hX hff x hx
  apply exists_empty_level_of_no_compatible_sequence
  · intro n p
    exact singularPrefix_parent_fiber_finite S hS hdS hRat f hff hX x hx p
  · rintro ⟨b, hb⟩
    let P := path b hb hclosed hne
    let : IsIntegrallyClosed (P.localRing 0) := hn
    let aP : A →+* P.localRing 0 := a
    let : IsLocalHom aP := inferInstanceAs (IsLocalHom a)
    obtain ⟨n, hn⟩ :=
      exists_regular_original_point_of_initial_cone_of_complete_base
        P hN hd hR t g hgen q hq0 hq hker A hdA aP hinj hres
    exact (path_eligible b hb hclosed hne hx n) hn

end AlgebraicGeometry.Scheme.RationalDoublePoint
