/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules.Stalk
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.AlgebraicGeometry.Modules.Pullback.LocalSpectrum
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.RegularLocalRing.RankOneKernel

/-!
# Ambient regularity along a regular Cartier closed subscheme

`Aglib.AlgebraicGeometry.IdealSheaf.Cartier.RegularQuotient` uses the actual ideal-module
stalk, the actual closed-immersion stalk map, and its canonical quotient equivalence.
Local rank one of the ideal module and regularity of the closed subscheme imply
regularity of the Noetherian ambient stalks along the immersion.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {Z X : Scheme.{u}}

/-- The stalk of the actual kernel ideal sheaf at an image point is the kernel
of the original closed-immersion stalk map. -/
theorem ker_stalkIdeal_eq_ker_stalkMap (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    i.ker.stalkIdeal (i z) = RingHom.ker (i.stalkMap z).hom := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show i z ∈ (⊤ : X.Opens) from trivial)
  rw [i.ker.stalkIdeal_eq_map ⟨U, hU⟩ (i z) hxU, i.ker_apply ⟨U, hU⟩,
    ker_stalkMap_eq_map_ker_app i U hU z hxU]

/-- A regular point of a closed subscheme with locally rank-one actual ideal module
has a regular ambient local ring, provided that ambient local ring is Noetherian. -/
theorem isRegularLocalRing_stalk_image_of_isLocallyRankOne_ideal
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (z : Z)
    [IsNoetherianRing (X.presheaf.stalk (i z))]
    [IsRegularLocalRing (Z.presheaf.stalk z)] :
    IsRegularLocalRing (X.presheaf.stalk (i z)) := by
  let R := X.presheaf.stalk (i z)
  let L : LineBundle (Spec R) :=
    ⟨(Scheme.Modules.pullback (X.fromSpecStalk (i z))).obj (idealModule i),
      pullback_locallyRankOne _ _ hI⟩
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing R L
  let eM : (moduleStalk X (i z)).obj (idealModule i) ≅ ModuleCat.of R R :=
    stalkFromSpecStalkSectionsIso X (i z) (idealModule i) ≪≫
      moduleSpecΓFunctor.mapIso e ≪≫ (tilde.isoTop (ModuleCat.of R R)).symm
  let eK : RingHom.ker (i.stalkMap z).hom ≃ₗ[R] R :=
    (LinearEquiv.ofEq _ _ (i.ker_stalkIdeal_eq_ker_stalkMap z).symm).trans
      ((idealModuleStalkEquiv i (i z)).symm.trans eM.toLinearEquiv)
  exact IsRegularLocalRing.of_surjective_ker_freeRankOne
    (i.stalkMap z).hom (i.stalkMap_surjective z) eK

/-- A regular Cartier closed subscheme of a locally Noetherian scheme has regular
ambient stalks at all of its image points. -/
theorem isRegularLocalRing_stalk_image_of_cartier
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (hZ : RegularStalks Z) (z : Z) :
    IsRegularLocalRing (X.presheaf.stalk (i z)) := by
  let := hZ z
  exact i.isRegularLocalRing_stalk_image_of_isLocallyRankOne_ideal hI z

end AlgebraicGeometry.Scheme.Hom
