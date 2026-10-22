/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoherentAlgebraGluing
public import Aglib.AlgebraicGeometry.Morphisms.Etale.AffineStalkAlgebra
public import Aglib.AlgebraicGeometry.Stalk.LocalBaseIdeal
public import Aglib.RingTheory.Etale.Adic.BaseChange

/-!
# Good affine covers from the original all-order algebra reductions

Every closed-fibre point has a good affine neighborhood by the finite local
criterion applied to the original germ. Universal closedness over the local
base then makes the entire family cover. The resulting finite-etale cover is
the native gluing of the original coherent section spectra.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonObj TensorProduct AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Algebra

universe u
variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) [UniversallyClosed f]
  (I : Ideal A) (hI : I ≠ ⊤)
  (M : X.Modules) [MonObj M] [IsCommMonObj M] [M.IsQuasicoherent]
  (hM : QuasiCoherent.affineLocallyFiniteType X M)

/-- The ideal in the original section ring induced by the base ideal. -/
abbrev sectionIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  I.map (idealSectionRingHom X (idealThickeningBaseScalar f) U)

variable (hred : ∀ (U : X.Opens), IsAffineOpen U → ∀ n : ℕ, 0 < n →
  Algebra.Etale (Γ(X, U) ⧸ sectionIdeal f I U ^ n)
    ((Γ(X, U) ⧸ sectionIdeal f I U ^ n) ⊗[Γ(X, U)] Γ(M, U)))

include hI hM hred in
/-- Actual all-order algebra reductions imply good affine neighborhoods
at every point of the proper model over the local base. -/
theorem goodOpen_cover_of_etale_quotients :
    ∀ x : X, ∃ U, FiniteEtale.AffineAlgebraGluing.IsGood
      (sectionRingPresheaf M) (sectionRingUnit M) U ∧ x ∈ U := by
  apply FiniteEtale.AffineAlgebraGluing.goodOpen_cover_of_etale_closedFiber_stalks
    (sectionRingPresheaf M) (sectionRingUnit M) (sectionRing_restriction_isPullback M) f
    (sectionToOpen_finite M hM) (sectionToOpen_locallyOfFinitePresentation M hM)
  intro x hx
  have hfx : f x = IsLocalRing.closedPoint A := by
    rw [LocalRing.ResidueFiber.projection, Scheme.Pullback.range_fst] at hx
    obtain ⟨y, hy⟩ := hx
    have he : y = IsLocalRing.closedPoint (IsLocalRing.ResidueField A) := Subsingleton.elim _ _
    subst y
    exact hy.symm.trans (IsLocalRing.comap_closedPoint (IsLocalRing.residue A))
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) by trivial)
  refine ⟨U, hU, hxU, ?_⟩
  change Etale (pullback.snd
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(M, U))) ≫ hU.isoSpec.inv)
    (U.toScheme.fromSpecStalk ⟨x, hxU⟩))
  apply etale_stalkBaseChange_of_etale_tensor hU Γ(M, U) x hxU
  let := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : Module.Finite Γ(X, U) Γ(M, U) := finite_sectionAlgebra M hM ⟨U, hU⟩
  apply Algebra.etale_baseChange_of_etale_quotient_pow (sectionIdeal f I U)
  · exact f.map_sectionIdeal_germ_ne_top_of_closedPoint x I hI hfx U hxU
  · exact hred U hU

/-- Native gluing of the original section spectra. The only all-order premise
is algebraic etaleness of their literal reductions, not a gluing oracle. -/
def finiteEtaleCoverOfEtaleQuotients : Scheme.FiniteEtale X :=
  FiniteEtale.AffineAlgebraGluing.cover (sectionRingPresheaf M) (sectionRingUnit M)
    (sectionRing_restriction_isPullback M)
    (goodOpen_cover_of_etale_quotients f I hI M hM hred) (sectionRingUnit_finite M hM)

/-- The global output restricts to each original good affine section spectrum. -/
def finiteEtaleCoverOfEtaleQuotientsLocalIso
    (U : FiniteEtale.AffineAlgebraGluing.GoodOpen (sectionRingPresheaf M) (sectionRingUnit M)) :
    (FiniteEtale.baseChange U.val.ι).obj (finiteEtaleCoverOfEtaleQuotients f I hI M hM hred) ≅
      FiniteEtale.AffineAlgebraGluing.localCover (sectionRingPresheaf M) (sectionRingUnit M)
        (sectionRing_restriction_isPullback M)
        (goodOpen_cover_of_etale_quotients f I hI M hM hred) (sectionRingUnit_finite M hM) U :=
  FiniteEtale.AffineAlgebraGluing.localCoverIso (sectionRingPresheaf M) (sectionRingUnit M)
    (sectionRing_restriction_isPullback M)
    (goodOpen_cover_of_etale_quotients f I hI M hM hred) (sectionRingUnit_finite M hM) U

end AlgebraicGeometry.Scheme.Modules.Algebra
