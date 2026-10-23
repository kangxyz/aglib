/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ArtinPullback
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Nilpotent
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Original root-cohomology across an actual Artin nilpotent quotient

The proof combines the actual finite-etale quotient-base-change equivalence,
the actual Artin site comparison, and original cohomology pullback. The Artin
ring is not replaced by its reduction in any multiplicative-coefficient claim.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'

/-- Original root-cohomology pullback across an actual nilpotent quotient of an Artin ring. -/
theorem rootsCohomologyPullback_quotient_bijective
    (R : Type u) [CommRing R] [IsArtinianRing R] (I : Ideal R) (hI : IsNilpotent I)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of R)))]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (Spec (.of (R ⧸ I))))]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of R), ⊤))) (q : ℕ) :
    Function.Bijective (rootsCohomologyPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) n hn hinv q) := by
  let f := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hnil : I ≤ _root_.nilradical R :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).mp hI
  let : Surjective f :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hnil).surjective⟩
  let : (FiniteEtale.baseChange f).IsEquivalence :=
    FiniteEtale.Nilpotent.quotient_baseChange_isEquivalence R I hI
  exact rootsCohomologyPullback_bijective_of_artin_finiteEtale_equivalence f n hn hinv q

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
