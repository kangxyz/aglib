/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraStructure
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.StageAlgebraEtale
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoherentGoodOpens
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.QuotientAlgebras

/-!
# Actual finite-etale covers from an algebraized original cover tower

The all-order algebra etaleness hypotheses are proved from the given original
finite-etale stages and the specified algebraization comparison. No etaleness,
good-cover, compatible-gluing, or finite-subcover hypothesis is exported.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonObj TensorProduct AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u
open Modules Modules.Coherent Modules.Algebra


variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) [UniversallyClosed f]
  (I : Ideal A) (hI : I ≠ ⊤)
  (T : CoverSystem (idealThickeningIdealSheaf f I))
  (d : AdicAlgebraizationData T.adicSystem)

omit [IsLocalRing A] [UniversallyClosed f] in
/-- The actual coherent algebraized underlying module is quasicoherent. -/
theorem algebraized_isQuasicoherent : d.algebra.X.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (d.algebra_coherent R j).1)

omit [IsLocalRing A] [UniversallyClosed f] in
/-- Every literal algebra reduction is etale, proved from the actual original
stage cover and the original quotient-map comparison. This is not an input. -/
theorem algebraized_quotient_etale (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Algebra.Etale (Γ(X, U) ⧸ sectionIdeal f I U ^ n)
      ((Γ(X, U) ⧸ sectionIdeal f I U ^ n) ⊗[Γ(X, U)] Γ(d.algebra.X, U)) := by
  let c := d.affineQuotientAlgebraCoordinates f I ⟨U, hU⟩ n
  let J := sectionIdeal f I U ^ n
  have hJ : J = (idealThickeningIdealSheaf f I ^ n).ideal ⟨U, hU⟩ := by
    simp only [J, sectionIdeal, IdealSheafData.ideal_pow, Pi.pow_apply,
      idealThickeningIdealSheaf_ideal, idealSectionRingHom]
  have hc : c.scalar.Etale :=
    etale_of_original_quotientScalar (idealThickeningIdealSheaf f I ^ n)
      (T.cover n) ⟨U, hU⟩ J hJ c.scalar c.factor
  let := c.scalar.toAlgebra
  have : Algebra.Etale (Γ(X, U) ⧸ J) Γ(T.adicSystem.obj.obj (op n), U) := hc
  exact Algebra.Etale.of_equiv c.equiv.symm

/-- The global cover constructed from the original tower and its actual
algebraization data, with no added local-etaleness or gluing premises. -/
def algebraizedCover : Scheme.FiniteEtale X := by
  let := algebraized_isQuasicoherent f I T d
  exact finiteEtaleCoverOfEtaleQuotients f I hI d.algebra.X d.algebra_coherent
    (fun U hU n _ => algebraized_quotient_etale f I T d U hU n)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
