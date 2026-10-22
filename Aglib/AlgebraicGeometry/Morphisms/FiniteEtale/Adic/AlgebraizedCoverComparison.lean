/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraizedCover
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.GoodAffineComparison
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.StageAlgebraComparison

/-!
# Specified comparisons with every original finite-etale stage

The comparison is glued from the spectra of the actual quotient maps of the
specified algebraization datum. It is not selected from an existence theorem,
and its first stage is the originally prescribed cover in the actual tower.
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
open Modules Modules.Coherent Modules.Algebra AffineAlgebraGluing

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) [UniversallyClosed f]
  (I : Ideal A) (hI : I ≠ ⊤)
  (T : CoverSystem (idealThickeningIdealSheaf f I))
  (d : AdicAlgebraizationData T.adicSystem)

/-- The actual base change of the global output is the original stage cover.
Its local maps are precisely the spectra of the original quotient-unit maps. -/
def algebraizedStageIso (n : ℕ) :
    (baseChange (idealThickeningIdealSheaf f I ^ n).subschemeι).obj
      (algebraizedCover f I hI T d) ≅ T.cover n := by
  let := algebraized_isQuasicoherent f I T d
  let F := sectionRingPresheaf d.algebra.X
  let scalarUnit := sectionRingUnit d.algebra.X
  let hcart := sectionRing_restriction_isPullback d.algebra.X
  let hred := fun U hU n (_ : 0 < n) => algebraized_quotient_etale f I T d U hU n
  let hcover := goodOpen_cover_of_etale_quotients f I hI d.algebra.X d.algebra_coherent hred
  let hfinite := sectionRingUnit_finite d.algebra.X d.algebra_coherent
  let q := d.quotientMaps.app (op n)
  refine ObjectProperty.isoMk _
    (originalComparisonIso F scalarUnit hcart hcover hfinite
      (idealThickeningIdealSheaf f I ^ n).subschemeι (T.cover n).obj
      (fun U => stageSectionMap (idealThickeningIdealSheaf f I ^ n) (T.cover n)
        d.algebra.X q ⟨U.val, U.property.1⟩) ?_ ?_)
  · intro U V j
    exact stageSectionMap_naturality (idealThickeningIdealSheaf f I ^ n) (T.cover n)
      d.algebra.X q (U := ⟨U.val, U.property.1⟩) (V := ⟨V.val, V.property.1⟩)
      (homOfLE j.le)
  · intro U
    change IsPullback _ _
      (colimit.ι (datum F scalarUnit hcart hcover).functor U ≫
        (datum F scalarUnit hcart hcover).toBase) _
    rw [(datum F scalarUnit hcart hcover).ι_toBase U]
    have hJ : sectionIdeal f I U.val ^ n =
        (idealThickeningIdealSheaf f I ^ n).ideal ⟨U.val, U.property.1⟩ := by
      simp only [sectionIdeal, IdealSheafData.ideal_pow, Pi.pow_apply,
        idealThickeningIdealSheaf_ideal, idealSectionRingHom]
    change IsPullback _ _
      ((Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U.val) Γ(d.algebra.X, U.val))) ≫ U.property.1.isoSpec.inv) ≫
          U.val.ι) _
    rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    exact stageSectionMap_isPullback (idealThickeningIdealSheaf f I ^ n) (T.cover n)
        d.algebra.X q ⟨U.val, U.property.1⟩ (sectionIdeal f I U.val ^ n) hJ
        (d.affineQuotientAlgebraCoordinates f I ⟨U.val, U.property.1⟩ n)

/-- The specified comparison with the original first-stage cover. -/
def algebraizedFirstStageIso :
    (baseChange (idealThickeningIdealSheaf f I ^ 1).subschemeι).obj
      (algebraizedCover f I hI T d) ≅ T.cover 1 :=
  algebraizedStageIso f I hI T d 1

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
