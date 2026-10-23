/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.LocalComponentCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DisjointSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ComponentSections
public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors

/-! # Original sections as the product over actual finite local components -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u v w

variable (A : Type v) [CommRing A] (R : Type u) [CommRing R]
  [HenselianLocalRing R] [Algebra R A] [Module.Finite R A]

/-- The literal local component as an object of the original small etale site. -/
abbrev localComponentEtale (p : MaximalSpectrum A) : (Spec (.of A)).Etale := by
  let := localComponentInclusion_isOpenImmersion A R p
  exact Scheme.Etale.mk (localComponentInclusion A p)

/-- The actual component restriction arrow to the identity etale object. -/
abbrev localComponentArrow (p : MaximalSpectrum A) :
    localComponentEtale A R p ⟶ StrictlyLocal.terminalObject A :=
  MorphismProperty.Over.homMk (localComponentInclusion A p) (Category.comp_id _)

instance (p : MaximalSpectrum A) : Mono (localComponentArrow A R p) where
  right_cancellation {Z} a b h := by
    let := localComponentInclusion_isOpenImmersion A R p
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (localComponentInclusion A p)).mp
    exact congrArg (fun k : Z ⟶ StrictlyLocal.terminalObject A => k.left) h

/-- The actual local-component arrows form a cover in the original site. -/
theorem localComponentArrow_cover :
    Sieve.ofArrows (localComponentEtale A R) (localComponentArrow A R) ∈
      (Spec (.of A)).smallEtaleTopology (StrictlyLocal.terminalObject A) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (localComponentArrow A R)).mpr
  change (⋃ p, Set.range (localComponentInclusion A p)) = Set.univ
  exact (localComponentOpenCover A R).iUnion_range

/-- The original section group is the product of its literal component
restrictions, not of replaced or constant coefficient groups. -/
def localComponentSectionsFanIsLimit (F : AbelianSheaf.{v, v + 1} (Spec (.of A))) :
    IsLimit (disjointSectionsFan F (localComponentArrow A R)) := by
  apply disjointSectionsFanIsLimit F (localComponentArrow A R)
    (localComponentArrow_cover A R)
  intro p q hpq Z a b h
  exact isEmpty_of_commSq_localComponentInclusion A R
    ⟨congrArg (fun k : Z ⟶ StrictlyLocal.terminalObject A => k.left) h⟩ hpq

variable [IsSepClosed (IsLocalRing.ResidueField R)]
  [HasSheafify (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{v + 1}]

/-- Component evaluation is exact for every original coefficient sheaf. -/
theorem localComponentSections_preservesEpimorphisms (p : MaximalSpectrum A) :
    ((sheafSections (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      (op (localComponentEtale A R p))).PreservesEpimorphisms := by
  let := HenselianLocalRing.henselian_localizationAtPrime R A p.asIdeal
  let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime R A p.asIdeal
  let := localComponentInclusion_isOpenImmersion A R p
  exact componentSections_preservesEpimorphisms
    (Localization.AtPrime p.asIdeal) (localComponentInclusion A p)

include R in
/-- Global sections on the actual finite scheme over a strictly local ring
preserve epimorphisms, including the empty finite scheme. -/
theorem finiteGlobalSections_preservesEpimorphisms :
    (StrictlyLocal.globalSections.{v, v + 1} A).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    let : Finite (MaximalSpectrum A) := Module.finiteAlgebra_maximalSpectrum_finite R A
    let hcomponents (p : MaximalSpectrum A) :
        Epi (φ.hom.app (op (localComponentEtale A R p))) := by
      let := localComponentSections_preservesEpimorphisms A R p
      exact Functor.map_epi
        ((sheafSections (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op (localComponentEtale A R p))) φ
    apply epi_sections_of_epi_components F (localComponentArrow A R)
      (localComponentArrow_cover A R) _ φ
    intro p q hpq Z a b h
    exact isEmpty_of_commSq_localComponentInclusion A R
      ⟨congrArg (fun k : Z ⟶ StrictlyLocal.terminalObject A => k.left) h⟩ hpq

include R in
/-- The original global-sections functor on a finite scheme over a strictly
local ring is exact. -/
theorem finiteGlobalSections_preservesFiniteColimits :
    PreservesFiniteColimits (StrictlyLocal.globalSections.{v, v + 1} A) := by
  let Γ := StrictlyLocal.globalSections.{v, v + 1} A
  let : PreservesFiniteLimits Γ := StrictlyLocal.globalSections_preservesFiniteLimits A
  let : Γ.PreservesEpimorphisms := finiteGlobalSections_preservesEpimorphisms A R
  let : Γ.Additive := { map_add := by intros; rfl }
  let : Γ.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels Γ
  exact Functor.preservesFiniteColimits_of_preservesHomology Γ

private theorem integer_projective : Projective (AddCommGrpCat.of (ULift.{v + 1} ℤ)) := by
  constructor
  intro E X f e he
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective e).mp he (f (ULift.up 1))
  let g := (AddCommGrpCat.uliftZMultiplesAddEquiv E).symm x
  refine ⟨g, ?_⟩
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv X).injective
  have hg : g (ULift.up 1) = x :=
    (AddCommGrpCat.uliftZMultiplesAddEquiv E).apply_symm_apply x
  change e (g (ULift.up 1)) = f (ULift.up 1)
  rw [hg]
  exact hx

include R in
/-- The original constant integer sheaf is projective on a finite scheme over
 a strictly local base, with no finiteness restriction on the coefficients. -/
theorem finite_constant_integer_projective :
    Projective ((constantSheaf (Spec (.of A)).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj (AddCommGrpCat.of (ULift.{v + 1} ℤ))) := by
  let := finiteGlobalSections_preservesEpimorphisms A R
  exact (constantSheafAdj (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{v + 1}
    (StrictlyLocal.terminalIsTerminal A)).map_projective _ integer_projective

include R in
/-- Original positive-degree etale Sheaf.H vanishes on the entire finite
scheme, not only on each of its local components. -/
theorem finite_subsingleton_H
    [HasExt.{w} (AbelianSheaf.{v, v + 1} (Spec (.of A)))]
    (F : AbelianSheaf.{v, v + 1} (Spec (.of A))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) := by
  let := finite_constant_integer_projective A R
  apply subsingleton_of_forall_eq 0
  intro x
  cases q with
  | zero => simp at hq
  | succ n => exact Abelian.Ext.eq_zero_of_projective x

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
