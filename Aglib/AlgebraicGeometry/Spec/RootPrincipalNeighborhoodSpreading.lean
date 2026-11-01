/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalNeighborhoodSpreading
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.OverBaseCharts
public import Aglib.AlgebraicGeometry.Spec.RootBaseChange

/-!
# Spreading the original root chart

The canonical root base-change isomorphism specializes principal-neighborhood
spreading to the actual root algebras. Both original local-chart comparisons and
the projection to the original model are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

open IsLocalization.PrincipalDiagram PrincipalNeighborhoodLimit

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (f : R)

/-- The native root comparison in the ordinary over-category pullback orientation. -/
def rootOrdinaryBaseChangeIso :
    Spec (.of (RootAlgebra n (algebraMap R A f))) ≅
      ((Over.pullback (Spec.algebraMap R A)).obj
        (Over.mk (Spec.algebraMap R (RootAlgebra n f)))).left :=
  rootBaseChangeSpecIso R A n f ≪≫ pullbackSymmetry _ _

/-- The ordinary root comparison retains the original root map. -/
@[reassoc (attr := simp)]
theorem rootOrdinaryBaseChangeIso_hom_fst :
    (rootOrdinaryBaseChangeIso R A n f).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom A n f).toRingHom) := by
  simp [rootOrdinaryBaseChangeIso]

/-- The ordinary root comparison retains the coefficient map. -/
@[reassoc (attr := simp)]
theorem rootOrdinaryBaseChangeIso_hom_snd :
    (rootOrdinaryBaseChangeIso R A n f).hom ≫ pullback.snd _ _ =
      Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) := by
  simp [rootOrdinaryBaseChangeIso]

variable {R} (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The original root-to-root map induced by the actual principal comparison. -/
def rootPrincipalComparison (j : Over (op (∅ : Finset M))) :
    Spec (.of (RootAlgebra n (algebraMap R S f))) ⟶
      Spec (.of (RootAlgebra n (algebraMap R (stage M j.left.unop) f))) :=
  OverBaseSpreading.chartComparison (specDiagram M) (specCone M S) (baseStructure M)
    (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅)
    (Spec.algebraMap R (RootAlgebra n f)) (rootOrdinaryBaseChangeIso R S n f)
    (fun j => rootOrdinaryBaseChangeIso R (stage M j.left.unop) n f) j

/-- The actual root comparison retains the original root projection. -/
@[reassoc (attr := simp)]
theorem rootPrincipalComparison_rootMap (j : Over (op (∅ : Finset M))) :
    rootPrincipalComparison n f M S j ≫
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom (stage M j.left.unop) n f).toRingHom) =
        Spec.map (CommRingCat.ofHom (rootBaseChangeHom S n f).toRingHom) := by
  rw [← rootOrdinaryBaseChangeIso_hom_fst R (stage M j.left.unop) n f]
  exact (OverBaseSpreading.chartComparison_fst (specDiagram M) (specCone M S)
    (baseStructure M) (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅)
    (Spec.algebraMap R (RootAlgebra n f)) (rootOrdinaryBaseChangeIso R S n f)
    (fun j => rootOrdinaryBaseChangeIso R (stage M j.left.unop) n f) j).trans
      (rootOrdinaryBaseChangeIso_hom_fst R S n f)

/-- The actual root comparison retains the original coefficient-cone projection. -/
@[reassoc (attr := simp)]
theorem rootPrincipalComparison_base (j : Over (op (∅ : Finset M))) :
    rootPrincipalComparison n f M S j ≫
      Spec.algebraMap (stage M j.left.unop)
        (RootAlgebra n (algebraMap R (stage M j.left.unop) f)) =
      Spec.algebraMap S (RootAlgebra n (algebraMap R S f)) ≫
        (specCone M S).π.app j.left := by
  rw [← rootOrdinaryBaseChangeIso_hom_snd R (stage M j.left.unop) n f]
  exact (OverBaseSpreading.chartComparison_snd (specDiagram M) (specCone M S)
    (baseStructure M) (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅)
    (Spec.algebraMap R (RootAlgebra n f)) (rootOrdinaryBaseChangeIso R S n f)
    (fun j => rootOrdinaryBaseChangeIso R (stage M j.left.unop) n f) j).trans
      (rootOrdinaryBaseChangeIso_hom_snd_assoc R S n f _)

/-- A supplied original local root chart spreads to an actual principal-stage
root chart, retaining its base map, both comparison directions and the original
model projection used to track points. -/
theorem exists_rootChart_principal_with_comparison {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (c : Spec (.of (RootAlgebra n (algebraMap R S f))) ≅
      pullback p (Spec.algebraMap R S))
    (hc : c.hom ≫ pullback.snd p (Spec.algebraMap R S) =
      Spec.algebraMap S (RootAlgebra n (algebraMap R S f))) :
    ∃ (j : Over (op (∅ : Finset M)))
      (c' : Spec (.of (RootAlgebra n (algebraMap R (stage M j.left.unop) f))) ≅
        pullback p ((baseStructure M).app j.left)),
      c'.hom ≫ pullback.snd p ((baseStructure M).app j.left) =
        Spec.algebraMap (stage M j.left.unop)
          (RootAlgebra n (algebraMap R (stage M j.left.unop) f)) ∧
      rootPrincipalComparison n f M S j ≫ c'.hom = c.hom ≫ comparison M S p j ∧
      comparison M S p j ≫ c'.inv = c.inv ≫ rootPrincipalComparison n f M S j ∧
      rootPrincipalComparison n f M S j ≫ c'.hom ≫
          pullback.fst p ((baseStructure M).app j.left) =
        c.hom ≫ pullback.fst p (Spec.algebraMap R S) := by
  have : LocallyOfFinitePresentation (Spec.algebraMap R (RootAlgebra n f)) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have (j : (Finset M)ᵒᵖ) : CompactSpace ((specDiagram M).obj j) := by
    change CompactSpace (Spec (.of (stage M j.unop)))
    infer_instance
  have (j : (Finset M)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram M).obj j) := by
    change QuasiSeparatedSpace (Spec (.of (stage M j.unop)))
    infer_instance
  obtain ⟨j, c', hb, hh, hi, hp⟩ := OverBaseSpreading.exists_chart_with_comparison
    (specDiagram M) (specCone M S) (baseStructure M) (Spec.algebraMap R S)
    (baseStructure_fac M S) (op ∅) (Spec.algebraMap R (RootAlgebra n f))
    (rootOrdinaryBaseChangeIso R S n f)
    (fun j => rootOrdinaryBaseChangeIso R (stage M j.left.unop) n f)
    (specConeIsLimit M S) p c (hc.trans (rootOrdinaryBaseChangeIso_hom_snd R S n f).symm)
  exact ⟨j, c', hb.trans (rootOrdinaryBaseChangeIso_hom_snd R (stage M j.left.unop) n f),
    hh, hi, hp⟩

end AlgebraicGeometry.Scheme.Kummer
