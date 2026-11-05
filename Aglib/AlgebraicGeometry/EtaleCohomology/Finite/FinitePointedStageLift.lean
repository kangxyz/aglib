/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FiniteNeighborhoodLift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.RepresentedPointedFactorization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport

/-! # A common genuine target neighborhood retaining the entire finite fibre

The whole finite Henselian source first lifts to the actual coproduct of all
specified etale neighborhoods. Its one original map then descends through the
actual geometric-neighborhood system. Every component residue mark is retained
at the same stage. No arithmetic approximation system is used here.

The final implication preserves a zero already on that actual coproduct. It
is not an assertion that the closed-support induction has produced this zero.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite
universe u
open Continuity GeometricNeighborhood
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Simultaneous marked descent from a whole finite Henselian model. The
presentation iso retains the actual limit and its structural map. -/
theorem exists_finite_pointed_stage_lift
    (R Ω S A : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    [CommRing S] [HenselianLocalRing S] [CommRing A]
    [Algebra S A] [Module.Finite S A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (E : Spec (.of A) ≅ (baseChangedCone R Ω f).pt.left)
    (U : MaximalSpectrum A → X.Etale)
    (t : ∀ i : MaximalSpectrum A,
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (ht : ∀ i : MaximalSpectrum A, t i ≫ (U i).hom =
      localComponentResidueMap A i ≫ localComponentInclusion A i ≫
        E.hom ≫ (baseChangedCone R Ω f).pt.hom) :
    ∃ (V : GeometricEtaleNeighborhood R Ω)
      (b : (baseChangedDiagram R Ω f).obj (op V) ⟶ Over.mk (coproductEtale U).hom),
      (∀ i : MaximalSpectrum A,
        (localComponentResidueMap A i ≫ localComponentInclusion A i ≫ E.hom ≫
          ((baseChangedCone R Ω f).π.app (op V)).left) ≫ b.left =
            t i ≫ Sigma.ι (fun i => (U i).left) i) ∧
      (∀ (M : AbelianSheaf.{u, u + 1} X) (q : ℕ) (δ : Sheaf.H.{u + 2} M q),
        cohomologyPullback.{u, u + 2, u + 2} (coproductEtale U).hom M q δ = 0 →
        cohomologyPullback.{u, u + 2, u + 2}
          ((baseChangedDiagram R Ω f).obj (op V)).hom M q δ = 0) := by
  let c := baseChangedCone R Ω f
  let a₀ : Spec (.of A) ⟶ X := E.hom ≫ c.pt.hom
  obtain ⟨s, hs, hmarks⟩ := exists_finite_pointed_neighborhood_lift A S a₀ U t
    (by intro i; simpa only [a₀, Category.assoc] using ht i)
  let T : Over X := Over.mk (coproductEtale U).hom
  let : LocallyOfFinitePresentation T.hom :=
    (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp
      (coproductEtale U).prop).2.2
  have ha : (E.inv ≫ s) ≫ (coproductEtale U).hom = c.pt.hom :=
    (Category.assoc E.inv s (coproductEtale U).hom).trans
      ((congrArg (fun k => E.inv ≫ k) hs).trans (E.inv_hom_id_assoc c.pt.hom))
  let a : c.pt ⟶ T := Over.homMk (E.inv ≫ s) ha
  obtain ⟨i, b, hb, hm⟩ := exists_represented_factorization_all_marks
    (baseChangedDiagram R Ω f) c T
    (baseChangedRepresentedSectionsIsColimit R Ω f T) a
  refine ⟨i.unop, b, ?_, ?_⟩
  · intro j
    have h := hm _ (localComponentResidueMap A j ≫ localComponentInclusion A j ≫ E.hom)
    simpa only [a, Category.assoc, Iso.hom_inv_id_assoc] using
      h.trans (by
        change (localComponentResidueMap A j ≫ localComponentInclusion A j ≫ E.hom) ≫
          (E.inv ≫ s) = t j ≫ Sigma.ι (fun i => (U i).left) j
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hmarks j)
  · intro M q δ hδ
    exact TwoFieldEffacement.original_class_zero_of_map_law b.left
      (coproductEtale U).hom ((baseChangedDiagram R Ω f).obj i).hom
      (Over.w b) M q δ hδ

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
