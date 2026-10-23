/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteGaloisCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback

/-! # Actual finite Galois trivializations of finite locally constant coefficients

One nonempty chart over the field point refines to an actual finite Galois
field cover. Original inverse-image composition and constant transport give
the actual coefficient isomorphism, with its finite additive value retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

variable (E : Type u) [Field E]

attribute [local instance] hasSheafifyLarge

/-- A genuine finite locally constant sheaf on a field becomes constant over
an actual finite Galois extension, not merely over an abstract covering site. -/
theorem exists_finiteGalois_trivialization
    (F : AbelianSheaf.{u, u + 1} (Spec (.of E))) (hF : IsFiniteLocallyConstant F) :
    ∃ (L : FiniteGaloisIntermediateField E (SeparableClosure E))
      (A : AddCommGrpCat.{u + 1}), Finite A ∧
        Nonempty ((inverseImage (Spec.algebraMap E L)).obj F ≅
          (constantSheaf (Scheme.smallEtaleTopology (Spec (.of L)))
            AddCommGrpCat.{u + 1}).obj A) := by
  obtain ⟨t⟩ := hF
  obtain ⟨i, x, _⟩ := t.covers (default : Spec (.of E))
  obtain ⟨L, s, hs⟩ := exists_finiteGalois_point E (t.chart i).hom x
  refine ⟨L, t.value i, t.finite_value i, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun q => (inverseImage q).obj F) hs.symm) ≪≫
    (inverseImageComp (t.chart i).hom s).app F ≪≫
      (inverseImage s).mapIso (t.trivialization i) ≪≫
        (inverseImageConstantIso s).app (t.value i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
