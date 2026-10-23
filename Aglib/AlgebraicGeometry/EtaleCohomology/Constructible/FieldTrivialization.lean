/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteGaloisCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence

/-! # Finite Galois trivialization of finite locally constant coefficients

A point of an actual trivializing chart over a field lifts to a finite Galois
intermediate field of the separable closure. The original chart trivialization,
native inverse-image composition, and native constant-sheaf transport then give
a trivialization along the literal map `Spec.algebraMap K L`. No perfection,
order restriction, fundamental-group dictionary or supplied marking is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FieldTrivialization

universe u

attribute [local instance] hasSheafifyLarge

private def pullbackIsoOfFactorization {X U T : Scheme.{u}}
    (f : U ⟶ X) (s : T ⟶ U) (p : T ⟶ X) (hs : s ≫ f = p)
    (F : AbelianSheaf.{u, u + 1} X) (A : AddCommGrpCat.{u + 1})
    (e : (inverseImage f).obj F ≅
      (constantSheaf (Scheme.smallEtaleTopology U) AddCommGrpCat.{u + 1}).obj A) :
    (inverseImage p).obj F ≅
      (constantSheaf (Scheme.smallEtaleTopology T) AddCommGrpCat.{u + 1}).obj A :=
  eqToIso (congrArg (fun q => (inverseImage q).obj F) hs.symm) ≪≫
    (inverseImageComp f s).app F ≪≫ (inverseImage s).mapIso e ≪≫
      (inverseImageConstantIso s).app A

variable (K : Type u) [Field K] (F : AbelianSheaf.{u, u + 1} (Spec (.of K)))

/-- Actual finite Galois field data and a finite constant coefficient, together
with a trivialization along the original field-extension morphism. -/
structure Trivialization where
  /-- A finite Galois intermediate field with its original inclusion over `K`. -/
  fieldExtension : FiniteGaloisIntermediateField K (SeparableClosure K)
  /-- The coefficient in the native sheaf-value universe. -/
  value : AddCommGrpCat.{u + 1}
  /-- Finiteness concerns the constant value, not all sets of sections. -/
  finite_value : Finite value
  /-- The isomorphism uses the literal field-extension map and constant sheaf. -/
  iso : (inverseImage (Spec.algebraMap K fieldExtension)).obj F ≅
    (constantSheaf (Scheme.smallEtaleTopology (Spec (.of fieldExtension)))
      AddCommGrpCat.{u + 1}).obj value

/-- A genuine finite Galois trivialization is produced from an actual finite
locally constant sheaf, by lifting a point of one of its trivializing charts. -/
theorem nonempty_trivialization (hF : IsFiniteLocallyConstant F) :
    Nonempty (Trivialization K F) := by
  obtain ⟨t⟩ := hF
  obtain ⟨i, y, _⟩ := t.covers (default : Spec (.of K))
  have : Etale (t.chart i).hom := (t.chart i).prop
  obtain ⟨L, s, hs⟩ := Fields.exists_finiteGalois_point K (t.chart i).hom y
  exact ⟨{
    fieldExtension := L
    value := t.value i
    finite_value := t.finite_value i
    iso := pullbackIsoOfFactorization (t.chart i).hom s (Spec.algebraMap K L) hs
      F (t.value i) (t.trivialization i) }⟩

/-- A chosen actual finite Galois trivialization, whose existence is proved
from finite local constancy rather than postulated as representation data. -/
def ofFiniteLocallyConstant (hF : IsFiniteLocallyConstant F) : Trivialization K F :=
  Classical.choice (nonempty_trivialization K F hF)

/-- Every finite locally constant abelian sheaf over a field becomes an actual
finite constant sheaf over an actual finite Galois extension. -/
theorem exists_finiteGalois_trivialization (hF : IsFiniteLocallyConstant F) :
    ∃ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (A : AddCommGrpCat.{u + 1}), Finite A ∧ Nonempty
        ((inverseImage (Spec.algebraMap K L)).obj F ≅
          (constantSheaf (Scheme.smallEtaleTopology (Spec (.of L)))
            AddCommGrpCat.{u + 1}).obj A) := by
  let t := ofFiniteLocallyConstant K F hF
  exact ⟨t.fieldExtension, t.value, t.finite_value, ⟨t.iso⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.FieldTrivialization
