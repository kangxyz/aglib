/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.GeometricNeighborhood
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The geometric etale-neighborhood colimit and its canonical maps

The underlying ring is the native filtered colimit of small pointed etale
neighborhoods. This leaf constructs the ring, its original-base algebra
structure, the stage maps, and its chosen-field-valued map. Localness and the
henselian property are subsequent theorems, not fields assumed in a structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace GeometricEtaleNeighborhood

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- The pointed neighborhood diagram forgotten to native commutative rings. -/
def ringDiagram : GeometricEtaleNeighborhood R Ω ⥤ CommRingCat.{u} :=
  diagram R Ω ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

end GeometricEtaleNeighborhood

/-- The native filtered-colimit ring of pointed etale neighborhoods.
Localness and henselianity are not assumed in this definition. -/
def GeometricEtaleColimit (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω] : Type u :=
  CommRingCat.FilteredColimits.colimit.{u, u} (GeometricEtaleNeighborhood.ringDiagram R Ω)

namespace GeometricEtaleColimit

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω]

instance : CommRing (GeometricEtaleColimit R Ω) :=
  inferInstanceAs <| CommRing
    (CommRingCat.FilteredColimits.colimit.{u, u} (GeometricEtaleNeighborhood.ringDiagram R Ω))

/-- The native cocone defining the geometric neighborhood ring. -/
abbrev ringCocone : Cocone (GeometricEtaleNeighborhood.ringDiagram R Ω) :=
  CommRingCat.FilteredColimits.colimitCocone.{u, u}
    (GeometricEtaleNeighborhood.ringDiagram R Ω)

/-- The native proof that the ring cocone is colimiting. -/
abbrev ringCoconeIsColimit : IsColimit (ringCocone R Ω) :=
  CommRingCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
    (GeometricEtaleNeighborhood.ringDiagram R Ω)

/-- The actual ring homomorphism from a pointed etale neighborhood. -/
def stageRingHom (X : GeometricEtaleNeighborhood R Ω) : X.algebra →+* GeometricEtaleColimit R Ω :=
  ((ringCocone R Ω).ι.app X).hom

variable {R Ω}

lemma stageRingHom_naturality {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (stageRingHom R Ω Y).comp f.val.toRingHom = stageRingHom R Ω X := by
  exact congrArg CommRingCat.Hom.hom ((ringCocone R Ω).w f)

/-- The original-base maps into the ring colimit agree along every arrow. -/
lemma stageRingHom_comp_algebraMap_eq {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (stageRingHom R Ω X).comp (algebraMap R X.algebra) =
      (stageRingHom R Ω Y).comp (algebraMap R Y.algebra) := by
  ext r
  have h := RingHom.congr_fun (stageRingHom_naturality f) (algebraMap R X.algebra r)
  change stageRingHom R Ω Y (f.val (algebraMap R X.algebra r)) =
    stageRingHom R Ω X (algebraMap R X.algebra r) at h
  rw [f.val.commutes] at h
  exact h.symm

variable (R Ω)

/-- The canonical ring homomorphism from the original base ring. -/
def of : R →+* GeometricEtaleColimit R Ω :=
  let X : GeometricEtaleNeighborhood R Ω := Classical.choice inferInstance
  (stageRingHom R Ω X).comp (algebraMap R X.algebra)

instance : Algebra R (GeometricEtaleColimit R Ω) := (of R Ω).toAlgebra

/-- Every stage induces the same original-base ring homomorphism. -/
lemma stageRingHom_comp_algebraMap (X : GeometricEtaleNeighborhood R Ω) :
    (stageRingHom R Ω X).comp (algebraMap R X.algebra) = of R Ω := by
  let Y : GeometricEtaleNeighborhood R Ω := Classical.choice inferInstance
  exact (stageRingHom_comp_algebraMap_eq (IsFiltered.leftToMax X Y)).trans
    (stageRingHom_comp_algebraMap_eq (IsFiltered.rightToMax X Y)).symm

/-- The actual algebra homomorphism from a pointed etale neighborhood. -/
def ι (X : GeometricEtaleNeighborhood R Ω) : X.algebra →ₐ[R] GeometricEtaleColimit R Ω where
  __ := stageRingHom R Ω X
  commutes' r := RingHom.congr_fun (stageRingHom_comp_algebraMap R Ω X) r

variable {R Ω}

@[simp]
lemma ι_naturality {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    (ι R Ω Y).comp f.val = ι R Ω X := by
  apply AlgHom.coe_ringHom_injective
  exact stageRingHom_naturality f

variable (R Ω)

/-- The actual field-valued points form a cocone over the native ring diagram. -/
def residueCocone : Cocone (GeometricEtaleNeighborhood.ringDiagram R Ω) where
  pt := CommRingCat.of (Ω)
  ι.app X := CommRingCat.ofHom X.point.toRingHom
  ι.naturality X Y f := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom f.property

/-- The ring homomorphism obtained by descending the field-point cocone. -/
def residueRingHom : GeometricEtaleColimit R Ω →+* Ω :=
  ((ringCoconeIsColimit R Ω).desc (residueCocone R Ω)).hom

/-- The descended ring homomorphism restricts to the given point at every stage. -/
lemma residueRingHom_comp_stageRingHom (X : GeometricEtaleNeighborhood R Ω) :
    (residueRingHom R Ω).comp (stageRingHom R Ω X) = X.point.toRingHom := by
  exact congrArg CommRingCat.Hom.hom ((ringCoconeIsColimit R Ω).fac (residueCocone R Ω) X)

/-- The chosen-field-valued algebra map induced by the actual points of all stages. -/
def residue : GeometricEtaleColimit R Ω →ₐ[R] Ω where
  __ := residueRingHom R Ω
  commutes' r := by
    let X : GeometricEtaleNeighborhood R Ω := Classical.choice inferInstance
    change residueRingHom R Ω (stageRingHom R Ω X (algebraMap R X.algebra r)) = _
    have h := RingHom.congr_fun (residueRingHom_comp_stageRingHom R Ω X)
      (algebraMap R X.algebra r)
    exact h.trans (X.point.commutes r)

/-- Restricting the colimit point map to a stage gives its specified point. -/
@[simp]
lemma residue_comp_ι (X : GeometricEtaleNeighborhood R Ω) :
    (residue R Ω).comp (ι R Ω X) = X.point := by
  apply AlgHom.coe_ringHom_injective
  exact residueRingHom_comp_stageRingHom R Ω X

/-- The composite with the original ring is the specified field-valued point. -/
@[simp]
lemma residue_comp_of :
    (residue R Ω : GeometricEtaleColimit R Ω →+* Ω).comp (of R Ω) =
      algebraMap R Ω := by
  ext r
  exact (residue R Ω).commutes r

/-- Every colimit element has a representative in one pointed etale stage. -/
lemma exists_rep (x : GeometricEtaleColimit R Ω) :
    ∃ (X : GeometricEtaleNeighborhood R Ω) (a : X.algebra), ι R Ω X a = x := by
  exact Concrete.isColimit_exists_rep (GeometricEtaleNeighborhood.ringDiagram R Ω)
    (ringCoconeIsColimit R Ω) x

/-- A representative can be chosen after any prescribed stage. This is the
finite-coefficient descent interface used to move successive coefficients to
one common stage. -/
lemma exists_rep_over (x : GeometricEtaleColimit R Ω) (X : GeometricEtaleNeighborhood R Ω) :
    ∃ (Y : GeometricEtaleNeighborhood R Ω) (_ : X ⟶ Y) (a : Y.algebra), ι R Ω Y a = x := by
  exact Concrete.exists_hom_ι_eq_of_isColimit (GeometricEtaleNeighborhood.ringDiagram R Ω)
    (ringCoconeIsColimit R Ω) x X

/-- Equality of stage representatives is witnessed in a common successor. -/
lemma rep_eq_iff {X Y : GeometricEtaleNeighborhood R Ω} (a : X.algebra) (b : Y.algebra) :
    ι R Ω X a = ι R Ω Y b ↔
      ∃ (Z : GeometricEtaleNeighborhood R Ω) (f : X ⟶ Z) (g : Y ⟶ Z), f.val a = g.val b := by
  exact Concrete.isColimit_rep_eq_iff_exists (GeometricEtaleNeighborhood.ringDiagram R Ω)
    (ringCoconeIsColimit R Ω) a b

end GeometricEtaleColimit
