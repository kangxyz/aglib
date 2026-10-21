/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.EtaleNeighborhood
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The henselization colimit and its canonical maps

The underlying ring is the native filtered colimit of small pointed etale
neighborhoods. This leaf constructs the ring, its original-base algebra
structure, the stage maps, and its residue-valued map. Localness and the
henselian property are subsequent theorems, not fields assumed in a structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace PointedEtaleNeighborhood

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The pointed neighborhood diagram forgotten to native commutative rings. -/
def ringDiagram : PointedEtaleNeighborhood R ⥤ CommRingCat.{u} :=
  diagram R ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

end PointedEtaleNeighborhood

/-- The native filtered-colimit ring of pointed etale neighborhoods.
Localness and henselianity are not assumed in this definition. -/
def Henselization (R : Type u) [CommRing R] [IsLocalRing R] : Type u :=
  CommRingCat.FilteredColimits.colimit.{u, u} (PointedEtaleNeighborhood.ringDiagram R)

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

instance : CommRing (Henselization R) :=
  inferInstanceAs <| CommRing
    (CommRingCat.FilteredColimits.colimit.{u, u} (PointedEtaleNeighborhood.ringDiagram R))

/-- The native cocone defining the henselization ring. -/
abbrev ringCocone : Cocone (PointedEtaleNeighborhood.ringDiagram R) :=
  CommRingCat.FilteredColimits.colimitCocone.{u, u}
    (PointedEtaleNeighborhood.ringDiagram R)

/-- The native proof that the ring cocone is colimiting. -/
abbrev ringCoconeIsColimit : IsColimit (ringCocone R) :=
  CommRingCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
    (PointedEtaleNeighborhood.ringDiagram R)

/-- The actual ring homomorphism from a pointed etale neighborhood. -/
def stageRingHom (X : PointedEtaleNeighborhood R) : X.algebra →+* Henselization R :=
  ((ringCocone R).ι.app X).hom

variable {R}

lemma stageRingHom_naturality {X Y : PointedEtaleNeighborhood R} (f : X ⟶ Y) :
    (stageRingHom R Y).comp f.val.toRingHom = stageRingHom R X := by
  exact congrArg CommRingCat.Hom.hom ((ringCocone R).w f)

/-- The original-base maps into the ring colimit agree along every arrow. -/
lemma stageRingHom_comp_algebraMap_eq {X Y : PointedEtaleNeighborhood R} (f : X ⟶ Y) :
    (stageRingHom R X).comp (algebraMap R X.algebra) =
      (stageRingHom R Y).comp (algebraMap R Y.algebra) := by
  ext r
  have h := RingHom.congr_fun (stageRingHom_naturality f) (algebraMap R X.algebra r)
  change stageRingHom R Y (f.val (algebraMap R X.algebra r)) =
    stageRingHom R X (algebraMap R X.algebra r) at h
  rw [f.val.commutes] at h
  exact h.symm

variable (R)

/-- The canonical ring homomorphism from the original local ring. -/
def of : R →+* Henselization R :=
  let X : PointedEtaleNeighborhood R := Classical.choice inferInstance
  (stageRingHom R X).comp (algebraMap R X.algebra)

instance : Algebra R (Henselization R) := (of R).toAlgebra

/-- Every stage induces the same original-base ring homomorphism. -/
lemma stageRingHom_comp_algebraMap (X : PointedEtaleNeighborhood R) :
    (stageRingHom R X).comp (algebraMap R X.algebra) = of R := by
  let Y : PointedEtaleNeighborhood R := Classical.choice inferInstance
  exact (stageRingHom_comp_algebraMap_eq (IsFiltered.leftToMax X Y)).trans
    (stageRingHom_comp_algebraMap_eq (IsFiltered.rightToMax X Y)).symm

/-- The actual algebra homomorphism from a pointed etale neighborhood. -/
def ι (X : PointedEtaleNeighborhood R) : X.algebra →ₐ[R] Henselization R where
  __ := stageRingHom R X
  commutes' r := RingHom.congr_fun (stageRingHom_comp_algebraMap R X) r

variable {R}

@[simp]
lemma ι_naturality {X Y : PointedEtaleNeighborhood R} (f : X ⟶ Y) :
    (ι R Y).comp f.val = ι R X := by
  apply AlgHom.coe_ringHom_injective
  exact stageRingHom_naturality f

variable (R)

/-- The actual residue points form a cocone over the native ring diagram. -/
def residueCocone : Cocone (PointedEtaleNeighborhood.ringDiagram R) where
  pt := CommRingCat.of (IsLocalRing.ResidueField R)
  ι.app X := CommRingCat.ofHom X.point.toRingHom
  ι.naturality X Y f := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom f.property

/-- The ring homomorphism obtained by descending the residue-point cocone. -/
def residueRingHom : Henselization R →+* IsLocalRing.ResidueField R :=
  ((ringCoconeIsColimit R).desc (residueCocone R)).hom

/-- The descended ring homomorphism restricts to the given point at every stage. -/
lemma residueRingHom_comp_stageRingHom (X : PointedEtaleNeighborhood R) :
    (residueRingHom R).comp (stageRingHom R X) = X.point.toRingHom := by
  exact congrArg CommRingCat.Hom.hom ((ringCoconeIsColimit R).fac (residueCocone R) X)

/-- The residue-valued algebra map induced by the actual points of all stages. -/
def residue : Henselization R →ₐ[R] IsLocalRing.ResidueField R where
  __ := residueRingHom R
  commutes' r := by
    let X : PointedEtaleNeighborhood R := Classical.choice inferInstance
    change residueRingHom R (stageRingHom R X (algebraMap R X.algebra r)) = _
    have h := RingHom.congr_fun (residueRingHom_comp_stageRingHom R X)
      (algebraMap R X.algebra r)
    exact h.trans (X.point.commutes r)

/-- Restricting the colimit residue map to a stage gives its specified point. -/
@[simp]
lemma residue_comp_ι (X : PointedEtaleNeighborhood R) :
    (residue R).comp (ι R X) = X.point := by
  apply AlgHom.coe_ringHom_injective
  exact residueRingHom_comp_stageRingHom R X

/-- The composite with the original ring is its literal native residue map. -/
@[simp]
lemma residue_comp_of :
    (residue R : Henselization R →+* IsLocalRing.ResidueField R).comp (of R) =
      IsLocalRing.residue R := by
  ext r
  exact (residue R).commutes r

/-- The residue-valued map is surjective already before proving localness. -/
lemma residue_surjective : Function.Surjective (residue R) := by
  intro x
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) x
  refine ⟨of R r, ?_⟩
  exact (RingHom.congr_fun (residue_comp_of R) r).trans hr

/-- Every colimit element has a representative in one pointed etale stage. -/
lemma exists_rep (x : Henselization R) :
    ∃ (X : PointedEtaleNeighborhood R) (a : X.algebra), ι R X a = x := by
  exact Concrete.isColimit_exists_rep (PointedEtaleNeighborhood.ringDiagram R)
    (ringCoconeIsColimit R) x

/-- A representative can be chosen after any prescribed stage. This is the
finite-coefficient descent interface used to move successive coefficients to
one common stage. -/
lemma exists_rep_over (x : Henselization R) (X : PointedEtaleNeighborhood R) :
    ∃ (Y : PointedEtaleNeighborhood R) (_ : X ⟶ Y) (a : Y.algebra), ι R Y a = x := by
  exact Concrete.exists_hom_ι_eq_of_isColimit (PointedEtaleNeighborhood.ringDiagram R)
    (ringCoconeIsColimit R) x X

/-- Equality of stage representatives is witnessed in a common successor. -/
lemma rep_eq_iff {X Y : PointedEtaleNeighborhood R} (a : X.algebra) (b : Y.algebra) :
    ι R X a = ι R Y b ↔
      ∃ (Z : PointedEtaleNeighborhood R) (f : X ⟶ Z) (g : Y ⟶ Z), f.val a = g.val b := by
  exact Concrete.isColimit_rep_eq_iff_exists (PointedEtaleNeighborhood.ringDiagram R)
    (ringCoconeIsColimit R) a b

end Henselization
