/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.LocalSplittingMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverReflection
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTorsorRepresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Geometric points at every base point, and the finite local constancy
consumer of the actual finite-cover splitting construction. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange)

universe u

/-- The field-valued point of `X` obtained from the algebraic closure of the residue field at
`x`. -/
def algebraicClosureResiduePoint (X : Scheme.{u}) (x : X) :
    Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x

@[simp] theorem algebraicClosureResiduePoint_image (X : Scheme.{u}) (x : X)
    (z : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x)))) :
    algebraicClosureResiduePoint X x z = x :=
  X.fromSpecResidueField_apply x _

theorem finiteCoverSectionSheaf_eq (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) :
    finiteCoverSectionSheaf Y = finiteRepresentedSetSheaf Y := rfl

/-- The empty label coproduct is initial by its typed universal property.
Together with the terminal empty tuple, this covers the rank-zero case. -/
def trivialCoverIsInitialOfIsEmpty (X : Scheme.{u}) (A : Type u)
    [Finite A] [IsEmpty A] : IsInitial (trivialCover X A) :=
  .ofUniqueHom (fun _ => Sigma.desc (fun a : A => isEmptyElim a))
    (fun _ _ => Sigma.hom_ext _ _ (fun a : A => isEmptyElim a))

/-- The field spectrum has one point, so a neighbourhood of the tuple point
contains the entire image and the actual scheme point lifts to the open. -/
def localSplitPointLift {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A]
    {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y)
    (U : (tupleCover X Y A).obj.left.Opens)
    (hu : tupleCoverPoint Y A s t (default : Spec (CommRingCat.of Ω)) ∈ U) :
    Spec (CommRingCat.of Ω) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (tupleCoverPoint Y A s t) (by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨tupleCoverPoint Y A s t z, ?_⟩, rfl⟩
    rw [Subsingleton.elim z (default : Spec (CommRingCat.of Ω))]
    exact hu)

@[reassoc] theorem localSplitPointLift_ι {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y)
    (U : (tupleCover X Y A).obj.left.Opens)
    (hu : tupleCoverPoint Y A s t (default : Spec (CommRingCat.of Ω)) ∈ U) :
    localSplitPointLift Y A s t U hu ≫ U.ι = tupleCoverPoint Y A s t :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem localSplitPointLift_chart {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
    (A : Type u) [Finite A] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (t : A → Fiber s Y)
    (U : (tupleCover X Y A).obj.left.Opens)
    (hu : tupleCoverPoint Y A s t (default : Spec (CommRingCat.of Ω)) ∈ U) :
    localSplitPointLift Y A s t U hu ≫ (localSplitChart Y A U).hom = s := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ (tupleCover X Y A).obj.left =>
      f ≫ (tupleCover X Y A).obj.hom) (localSplitPointLift_ι Y A s t U hu)).trans
      (tupleCoverPoint_struct Y A s t))

/-- Every enumeration of the geometric fibre produces an actual étale
neighbourhood over which the cover and its represented sheaf are trivial. -/
theorem exists_etale_trivialization_at_geometric_point {X : Scheme.{u}}
    (Y : Scheme.FiniteEtale X) (A : Type u) [Finite A] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) (e : A ≃ Fiber s Y) :
    ∃ (U : X.Etale) (q : Spec (CommRingCat.of Ω) ⟶ U.left), q ≫ U.hom = s ∧
      Nonempty (trivialCover U.left A ≅ (baseChange U.hom).obj Y) ∧
      Nonempty ((setInverseImage U.hom).obj (finiteRepresentedSetSheaf Y) ≅
        (constantSheaf (Scheme.smallEtaleTopology U.left) (Type (u + 1))).obj
          (ULift.{u + 1} A)) := by
  obtain ⟨V, hv, hV⟩ := exists_open_isIso_of_bijective_fiber
    (tupleCoverPoint Y A s e) (splitMap X Y A) (splitMap_fiber_bijective Y A s e)
  let := hV
  exact ⟨localSplitChart Y A V, localSplitPointLift Y A s e V hv,
    localSplitPointLift_chart Y A s e V hv, ⟨localSplitIso Y A V⟩,
    ⟨localSplitSheafIso Y A V⟩⟩

theorem exists_etale_trivialization_at_point {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (x : X) :
    ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧
      Nonempty (trivialCover U.left (Fiber (algebraicClosureResiduePoint X x) Y) ≅
        (baseChange U.hom).obj Y) ∧
      Nonempty ((setInverseImage U.hom).obj (finiteRepresentedSetSheaf Y) ≅
        (constantSheaf (Scheme.smallEtaleTopology U.left) (Type (u + 1))).obj
          (ULift.{u + 1} (Fiber (algebraicClosureResiduePoint X x) Y))) := by
  obtain ⟨U, q, hq, hc, hs⟩ := exists_etale_trivialization_at_geometric_point Y
    (Fiber (algebraicClosureResiduePoint X x) Y) (algebraicClosureResiduePoint X x)
    (Equiv.refl _)
  refine ⟨U, q default, ?_, hc, hs⟩
  exact (congrArg
    (fun f : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X =>
      f default) hq).trans (algebraicClosureResiduePoint_image X x default)

/-- The finite label set is the geometric fibre at each base point, so the
construction permits rank to vary between connected components. -/
def finiteCoverLocalTrivialization {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) :
    FiniteSetLocalTrivialization (finiteRepresentedSetSheaf Y) := by
  choose U y hy hc hs using exists_etale_trivialization_at_point Y
  exact {
    index := X
    chart := U
    covers := fun x => ⟨x, y x, hy x⟩
    value := fun x => ULift.{u + 1} (Fiber (algebraicClosureResiduePoint X x) Y)
    finite_value := fun x => inferInstance
    trivialization := fun x => (hs x).some }

theorem finiteRepresentedSetSheaf_isFiniteLocallyConstant {X : Scheme.{u}}
    (Y : Scheme.FiniteEtale X) :
    IsFiniteLocallyConstantSet (finiteRepresentedSetSheaf Y) :=
  ⟨finiteCoverLocalTrivialization Y⟩

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3dbe615e69afcfe41b81e62e47f23c374b0c816050ee2547373b78dbdeac4434.
Definitions, hypotheses and universes are retained modulo native names. -/
