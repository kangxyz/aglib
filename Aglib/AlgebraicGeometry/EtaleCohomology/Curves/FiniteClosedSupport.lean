/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ComponentSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DisjointSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.AlgebraicGeometry.Sites.EtaleSigmaGeometry
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Finite closed supports and their original cohomology

A finite set of closed points determines the literal coproduct of their actual
residue-field spectra. Its original coproduct map is a finite closed immersion.
If those residue fields are separably closed, every original abelian etale
coefficient on the coproduct has zero positive cohomology. No reducedness of the
ambient scheme or finiteness restriction on the coefficient is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport

universe u w

variable (X : Scheme.{u}) (Z : Set X)

/-- The literal coproduct of the actual residue-field spectra at the support. -/
abbrev pointScheme : Scheme.{u} := ∐ fun x : Z => Spec (X.residueField x.val)

/-- The original sum of the native residue-field maps into the ambient scheme. -/
def inclusion : pointScheme X Z ⟶ X :=
  Sigma.desc (fun x : Z => X.fromSpecResidueField x.val)

@[reassoc (attr := simp)]
theorem component_inclusion (x : Z) :
    Sigma.ι (fun x : Z => Spec (X.residueField x.val)) x ≫ inclusion X Z =
      X.fromSpecResidueField x.val :=
  Sigma.ι_comp_desc _ _

@[simp]
theorem inclusion_component_apply (x : Z) (t : Spec (X.residueField x.val)) :
    inclusion X Z (Sigma.ι (fun x : Z => Spec (X.residueField x.val)) x t) = x.val := by
  rw [← Scheme.Hom.comp_apply, component_inclusion, Scheme.fromSpecResidueField_apply]

/-- The literal inclusion has exactly the requested set as image. -/
theorem range_inclusion : Set.range (inclusion X Z) = Z := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨z, t⟩, rfl⟩ :=
      (sigmaMk (fun z : Z => Spec (X.residueField z.val))).surjective t
    simpa only [sigmaMk_mk, inclusion_component_apply] using z.property
  · intro hx
    exact ⟨Sigma.ι (fun z : Z => Spec (X.residueField z.val)) ⟨x, hx⟩
      (IsLocalRing.closedPoint (X.residueField x)), inclusion_component_apply X Z _ _⟩

/-- Different points of the residue-field coproduct have different images. -/
theorem inclusion_injective : Function.Injective (inclusion X Z) := by
  intro a b hab
  obtain ⟨⟨x, a⟩, rfl⟩ :=
    (sigmaMk (fun z : Z => Spec (X.residueField z.val))).surjective a
  obtain ⟨⟨y, b⟩, rfl⟩ :=
    (sigmaMk (fun z : Z => Spec (X.residueField z.val))).surjective b
  simp only [sigmaMk_mk, inclusion_component_apply] at hab
  obtain rfl : x = y := Subtype.ext hab
  rw [Subsingleton.elim a b]

/-- Stalk surjectivity is inherited from the actual residue-field components. -/
instance inclusion_surjectiveOnStalks : SurjectiveOnStalks (inclusion X Z) :=
  IsZariskiLocalAtSource.sigmaDesc
    (P := @SurjectiveOnStalks) (fun _ => inferInstance)

instance inclusion_mono : Mono (inclusion X Z) :=
  SurjectiveOnStalks.mono_of_injective (inclusion_injective X Z)

/-- A finite union of actual closed residue-field points is a closed immersion. -/
theorem inclusion_isClosedImmersion (hfin : Z.Finite)
    (hclosed : ∀ x ∈ Z, IsClosed ({x} : Set X)) :
    IsClosedImmersion (inclusion X Z) := by
  let : Finite Z := hfin.to_subtype
  let : ∀ x : Z, IsClosedImmersion (X.fromSpecResidueField x.val) :=
    fun x => isClosed_singleton_iff_isClosedImmersion.mp (hclosed x.val x.property)
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (inclusion X Z).continuous (inclusion_injective X Z) ?_⟩
  intro C hC
  have hCimage : inclusion X Z '' C = ⋃ x : Z,
      X.fromSpecResidueField x.val ''
        ((Sigma.ι (fun x : Z => Spec (X.residueField x.val)) x) ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨⟨x, t⟩, rfl⟩ :=
        (sigmaMk (fun x : Z => Spec (X.residueField x.val))).surjective t
      refine Set.mem_iUnion.mpr ⟨x, t, ?_, ?_⟩
      · simpa only [Set.mem_preimage, sigmaMk_mk] using ht
      · simp only [sigmaMk_mk, inclusion_component_apply,
          Scheme.fromSpecResidueField_apply]
    · intro hy
      obtain ⟨x, t, ht, rfl⟩ := Set.mem_iUnion.mp hy
      refine ⟨Sigma.ι (fun x : Z => Spec (X.residueField x.val)) x t, ht, ?_⟩
      simp only [inclusion_component_apply, Scheme.fromSpecResidueField_apply]
  rw [hCimage]
  exact isClosed_iUnion_of_finite fun x =>
    (X.fromSpecResidueField x.val).isClosedEmbedding.isClosedMap _
      (hC.preimage (Sigma.ι (fun x : Z => Spec (X.residueField x.val)) x).continuous)

/-- The finite support inclusion is finite, without a reducedness premise on `X`. -/
theorem inclusion_isFinite (hfin : Z.Finite)
    (hclosed : ∀ x ∈ Z, IsClosed ({x} : Set X)) : IsFinite (inclusion X Z) := by
  let := inclusion_isClosedImmersion X Z hfin hclosed
  infer_instance

/-- A field-valued point lifts to the literal support exactly when its image lies there. -/
theorem exists_lift_iff {K : Type u} [Field K] (s : Spec (.of K) ⟶ X) :
    (∃ t : Spec (.of K) ⟶ pointScheme X Z, t ≫ inclusion X Z = s) ↔
      s (IsLocalRing.closedPoint K) ∈ Z := by
  constructor
  · rintro ⟨t, rfl⟩
    change inclusion X Z (t (IsLocalRing.closedPoint K)) ∈ Z
    exact (range_inclusion X Z).subset ⟨t (IsLocalRing.closedPoint K), rfl⟩
  · intro hs
    let x : Z := ⟨s (IsLocalRing.closedPoint K), hs⟩
    refine ⟨Spec.map (X.descResidueField (Scheme.stalkClosedPointTo s)) ≫
      Sigma.ι (fun x : Z => Spec (X.residueField x.val)) x, ?_⟩
    rw [Category.assoc, component_inclusion]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X s

attribute [local instance] hasSheafifyLarge

variable (hfin : Z.Finite) (hsep : ∀ x : Z, IsSepClosed (X.residueField x.val))

include hfin hsep

set_option backward.isDefEq.respectTransparency false in
/-- Exact original component evaluation makes global sections on the finite
support preserve epimorphisms of arbitrary abelian sheaves. -/
theorem globalSections_preservesEpimorphisms :
    (globalSections (pointScheme X Z)).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    let : Finite Z := hfin.to_subtype
    let Y := fun x : Z => Spec (X.residueField x.val)
    let hcomponents (x : Z) : Epi (φ.hom.app (op (Scheme.Etale.sigmaChart Y x))) := by
      let : IsSepClosed (X.residueField x.val) := hsep x
      let : HenselianLocalRing (X.residueField x.val) := Field.henselian _
      let : Etale (Sigma.ι Y x) := (Scheme.Etale.sigmaChart Y x).prop
      let : IsSepClosed (IsLocalRing.ResidueField (X.residueField x.val)) :=
        Algebra.IsAlgebraic.isSepClosed (F := X.residueField x.val)
      let : ((sheafSections (pointScheme X Z).smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.sigmaChart Y x))).PreservesEpimorphisms :=
        Finite.componentSections_preservesEpimorphisms
          (X.residueField x.val) (Sigma.ι Y x)
      exact Functor.map_epi
        ((sheafSections (pointScheme X Z).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op (Scheme.Etale.sigmaChart Y x))) φ
    apply Finite.epi_sections_of_epi_components F (Scheme.Etale.sigmaChartInclusion Y)
      (Scheme.Etale.sigmaCharts_cover Y) _ φ
    intro x y hxy T a b hab
    exact isEmpty_of_commSq_sigmaι_of_ne
      (g := Y) (a := a.left) (b := b.left)
      ⟨congrArg (fun k : T ⟶ Scheme.Etale.mk (𝟙 (∐ Y)) => k.left) hab⟩ hxy

/-- The original constant integer source is projective on the finite support. -/
theorem constant_integer_projective :
    Projective ((constantSheaf (pointScheme X Z).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  let := globalSections_preservesEpimorphisms X Z hfin hsep
  let J := (pointScheme X Z).smallEtaleTopology
  let T := etaleTerminal (pointScheme X Z)
  let hP := Sheaf.Hypercohomology.projective_freeAbelianSheaf.{u + 1, u, u + 1}
    J T (fun {F G} φ _ => (AddCommGrpCat.epi_iff_surjective _).mp
      (Functor.map_epi (globalSections (pointScheme X Z)) φ))
  exact Projective.of_iso
    (Sheaf.Hypercohomology.constantIntegerFreeTerminalIso
      J (etaleTerminalIsTerminal (pointScheme X Z))).symm hP

/-- Every original coefficient on a finite separably closed support is acyclic
in positive degree, with the independently specified original Ext universe. -/
theorem subsingleton_H
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (pointScheme X Z))]
    (F : AbelianSheaf.{u, u + 1} (pointScheme X Z)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) := by
  let := constant_integer_projective X Z hfin hsep
  apply subsingleton_of_forall_eq 0
  intro a
  cases q with
  | zero => simp at hq
  | succ q => exact Abelian.Ext.eq_zero_of_projective a

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport
