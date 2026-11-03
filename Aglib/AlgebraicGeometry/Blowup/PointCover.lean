/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Restriction
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Stalk.GenericPoint
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Aglib.AlgebraicGeometry.Stalk.GenericPoint.Dimension

/-!
# A closed-point blowup cover on the original canonical affine model

The two components are the canonical blowup of the actual centre ideal on a
specified affine neighbourhood and the original open complement of the centre.
Their maps are the existing native base-change map and open inclusion. No
regularity, integrality or Noetherianity is needed for the cover itself.

For an integral base and an original stalk of dimension two, the original
generic point proves that both components and the off-centre open are nonempty;
the existing blowup integrality theorem supplies integrality of the same objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.PointCover

variable {X : Scheme.{u}} (x : X)

/-- The canonical blowup of the actual section ideal, with no change of generators. -/
def localDatum (V : X.affineOpens) :
    BlowupDatum (affineCenter Γ(X, V) ((X.fromSpecResidueField x).ker.ideal V)) :=
  blowupDatum (affineCenter Γ(X, V) ((X.fromSpecResidueField x).ker.ideal V))

variable (B : BlowupDatum (X.fromSpecResidueField x).ker)

/-- The original canonical affine model maps to the specified original blowup. -/
def localMap (V : X.affineOpens) : (localDatum x V).Y ⟶ B.Y :=
  BaseChange.map V.2.fromSpec
    (comap_fromSpec_eq_affineCenter (X.fromSpecResidueField x).ker V) B (localDatum x V)

/-- The constructor is precisely the native base-change map on the canonical datum. -/
theorem localMap_eq (V : X.affineOpens) :
    localMap x B V = BaseChange.map V.2.fromSpec
      (comap_fromSpec_eq_affineCenter (X.fromSpecResidueField x).ker V) B
      (blowupDatum (affineCenter Γ(X, V) ((X.fromSpecResidueField x).ker.ideal V))) := rfl

/-- The original projection triangle, with no comparison to an affine Proj model. -/
@[reassoc]
theorem localMap_map (V : X.affineOpens) :
    localMap x B V ≫ B.map = (localDatum x V).map ≫ V.2.fromSpec :=
  BaseChange.map_triangle _ _ _ _

/-- Native flat base change supplies the actual square for the same map. -/
theorem localMap_isPullback (V : X.affineOpens) :
    IsPullback (localMap x B V) (localDatum x V).map B.map V.2.fromSpec := by
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  exact BaseChange.isPullback_of_flat V.2.fromSpec inferInstance
    (comap_fromSpec_eq_affineCenter (X.fromSpecResidueField x).ker V) B (localDatum x V)

instance localMap_isOpenImmersion (V : X.affineOpens) :
    IsOpenImmersion (localMap x B V) := by
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (localMap_isPullback x B V).flip inferInstance

/-- The component range is the original inverse image of the chosen affine open. -/
theorem localMap_range (V : X.affineOpens) :
    Set.range (localMap x B V) = B.map ⁻¹' (V.1 : Set X) := by
  rw [Scheme.Pullback.Fibre.pullback_range_fst (localMap_isPullback x B V),
    V.2.range_fromSpec]

/-- The actual off-centre open in the specified original blowup. -/
def awayOpen : B.Y.Opens := B.map ⁻¹ᵁ centreComplement (X.fromSpecResidueField x).ker

/-- The actual structural map is an isomorphism off the original centre. -/
theorem away_isIso : IsIso (B.map ∣_ centreComplement (X.fromSpecResidueField x).ker) :=
  B.restrict_isIso_of_disjoint _ (centreComplement_disjoint _)

/-- The isomorphism is the native restriction of the same structural map. -/
def awayIso :
    (awayOpen x B).toScheme ≅ (centreComplement (X.fromSpecResidueField x).ker).toScheme :=
  @asIso Scheme.{u} _
    (B.map ⁻¹ᵁ centreComplement (X.fromSpecResidueField x).ker).toScheme
    (centreComplement (X.fromSpecResidueField x).ker).toScheme
    (B.map ∣_ centreComplement (X.fromSpecResidueField x).ker) (away_isIso x B)

/-- The original forward map of the off-centre isomorphism. -/
theorem awayIso_hom :
    (awayIso x B).hom = B.map ∣_ centreComplement (X.fromSpecResidueField x).ker := rfl

/-- The off-centre isomorphism retains the original map to the base. -/
@[reassoc]
theorem awayIso_hom_ι :
    (awayIso x B).hom ≫ (centreComplement (X.fromSpecResidueField x).ker).ι =
      (awayOpen x B).ι ≫ B.map :=
  morphismRestrict_ι B.map _

/-- Closedness, not just affine-neighbourhood membership, identifies the support. -/
theorem support_eq (hclosed : IsClosed ({x} : Set X)) :
    ((X.fromSpecResidueField x).ker.support : Set X) = {x} := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hclosed.closure_eq]

/-- The canonical affine component and the literal off-centre open. -/
def component (V : X.affineOpens) : Bool → Scheme.{u}
  | true => (localDatum x V).Y
  | false => (awayOpen x B).toScheme

/-- The two original component maps, before forming a cover. -/
def componentMap (V : X.affineOpens) : (i : Bool) → component x B V i ⟶ B.Y
  | true => localMap x B V
  | false => (awayOpen x B).ι

instance componentMap_isOpenImmersion (V : X.affineOpens) (i : Bool) :
    IsOpenImmersion (componentMap x B V i) := by
  cases i
  · exact (inferInstance : IsOpenImmersion (awayOpen x B).ι)
  · exact localMap_isOpenImmersion x B V

/-- The two original maps jointly cover the original blowup at a closed point. -/
theorem covers (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens) (hxV : x ∈ V.1)
    (y : B.Y) : ∃ i z, componentMap x B V i z = y := by
  by_cases hy : B.map y ∈ V.1
  · have hr : y ∈ Set.range (localMap x B V) := by
      rw [localMap_range]
      exact hy
    obtain ⟨z, hz⟩ := hr
    exact ⟨true, z, hz⟩
  · have hne : B.map y ≠ x := by
      intro h
      apply hy
      rw [h]
      exact hxV
    have hw : y ∈ awayOpen x B := by
      change B.map y ∉ ((X.fromSpecResidueField x).ker.support : Set X)
      rw [support_eq x hclosed]
      exact hne
    exact ⟨false, ⟨y, hw⟩, rfl⟩

/-- The literal two-component open cover, without changing either source model. -/
def cover (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens) (hxV : x ∈ V.1) :
    B.Y.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (component x B V) (componentMap x B V)
    (covers x B hclosed V hxV) (fun i => componentMap_isOpenImmersion x B V i)

/-- The index type is exactly the two chosen components. -/
theorem cover_I₀ (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens) (hxV : x ∈ V.1) :
    (cover x B hclosed V hxV).I₀ = Bool := rfl

/-- The affine component remains the same original canonical blowup. -/
theorem cover_X_true (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) : (cover x B hclosed V hxV).X true = (localDatum x V).Y := rfl

/-- The second component is the actual open complement in the original blowup. -/
theorem cover_X_false (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) : (cover x B hclosed V hxV).X false = (awayOpen x B).toScheme := rfl

/-- The first cover arrow is the original canonical base-change map. -/
theorem cover_f_true (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) : (cover x B hclosed V hxV).f true = localMap x B V := rfl

/-- The second cover arrow is the original open inclusion. -/
theorem cover_f_false (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) : (cover x B hclosed V hxV).f false = (awayOpen x B).ι := rfl

/-- The first cover range is the actual inverse image of the affine neighbourhood. -/
theorem cover_range_true (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) :
    Set.range ((cover x B hclosed V hxV).f true) = B.map ⁻¹' (V.1 : Set X) :=
  localMap_range x B V

/-- The second cover range is the original off-centre open. -/
theorem cover_range_false (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) :
    Set.range ((cover x B hclosed V hxV).f false) = (awayOpen x B : Set B.Y) :=
  (awayOpen x B).range_ι

section Integral

variable [IsIntegral X]

/-- The dimension-two stalk excludes the original generic point from the centre. -/
theorem genericPoint_not_mem_support (hclosed : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    genericPoint X ∉ ((X.fromSpecResidueField x).ker.support : Set X) :=
  genericPoint_not_mem_pointCentre x hclosed (ne_genericPoint_of_stalk_dimension_two x hd)

/-- Integrality of the specified original blowup, derived rather than assumed. -/
theorem isIntegral (hclosed : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) : IsIntegral B.Y :=
  B.isIntegral_of_genericPoint_not_mem_support (genericPoint_not_mem_support x hclosed hd)

/-- An actual preimage of the generic point lies in the original off-centre open. -/
theorem awayOpen_nonempty (hclosed : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) : Nonempty (awayOpen x B) := by
  have hη := genericPoint_not_mem_support x hclosed hd
  obtain ⟨y, hy⟩ := B.mem_range_of_not_mem_support hη
  refine ⟨⟨y, ?_⟩⟩
  change B.map y ∉ ((X.fromSpecResidueField x).ker.support : Set X)
  rwa [hy]

include B in
/-- The same generic-point preimage meets the canonical affine component. -/
theorem localDatum_nonempty (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    Nonempty (localDatum x V).Y := by
  have hη := genericPoint_not_mem_support x hclosed hd
  have hηV : genericPoint X ∈ V.1 :=
    ((genericPoint_spec X).mem_open_set_iff V.1.isOpen).mpr ⟨x, Set.mem_univ x, hxV⟩
  obtain ⟨y, hy⟩ := B.mem_range_of_not_mem_support hη
  have hr : y ∈ Set.range (localMap x B V) := by
    rw [localMap_range]
    change B.map y ∈ V.1
    rwa [hy]
  obtain ⟨z, _⟩ := hr
  exact ⟨z⟩

/-- Both original cover sources are nonempty under the genuine geometric hypotheses. -/
theorem component_nonempty (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) (hd : ringKrullDim (X.presheaf.stalk x) = 2) (i : Bool) :
    Nonempty (component x B V i) := by
  cases i
  · exact awayOpen_nonempty x B hclosed hd
  · exact localDatum_nonempty x B hclosed V hxV hd

/-- Integrality of each same nonempty open component follows from its original map. -/
theorem component_isIntegral (hclosed : IsClosed ({x} : Set X)) (V : X.affineOpens)
    (hxV : x ∈ V.1) (hd : ringKrullDim (X.presheaf.stalk x) = 2) (i : Bool) :
    IsIntegral (component x B V i) := by
  let : IsIntegral B.Y := isIntegral x B hclosed hd
  let : Nonempty (component x B V i) := component_nonempty x B hclosed V hxV hd i
  exact isIntegral_of_isOpenImmersion (componentMap x B V i)

end Integral

end AlgebraicGeometry.Scheme.Blowup.PointCover
