/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.CommonDomination
public import Aglib.AlgebraicGeometry.Surfaces.Birational.TraitGraph
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Trait
public import Aglib.AlgebraicGeometry.Morphisms.Proper.TraitSections
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GenericExtension
public import Aglib.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The original trait graph and regular point domination

The original generic-point map enters the literal generic fibre and then the
actual graph of the specified generic-fibre isomorphism. Its extension from
the regular source retains both original projections. The resulting literal
generic-fibre comparisons retain the given isomorphism over the fraction field.
Dense generic opens give birationality of the original projections, and the
same compatible original sections lift uniquely with both projection equations.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap)

universe u

namespace AlgebraicGeometry.Scheme.TraitDomination

variable (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of R))

private theorem noetherian_of_proper {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of R)) [IsProper f] : IsNoetherian Z := by
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

variable [IsIntegral X] [IsProper p] [Flat p]

/-- The original proper flat integral source has an inhabited literal generic open. -/
theorem sourceOpen_nonempty :
    (TraitGraph.sourceOpen R F p : Set X).Nonempty :=
  Set.nonempty_coe_sort.mp
    (inferInstanceAs (Nonempty (TraitGraph.sourceOpen R F p).toScheme))

/-- The original source generic point lifted into its literal fraction-field fibre. -/
def genericToSourceFibre : Spec X.functionField ⟶ pullback p (baseMap R F) :=
  Scheme.genericToOpen (TraitGraph.sourceOpen R F p) (sourceOpen_nonempty R F p) ≫
    (TraitGraph.sourceOpenIso R F p).inv

@[reassoc (attr := simp)]
theorem genericToSourceFibre_fst :
    genericToSourceFibre R F p ≫ pullback.fst p (baseMap R F) =
      X.fromSpecStalk (genericPoint X) := by
  have hι : (TraitGraph.sourceOpenIso R F p).inv ≫ pullback.fst p (baseMap R F) =
      (TraitGraph.sourceOpen R F p).ι := by
    simp [TraitGraph.sourceOpenIso, TraitGraph.sourceOpen]
  rw [genericToSourceFibre, Category.assoc, hι, Scheme.genericToOpen_ι]

variable (e : (Over.pullback (baseMap R F)).obj (Over.mk p) ≅
  (Over.pullback (baseMap R F)).obj (Over.mk q))

/-- The original source generic map into the actual graph of the given fibre isomorphism. -/
def genericToGraph : Spec X.functionField ⟶ TraitGraph.model R F p q e :=
  genericToSourceFibre R F p ≫ TraitGraph.fromGeneric R F p q e

@[reassoc (attr := simp)]
theorem genericToGraph_toSource :
    genericToGraph R F p q e ≫ TraitGraph.toSource R F p q e =
      X.fromSpecStalk (genericPoint X) := by
  rw [genericToGraph, Category.assoc, TraitGraph.fromGeneric_toSource,
    genericToSourceFibre_fst]

@[reassoc]
theorem genericToGraph_toBase :
    genericToGraph R F p q e ≫ TraitGraph.toBase R F p q e =
      X.fromSpecStalk (genericPoint X) ≫ p := by
  rw [TraitGraph.toBase, ← Category.assoc, genericToGraph_toSource]

/-- The map enters the dense original graph open, hence is dominant onto the actual graph. -/
instance genericToGraph_dominant [IsNoetherian X] [IsProper q] :
    IsDominant (genericToGraph R F p q e) := by
  let U := TraitGraph.sourceOpen R F p
  let k := GraphClosure.fromOpen p q U (TraitGraph.openToTarget R F p q e)
    (TraitGraph.openToTarget_comp R F p q e)
  let a := Scheme.genericToOpen U (sourceOpen_nonempty R F p)
  have hform : genericToGraph R F p q e = a ≫ k := by
    simp only [genericToGraph, genericToSourceFibre, TraitGraph.fromGeneric,
      Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  let : IsDominant (a ≫ U.ι) := by
    change IsDominant (Scheme.genericToOpen U (sourceOpen_nonempty R F p) ≫ U.ι)
    rw [Scheme.genericToOpen_ι]
    infer_instance
  let : IsDominant a := IsDominant.of_comp_of_isOpenImmersion a U.ι
  let : IsIntegral U.toScheme := inferInstance
  let : IsIntegral (TraitGraph.model R F p q e) := inferInstance
  let : IsOpenImmersion k := inferInstance
  let : IsDominant k := Scheme.isDominant_of_isOpenImmersion k
  rw [hform]
  infer_instance

/-- The extension's first original graph projection is exactly its original point-chain map. -/
theorem graphLift_toSource {W : Scheme.{u}} [IsIntegral W]
    (β : W ⟶ X) [IsDominant β] (h : W ⟶ TraitGraph.model R F p q e)
    (hbase : h ≫ TraitGraph.toBase R F p q e = β ≫ p)
    (hgeneric : W.fromSpecStalk (genericPoint W) ≫ h =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ genericToGraph R F p q e) :
    h ≫ TraitGraph.toSource R F p q e = β := by
  apply ext_of_isDominant_of_isSeparated p
    (by simpa only [TraitGraph.toBase, Category.assoc] using hbase)
    (W.fromSpecStalk (genericPoint W))
  calc
    _ = (W.fromSpecStalk (genericPoint W) ≫ h) ≫ TraitGraph.toSource R F p q e :=
      (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
        genericToGraph R F p q e) ≫ TraitGraph.toSource R F p q e :=
      congrArg (fun a ↦ a ≫ TraitGraph.toSource R F p q e) hgeneric
    _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
        X.fromSpecStalk (genericPoint X) := by
      rw [Category.assoc, genericToGraph_toSource]
    _ = _ := (Scheme.fromSpecStalk_genericPoint_naturality β).symm

omit [IsIntegral X] [IsProper p] [Flat p] in
/-- The second original graph projection has the same original trait structure map. -/
theorem graphLift_toTarget_base {W : Scheme.{u}} (β : W ⟶ X)
    (h : W ⟶ TraitGraph.model R F p q e)
    (hsource : h ≫ TraitGraph.toSource R F p q e = β) :
    (h ≫ TraitGraph.toTarget R F p q e) ≫ q = β ≫ p := by
  rw [Category.assoc, ← TraitGraph.toSource_comp, ← Category.assoc, hsource]

omit [IsIntegral X] [Flat p] in
/-- Composition with the original graph-source generic isomorphism is the actual chain map. -/
theorem graphGenericMap_comp_source [IsNoetherian X] [IsProper q]
    {W : Scheme.{u}} (β : W ⟶ X) (c : Blowup.PointBlowupChain β)
    (h : W ⟶ TraitGraph.model R F p q e)
    (hbase : h ≫ TraitGraph.toBase R F p q e = β ≫ p)
    (hsource : h ≫ TraitGraph.toSource R F p q e = β) :
    (Over.pullback (baseMap R F)).map
        (Over.homMk h hbase : Over.mk (β ≫ p) ⟶ Over.mk (TraitGraph.toBase R F p q e)) ≫
      (TraitGraph.sourceGenericIso R F p q e).hom =
        (c.genericIso R F p).hom := by
  rw [TraitGraph.sourceGenericIso_hom, Blowup.PointBlowupChain.genericIso_hom,
    ← Functor.map_comp]
  apply congrArg (Over.pullback (baseMap R F)).map
  apply Over.OverMorphism.ext
  exact hsource

omit [IsIntegral X] [Flat p] in
/-- The original graph lift itself is an isomorphism on the literal generic fibres. -/
theorem graphGenericMap_isIso [IsNoetherian X] [IsProper q]
    {W : Scheme.{u}} (β : W ⟶ X) (c : Blowup.PointBlowupChain β)
    (h : W ⟶ TraitGraph.model R F p q e)
    (hbase : h ≫ TraitGraph.toBase R F p q e = β ≫ p)
    (hsource : h ≫ TraitGraph.toSource R F p q e = β) :
    IsIso ((Over.pullback (baseMap R F)).map
      (Over.homMk h hbase : Over.mk (β ≫ p) ⟶ Over.mk (TraitGraph.toBase R F p q e))) := by
  let m := (Over.pullback (baseMap R F)).map
    (Over.homMk h hbase : Over.mk (β ≫ p) ⟶ Over.mk (TraitGraph.toBase R F p q e))
  have : IsIso (m ≫ (TraitGraph.sourceGenericIso R F p q e).hom) := by
    rw [graphGenericMap_comp_source R F p q e β c h hbase hsource]
    infer_instance
  exact IsIso.of_isIso_comp_right m (TraitGraph.sourceGenericIso R F p q e).hom

omit [IsIntegral X] [Flat p] in
/-- The second literal generic map retains the originally given fibre isomorphism. -/
theorem graphGenericMap_toTarget [IsNoetherian X] [IsProper q]
    {W : Scheme.{u}} (β : W ⟶ X) (c : Blowup.PointBlowupChain β)
    (h : W ⟶ TraitGraph.model R F p q e)
    (hbase : h ≫ TraitGraph.toBase R F p q e = β ≫ p)
    (hsource : h ≫ TraitGraph.toSource R F p q e = β) :
    (c.genericIso R F p).hom ≫ e.hom =
      (Over.pullback (baseMap R F)).map
        (Over.homMk (h ≫ TraitGraph.toTarget R F p q e)
          (graphLift_toTarget_base R F p q e β h hsource) :
          Over.mk (β ≫ p) ⟶ Over.mk q) := by
  let m := (Over.pullback (baseMap R F)).map
    (Over.homMk h hbase : Over.mk (β ≫ p) ⟶ Over.mk (TraitGraph.toBase R F p q e))
  calc
    _ = (m ≫ (TraitGraph.sourceGenericIso R F p q e).hom) ≫ e.hom :=
      congrArg (fun a ↦ a ≫ e.hom)
        (graphGenericMap_comp_source R F p q e β c h hbase hsource).symm
    _ = m ≫ (TraitGraph.targetGenericIso R F p q e).hom := by
      rw [Category.assoc]
      rfl
    _ = _ := by
      rw [TraitGraph.targetGenericIso_hom, ← Functor.map_comp]
      apply congrArg (Over.pullback (baseMap R F)).map
      apply Over.OverMorphism.ext
      rfl

/-- The original structure map of the actual integral point chain is flat
by dominance and the native Dedekind torsion-free criterion. -/
theorem chain_toBase_flat {W : Scheme.{u}} (β : W ⟶ X)
    (c : Blowup.PointBlowupChain β) :
    letI : IsIntegral W := c.isIntegral inferInstance
    letI : IsDominant β := c.isDominant inferInstance
    Flat (β ≫ p) := by
  let : IsIntegral W := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsProper β := c.isProper inferInstance
  let : IsDominant p := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace p p.isOpenMap⟩
  exact Hom.flat_of_isIntegral_of_isDominant (β ≫ p)

/-- The original proper flat regular source has an actual regular graph domination. -/
theorem exists_regular_graphLift [IsIntegral Y] [IsProper q]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2) :
    ∃ (W : Scheme.{u}) (β : W ⟶ X) (c : Blowup.PointBlowupChain β),
      letI : IsIntegral W := c.isIntegral inferInstance
      letI : IsDominant β := c.isDominant inferInstance
      ∃ h : W ⟶ TraitGraph.model R F p q e,
        IsNoetherian W ∧ RegularStalks W ∧ topologicalKrullDim W ≤ 2 ∧
        IsProper β ∧ Surjective β ∧ IsProper (β ≫ p) ∧ Flat (β ≫ p) ∧
        IsProper h ∧ Surjective h ∧
        IsProper (h ≫ TraitGraph.toTarget R F p q e) ∧
        Surjective (h ≫ TraitGraph.toTarget R F p q e) ∧
        h ≫ TraitGraph.toSource R F p q e = β ∧
        h ≫ TraitGraph.toBase R F p q e = β ≫ p := by
  let : IsNoetherian X := noetherian_of_proper R p
  obtain ⟨W, β, c, hout⟩ :=
    CommonDomination.exists_proper_pointBlowupChain_commonDomination R hX hd p
      (TraitGraph.toBase R F p q e) (genericToGraph R F p q e)
      (genericToGraph_toBase R F p q e)
  let : IsIntegral W := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  obtain ⟨h, j, hpβ, _, hN, hreg, hdim, hph, hsurjh, hbase, hgeneric, _, _⟩ := hout
  let : IsProper β := hpβ
  let : IsProper h := hph
  let : Surjective h := hsurjh
  have hsource := graphLift_toSource R F p q e β h hbase hgeneric
  have hsurjβ : Surjective β :=
    surjective_of_isDominant_of_isClosed_range β β.isClosedMap.isClosed_range
  exact ⟨W, β, c, h, hN, hreg, hdim, hpβ, hsurjβ, inferInstance,
    chain_toBase_flat R p β c, hph, hsurjh,
    inferInstance, inferInstance, hsource, hbase⟩


private theorem birationalOver_of_genericIso
    {W Z : Scheme.{u}} [IsIntegral W] [IsIntegral Z]
    (r : W ⟶ Spec (.of R)) [IsProper r] [Flat r]
    (s : Z ⟶ Spec (.of R)) (a : W ⟶ Z) (ha : a ≫ s = r)
    (ξ : (Over.pullback (baseMap R F)).obj (Over.mk r) ≅
      (Over.pullback (baseMap R F)).obj (Over.mk s))
    (hξ : ξ.hom = (Over.pullback (baseMap R F)).map
      (Over.homMk a ha : Over.mk r ⟶ Over.mk s)) : BirationalOver a (𝟙 Z) := by
  let U := TraitGraph.sourceOpen R F r
  let V := TraitGraph.sourceOpen R F s
  let eU := TraitGraph.sourceOpenIso R F r
  let eV := TraitGraph.sourceOpenIso R F s
  let : Nonempty U.toScheme := inferInstance
  have hV : Nonempty V.toScheme :=
    ⟨eV.hom (ξ.hom.left (eU.inv (Classical.choice (inferInstance : Nonempty U.toScheme))))⟩
  let E : W.PartialIso Z := {
    source := U
    dense_source := U.isOpen.dense
      (Set.nonempty_coe_sort.mp (inferInstanceAs (Nonempty U.toScheme)))
    target := V
    dense_target := V.isOpen.dense (Set.nonempty_coe_sort.mp hV)
    iso := eU.symm ≪≫ (Over.forget (Spec (.of F))).mapIso ξ ≪≫ eV }
  have hUι : eU.inv ≫ pullback.fst r (baseMap R F) = U.ι := by
    simp [eU, U, TraitGraph.sourceOpenIso, TraitGraph.sourceOpen]
  have hVι : eV.hom ≫ V.ι = pullback.fst s (baseMap R F) := by
    simp [eV, V, TraitGraph.sourceOpenIso, TraitGraph.sourceOpen]
  have hfst : ξ.hom.left ≫ pullback.fst s (baseMap R F) =
      pullback.fst r (baseMap R F) ≫ a := by
    rw [hξ]
    simp [Over.pullback_map_left]
  refine ⟨E, ?_⟩
  change ((eU.inv ≫ ξ.hom.left) ≫ eV.hom) ≫ V.ι ≫ 𝟙 Z = U.ι ≫ a
  rw [Category.comp_id, Category.assoc, Category.assoc, hVι, hfst,
    ← Category.assoc, hUι]

omit [IsIntegral X] [IsProper p] [Flat p] in
/-- A compatible pair of original sections lifts uniquely through an actual
proper projection whose literal generic map retains the given fibre isomorphism. -/
theorem existsUnique_compatible_section {W : Scheme.{u}}
    (β : W ⟶ X) (γ : W ⟶ Y) (hγ : γ ≫ q = β ≫ p) [IsProper β] [IsSeparated q]
    [IsIso ((Over.pullback (baseMap R F)).map
      (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p))]
    (hcompat : (Over.pullback (baseMap R F)).map
        (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p) ≫ e.hom =
      (Over.pullback (baseMap R F)).map
        (Over.homMk γ hγ : Over.mk (β ≫ p) ⟶ Over.mk q))
    (sX : Spec (.of R) ⟶ X) (hsX : sX ≫ p = 𝟙 _)
    (sY : Spec (.of R) ⟶ Y) (hsY : sY ≫ q = 𝟙 _)
    (he : TraitGraph.genericSection R F p sX hsX ≫ e.hom.left =
      TraitGraph.genericSection R F q sY hsY) :
    ∃! sW : Spec (.of R) ⟶ W,
      sW ≫ β = sX ∧ sW ≫ γ = sY ∧ sW ≫ (β ≫ p) = 𝟙 _ := by
  let sW := ProperTraitSections.lift R F p β sX hsX
  have hWβ : sW ≫ β = sX := ProperTraitSections.lift_comp R F p β sX hsX
  have hWbase : sW ≫ (β ≫ p) = 𝟙 _ := ProperTraitSections.lift_toBase R F p β sX hsX
  let mX := (Over.pullback (baseMap R F)).map
    (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p)
  let mY := (Over.pullback (baseMap R F)).map
    (Over.homMk γ hγ : Over.mk (β ≫ p) ⟶ Over.mk q)
  let sF := TraitGraph.genericSection R F (β ≫ p) sW hWbase
  have hFX : sF ≫ mX.left = TraitGraph.genericSection R F p sX hsX :=
    ProperTraitSections.lift_genericSection_comp R F p β sX hsX
  have hleft : mX.left ≫ e.hom.left = mY.left := congrArg
    (fun f : (Over.pullback (baseMap R F)).obj (Over.mk (β ≫ p)) ⟶
        (Over.pullback (baseMap R F)).obj (Over.mk q) ↦ f.left) hcompat
  have hFY : sF ≫ mY.left = TraitGraph.genericSection R F q sY hsY := by
    calc
      _ = sF ≫ (mX.left ≫ e.hom.left) := congrArg (fun a ↦ sF ≫ a) hleft.symm
      _ = (sF ≫ mX.left) ≫ e.hom.left := (Category.assoc _ _ _).symm
      _ = TraitGraph.genericSection R F p sX hsX ≫ e.hom.left :=
        congrArg (fun a ↦ a ≫ e.hom.left) hFX
      _ = _ := he
  have hfst : mY.left ≫ pullback.fst q (baseMap R F) =
      pullback.fst (β ≫ p) (baseMap R F) ≫ γ := by
    simp [mY, Over.pullback_map_left]
  have hgeneric : baseMap R F ≫ (sW ≫ γ) = baseMap R F ≫ sY := by
    calc
      _ = (sF ≫ pullback.fst (β ≫ p) (baseMap R F)) ≫ γ := by
        rw [TraitGraph.genericSection_fst, Category.assoc]
      _ = (sF ≫ mY.left) ≫ pullback.fst q (baseMap R F) :=
        (Category.assoc sF (pullback.fst (β ≫ p) (baseMap R F)) γ).trans
          ((congrArg (fun a ↦ sF ≫ a) hfst.symm).trans
            (Category.assoc sF mY.left (pullback.fst q (baseMap R F))).symm)
      _ = TraitGraph.genericSection R F q sY hsY ≫ pullback.fst q (baseMap R F) :=
        congrArg (fun a ↦ a ≫ pullback.fst q (baseMap R F)) hFY
      _ = _ := TraitGraph.genericSection_fst R F q sY hsY
  have hWγ : sW ≫ γ = sY := by
    let : IsDominant (baseMap R F) := LocalRing.GenericFiber.fraction_base_dominant R F
    apply ext_of_isDominant_of_isSeparated q ?_ (baseMap R F) hgeneric
    rw [Category.assoc, hγ, hWbase, hsY]
  refine ⟨sW, ⟨hWβ, hWγ, hWbase⟩, ?_⟩
  intro t ht
  exact ProperTraitSections.lift_unique R F p β sX hsX t ht.1


/-- The same literal generic fibre has an actual regular proper flat common
model, with both original projections and unique lifts of compatible original sections. -/
theorem exists_regular_commonDomination [IsIntegral Y] [IsProper q]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2) :
    ∃ (W : Scheme.{u}) (β : W ⟶ X) (c : Blowup.PointBlowupChain β),
      letI : IsIntegral W := c.isIntegral inferInstance
      letI : IsDominant β := c.isDominant inferInstance
      ∃ (h : W ⟶ TraitGraph.model R F p q e) (γ : W ⟶ Y)
        (hbase : h ≫ TraitGraph.toBase R F p q e = β ≫ p)
        (hγ : γ ≫ q = β ≫ p)
        (eX : (Over.pullback (baseMap R F)).obj (Over.mk (β ≫ p)) ≅
          (Over.pullback (baseMap R F)).obj (Over.mk p))
        (eY : (Over.pullback (baseMap R F)).obj (Over.mk (β ≫ p)) ≅
          (Over.pullback (baseMap R F)).obj (Over.mk q)),
        IsNoetherian W ∧ RegularStalks W ∧ topologicalKrullDim W ≤ 2 ∧
        IsProper (β ≫ p) ∧ Flat (β ≫ p) ∧
        IsProper β ∧ Surjective β ∧ BirationalOver β (𝟙 X) ∧
        IsProper h ∧ Surjective h ∧ BirationalOver h (𝟙 (TraitGraph.model R F p q e)) ∧
        IsProper γ ∧ Surjective γ ∧ BirationalOver γ (𝟙 Y) ∧
        h ≫ TraitGraph.toSource R F p q e = β ∧ h ≫ TraitGraph.toTarget R F p q e = γ ∧
        IsIso ((Over.pullback (baseMap R F)).map
          (Over.homMk h hbase : Over.mk (β ≫ p) ⟶ Over.mk (TraitGraph.toBase R F p q e))) ∧
        eX.hom = (Over.pullback (baseMap R F)).map
          (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p) ∧
        eY.hom = (Over.pullback (baseMap R F)).map
          (Over.homMk γ hγ : Over.mk (β ≫ p) ⟶ Over.mk q) ∧
        eX ≪≫ e = eY ∧
        ∀ (sX : Spec (.of R) ⟶ X) (hsX : sX ≫ p = 𝟙 _)
          (sY : Spec (.of R) ⟶ Y) (hsY : sY ≫ q = 𝟙 _),
          TraitGraph.genericSection R F p sX hsX ≫ e.hom.left =
            TraitGraph.genericSection R F q sY hsY →
          ∃! sW : Spec (.of R) ⟶ W,
            sW ≫ β = sX ∧ sW ≫ γ = sY ∧ sW ≫ (β ≫ p) = 𝟙 _ := by
  let : IsNoetherian X := noetherian_of_proper R p
  obtain ⟨W, β, c, hout⟩ := exists_regular_graphLift R F p q e hX hd
  let : IsIntegral W := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  obtain ⟨h, hN, hreg, hdim, hpβ, hsβ, hpbase, hfbase, hph, hsh,
    hpγ, hsγ, hsource, hbase⟩ := hout
  let : IsProper β := hpβ
  let : IsProper (β ≫ p) := hpbase
  let : Flat (β ≫ p) := hfbase
  let γ := h ≫ TraitGraph.toTarget R F p q e
  have hγ : γ ≫ q = β ≫ p := graphLift_toTarget_base R F p q e β h hsource
  let eX := c.genericIso R F p
  let eY := eX ≪≫ e
  have heX : eX.hom = (Over.pullback (baseMap R F)).map
      (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p) :=
    c.genericIso_hom R F p
  have heY : eY.hom = (Over.pullback (baseMap R F)).map
      (Over.homMk γ hγ : Over.mk (β ≫ p) ⟶ Over.mk q) :=
    graphGenericMap_toTarget R F p q e β c h hbase hsource
  have hbirγ : BirationalOver γ (𝟙 Y) :=
    birationalOver_of_genericIso R F (β ≫ p) q γ hγ eY heY
  let mH := (Over.pullback (baseMap R F)).map
    (Over.homMk h hbase : Over.mk (β ≫ p) ⟶ Over.mk (TraitGraph.toBase R F p q e))
  let : IsIso mH := graphGenericMap_isIso R F p q e β c h hbase hsource
  have hbirh : BirationalOver h (𝟙 (TraitGraph.model R F p q e)) :=
    birationalOver_of_genericIso R F (β ≫ p) (TraitGraph.toBase R F p q e)
      h hbase (asIso mH) rfl
  let : IsIso ((Over.pullback (baseMap R F)).map
      (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p)) :=
    c.genericBaseChange_isIso R F p
  have hcompat : (Over.pullback (baseMap R F)).map
        (Over.homMk β rfl : Over.mk (β ≫ p) ⟶ Over.mk p) ≫ e.hom =
      (Over.pullback (baseMap R F)).map
        (Over.homMk γ hγ : Over.mk (β ≫ p) ⟶ Over.mk q) := by
    rw [← heX]
    exact heY
  refine ⟨W, β, c, h, γ, hbase, hγ, eX, eY, hN, hreg, hdim,
    hpbase, hfbase, hpβ, hsβ, c.birationalOver inferInstance,
    hph, hsh, hbirh, hpγ, hsγ, hbirγ, hsource, rfl,
    graphGenericMap_isIso R F p q e β c h hbase hsource, heX, heY, rfl, ?_⟩
  intro sX hsX sY hsY he
  exact existsUnique_compatible_section R F p q e β γ hγ hcompat sX hsX sY hsY he

end AlgebraicGeometry.Scheme.TraitDomination
