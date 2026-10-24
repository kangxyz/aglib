/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineEmbedding
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedLine
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalStructureSheaf
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.Topology.Inseparable

/-!
# Original structure direct images of a regular closed-point blowup

The actual two-generator affine Rees blowup embeds in the original
projective line, so its structure module is acyclic in positive degrees.
On the literal local-spectrum pullbacks of an actual regular point
blowup, this applies at the centre; away from the centre the original
pullback projection is an isomorphism. The native higher-image stalk
comparison therefore kills every positive structure direct image.

The ordinary structural unit is the actual proper-birational-normal unit.
The current consumer is regular-source point-chain cohomology; the chain
induction and rationality assembly are separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Full original ideal generators give a closed embedding of the actual
affine blowup, retaining its original structural map. -/
private theorem exists_closedLine_twoGeneratedBlowup
    (A : Type u) [CommRing A] (I : Ideal A) (B : BlowupDatum (affineCenter A I))
    (a b : I) (hI : Ideal.span {(a : A), (b : A)} = I) :
    ∃ j : B.Y ⟶ ProjectiveSpace A (ULift.{u} (Fin 2)),
      IsClosedImmersion j ∧
        j ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin 2)) = B.map := by
  let v : ULift.{u} (Fin 2) → I := fun k => if k.down = 0 then a else b
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    apply top_unique
    intro z _
    have hz : (z : A) ∈ Ideal.span {(a : A), (b : A)} := by
      rw [hI]
      exact z.property
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hz
    have ha : a ∈ Submodule.span A (Set.range v) :=
      Submodule.subset_span ⟨⟨0⟩, by simp [v]⟩
    have hb : b ∈ Submodule.span A (Set.range v) :=
      Submodule.subset_span ⟨⟨1⟩, by simp [v]⟩
    have he : r • a + s • b = z := by
      apply Subtype.ext
      exact hrs
    rw [← he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ r ha) (Submodule.smul_mem _ s hb)
  let g : ULift.{u} (Fin 2) → reesAlgebra I :=
    fun k => reesAlgebra.degreeOneLinearMap I (v k)
  have hg : Submodule.span A (Set.range g) = reesAlgebra.grading I 1 := by
    calc
      _ = (Submodule.span A (Set.range v)).map (reesAlgebra.degreeOneLinearMap I) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = reesAlgebra.grading I 1 := by
        rw [hv, Submodule.map_top, reesAlgebra.degreeOneLinearMap_range]
  let j₀ : affineProj I ⟶ ProjectiveSpace A (ULift.{u} (Fin 2)) :=
    Proj.DegreeOneEmbedding.embedding (reesAlgebra.grading I) g hg
      (reesAlgebra.grading_one_pow I)
  let : IsClosedImmersion j₀ := Proj.DegreeOneEmbedding.embedding_isClosedImmersion
    (reesAlgebra.grading I) g hg (reesAlgebra.grading_one_pow I)
  have hj₀ : j₀ ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin 2)) = affineProjMap I :=
    (Proj.DegreeOneEmbedding.embedding_toSpec (reesAlgebra.grading I) g hg
      (reesAlgebra.grading_one_pow I)).trans
        (ProjectivePresentation.AffineEmbedding.affineProjMap_eq_structureMap
          (R := A) (I := I)).symm
  let e : affineProj I ≅ B.Y := (affineProjBlowupDatum I).comparisonIso B
  have he : e.inv ≫ affineProjMap I = B.map :=
    BlowupDatum.comparisonIso_inv_map (affineProjBlowupDatum I) B
  refine ⟨e.inv ≫ j₀, inferInstance, ?_⟩
  rw [Category.assoc, hj₀]
  exact he

/-- Positive original structure cohomology vanishes on the actual
two-generated affine blowup, with no normality or flatness premise. -/
private theorem twoGeneratedBlowup_structureCohomology
    (A : Type u) [CommRing A] (I : Ideal A) (B : BlowupDatum (affineCenter A I))
    (a b : I) (hI : Ideal.span {(a : A), (b : A)} = I) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf B.Y (SheafOfModules.unit B.Y.ringCatSheaf)) q) := by
  obtain ⟨j, hj, _⟩ := exists_closedLine_twoGeneratedBlowup A I B a b hI
  let : IsClosedImmersion j := hj
  exact subsingleton_structureCohomology_of_closedLine A (ULift.{u} (Fin 2))
    Equiv.ulift j q hq

/-- The literal local-spectrum pullback away from the original closed
point is the original unit-centre blowup isomorphism. -/
private theorem pointBlowup_localProjection_isIso_of_ne
    (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) (y : X) (hy : y ≠ x) :
    IsIso (pullback.snd (blowupDatum (X.fromSpecResidueField x).ker).map
      (X.fromSpecStalk y)) := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let B := blowupDatum (X.fromSpecResidueField x).ker
  have hs : ((X.fromSpecResidueField x).ker.support : Set X) = {x} := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
  apply B.pullback_snd_isIso_of_comap_eq_top (X.fromSpecStalk y)
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext z
  change (X.fromSpecStalk y) z ∈ ((X.fromSpecResidueField x).ker.support : Set X) ↔ False
  rw [hs, Set.mem_singleton_iff]
  constructor
  · intro he
    have hz : (X.fromSpecStalk y) z ⤳ y := by
      have hm : (X.fromSpecStalk y) z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hm
      exact hm
    rw [he] at hz
    exact hx.not_specializes (Set.mem_singleton x) hy hz
  · exact False.elim

/-- Every positive higher direct image of the original structure module
of an actual regular closed-point blowup is zero. -/
public theorem isZero_higherDirectImage_structure_of_regular_point
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : RegularStalks X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward
      (blowupDatum (X.fromSpecResidueField x).ker).map).rightDerived q).obj
        (SheafOfModules.unit
          (blowupDatum (X.fromSpecResidueField x).ker).Y.ringCatSheaf)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let M : B.Y.Modules := SheafOfModules.unit B.Y.ringCatSheaf
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : M.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit B.Y
  apply (Scheme.Modules.isZero_iff_stalks _).mpr
  intro y
  let Q := pullback B.map (X.fromSpecStalk y)
  let a := pullback.fst B.map (X.fromSpecStalk y)
  let N : Q.Modules := (Scheme.Modules.pullback a).obj M
  have hQ : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf Q (SheafOfModules.unit Q.ringCatSheaf)) (n + 1)) := by
    by_cases hy : y = x
    · subst y
      let A := X.presheaf.stalk x
      let : IsRegularLocalRing A := hX x
      let I := IsLocalRing.maximalIdeal A
      let aa : I := ⟨Blowup.RegularPoint.firstParameter A hd,
        (Blowup.RegularPoint.parameters_spec A hd).1⟩
      let bb : I := ⟨Blowup.RegularPoint.secondParameter A hd,
        (Blowup.RegularPoint.parameters_spec A hd).2.1⟩
      have hI : Ideal.span {(aa : A), (bb : A)} = I :=
        (Blowup.RegularPoint.parameters_spec A hd).2.2.1
      have hB := twoGeneratedBlowup_structureCohomology A I
        (blowupDatum (affineCenter A I)) aa bb hI (n + 1) (Nat.zero_lt_succ n)
      let e := Blowup.RegularPoint.stalkBlowupIso X x hx
      have hinj := (moduleCohomologyMapAlong_bijective e.hom
        (Scheme.Hom.structureModuleMap e.hom) (n + 1)).1
      exact ⟨fun u v => hinj (@Subsingleton.elim _ hB _ _)⟩
    · let : IsIso (pullback.snd B.map (X.fromSpecStalk y)) :=
        pointBlowup_localProjection_isIso_of_ne X x hx y hy
      let : IsAffine Q := isAffine_of_isAffineHom (pullback.snd B.map (X.fromSpecStalk y))
      let : (SheafOfModules.unit Q.ringCatSheaf).IsQuasicoherent :=
        Scheme.Modules.isQuasicoherent_unit Q
      exact subsingleton_moduleAddSheafH_of_isAffine (X := Q)
        (SheafOfModules.unit Q.ringCatSheaf) n
  have hN : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Q N) (n + 1)) :=
    moduleCohomology_subsingleton_of_iso (Scheme.Modules.pullbackUnitIso a).symm (n + 1) hQ
  let E :
      (Scheme.Modules.moduleStalk X y).obj
          (((Scheme.Modules.pushforward B.map).rightDerived (n + 1)).obj M) ≃
        Sheaf.H.{u + 1} (moduleAddSheaf Q N) (n + 1) :=
    (moduleHigherDirectImageStalkLinearEquiv B.map M y (n + 1)).toEquiv
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  change Subsingleton ((Scheme.Modules.moduleStalk X y).obj
    (((Scheme.Modules.pushforward B.map).rightDerived (n + 1)).obj M))
  exact ⟨fun u v => E.injective (@Subsingleton.elim _ hN _ _)⟩

/-- For an integral regular original source, the ordinary structural unit
of the same actual point blowup is the proper-birational-normal unit. -/
public theorem isIso_structureModuleMap_of_regular_point
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (hX : RegularStalks X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2) :
    IsIso (Scheme.Hom.structureModuleMap
      (blowupDatum (X.fromSpecResidueField x).ker).map) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let c : PointBlowupChain B.map := by
    simpa only [Category.id_comp] using
      (PointBlowupChain.cons x hx hd (𝟙 B.Y) (PointBlowupChain.refl B.Y))
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsIntegral B.Y := c.isIntegral inferInstance
  let : IsDominant B.map := c.isDominant inferInstance
  have hff := c.functionFieldMap_isIso inferInstance
  have hnormal : NormalStalks X := by
    intro y
    let : IsRegularLocalRing (X.presheaf.stalk y) := hX y
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  exact Scheme.Modules.isIso_unitToPushforwardObjUnit_of_isProper_birational
    B.map hnormal hff

end AlgebraicGeometry.Scheme.Cohomology
