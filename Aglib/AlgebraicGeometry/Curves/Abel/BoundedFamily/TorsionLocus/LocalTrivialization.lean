/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.Fibres
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.Restricted
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.GlobalFrame
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Trivialization

/-! # Actual local power trivializations over the reduced torsion locus

Original q=0 Grauert on reduced Noetherian affine charts lifts a nonzero
fibre section to an actual global section. The actual fibre bundle is trivial;
proper geometrically integral constants make that section nowhere vanishing
on the fibre. The proper image of its closed zero set then allows shrinking
the base, giving an actual unit isomorphism of the actual power coefficient.

No vanishing in positive cohomological degrees is assumed or asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hX : Properties X)

include hX

/-- The actual intrinsic point-fibre coefficient is trivial on the closed
support, not just the coefficient on an isomorphic chosen curve. -/
theorem powerLineBundle_pointFibre_trivial_of_pos (g n : ℕ)
    (y : (parameter X.hom g).left)
    (hy : 0 < powerH0Dimension X.hom o ho g n y) :
    Nonempty (((Modules.pullback
      ((pullback.snd X.hom (parameter X.hom g).hom).fiberι y)).obj
        (powerLineBundle X.hom o ho g n).val) ≅
          SheafOfModules.unit
            ((pullback.snd X.hom (parameter X.hom g).hom).fiber y).ringCatSheaf) := by
  let t := (parameter X.hom g).hom
  let a := (parameter X.hom g).left.fromSpecResidueField y
  let f := pullback.snd X.hom t
  let M := (powerLineBundle X.hom o ho g n).val
  let h := Hom.familyMap_isPullback X.hom t (a ≫ t) a rfl
  let e := h.isoPullback
  let C : (Modules.pullback e.hom).obj ((Modules.pullback (f.fiberι y)).obj M) ≅
      (powerPointFibreLineBundle X o ho g n y).val :=
    (Modules.pullbackComp e.hom (f.fiberι y)).app M ≪≫
      (Modules.pullbackCongr h.isoPullback_hom_fst).app M
  obtain ⟨d⟩ := (powerH0Dimension_pos_iff_fibre_trivial X o ho hX g n y).mp hy
  let : (Modules.pullback e.hom).IsEquivalence :=
    Modules.pullback_isEquivalence_of_isIso e.hom
  exact ⟨(Modules.pullback e.hom).preimageIso
    (C ≪≫ d ≪≫ (Modules.pullbackUnitIso e.hom).symm)⟩

/-- The actual restricted family's intrinsic fibre is trivial through the
native closed-immersion fibre map and coefficient comparison. -/
theorem powerLocusLineBundle_pointFibre_trivial (g n : ℕ)
    (z : powerNonvanishingLocus X.hom o ho g n) :
    Nonempty (((Modules.pullback ((powerLocusProjection X o ho g n).fiberι z)).obj
      (powerLocusLineBundle X o ho g n).val) ≅
        SheafOfModules.unit ((powerLocusProjection X o ho g n).fiber z).ringCatSheaf) := by
  let i := powerNonvanishingι X.hom o ho g n
  let h := Hom.familyMap_isPullback X.hom (parameter X.hom g).hom
    (i ≫ (parameter X.hom g).hom) i rfl
  let : IsIso (i.residueFieldMap z) := residueFieldMap_isIso_of_surjectiveOnStalks i z
  let e := modulePointFiberBaseChangeIso h z
  let C := modulePointFiberBaseChangeCoefficientIso h z (powerLineBundle X.hom o ho g n).val
  obtain ⟨d⟩ := powerLineBundle_pointFibre_trivial_of_pos X o ho hX g n (i z)
    (powerH0Dimension_pos_on_locus X.hom o ho g n z)
  exact ⟨C.symm ≪≫ (Modules.pullback e.hom).mapIso d ≪≫ Modules.pullbackUnitIso e.hom⟩

section AffineChart

variable {R : Type u} [CommRing R] (g n : ℕ)
  (j : Spec (.of R) ⟶ powerNonvanishingLocus X.hom o ho g n) [IsOpenImmersion j]

/-- Triviality on the literal ordinary residue-field fibre used by affine
Grauert, through its original affine-coordinate coefficient isomorphism. -/
theorem powerLocusLineBundle_affineFibre_trivial (r : PrimeSpectrum R) :
    let f := pullback.snd (powerLocusProjection X o ho g n) j
    let a := pullback.fst (powerLocusProjection X o ho g n) j
    let σ := Spec.map (CommRingCat.ofHom (algebraMap R r.asIdeal.ResidueField))
    Nonempty (((Modules.pullback (pullback.fst f σ)).obj
      ((Modules.pullback a).obj (powerLocusLineBundle X o ho g n).val)) ≅
        SheafOfModules.unit (pullback f σ).ringCatSheaf) := by
  let e := modulePointFiberAffineIso (powerLocusProjection X o ho g n) j r
  let C := modulePointFiberAffineCoefficientIso (powerLocusProjection X o ho g n) j r
    (powerLocusLineBundle X o ho g n).val
  obtain ⟨d⟩ := powerLocusLineBundle_pointFibre_trivial X o ho hX g n (j r)
  exact ⟨C.symm ≪≫ (Modules.pullback e.hom).mapIso d ≪≫ Modules.pullbackUnitIso e.hom⟩

/-- Around every point in every actual affine chart of the reduced closed
locus, the actual pulled power bundle has an actual unit isomorphism above
an open neighbourhood. The section is supplied by native q=0 Grauert. -/
theorem exists_powerLocusLineBundle_trivial_on_affine_base_open (r : PrimeSpectrum R) :
    let f := pullback.snd (powerLocusProjection X o ho g n) j
    let M := (Modules.pullback (pullback.fst (powerLocusProjection X o ho g n) j)).obj
      (powerLocusLineBundle X o ho g n).val
    ∃ U : (Spec (.of R)).Opens, r ∈ U ∧
      Nonempty (((Modules.pullback (f ⁻¹ᵁ U).ι).obj M) ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let f := pullback.snd (powerLocusProjection X o ho g n) j
  let L := pullbackLineBundle (pullback.fst (powerLocusProjection X o ho g n) j)
    (powerLocusLineBundle X o ho g n)
  let K := r.asIdeal.ResidueField
  let σ : R →+* K := algebraMap R K
  let a := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCohomologyModuleOfHom _ β ((Modules.pullback a).obj L.val) 0
  have hd : 0 < Module.finrank K (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ)))
        ((Modules.pullback a).obj L.val)) 0) := by
    change 0 < moduleFiberCohomologyDimension f L.val 0 r
    have hdim : moduleFiberCohomologyDimension f L.val 0 r = 1 :=
      powerLocusLineBundle_affineFiberH0Dimension X o ho hX g n j r
    exact hdim.symm ▸ Nat.zero_lt_one
  let : Nontrivial (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ)))
        ((Modules.pullback a).obj L.val)) 0) := Module.nontrivial_of_finrank_pos hd
  let : IsIso (moduleCohomologyBaseChangeMap f σ L.val 0) :=
    powerLocusLineBundle_affineH0BaseChange_isIso X o ho hX g n j σ
  obtain ⟨s, hs⟩ := exists_section_pullback_ne_zero_of_baseChange_isIso f σ L.val
  let Z : FScheme K := Over.mk q
  let : GeometricallyIntegral X.hom :=
    curveProperties_geometricallyIntegral smoothFieldNormality normalComponentsOpen hX
  let : GeometricallyIntegral (powerLocusProjection X o ho g n) := by
    change GeometricallyIntegral (pullback.snd X.hom _)
    infer_instance
  let : GeometricallyIntegral f := by
    dsimp only [f]
    infer_instance
  let : GeometricallyIntegral Z.hom := by
    change GeometricallyIntegral q
    dsimp only [q]
    infer_instance
  let : IsProper Z.hom := by
    change IsProper q
    dsimp only [q]
    infer_instance
  obtain ⟨d⟩ := powerLocusLineBundle_affineFibre_trivial X o ho hX g n j r
  have hn : nonvanishingOpen (pullbackLineBundle a L) (pullbackSection a L.val s) = ⊤ :=
    nonvanishingOpen_eq_top_of_field_constants (constants Z)
      (constants_bijective_of_proper_geometricallyIntegral Z).2
      (pullbackLineBundle a L) d _ hs
  have hr : Set.range (Spec.map (CommRingCat.ofHom σ)) = {r} := by
    let e := Spec.map (Scheme.Spec.residueFieldIso (.of R) r).inv
    have he := congrArg
      (fun t : Spec ((Spec (.of R)).residueField r) ⟶ Spec (.of R) => Set.range t)
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) r)
    change Set.range ((Spec.map (CommRingCat.ofHom σ)) ∘ e) = _ at he
    rw [e.surjective.range_comp, Scheme.range_fromSpecResidueField] at he
    exact he
  have ha : Set.range a = f ⁻¹' {r} := by
    rw [Scheme.Pullback.range_fst, hr]
  apply exists_trivial_on_base_open_of_nonvanishing_on_fibre f L s r
  intro x hx
  have hx' : x ∈ Set.range a := by
    rw [ha]
    exact hx
  obtain ⟨z, rfl⟩ := hx'
  have hz : z ∈ nonvanishingOpen (pullbackLineBundle a L) (pullbackSection a L.val s) := by
    rw [hn]
    trivial
  rw [nonvanishingOpen_pullback] at hz
  exact hz

end AffineChart

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
