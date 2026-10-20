/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.SpecialFiber
public import Aglib.AlgebraicGeometry.Curves.Nodal.TwoGon.Intersections
public import Aglib.AlgebraicGeometry.Limits.PullbackTransport

/-!
# Actual closed components and their scheme-theoretic intersections

Source: frozen R5 `LocalModels/Incidence/Intersections.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
open Scheme.TwoGon
open Scheme.Hom.ActualSpecialFiber
universe u
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- The actual reduced component chosen by the original left/right test. -/
def twoGonComponentScheme (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : Scheme.{u} :=
  if v.val = twoGonLeftComponent π e then
    twoGonLeftComponentScheme π e else twoGonRightComponentScheme π e

/-- The selected component inclusion retains the original closed-image arrow. -/
def twoGonComponentInclusion (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : twoGonComponentScheme π e v ⟶ obj π :=
  if h : v.val = twoGonLeftComponent π e then
    eqToHom (by simp only [twoGonComponentScheme, ite_eq_left h]) ≫
      (twoGonLeftComponentMap π e).imageι
  else
    eqToHom (by simp only [twoGonComponentScheme, ite_eq_right h]) ≫
      (twoGonRightComponentMap π e).imageι

/-- The inclusion of the selected actual two-gon component is a closed immersion. -/
instance twoGonComponentInclusion_closed (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) :
    IsClosedImmersion (twoGonComponentInclusion π e v) := by
  classical
  unfold twoGonComponentInclusion
  split_ifs <;> infer_instance

/-- The selected actual two-gon component scheme is reduced. -/
instance twoGonComponentScheme_reduced (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : IsReduced (twoGonComponentScheme π e v) := by
  classical
  unfold twoGonComponentScheme
  split <;> infer_instance

/-- Both selected closed images are actual integral component schemes. -/
instance twoGonComponentScheme_integral (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : IsIntegral (twoGonComponentScheme π e v) := by
  classical
  unfold twoGonComponentScheme
  split
  · exact IsIntegral.of_isIso (twoGonLeftComponentMap π e).toImage
  · exact IsIntegral.of_isIso (twoGonRightComponentMap π e).toImage

/-- The selected actual two-gon component identified with the projective line over the residue
field. -/
def twoGonComponentSchemeIsoP1 (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) :
    twoGonComponentScheme π e v ≅ Scheme.ProjectiveLine.projectiveP1 (IsLocalRing.ResidueField
      R) := by
  classical
  unfold twoGonComponentScheme
  split
  · exact twoGonLeftComponentSchemeIsoP1 π e
  · exact twoGonRightComponentSchemeIsoP1 π e

/-- This is exhaustive on the actual irreducible-component subtype. -/
theorem twoGonComponentInclusion_range (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) :
    Set.range (twoGonComponentInclusion π e v) = v.val := by
  classical
  unfold twoGonComponentInclusion
  split_ifs with h
  · let a : twoGonComponentScheme π e v ⟶ twoGonLeftComponentScheme π e :=
      eqToHom (by simp only [twoGonComponentScheme, ite_eq_left h])
    change Set.range ((twoGonLeftComponentMap π e).imageι ∘ a) = v.val
    exact (a.homeomorph.surjective.range_comp _).trans
      ((twoGonLeftComponentScheme_range π e).trans h.symm)
  · let a : twoGonComponentScheme π e v ⟶ twoGonRightComponentScheme π e :=
      eqToHom (by simp only [twoGonComponentScheme, ite_eq_right h])
    change Set.range ((twoGonRightComponentMap π e).imageι ∘ a) = v.val
    have hv := (Set.ext_iff.mp (twoGon_components_eq π e) v.val).mp v.property
    have h' := Set.mem_singleton_iff.mp ((Set.mem_insert_iff.mp hv).resolve_left h)
    exact (a.homeomorph.surjective.range_comp _).trans
      ((twoGonRightComponentScheme_range π e).trans h'.symm)

/-- The normal-source branch set on the actual selected component. Its points
lie above the intersection of the two distinct special-fibre components. -/
def twoGonComponentBranches (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : Set (normalized (IsLocalRing.ResidueField R)) :=
  if v.val = twoGonLeftComponent π e then
    {z | z ∈ Set.range (leftComponent (IsLocalRing.ResidueField R)) ∧
      twoGonNormalization π e z ∈ twoGonLeftComponent π e ∩ twoGonRightComponent π e}
  else
    {z | z ∈ Set.range (rightComponent (IsLocalRing.ResidueField R)) ∧
      twoGonNormalization π e z ∈ twoGonLeftComponent π e ∩ twoGonRightComponent π e}

/-- The numeric branch field is derived for every actual component. -/
theorem twoGonComponentBranches_card (e : TwoGonIso π)
    (v : irreducibleComponents (obj π)) : (twoGonComponentBranches π e v).ncard = 2 := by
  unfold twoGonComponentBranches
  split
  · exact twoGon_left_branchSet_card π e
  · exact twoGon_right_branchSet_card π e

/-- A branch really lies over its actual component, including in the right-hand case. -/
theorem twoGonComponentBranches_over (e : TwoGonIso π)
    (v : irreducibleComponents (obj π))
    {z : normalized (IsLocalRing.ResidueField R)}
    (hz : z ∈ twoGonComponentBranches π e v) : twoGonNormalization π e z ∈ v.val := by
  unfold twoGonComponentBranches at hz
  split_ifs at hz with h
  · rw [h]
    exact hz.2.1
  · have hv := (Set.ext_iff.mp (twoGon_components_eq π e) v.val).mp v.property
    rcases Set.mem_insert_iff.mp hv with hl | hr
    · exact (h hl).elim
    · rw [Set.mem_singleton_iff.mp hr]
      exact hz.2.2

/-- The actual one-gon special fibre is not a projective line; the normalization
being P1 never makes the nodal component smooth rational. -/
theorem oneGon_not_isoP1 (e : OneGonIso π) :
    ¬ Nonempty ((obj π) ≅
      Scheme.ProjectiveLine.projectiveP1 (IsLocalRing.ResidueField R)) := by
  rintro ⟨f⟩
  exact Scheme.PinchedLine.pinchedGluing_not_iso_projectiveP1 _
    ⟨((Over.forget _).mapIso e).symm ≪≫ f⟩

/-- The intersection of the two parametrized components in the actual residue fibre. -/
abbrev twoGonParameterIntersection (e : TwoGonIso π) : Scheme.{u} :=
  pullback (twoGonLeftComponentMap π e) (twoGonRightComponentMap π e)

/-- The scheme-theoretic intersection of the two closed component images in the residue fibre. -/
abbrev twoGonFibreIntersection (e : TwoGonIso π) : Scheme.{u} :=
  pullback (twoGonLeftComponentMap π e).imageι (twoGonRightComponentMap π e).imageι

/-- The map from the parametrized intersection to the intersection of the closed component
images. -/
def twoGonParameterToClosedIntersection (e : TwoGonIso π) :
    twoGonParameterIntersection π e ⟶ twoGonFibreIntersection π e :=
  pullback.map (twoGonLeftComponentMap π e) (twoGonRightComponentMap π e)
    (twoGonLeftComponentMap π e).imageι (twoGonRightComponentMap π e).imageι
    (twoGonLeftComponentMap π e).toImage (twoGonRightComponentMap π e).toImage (𝟙 _)
    (by simp) (by simp)

/-- Passing to the closed component images preserves the parametrized intersection up to
isomorphism. -/
instance twoGonParameterToClosedIntersection_isIso (e : TwoGonIso π) :
    IsIso (twoGonParameterToClosedIntersection π e) := by
  unfold twoGonParameterToClosedIntersection
  infer_instance

/-- The residue-field structure map of the intersection of the closed component images. -/
abbrev twoGonFibreIntersectionStructure (e : TwoGonIso π) :
    twoGonFibreIntersection π e ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.fst _ _ ≫ (twoGonLeftComponentMap π e).imageι ≫ (structureMap π)

@[reassoc] theorem twoGonParameterToClosedIntersection_over (e : TwoGonIso π) :
    twoGonParameterToClosedIntersection π e ≫ twoGonFibreIntersectionStructure π e =
      pullback.fst (twoGonLeftComponentMap π e) (twoGonRightComponentMap π e) ≫
        Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R) := by
  simp only [twoGonParameterToClosedIntersection, twoGonFibreIntersectionStructure,
    pullback.map, Category.assoc, pullback.lift_fst_assoc, Scheme.Hom.toImage_imageι_assoc,
    twoGonLeftComponentMap_over]

/-- The isomorphism identifies the actual closed-component fibre product in
π's literal special fibre, conditional only on the whole-fibre classification iso. -/
def twoGonFibreIntersectionIsoTwoPoints (e : TwoGonIso π) :
    twoGonFibreIntersection π e ≅
      Spec (.of (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  (asIso (twoGonParameterToClosedIntersection π e)).symm ≪≫
    pullbackCompMonoIso
      (Scheme.TwoGon.leftTargetMap (IsLocalRing.ResidueField R))
      (Scheme.TwoGon.rightTargetMap (IsLocalRing.ResidueField R)) e.inv.left ≪≫
    Scheme.TwoGon.globalIntersectionIsoTwoPoints (IsLocalRing.ResidueField R)

theorem twoGonFibreIntersectionIsoTwoPoints_over (e : TwoGonIso π) :
    (twoGonFibreIntersectionIsoTwoPoints π e).hom ≫
      Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      twoGonFibreIntersectionStructure π e := by
  simp only [twoGonFibreIntersectionIsoTwoPoints, Iso.trans_hom, Category.assoc,
    Scheme.TwoGon.globalIntersectionIsoTwoPoints_over,
    pullbackCompMonoIso_hom_fst_assoc]
  change (asIso (twoGonParameterToClosedIntersection π e)).inv ≫
    (pullback.fst (twoGonLeftComponentMap π e) (twoGonRightComponentMap π e) ≫
      Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R)) = _
  rw [← twoGonParameterToClosedIntersection_over π e]
  simp

/-- The closed-component intersection identified over the residue field with two rational points. -/
def twoGonFibreIntersectionOverIsoTwoPoints (e : TwoGonIso π) :
    Over.mk (twoGonFibreIntersectionStructure π e) ≅
      Over.mk (Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  Over.isoMk (twoGonFibreIntersectionIsoTwoPoints π e)
    (twoGonFibreIntersectionIsoTwoPoints_over π e)

/-- The same reduced closed component schemes, now intersected in the actual
regular surface Y rather than just its special fibre. -/
abbrev twoGonSurfaceIntersection (e : TwoGonIso π) : Scheme.{u} :=
  pullback ((twoGonLeftComponentMap π e).imageι ≫ (projection π))
    ((twoGonRightComponentMap π e).imageι ≫ (projection π))

/-- The residue-field structure map of the two-component intersection in the ambient scheme. -/
abbrev twoGonSurfaceIntersectionStructure (e : TwoGonIso π) :
    twoGonSurfaceIntersection π e ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.fst _ _ ≫ (twoGonLeftComponentMap π e).imageι ≫ (structureMap π)

/-- The intersection in the ambient scheme identified with the spectrum of the product of two
residue fields. -/
def twoGonSurfaceIntersectionIsoTwoPoints (e : TwoGonIso π) :
    twoGonSurfaceIntersection π e ≅
      Spec (.of (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  pullbackCompMonoIso (twoGonLeftComponentMap π e).imageι
    (twoGonRightComponentMap π e).imageι (projection π) ≪≫
    twoGonFibreIntersectionIsoTwoPoints π e

theorem twoGonSurfaceIntersectionIsoTwoPoints_over (e : TwoGonIso π) :
    (twoGonSurfaceIntersectionIsoTwoPoints π e).hom ≫
      Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      twoGonSurfaceIntersectionStructure π e := by
  simp only [twoGonSurfaceIntersectionIsoTwoPoints, Iso.trans_hom, Category.assoc,
    twoGonFibreIntersectionIsoTwoPoints_over, twoGonFibreIntersectionStructure,
    pullbackCompMonoIso_hom_fst_assoc, twoGonSurfaceIntersectionStructure]

/-- The ambient two-component intersection identified with two points over the original residue
field. -/
def twoGonSurfaceIntersectionOverIsoTwoPoints (e : TwoGonIso π) :
    Over.mk (twoGonSurfaceIntersectionStructure π e) ≅
      Over.mk (Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  Over.isoMk (twoGonSurfaceIntersectionIsoTwoPoints π e)
    (twoGonSurfaceIntersectionIsoTwoPoints_over π e)

/-- The intersection of the two actual surface components is reduced. -/
instance twoGonSurfaceIntersection_reduced (e : TwoGonIso π) :
    IsReduced (twoGonSurfaceIntersection π e) :=
  isReduced_of_isOpenImmersion (twoGonSurfaceIntersectionIsoTwoPoints π e).hom

/-- The intersection of the two actual surface components is finite over the residue field. -/
instance twoGonSurfaceIntersection_finite (e : TwoGonIso π) :
    IsFinite (twoGonSurfaceIntersectionStructure π e) := by
  rw [← twoGonSurfaceIntersectionIsoTwoPoints_over]
  have : IsFinite (Spec.algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) := by
    unfold Spec.algebraMap
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
