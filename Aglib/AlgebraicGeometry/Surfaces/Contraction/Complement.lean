/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.ProjectiveImage
public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Colimit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Original mixed coordinates on the exceptional complement

The actual common Cartier inclusion is invertible off the original exceptional
curve. Its original pullback and ample-power comparisons give actual frames
in which the prescribed mixed coordinates recover the original projective
ratios. New diagonal preimages retain the original old coordinate preimages.
All original section maps, structural rings and coordinate indices are kept.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent MvPolynomial

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}}
  (p : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion p]
  {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  (eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)) (d : ℕ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackSection_comp {Z Y T : Scheme.{u}} (g : T ⟶ Y) (h : Y ⟶ Z)
    {M : Z.Modules} (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    FromSections.pullbackSection g (FromSections.pullbackSection h s) ≫
      (Scheme.Modules.pullbackComp g h).hom.app M =
        FromSections.pullbackSection (g ≫ h) s := by
  have hu : (pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map (pullbackUnitIso h).inv ≫
      (Scheme.Modules.pullbackComp g h).hom.app (SheafOfModules.unit Z.ringCatSheaf) =
        (pullbackUnitIso (g ≫ h)).inv := by
    apply (cancel_mono (pullbackUnitIso (g ≫ h)).hom).mp
    simp only [Category.assoc]
    rw [pullbackUnitIso_comp]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    have hmap : (Scheme.Modules.pullback g).map
        (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) =
        𝟙 ((Scheme.Modules.pullback g).obj
          (SheafOfModules.unit Y.ringCatSheaf)) :=
      (Scheme.Modules.pullback g).map_id _
    exact (congrArg (fun f => (pullbackUnitIso g).inv ≫ f ≫
      (pullbackUnitIso g).hom) hmap).trans
        (by simpa only [Category.id_comp] using (pullbackUnitIso g).inv_hom_id)
  unfold FromSections.pullbackSection
  rw [Functor.map_comp]
  calc
    _ = (pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map (pullbackUnitIso h).inv ≫
        (Scheme.Modules.pullbackComp g h).hom.app
          (SheafOfModules.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.pullback (g ≫ h)).map s := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f => (pullbackUnitIso g).inv ≫
          (Scheme.Modules.pullback g).map (pullbackUnitIso h).inv ≫ f)
          ((Scheme.Modules.pullbackComp g h).hom.naturality s)
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ (Scheme.Modules.pullback (g ≫ h)).map s) hu

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the original complement, the actual common inclusion and given ample
comparison identify L_n with the original pulled projective O(n). -/
def offExceptionalProjectivePowerIso {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (n : ℕ) :
    (Scheme.Modules.pullback g).obj
        (cartierPowerTwist i hI H n (n * d)).val ≅
      (Scheme.Modules.pullback (g ≫ p)).obj
        (twistingSheaf A ι (n : ℤ)) := by
  let j := g
  let _ : IsIso ((Scheme.Modules.pullback j).map (cartierPowerInclusion i hI H n (n * d))) :=
    cartierPowerInclusion_pullback_isIso_of_disjoint i hI H g hg n (n * d)
  exact (asIso ((Scheme.Modules.pullback j).map
      (cartierPowerInclusion i hI H n (n * d)))).symm ≪≫
    (Scheme.Modules.pullback j).mapIso (projectivePowerIso p H eP n) ≪≫
      (Scheme.Modules.pullbackComp j p).app (twistingSheaf A ι (n : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This actual comparison cancels the original common Cartier multiplier and
recovers each original mixed homogeneous section, with its original pullback maps. -/
theorem mixedCartierSection_offExceptional {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (n : ℕ) (hn : 1 ≤ n) (a b : ι) :
    FromSections.pullbackSection g
        (mixedCartierSection p i hI H eP d n hn a b) ≫
      (offExceptionalProjectivePowerIso p i hI H eP d g hg n).hom =
    FromSections.pullbackSection (g ≫ p)
      (mixedTwistSection (A := A) n hn a b) := by
  let j := g
  let T := Scheme.Modules.pullback j
  let c := cartierPowerInclusion i hI H n (n * d)
  let _ : IsIso (T.map c) := cartierPowerInclusion_pullback_isIso_of_disjoint i hI H g hg n (n * d)
  change (pullbackUnitIso j).inv ≫
      T.map ((pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map
        (mixedTwistSection (A := A) n hn a b) ≫ (projectivePowerIso p H eP n).inv ≫ c) ≫
      inv (T.map c) ≫ T.map (projectivePowerIso p H eP n).hom ≫
      (Scheme.Modules.pullbackComp j p).hom.app (twistingSheaf A ι (n : ℤ)) = _
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have hcancel : T.map (projectivePowerIso p H eP n).inv ≫
      T.map (projectivePowerIso p H eP n).hom = 𝟙 _ :=
    (T.mapIso (projectivePowerIso p H eP n)).inv_hom_id
  calc
    _ = (pullbackUnitIso j).inv ≫ T.map (pullbackUnitIso p).inv ≫
        T.map ((Scheme.Modules.pullback p).map (mixedTwistSection (A := A) n hn a b)) ≫
        (Scheme.Modules.pullbackComp j p).hom.app (twistingSheaf A ι (n : ℤ)) := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun f => (pullbackUnitIso j).inv ≫ T.map (pullbackUnitIso p).inv ≫
          T.map ((Scheme.Modules.pullback p).map (mixedTwistSection (A := A) n hn a b)) ≫
          f ≫ (Scheme.Modules.pullbackComp j p).hom.app (twistingSheaf A ι (n : ℤ))) hcancel
    _ = _ := by
      simpa only [FromSections.pullbackSection, Functor.map_comp, Category.assoc] using
        pullbackSection_comp j p (mixedTwistSection (A := A) n hn a b)


omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual off-E Cartier comparison, in the original pulled projective cocycle. -/
def offExceptionalCocycleIso {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (n : ℕ) :
    (Scheme.Modules.pullback g).obj
        (cartierPowerTwist i hI H n (n * d)).val ≅
      (FromSections.pullbackCocycle (g ≫ p)
        ((coordinateUnitCocycle A ι).zpow (-(n : ℤ)))).sheaf :=
  offExceptionalProjectivePowerIso p i hI H eP d g hg n ≪≫
    FromSections.pullbackCocycleIso (g ≫ p)
      ((coordinateUnitCocycle A ι).zpow (-(n : ℤ))) (iSup_coordinateOpen_eq_top A ι)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original mixed coordinate has its original projective ratio as coefficient
in this actual off-E frame. -/
theorem mixedCartierSection_offExceptional_chart {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (n : ℕ) (hn : 1 ≤ n) (a b c : ι) :
    (FromSections.pullbackCocycle (g ≫ p)
        ((coordinateUnitCocycle A ι).zpow (-(n : ℤ)))).localSectionsEquiv c le_rfl
      ((offExceptionalCocycleIso p i hI H eP d g hg n).hom.val.app
        (op ((g ≫ p) ⁻¹ᵁ coordinateOpen A ι c))
        ((FromSections.pullbackSection g
          (mixedCartierSection p i hI H eP d n hn a b)).val.app
            (op ((g ≫ p) ⁻¹ᵁ coordinateOpen A ι c))
            (1 : Γ(Y,
              (g ≫ p) ⁻¹ᵁ coordinateOpen A ι c)))) =
      ((g ≫ p).app (coordinateOpen A ι c)).hom
        (homogeneousChartSection A ι n (mixedPolynomial (A := A) n hn a b) c) := by
  let T := Y
  let j := g
  let q := j ≫ p
  let C := (coordinateUnitCocycle A ι).zpow (-(n : ℤ))
  let O := q ⁻¹ᵁ coordinateOpen A ι c
  let s := mixedTwistSection (A := A) n hn a b
  have hcomp : FromSections.pullbackSection j
      (mixedCartierSection p i hI H eP d n hn a b) ≫
        (offExceptionalCocycleIso p i hI H eP d g hg n).hom =
      FromSections.pullbackSection q s ≫
        (FromSections.pullbackCocycleIso q C (iSup_coordinateOpen_eq_top A ι)).hom := by
    simpa only [offExceptionalCocycleIso, Iso.trans_hom, Category.assoc] using
      congrArg (fun f => f ≫
        (FromSections.pullbackCocycleIso q C (iSup_coordinateOpen_eq_top A ι)).hom)
          (mixedCartierSection_offExceptional p i hI H eP d g hg n hn a b)
  have hvalue := congrArg (fun f : 𝟙_ T.Modules ⟶ (FromSections.pullbackCocycle q C).sheaf =>
    f.val.app (op O) (1 : Γ(T, O))) hcomp
  have hsource : C.localSectionsEquiv c le_rfl
      (s.val.app (op (coordinateOpen A ι c)) (1 : Γ(ProjectiveSpace A ι, coordinateOpen A ι c))) =
        homogeneousChartSection A ι n (mixedPolynomial (A := A) n hn a b) c := by
    change twistingSectionsEquiv A ι (n : ℤ) c le_rfl
      (s.val.app (op (coordinateOpen A ι c)) (1 : Γ(ProjectiveSpace A ι, coordinateOpen A ι c))) = _
    have hs : s.val.app (op (coordinateOpen A ι c))
        (1 : Γ(ProjectiveSpace A ι, coordinateOpen A ι c)) =
        (twistingSheaf A ι (n : ℤ)).val.map (homOfLE le_top).op
          (homogeneousSection A ι n (mixedPolynomial (A := A) n hn a b)) := by
      exact (unitHomGlobalSectionsEquiv_symm_app (ProjectiveSpace A ι)
        (twistingSheaf A ι (n : ℤ))
        (homogeneousSection A ι n (mixedPolynomial (A := A) n hn a b))
        (coordinateOpen A ι c) 1).trans (one_smul _ _)
    rw [hs]
    exact homogeneousSection_local A ι n (mixedPolynomial (A := A) n hn a b) c
  change (FromSections.pullbackCocycle q C).localSectionsEquiv c le_rfl _ = _
  have happ : q.appLE (coordinateOpen A ι c) O le_rfl =
      q.app (coordinateOpen A ι c) := q.app_eq_appLE.symm
  exact (congrArg ((FromSections.pullbackCocycle q C).localSectionsEquiv c le_rfl) hvalue).trans
    ((FromSections.pullbackCocycleIso_section_coefficient q C
      (iSup_coordinateOpen_eq_top A ι) s c le_rfl).trans
        ((congrArg (q.appLE (coordinateOpen A ι c) O le_rfl).hom hsource).trans
          (congrArg (fun f : Γ(ProjectiveSpace A ι, coordinateOpen A ι c) ⟶ Γ(T, O) =>
            f.hom (homogeneousChartSection A ι n (mixedPolynomial (A := A) n hn a b) c)) happ)))

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-diagonal frames for the original pulled family on an off-E source. -/
def offExceptionalFrames {Y : Scheme.{u}} (g : Y ⟶ X) (hg : ∀ y : Y, g y ∉ Set.range i) :
    FromSections.SectionFrames
      ((Scheme.Modules.pullback g).obj
        (cartierPowerTwist i hI H n (n * d)).val)
      (fun j : F.index => ((Scheme.Modules.pullback g).obj
        (cartierPowerTwist i hI H n (n * d)).val).unitHomEquiv
          (FromSections.pullbackSection g (F.sections j))) := by
  let T := Y
  let j := g
  let q := j ≫ p
  let M := (Scheme.Modules.pullback j).obj (cartierPowerTwist i hI H n (n * d)).val
  let C := FromSections.pullbackCocycle q ((coordinateUnitCocycle A ι).zpow (-(n : ℤ)))
  let e := offExceptionalCocycleIso p i hI H eP d g hg n
  refine {
    K := ι
    U := fun a => q ⁻¹ᵁ coordinateOpen A ι a
    covers := q.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top A ι)
    coordinate := fun a => F.mixedIndex (a, a)
    frame := fun a =>
      (SheafOfModules.overFunctor T.ringCatSheaf (q ⁻¹ᵁ coordinateOpen A ι a)).mapIso e ≪≫
        C.localIso a
    selected := ?_ }
  intro a
  change C.localSectionsEquiv a le_rfl
      (e.hom.val.app (op (q ⁻¹ᵁ coordinateOpen A ι a))
        ((FromSections.pullbackSection j (F.sections (F.mixedIndex (a, a)))).val.app
          (op (q ⁻¹ᵁ coordinateOpen A ι a)) (1 : Γ(T, q ⁻¹ᵁ coordinateOpen A ι a)))) = 1
  rw [F.mixedEq]
  have hpoly : homogeneousChartSection A ι n (mixedPolynomial (A := A) n hn a a) a = 1 := by
    rw [mixedPolynomial_self, homogeneousChartSection_coordinatePower,
      coordinateRatioSection_self, one_pow]
  exact (mixedCartierSection_offExceptional_chart p i hI H eP d g hg n hn a a a).trans
    ((congrArg ((g ≫ p).app (coordinateOpen A ι a)).hom hpoly).trans
      (map_one ((g ≫ p).app (coordinateOpen A ι a)).hom))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- These actual original-diagonal frames compute every prescribed mixed coordinate. -/
theorem offExceptionalFrames_coefficient_mixed {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (a b c : ι) :
    (F.offExceptionalFrames g hg).coefficientOn c le_rfl (F.mixedIndex (a, b)) =
      ((g ≫ p).app (coordinateOpen A ι c)).hom
        (homogeneousChartSection A ι n (mixedPolynomial (A := A) n hn a b) c) := by
  change (FromSections.pullbackCocycle (g ≫ p)
      ((coordinateUnitCocycle A ι).zpow (-(n : ℤ)))).localSectionsEquiv c le_rfl
      ((offExceptionalCocycleIso p i hI H eP d g hg n).hom.val.app
        (op ((g ≫ p) ⁻¹ᵁ coordinateOpen A ι c))
        ((FromSections.pullbackSection g
          (F.sections (F.mixedIndex (a, b)))).val.app
            (op ((g ≫ p) ⁻¹ᵁ coordinateOpen A ι c))
            (1 : Γ(Y,
              (g ≫ p) ⁻¹ᵁ coordinateOpen A ι c)))) = _
  rw [F.mixedEq]
  exact mixedCartierSection_offExceptional_chart p i hI H eP d g hg n hn a b c

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original projective map on X minus E is exactly the map from these actual frames. -/
theorem offExceptional_toProjective_eq {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) :
    g ≫ F.toProjective =
      (F.offExceptionalFrames g hg).map (g ≫ p ≫ toSpec A ι) := by
  let _ : Epi (Sigma.desc F.sections) := F.epiSections
  let _ : Finite F.index := F.finiteIndex
  let j := g
  have h := FromSections.mapOfFiniteFamily_pullback j (p ≫ toSpec A ι)
    (cartierPowerTwist i hI H n (n * d)).val
    (cartierPowerTwist i hI H n (n * d)).property F.sections
  refine h.trans ?_
  apply FromSections.SectionFrames.map_eq_of_iso _ _ (j ≫ p ≫ toSpec A ι) (Iso.refl _)
  intro a O
  simp only [FromSections.generatingSectionsOfFamily_section]
  rfl

end CartierProjectivePresentation


namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original diagonal coordinate on another original chart is the nth power
of the original old-coordinate ratio. -/
theorem offExceptionalFrames_coefficient_diagonal {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (a c : ι) :
    (F.offExceptionalFrames g hg).coefficientOn c le_rfl (F.mixedIndex (a, a)) =
      (((g ≫ p).app (coordinateOpen A ι c)).hom (coordinateRatioSection A ι c a)) ^ n := by
  have h := F.offExceptionalFrames_coefficient_mixed g hg a a c
  rw [mixedPolynomial_self, homogeneousChartSection_coordinatePower, map_pow] at h
  exact h

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On any actual off-E source, the new diagonal preimage is exactly the old coordinate preimage. -/
theorem offExceptional_preimage_diagonal {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : ∀ y : Y, g y ∉ Set.range i) (a : ι) :
    (g ≫ F.toProjective) ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a)) =
      (g ≫ p) ⁻¹ᵁ coordinateOpen A ι a := by
  let G := F.offExceptionalFrames g hg
  let q := g ≫ p
  let b := g ≫ p ≫ toSpec A ι
  have hlocal (c : ι) :
      G.U c ⊓ (G.map b ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a))) =
        G.U c ⊓ q ⁻¹ᵁ coordinateOpen A ι a := by
    calc
      _ = Y.basicOpen (G.coefficientOn c le_rfl (F.mixedIndex (a, a))) :=
        G.map_preimage_coordinateOpen_inf b c (F.mixedIndex (a, a))
      _ = Y.basicOpen ((q.app (coordinateOpen A ι c)).hom
          (coordinateRatioSection A ι c a) ^ n) :=
        congrArg (fun r : Γ(Y, q ⁻¹ᵁ coordinateOpen A ι c) => Y.basicOpen r)
          (F.offExceptionalFrames_coefficient_diagonal g hg a c)
      _ = Y.basicOpen ((q.app (coordinateOpen A ι c)).hom
          (coordinateRatioSection A ι c a)) :=
        Y.basicOpen_pow ((q.app (coordinateOpen A ι c)).hom
          (coordinateRatioSection A ι c a)) (by omega)
      _ = q ⁻¹ᵁ (ProjectiveSpace A ι).basicOpen (coordinateRatioSection A ι c a) :=
        (Scheme.preimage_basicOpen q (coordinateRatioSection A ι c a)).symm
      _ = G.U c ⊓ q ⁻¹ᵁ coordinateOpen A ι a := by
        rw [basicOpen_coordinateRatioSection, Scheme.Hom.preimage_inf]
        rfl
  rw [F.offExceptional_toProjective_eq g hg]
  ext y
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y ∈ iSup G.U by rw [G.covers]; trivial)
  constructor
  · intro hy
    have hp : y ∈ G.U c ⊓ (G.map b ⁻¹ᵁ
        coordinateOpen A F.index (F.mixedIndex (a, a))) := ⟨hc, hy⟩
    rw [hlocal c] at hp
    exact hp.2
  · intro hy
    have hp : y ∈ G.U c ⊓ q ⁻¹ᵁ coordinateOpen A ι a := ⟨hc, hy⟩
    rw [← hlocal c] at hp
    exact hp.2

end CartierProjectivePresentation


omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectiveMap_preimage_of_section_zero {Y : Scheme.{u}}
    (b : Y ⟶ Spec (.of A)) (M : Y.Modules) (hM : IsLocallyRankOne Y M)
    {J : Type u} [Finite J] (s : J → (𝟙_ Y.Modules ⟶ M)) [Epi (Sigma.desc s)]
    (j : J) (hj : s j = 0) :
    FromSections.mapOfFiniteFamily b M hM s ⁻¹ᵁ coordinateOpen A J j = ⊥ := by
  let σ := FromSections.generatingSectionsOfFamily s
  let G := FromSections.framesOfGeneratingSections M hM σ
  change G.map b ⁻¹ᵁ coordinateOpen A J j = ⊥
  have hpre : G.map b ⁻¹ᵁ coordinateOpen A J j = G.nonvanishingOpen j :=
    G.map_preimage_coordinateOpen b j
  refine hpre.trans ?_
  apply iSup_eq_bot.mpr
  intro z
  have hsection : (σ.s j).val (op (G.U z)) = 0 := by
    rw [FromSections.generatingSectionsOfFamily_section, hj]
    rfl
  have hc : G.coefficientOn z le_rfl j = 0 :=
    (congrArg (LocalFrames.coefficient G.U M G.frame z le_rfl) hsection).trans (map_zero _)
  change Y.basicOpen (G.coefficientOn z le_rfl j) = ⊥
  rw [hc, Y.basicOpen_zero]

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual restricted coefficients of every prescribed mixed coordinate are zero. -/
theorem residueCoefficient_mixed (hnd : 1 ≤ n * d) (a b : ι) :
    cartierResidueCoefficient i hI H d eI eH n (F.sections (F.mixedIndex (a, b))) = 0 := by
  let E := ProjectiveSpace k (ULift.{u} (Fin 2))
  let N := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit E.ringCatSheaf)
  let γ := globalFunctionsRingEquiv k (ULift.{u} (Fin 2))
  calc
    _ = cartierResidueCoefficient i hI H d eI eH n
        (mixedCartierSection p i hI H eP d n hn a b) :=
      congrArg (cartierResidueCoefficient i hI H d eI eH n) (F.mixedEq (a, b))
    _ = γ.symm (unitHomGlobalSectionsEquiv X N
        (mixedCartierSection p i hI H eP d n hn a b ≫ cartierResidueMap i hI H d eI eH n)) :=
      cartierResidueCoefficient_eq i hI H d eI eH n _
    _ = γ.symm (unitHomGlobalSectionsEquiv X N 0) :=
      congrArg (fun s : 𝟙_ X.Modules ⟶ N => γ.symm (unitHomGlobalSectionsEquiv X N s))
        (mixedCartierSection_residueMap p i hI H eP d eI eH n hn hnd a b)
    _ = 0 := by
      change γ.symm (0 : Γ(E, ⊤)) = 0
      exact map_zero γ.symm

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original Spec k point has zero original mixed-coordinate maps. -/
theorem residuePointFamily_mixed (hnd : 1 ≤ n * d) (a b : ι) :
    F.residuePointFamily eI eH (F.mixedIndex (a, b)) = 0 := by
  rw [residuePointFamily, F.residueCoefficient_mixed eI eH hnd, map_zero, unitMul_zero]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual residue point misses every new diagonal mixed-coordinate open. -/
theorem residuePoint_preimage_diagonal (hnd : 1 ≤ n * d) (a : ι) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residuePoint eI eH j₀ h₀ ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a)) = ⊥ := by
  let _ : Finite F.index := F.finiteIndex
  let _ : Epi (Sigma.desc (F.residuePointFamily eI eH)) := F.residuePointFamily_epi eI eH j₀ h₀
  exact projectiveMap_preimage_of_section_zero _ _ _ _ _
    (F.residuePointFamily_mixed eI eH hnd a a)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Hence the original preimage of a diagonal chart is genuinely disjoint from E. -/
theorem diagonalSource_disjoint (hnd : 1 ≤ n * d) (a : ι) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    ∀ y : (F.toProjective ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a))).toScheme,
      (F.toProjective ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a))).ι y ∉ Set.range i := by
  intro y hy
  obtain ⟨z, hz⟩ := hy
  have hEz : z ∈ (i ≫ F.toProjective) ⁻¹ᵁ
      coordinateOpen A F.index (F.mixedIndex (a, a)) := by
    change F.toProjective (i z) ∈ coordinateOpen A F.index (F.mixedIndex (a, a))
    rw [hz]
    exact y.property
  rw [F.exceptional_toProjective_eq eI eH j₀ h₀, Scheme.Hom.comp_preimage,
    F.residuePoint_preimage_diagonal eI eH hnd a j₀ h₀, Scheme.Hom.preimage_bot] at hEz
  exact hEz

end CartierProjectivePresentation


namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual proper map to its original kernel image is schematically dominant. -/
theorem toImage_schemeTheoreticallyDominant (r : ℕ) (e : ι ≃ Fin (r + 1)) :
    IsSchemeTheoreticallyDominant F.toImage := by
  let _ : IsProper F.toProjective := F.toProjective_isProper r e
  let _ : IsProper F.toImage := F.toImage_isProper r e
  let Y := ProjectiveSpace A F.index
  let U : Y.affineOpens → F.image.affineOpens :=
    fun V => ⟨F.imageInclusion ⁻¹ᵁ V.val, V.property.preimage F.imageInclusion⟩
  have hU : (⨆ V, (U V).val) = ⊤ :=
    F.imageInclusion.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top U hU (fun V => ?_)⟩
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  change RingHom.ker (F.toImage.app (F.imageInclusion ⁻¹ᵁ V.val)).hom = ⊥
  exact (RingHom.injective_iff_ker_eq_bot
    (F.toImage.app (F.imageInclusion ⁻¹ᵁ V.val)).hom).mp
      (F.toProjective.toImage_app_injective V)

end CartierProjectivePresentation

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original full residue-field span embeds the literal native Spec k point. -/
theorem residuePoint_isClosedImmersion (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    IsClosedImmersion (F.residuePoint eI eH j₀ h₀) := by
  let _ : Field k := hk.toField
  let _ : Finite F.index := F.finiteIndex
  let a := fun j => cartierResidueCoefficient i hI H d eI eH n (F.sections j)
  let _ : Epi (Sigma.desc (FromSections.FieldSpan.family a)) :=
    F.residuePointFamily_epi eI eH j₀ h₀
  exact FromSections.FieldSpan.isClosedImmersion_mapOfFiniteFamily (exceptionalBaseHom p i) a
    (F.residueCoefficients_span eI eH hρ)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual image factor embeds the original Spec k, retaining the whole residue field. -/
theorem residueToImage_isClosedImmersion (hk : IsField k) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤))) :
    IsClosedImmersion (F.residueToImage eI eH j₀ h₀) := by
  let _ : IsClosedImmersion (F.residuePoint eI eH j₀ h₀) :=
    F.residuePoint_isClosedImmersion eI eH hk j₀ h₀ hρ
  let _ : IsClosedImmersion (F.residueToImage eI eH j₀ h₀ ≫ F.imageInclusion) := by
    rw [F.residueToImage_imageInclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ F.imageInclusion

end CartierProjectivePresentation

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinateRingHom_ext {B : Type u} [CommRing B] (a : ι)
    {φ ψ : coordinateRing A ι a →+* B}
    (hc : ∀ r, φ (coordinateRingCoefficient A ι a r) = ψ (coordinateRingCoefficient A ι a r))
    (hx : ∀ b, φ (coordinateRatio A ι a b) = ψ (coordinateRatio A ι a b)) : φ = ψ := by
  have h : φ.comp (polynomialToCoordinateRing A ι a) =
      ψ.comp (polynomialToCoordinateRing A ι a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using hc r
    · intro b
      simpa using hx b.1
  have h' := congrArg (fun f => f.comp (coordinateRingToPolynomial A ι a)) h
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h'

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem structuralCoefficient_chart {Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace A ι) (a : ι) (O : Y.Opens)
    (h : O ≤ q ⁻¹ᵁ coordinateOpen A ι a) (r : A) :
    (q.appLE (coordinateOpen A ι a) O h).hom
        ((Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom
          (coordinateRingCoefficient A ι a r)) =
      FromSections.SectionFrames.baseCoefficient (q ≫ toSpec A ι) O r := by
  let c : Γ(ProjectiveSpace A ι, ⊤) :=
    (toSpec A ι).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom r)
  have hc : sectionRestrict (ProjectiveSpace A ι) le_top c =
      (Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom
        (coordinateRingCoefficient A ι a r) :=
    constant_restriction A ι (MvPolynomial.X a) (isHomogeneous_X A a) Nat.zero_lt_one r
  calc
    _ = (q.appLE (coordinateOpen A ι a) O h).hom
        (sectionRestrict (ProjectiveSpace A ι) le_top c) :=
      congrArg (q.appLE (coordinateOpen A ι a) O h).hom hc.symm
    _ = (q.appLE ⊤ O (by simp)).hom c := by
      exact congrArg (fun f => f.hom c)
        (q.map_appLE h (homOfLE (show coordinateOpen A ι a ≤ ⊤ from le_top)).op)
    _ = _ := rfl

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

/-- The original old chart coordinates occur as literal original mixed ratios
in the new diagonal chart. -/
def mixedBaseChartLift (a : ι) : coordinateRing A ι a →+*
    coordinateRing A F.index (F.mixedIndex (a, a)) :=
  (eval₂Hom (coordinateRingCoefficient A F.index (F.mixedIndex (a, a)))
    (fun b => coordinateRatio A F.index (F.mixedIndex (a, a)) (F.mixedIndex (a, b.1)))).comp
      (coordinateRingToPolynomial A ι a)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
@[simp]
theorem mixedBaseChartLift_coefficient (a : ι) (r : A) :
    F.mixedBaseChartLift a (coordinateRingCoefficient A ι a r) =
      coordinateRingCoefficient A F.index (F.mixedIndex (a, a)) r := by
  simp [mixedBaseChartLift]

omit [IsNoetherianRing A] [IsClosedImmersion p] in
@[simp]
theorem mixedBaseChartLift_ratio (a b : ι) :
    F.mixedBaseChartLift a (coordinateRatio A ι a b) =
      coordinateRatio A F.index (F.mixedIndex (a, a)) (F.mixedIndex (a, b)) := by
  classical
  by_cases h : b = a
  · subst b
    rw [coordinateRatio_self, map_one, coordinateRatio_self]
  · change (eval₂Hom _ _)
      (coordinateRingToPolynomial A ι a
        (coordinateRatio A ι a (⟨b, h⟩ : {b : ι // b ≠ a}).1)) = _
    rw [coordinateRingToPolynomial_ratio, eval₂Hom_X']

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Mixed ratios in the actual off-E frames recover the original old chart ring map. -/
theorem offExceptionalFrames_chartRingHom_mixedBaseChartLift
    {Y : Scheme.{u}} (g : Y ⟶ X) (hg : ∀ y : Y, g y ∉ Set.range i)
    (a : ι) (O : Y.Opens) (h : O ≤ (g ≫ p) ⁻¹ᵁ coordinateOpen A ι a) :
    ((F.offExceptionalFrames g hg).chartRingHom (g ≫ p ≫ toSpec A ι) a h).comp
      (F.mixedBaseChartLift a) =
    ((g ≫ p).appLE (coordinateOpen A ι a) O h).hom.comp
      (Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom := by
  let G := F.offExceptionalFrames g hg
  let q := g ≫ p
  apply coordinateRingHom_ext a
  · intro r
    change G.chartRingHom (q ≫ toSpec A ι) a h
        (F.mixedBaseChartLift a (coordinateRingCoefficient A ι a r)) = _
    calc
      _ = G.chartRingHom (q ≫ toSpec A ι) a h
          (coordinateRingCoefficient A F.index (F.mixedIndex (a, a)) r) :=
        congrArg (G.chartRingHom (q ≫ toSpec A ι) a h)
          (F.mixedBaseChartLift_coefficient a r)
      _ = FromSections.SectionFrames.baseCoefficient (q ≫ toSpec A ι) O r :=
        G.chartRingHom_coefficient (q ≫ toSpec A ι) a h r
      _ = _ := (structuralCoefficient_chart q a O h r).symm
  · intro b
    change G.chartRingHom (q ≫ toSpec A ι) a h
        (F.mixedBaseChartLift a (coordinateRatio A ι a b)) = _
    have hfull : G.coefficientOn a le_rfl (F.mixedIndex (a, b)) =
        (q.app (coordinateOpen A ι a)).hom (coordinateRatioSection A ι a b) := by
      have hc := F.offExceptionalFrames_coefficient_mixed g hg a b a
      exact hc.trans (congrArg (q.app (coordinateOpen A ι a)).hom
        (congrArg (Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom
          (homogeneousChartFraction_mixed (A := A) n hn a b)))
    calc
      _ = G.chartRingHom (q ≫ toSpec A ι) a h
          (coordinateRatio A F.index (F.mixedIndex (a, a)) (F.mixedIndex (a, b))) :=
        congrArg (G.chartRingHom (q ≫ toSpec A ι) a h) (F.mixedBaseChartLift_ratio a b)
      _ = G.coefficientOn a h (F.mixedIndex (a, b)) :=
        G.chartRingHom_ratio (q ≫ toSpec A ι) a h (F.mixedIndex (a, b))
      _ = sectionRestrict Y h (G.coefficientOn a le_rfl (F.mixedIndex (a, b))) :=
        (G.coefficientOn_restrict a h le_rfl (F.mixedIndex (a, b))).symm
      _ = sectionRestrict Y h ((q.app (coordinateOpen A ι a)).hom
          (coordinateRatioSection A ι a b)) := congrArg (sectionRestrict Y h) hfull
      _ = _ := rfl

end CartierProjectivePresentation

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectiveChart_factorization {Y : Scheme.{u}}
    (q : Y ⟶ ProjectiveSpace A ι) (a : ι) (O : Y.Opens)
    (h : O ≤ q ⁻¹ᵁ coordinateOpen A ι a) :
    q.resLE (coordinateOpen A ι a) O h =
      O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        ((q.appLE (coordinateOpen A ι a) O h).hom.comp
          (Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom)) ≫
        (Proj.basicOpenIsoSpec (homogeneousSubmodule ι A) (MvPolynomial.X a)
          (isHomogeneous_X A a) Nat.zero_lt_one).inv := by
  let E := Proj.basicOpenIsoSpec (homogeneousSubmodule ι A) (MvPolynomial.X a)
    (isHomogeneous_X A a) Nat.zero_lt_one
  let φ := (q.appLE (coordinateOpen A ι a) O h).hom.comp
    (Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom
  have hfac : q.resLE (coordinateOpen A ι a) O h ≫ E.hom =
      O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.comp_appTop, E, Proj.basicOpenIsoSpec_hom,
      Proj.basicOpenToSpec_app_top, Scheme.Hom.resLE_app_top,
      Scheme.Opens.toSpecΓ_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality_assoc]
    rfl
  apply (cancel_mono E.hom).mp
  exact hfac.trans (by
    simpa only [Category.assoc, Category.comp_id] using
      (congrArg (fun f => O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ f)
        E.inv_hom_id).symm)

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

/-- The actual morphism from a new diagonal chart back to the original old a-chart. -/
def mixedBaseChartMap (a : ι) :
    (coordinateOpen A F.index (F.mixedIndex (a, a))).toScheme ⟶
      (coordinateOpen A ι a).toScheme :=
  (Proj.basicOpenIsoSpec (homogeneousSubmodule F.index A)
    (MvPolynomial.X (F.mixedIndex (a, a)))
    (isHomogeneous_X A (F.mixedIndex (a, a))) Nat.zero_lt_one).hom ≫
      Spec.map (CommRingCat.ofHom (F.mixedBaseChartLift a)) ≫
        (Proj.basicOpenIsoSpec (homogeneousSubmodule ι A) (MvPolynomial.X a)
          (isHomogeneous_X A a) Nat.zero_lt_one).inv

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On an original diagonal preimage, the actual mixed chart map recovers the original p. -/
theorem diagonal_recovery
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hnd : 1 ≤ n * d) (a : ι) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (F.toProjective ∣_ coordinateOpen A F.index (F.mixedIndex (a, a))) ≫
      F.mixedBaseChartMap a ≫ (coordinateOpen A ι a).ι =
    (F.toProjective ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a))).ι ≫ p := by
  let D := coordinateOpen A F.index (F.mixedIndex (a, a))
  let W := F.toProjective ⁻¹ᵁ D
  let Y := W.toScheme
  let g := W.ι
  let hg := F.diagonalSource_disjoint eI eH hnd a j₀ h₀
  let q := g ≫ p
  let G := F.offExceptionalFrames g hg
  let b := q ≫ toSpec A ι
  let r := F.toProjective ∣_ D
  have hk : (⊤ : Y.Opens) ≤ G.U a := by
    intro y _
    have hy : y ∈ (g ≫ F.toProjective) ⁻¹ᵁ D := y.property
    rw [F.offExceptional_preimage_diagonal g hg a] at hy
    exact hy
  let Enew := Proj.basicOpenIsoSpec (homogeneousSubmodule F.index A)
    (MvPolynomial.X (F.mixedIndex (a, a)))
    (isHomogeneous_X A (F.mixedIndex (a, a))) Nat.zero_lt_one
  let Eold := Proj.basicOpenIsoSpec (homogeneousSubmodule ι A) (MvPolynomial.X a)
    (isHomogeneous_X A a) Nat.zero_lt_one
  let φ := G.chartRingHom b a hk
  have hchart : (⊤ : Y.Opens).ι ≫ r =
      (⊤ : Y.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ Enew.inv := by
    apply (cancel_mono D.ι).mp
    calc
      _ = (⊤ : Y.Opens).ι ≫ (g ≫ F.toProjective) := by
        rw [Category.assoc, morphismRestrict_ι]
      _ = (⊤ : Y.Opens).ι ≫ G.map b :=
        congrArg (fun f => (⊤ : Y.Opens).ι ≫ f)
          (F.offExceptional_toProjective_eq g hg)
      _ = _ := by
        change (⊤ : Y.Opens).ι ≫ G.map b = G.chartMap b a hk
        exact G.ι_map_on b a hk
  let _ : IsIso ((⊤ : Y.Opens).ι) := Y.topIso.isIso_hom
  apply (cancel_epi (⊤ : Y.Opens).ι).mp
  calc
    (⊤ : Y.Opens).ι ≫ r ≫ F.mixedBaseChartMap a ≫ (coordinateOpen A ι a).ι =
      (⊤ : Y.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
        Enew.inv ≫ Enew.hom ≫ Spec.map (CommRingCat.ofHom (F.mixedBaseChartLift a)) ≫
          Eold.inv ≫ (coordinateOpen A ι a).ι := by
      rw [← Category.assoc, ← Category.assoc, hchart]
      rfl
    _ = (⊤ : Y.Opens).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        ((q.appLE (coordinateOpen A ι a) ⊤ hk).hom.comp
          (Proj.awayToSection (homogeneousSubmodule ι A) (MvPolynomial.X a)).hom)) ≫
          Eold.inv ≫ (coordinateOpen A ι a).ι := by
      rw [Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc]
      exact congrArg (fun h => (⊤ : Y.Opens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom h) ≫ Eold.inv ≫ (coordinateOpen A ι a).ι)
          (F.offExceptionalFrames_chartRingHom_mixedBaseChartLift g hg a ⊤ hk)
    _ = q.resLE (coordinateOpen A ι a) ⊤ hk ≫ (coordinateOpen A ι a).ι :=
      congrArg (fun h => h ≫ (coordinateOpen A ι a).ι)
        (projectiveChart_factorization q a ⊤ hk).symm
    _ = (⊤ : Y.Opens).ι ≫ q := Scheme.Hom.resLE_comp_ι q hk

end CartierProjectivePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem preimmersion_of_composite {Y Z T : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ T) [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  isEmbedding := Topology.IsEmbedding.of_comp f.continuous g.continuous
    (f ≫ g).isEmbedding
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original new map over each diagonal chart is a closed immersion,
by literal recovery of the original closed embedding and actual properness. -/
theorem diagonal_isClosedImmersion (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (a : ι) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    IsClosedImmersion (F.toProjective ∣_
      coordinateOpen A F.index (F.mixedIndex (a, a))) := by
  let D := coordinateOpen A F.index (F.mixedIndex (a, a))
  let f := F.toProjective ∣_ D
  let g := F.mixedBaseChartMap a ≫ (coordinateOpen A ι a).ι
  let _ : IsPreimmersion (f ≫ g) := by
    rw [show f ≫ g = (F.toProjective ⁻¹ᵁ D).ι ≫ p from
      F.diagonal_recovery eI eH hnd a j₀ h₀]
    infer_instance
  let _ : IsPreimmersion f := preimmersion_of_composite f g
  let _ : IsProper F.toProjective := F.toProjective_isProper r e
  let _ : IsProper f := inferInstance
  exact IsClosedImmersion.of_isPreimmersion f (by
    simpa only [Set.image_univ] using f.isClosedMap Set.univ isClosed_univ)

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original map to its actual image is an isomorphism on every diagonal image chart. -/
theorem toImage_diagonal_isIso (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (a : ι) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    IsIso (F.toImage ∣_ F.imageInclusion ⁻¹ᵁ
      coordinateOpen A F.index (F.mixedIndex (a, a))) := by
  let D := coordinateOpen A F.index (F.mixedIndex (a, a))
  let V := F.imageInclusion ⁻¹ᵁ D
  let f := F.toImage ∣_ V
  let j := F.imageInclusion ∣_ D
  let _ : IsProper F.toImage := F.toImage_isProper r e
  let _ : IsSchemeTheoreticallyDominant F.toImage := F.toImage_schemeTheoreticallyDominant r e
  let _ : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isPullback
    (isPullback_morphismRestrict F.toImage V).flip
  have hcomp : IsClosedImmersion ((F.toImage ≫ F.imageInclusion) ∣_ D) := by
    rw [F.toImage_imageInclusion]
    exact F.diagonal_isClosedImmersion eI eH r e hnd a j₀ h₀
  let _ : IsClosedImmersion (f ≫ j) := by
    simpa only [morphismRestrict_comp] using hcomp
  let _ : IsClosedImmersion f := IsClosedImmersion.of_comp_isClosedImmersion f j
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr f.ker_eq_bot

end CartierProjectivePresentation

namespace CartierProjectivePresentation

variable {p i hI H eP d} {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The original image open selected by an original diagonal coordinate. -/
def diagonalImageOpen (a : ι) : F.image.Opens :=
  F.imageInclusion ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The union of the actual diagonal image charts. -/
def imageComplementOpen : F.image.Opens := ⨆ a, F.diagonalImageOpen a

variable (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original image map is an isomorphism over the union of diagonal charts. -/
theorem imageComplement_restrict_isIso (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    IsIso (F.toImage ∣_ F.imageComplementOpen) := by
  let V := F.imageComplementOpen
  let U : ι → V.toScheme.Opens := fun a => V.ι ⁻¹ᵁ F.diagonalImageOpen a
  have hU : iSup U = ⊤ := by
    rw [show iSup U = V.ι ⁻¹ᵁ V from (Scheme.Hom.preimage_iSup V.ι _).symm]
    exact V.ι_preimage_self
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) U hU).mpr
  intro a
  have hle : F.diagonalImageOpen a ≤ V := le_iSup (F.diagonalImageOpen) a
  have himage : V.ι ''ᵁ U a = F.diagonalImageOpen a := by
    exact (V.ι.image_preimage_eq_opensRange_inf (F.diagonalImageOpen a)).trans
      (by rw [Scheme.Opens.opensRange_ι, inf_eq_right.mpr hle])
  have hlocal : IsIso (F.toImage ∣_ V.ι ''ᵁ U a) := by
    rw [himage]
    exact F.toImage_diagonal_isIso eI eH r e hnd a j₀ h₀
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict F.toImage V (U a))).mpr hlocal

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal original residue point misses the entire diagonal image open. -/
theorem residueToImage_preimage_imageComplement (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.residueToImage eI eH j₀ h₀ ⁻¹ᵁ F.imageComplementOpen = ⊥ := by
  rw [imageComplementOpen, Scheme.Hom.preimage_iSup]
  apply iSup_eq_bot.mpr
  intro a
  change F.residueToImage eI eH j₀ h₀ ⁻¹ᵁ
    (F.imageInclusion ⁻¹ᵁ coordinateOpen A F.index (F.mixedIndex (a, a))) = ⊥
  rw [← Scheme.Hom.comp_preimage, F.residueToImage_imageInclusion]
  exact F.residuePoint_preimage_diagonal eI eH hnd a j₀ h₀

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original preimage of the diagonal image open is exactly X minus E. -/
theorem toImage_preimage_imageComplement (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    F.toImage ⁻¹ᵁ F.imageComplementOpen = exceptionalComplement i := by
  let C := exceptionalComplement i
  let g := C.ι
  have hg : ∀ y : C.toScheme, g y ∉ Set.range i := fun y => y.property
  have hlocal (a : ι) :
      (g ≫ F.toImage) ⁻¹ᵁ F.diagonalImageOpen a =
        (g ≫ p) ⁻¹ᵁ coordinateOpen A ι a := by
    calc
      _ = (g ≫ F.toProjective) ⁻¹ᵁ
          coordinateOpen A F.index (F.mixedIndex (a, a)) := by
        rw [diagonalImageOpen, ← Scheme.Hom.comp_preimage,
          Category.assoc, F.toImage_imageInclusion]
      _ = _ := F.offExceptional_preimage_diagonal g hg a
  have hcover : (g ≫ F.toImage) ⁻¹ᵁ F.imageComplementOpen = ⊤ := by
    rw [imageComplementOpen, Scheme.Hom.preimage_iSup]
    simp_rw [hlocal]
    exact (g ≫ p).iSup_preimage_eq_top (iSup_coordinateOpen_eq_top A ι)
  have hE : (i ≫ F.toImage) ⁻¹ᵁ F.imageComplementOpen = ⊥ := by
    rw [F.exceptional_toImage_eq eI eH j₀ h₀, Scheme.Hom.comp_preimage,
      F.residueToImage_preimage_imageComplement eI eH hnd j₀ h₀,
      Scheme.Hom.preimage_bot]
  apply le_antisymm
  · intro x hx
    change x ∉ Set.range i
    rintro ⟨z, rfl⟩
    have hz : z ∈ (i ≫ F.toImage) ⁻¹ᵁ F.imageComplementOpen := hx
    rw [hE] at hz
    exact hz
  · intro x hx
    have hy : (⟨x, hx⟩ : C) ∈ (g ≫ F.toImage) ⁻¹ᵁ F.imageComplementOpen := by
      rw [hcover]
      trivial
    exact hy

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual inverse on the original exceptional complement, preserving its image map. -/
def complementIso (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (exceptionalComplement i).toScheme ≅ F.imageComplementOpen.toScheme := by
  let _ : IsIso (F.toImage ∣_ F.imageComplementOpen) :=
    F.imageComplement_restrict_isIso eI eH r e hnd j₀ h₀
  exact Scheme.isoOfEq X (F.toImage_preimage_imageComplement eI eH hnd j₀ h₀).symm ≪≫
    asIso (F.toImage ∣_ F.imageComplementOpen)

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem complementIso_hom_ι (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (F.complementIso eI eH r e hnd j₀ h₀).hom ≫ F.imageComplementOpen.ι =
      (exceptionalComplement i).ι ≫ F.toImage := by
  change (Scheme.isoOfEq X
    (F.toImage_preimage_imageComplement eI eH hnd j₀ h₀).symm).hom ≫
      (F.toImage ∣_ F.imageComplementOpen) ≫ F.imageComplementOpen.ι = _
  rw [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem complementIso_inv_ι_toImage (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (F.complementIso eI eH r e hnd j₀ h₀).inv ≫
      (exceptionalComplement i).ι ≫ F.toImage = F.imageComplementOpen.ι := by
  rw [← F.complementIso_hom_ι eI eH r e hnd j₀ h₀]
  exact (F.complementIso eI eH r e hnd j₀ h₀).inv_hom_id_assoc _

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same diagonal image open is the complement of the entire original Spec k image. -/
theorem imageComplement_carrier (r : ℕ) (e : ι ≃ Fin (r + 1))
    (hnd : 1 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀))) :
    (F.imageComplementOpen : Set F.image) =
      (Set.range (F.residueToImage eI eH j₀ h₀))ᶜ := by
  let _ : Surjective F.toImage := F.toImage_surjective r e
  ext y
  constructor
  · intro hy
    rintro ⟨z, rfl⟩
    have hz : z ∈ F.residueToImage eI eH j₀ h₀ ⁻¹ᵁ F.imageComplementOpen := hy
    rw [F.residueToImage_preimage_imageComplement eI eH hnd j₀ h₀] at hz
    exact hz
  · intro hy
    obtain ⟨x, rfl⟩ := F.toImage.surjective y
    have hx : x ∈ exceptionalComplement i := by
      change x ∉ Set.range i
      rintro ⟨z, rfl⟩
      apply hy
      refine ⟨toSpec k (ULift.{u} (Fin 2)) z, ?_⟩
      exact congrArg (fun f => f z) (F.exceptional_toImage_eq eI eH j₀ h₀).symm
    have hpre : x ∈ F.toImage ⁻¹ᵁ F.imageComplementOpen := by
      rw [F.toImage_preimage_imageComplement eI eH hnd j₀ h₀]
      exact hx
    exact hpre

end CartierProjectivePresentation

include p eP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For every sufficiently large n, the original cohomological construction gives
an actual image with the original residue field and an actual complement inverse,
while retaining both proved first-order lifts as literal original coordinates. -/
theorem exists_cartier_projective_complement
    (r : ℕ) (e : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hk : IsField k) (hd : 0 < d) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n),
      ∃ (hn2 : 2 ≤ n * d)
        (F : CartierProjectivePresentation p i hI H eP d n (hB.trans hn))
        (t : ULift.{u} (Fin 2) → (𝟙_ X.Modules ⟶
          (cartierStepSequence i hI (cartierPowerTwist i hI H n (n * d - 2))).X₂))
        (q : ULift.{u} (Fin 2) ↪ F.index)
        (j₀ : F.index)
        (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
        (ε : (exceptionalComplement i).toScheme ≅ F.imageComplementOpen.toScheme),
        (∀ a, t a ≫ (cartierStepSequence i hI
          (cartierPowerTwist i hI H n (n * d - 2))).g =
            firstOrderQuotientCoordinate i hI H d eI eH n hn2 a) ∧
        (∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) ∧
        Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)) ∧
        IsClosedImmersion (F.residueToImage eI eH j₀ h₀) ∧
        ε.hom ≫ F.imageComplementOpen.ι = (exceptionalComplement i).ι ≫ F.toImage ∧
        (F.imageComplementOpen : Set F.image) =
          (Set.range (F.residueToImage eI eH j₀ h₀))ᶜ ∧
        i ≫ F.toImage =
          toSpec k (ULift.{u} (Fin 2)) ≫ F.residueToImage eI eH j₀ h₀ := by
  obtain ⟨Bg, hBg, hgen⟩ :=
    exists_cartier_firstOrder_projective_presentation p i hI H eP d r e eI eH
  obtain ⟨Br, hres⟩ :=
    exists_cartierResidueMap_sections_surjective p i hI H eP d r e eI eH
  let B := max (max Bg Br) 2
  have hB : 1 ≤ B := hBg.trans ((le_max_left Bg Br).trans (le_max_left _ _))
  refine ⟨B, hB, fun n hn => ?_⟩
  have hn2 : 2 ≤ n * d := by
    simpa using Nat.mul_le_mul ((le_max_right (max Bg Br) 2).trans hn)
      (Nat.succ_le_iff.mpr hd)
  have hnd : 1 ≤ n * d := by omega
  obtain ⟨F, t, q, ht, hq⟩ := hgen n
    ((le_max_left Bg Br).trans ((le_max_left (max Bg Br) 2).trans hn)) hn2
  have hρ := hres n
    ((le_max_right Bg Br).trans ((le_max_left (max Bg Br) 2).trans hn)) hnd
  obtain ⟨j₀, h₀⟩ := F.exists_residueCoefficient_isUnit eI eH hk hρ
  refine ⟨hn2, F, t, q, j₀, h₀, F.complementIso eI eH r e hnd j₀ h₀,
    ht, hq, hρ, F.residueToImage_isClosedImmersion eI eH hk j₀ h₀ hρ,
    F.complementIso_hom_ι eI eH r e hnd j₀ h₀,
    F.imageComplement_carrier eI eH r e hnd j₀ h₀,
    F.exceptional_toImage_eq eI eH j₀ h₀⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
