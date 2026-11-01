/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.AmpleKernel
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.FamilyFormula
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Square
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Finite
public import Aglib.AlgebraicGeometry.Group.Kernel.Finite
public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Power
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Nonzero
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Nonvanishing
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ProductRigidity
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral

/-!
# Effective finite-kernel ampleness on projective geometrically integral groups

The original nonzero global section and the original square identity give
nonvanishing sections of the actual tensor square at every point. Compactness
then supplies a projective map with finitely many coordinates and its original
O(1)-bundle equation. Whole product rigidity and finiteness of the original
Picard morphism make this map finite, hence the original bundle ample.
This follows the finite-kernel ampleness route of Edixhoven--van der
Geer--Moonen, Chapter II, (2.20)--(2.22), using schematic images of generic
points to handle the actual fibres.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
open TopologicalSpace

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G]

private theorem mulRight_apply_point_swap
    (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (GrpObj.mulRight a).hom.left (b.left (IsLocalRing.closedPoint k)) =
      (GrpObj.mulRight b).hom.left (a.left (IsLocalRing.closedPoint k)) := by
  have h : b ≫ (GrpObj.mulRight a).hom = a ≫ (GrpObj.mulRight b).hom := by
    change b ≫ (𝟙 G * (toUnit G ≫ a)) = a ≫ (𝟙 G * (toUnit G ≫ b))
    simp only [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, toUnit_unit,
      Category.id_comp]
    exact _root_.mul_comm b a
  exact congrArg (fun f : 𝟙_ (Over (Spec (.of k))) ⟶ G =>
    f.left (IsLocalRing.closedPoint k)) h

variable [IsAlgClosed k] [IsHProjective G.hom] [GeometricallyIntegral G.hom]

/-- A genuine nonzero section gives an original tensor-square section
nonvanishing at each closed point. Only the original translations and square
class equation are used. -/
theorem exists_tensorSquareSection_nonvanishing_at_closedPoint
    (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0)
    (x : G.left) (hx : IsClosed {x}) :
    ∃ t : Γ((tensorPowerLineBundle G.left L 2).val, ⊤),
      x ∈ nonvanishingOpen (tensorPowerLineBundle G.left L 2) t := by
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  let b : 𝟙_ (Over (Spec (.of k))) ⟶ G :=
    Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx)
  have hb : b.left (IsLocalRing.closedPoint k) = x := pointOfClosedPoint_apply G.hom x hx _
  have : IsIso (GrpObj.mulRight b).hom.left :=
    (Over.forget (Spec (.of k))).map_isIso (GrpObj.mulRight b).hom
  have : IsIso ι[G].left := (Over.forget (Spec (.of k))).map_isIso ι[G]
  let U := nonvanishingOpen L s
  let V := (GrpObj.mulRight b).hom.left ⁻¹ᵁ U
  let W := ι[G].left ⁻¹ᵁ V
  have hU : (U : Set G.left).Nonempty := nonempty_nonvanishingOpen_of_ne_zero L s hs
  have hV : (V : Set G.left).Nonempty := hU.preimage (GrpObj.mulRight b).hom.left.surjective
  have hW : (W : Set G.left).Nonempty := hV.preimage ι[G].left.surjective
  obtain ⟨a₀, ha, hac⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter V.isOpen W.isOpen hV hW)
    (V ⊓ W).isOpen.isLocallyClosed
  let a : 𝟙_ (Over (Spec (.of k))) ⟶ G :=
    Over.homMk (pointOfClosedPoint G.hom a₀ hac) (pointOfClosedPoint_comp G.hom a₀ hac)
  have ha₀ : a.left (IsLocalRing.closedPoint k) = a₀ :=
    pointOfClosedPoint_apply G.hom a₀ hac _
  have haInv : (a⁻¹).left (IsLocalRing.closedPoint k) = ι[G].left a₀ := by
    have he : a ≫ ι[G] = a⁻¹ := by
      rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id]
    rw [← he, Over.comp_left, Scheme.Hom.comp_apply, ha₀]
  let A := pullbackLineBundle (GrpObj.mulRight a).hom.left L
  let B := pullbackLineBundle (GrpObj.mulRight a⁻¹).hom.left L
  let sA := Nonvanishing.pullbackSection (GrpObj.mulRight a).hom.left L.val s
  let sB := Nonvanishing.pullbackSection (GrpObj.mulRight a⁻¹).hom.left L.val s
  have hxA : x ∈ nonvanishingOpen A sA := by
    rw [Nonvanishing.nonvanishingOpen_pullback]
    change (GrpObj.mulRight a).hom.left x ∈ U
    rw [← hb, mulRight_apply_point_swap G a b, ha₀]
    exact ha.1
  have hxB : x ∈ nonvanishingOpen B sB := by
    rw [Nonvanishing.nonvanishingOpen_pullback]
    change (GrpObj.mulRight a⁻¹).hom.left x ∈ U
    rw [← hb, mulRight_apply_point_swap G a⁻¹ b, haInv]
    exact ha.2
  have hunit : (GrpObj.mulRight (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G)).hom = 𝟙 G := by
    change 𝟙 G * (toUnit G ≫ (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G)) = 𝟙 G
    rw [MonObj.comp_one, _root_.mul_one]
  have hc : classOf G.left (tensorLineBundle G.left A B) =
      classOf G.left (tensorPowerLineBundle G.left L 2) := by
    have h := Group.LineBundleCube.pullbackClass_translation_mul G a a⁻¹ (classOf G.left L)
    rw [mul_inv_cancel, hunit, Over.id_left, pullbackClass_id] at h
    rw [classOf_tensor, classOf_tensorPower]
    change classOf G.left (pullbackLineBundle (GrpObj.mulRight a).hom.left L) +
        classOf G.left (pullbackLineBundle (GrpObj.mulRight a⁻¹).hom.left L) =
      2 • classOf G.left L
    rw [← pullbackClass_classOf, ← pullbackClass_classOf]
    exact h.symm.trans (two_nsmul (classOf G.left L)).symm
  obtain ⟨e⟩ := (class_eq_iff G.left _ _).mp hc
  let t := moduleTensorSection G.left A.val B.val ⊤ sA sB
  refine ⟨e.hom.val.app (op ⊤) t, ?_⟩
  rw [nonvanishingOpen_iso, nonvanishingOpen_tensor]
  exact ⟨hxA, hxB⟩

/-- The actual tensor square of an effective bundle has a nonvanishing
original section at every scheme point, including nonclosed points. -/
theorem tensorSquare_has_nonvanishing_sections
    (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0) :
    ∀ x : G.left, ∃ t : Γ((tensorPowerLineBundle G.left L 2).val, ⊤),
      x ∈ nonvanishingOpen (tensorPowerLineBundle G.left L 2) t := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  let U : G.left.Opens := ⨆ t : Γ((tensorPowerLineBundle G.left L 2).val, ⊤),
    nonvanishingOpen (tensorPowerLineBundle G.left L 2) t
  have hU : U = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    by_contra hx
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
      (show ((U : Set G.left)ᶜ).Nonempty from ⟨x, hx⟩)
      U.isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨t, ht⟩ := exists_tensorSquareSection_nonvanishing_at_closedPoint G L s hs y hyc
    exact hy (Opens.mem_iSup.mpr ⟨t, ht⟩)
  intro x
  exact Opens.mem_iSup.mp (show x ∈ U by rw [hU]; trivial)

/-- One actual finite-coordinate projective map has pullback O(1) equal to
the original tensor square. The map and comparison are constructed from
original sections; no separate semiampleness supplier is assumed. -/
theorem exists_projectiveMap_tensorSquare_of_section_ne_zero
    (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0) :
    ∃ (I : Type u) (_ : Finite I) (f : G.left ⟶ ProjectiveSpace k I),
      f ≫ ProjectiveSpace.toSpec k I = G.hom ∧
        Nonempty ((Scheme.Modules.pullback f).obj (ProjectiveSpace.twistingSheaf k I 1) ≅
          (tensorPowerLineBundle G.left L 2).val) := by
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  exact ProjectiveSpace.FromSections.exists_projectiveMap_of_nonvanishing_cover G.hom
    (tensorPowerLineBundle G.left L 2) (fun t => t)
    (tensorSquare_has_nonvanishing_sections G L s hs)

section Picard

variable (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

omit [IsHProjective G.hom] [IsCommMonObj G] [LocallyOfFiniteType P.obj.hom] in
/-- On a proper integral parameter whose original map is contracted by f,
the original Picard morphism of f*L is constant. The proof first establishes
the whole translation-map equation, then evaluates the original class. -/
theorem comp_lineBundleClassMorphism_pullback_eq_of_constant
    [IsProper G.hom]
    (Y : Over (Spec (.of k))) [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : G ⟶ Y) (L : LineBundle Y.left)
    (Z : Over (Spec (.of k))) [IsProper Z.hom] [IsIntegral Z.left]
    (t : Z ⟶ G) (z : 𝟙_ (Over (Spec (.of k))) ⟶ Z)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) (ht : t ≫ f = toUnit Z ≫ y) :
    t ≫ lineBundleClassMorphism G P R (pullbackClass f.left (classOf Y.left L)) =
      (toUnit Z ≫ z ≫ t) ≫
        lineBundleClassMorphism G P R (pullbackClass f.left (classOf Y.left L)) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsIntegral (G ⊗ Z).left := by dsimp; infer_instance
  let σ : G ⊗ Z ⟶ Y := translationFamilyMorphism G t ≫ f
  have hleft : (η[G] ▷ Z) ≫ σ = toUnit _ ≫ y := by
    dsimp only [σ, translationFamilyMorphism]
    rw [← Category.assoc, MonObj.comp_mul, whiskerRight_fst, whiskerRight_snd_assoc]
    rw [show fst (𝟙_ (Over (Spec (.of k)))) Z = toUnit _ from toUnit_unique _ _,
      ← Hom.one_def, _root_.one_mul, Category.assoc, ht, comp_toUnit_assoc]
  have hrigid := Scheme.OverField.eq_fst_comp_of_isProper_of_integral_tensor
    G Z Y η[G] z y σ hleft
  have haxis : fst G Z ≫ (ρ_ G).inv ≫ G ◁ z ≫ translationFamilyMorphism G t =
      translationFamilyMorphism G (toUnit Z ≫ z ≫ t) := by
    simp [translationFamilyMorphism, MonObj.comp_mul]
  have hmaps : translationFamilyMorphism G t ≫ f =
      translationFamilyMorphism G (toUnit Z ≫ z ≫ t) ≫ f := by
    calc
      _ = fst G Z ≫ (ρ_ G).inv ≫ G ◁ z ≫ translationFamilyMorphism G t ≫ f := hrigid
      _ = (fst G Z ≫ (ρ_ G).inv ≫ G ◁ z ≫ translationFamilyMorphism G t) ≫ f := by
        simp only [Category.assoc]
      _ = _ := congrArg (fun q => q ≫ f) haxis
  let a := pullbackClass f.left (classOf Y.left L)
  have hclass : translationFamilyClass G t a =
      translationFamilyClass G (toUnit Z ≫ z ≫ t) a := by
    simp only [translationFamilyClass, a, ← pullbackClass_comp, ← Over.comp_left]
    rw [hmaps]
  let T : LocallyNoetherianOver (Spec (.of k)) := ⟨Z, inferInstance⟩
  have he : (ObjectProperty.homMk (t ≫ lineBundleClassMorphism G P R a) : T ⟶ P) =
      ObjectProperty.homMk ((toUnit Z ≫ z ≫ t) ≫ lineBundleClassMorphism G P R a) := by
    apply R.homEquiv.injective
    rw [fppf_homEquiv_comp_lineBundleClassMorphism,
      fppf_homEquiv_comp_lineBundleClassMorphism]
    exact congrArg ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
      hclass
  exact congrArg (fun q : T ⟶ P => q.hom) he

omit [IsHProjective G.hom] [IsCommMonObj G] [LocallyOfFiniteType P.obj.hom] in
private theorem finite_integral_parameter_of_finite_phi_pullback
    [IsProper G.hom]
    (Y : Over (Spec (.of k))) [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : G ⟶ Y) (L : LineBundle Y.left)
    [IsFinite (lineBundleClassMorphism G P R (pullbackClass f.left (classOf Y.left L))).left]
    (Z : Over (Spec (.of k))) [IsProper Z.hom] [IsIntegral Z.left]
    (t : Z ⟶ G) [IsClosedImmersion t.left]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) (ht : t ≫ f = toUnit Z ≫ y) :
    Finite Z.left := by
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  obtain ⟨z₀, -, hz₀⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Z.left).Nonempty) isOpen_univ.isLocallyClosed
  let z : 𝟙_ (Over (Spec (.of k))) ⟶ Z :=
    Over.homMk (pointOfClosedPoint Z.hom z₀ hz₀) (pointOfClosedPoint_comp Z.hom z₀ hz₀)
  let φ := lineBundleClassMorphism G P R (pullbackClass f.left (classOf Y.left L))
  let q : 𝟙_ (Over (Spec (.of k))) ⟶ P.obj := z ≫ t ≫ φ
  have he := comp_lineBundleClassMorphism_pullback_eq_of_constant G P R Y f L Z t z y ht
  have hr : Set.range t.left ⊆ φ.left ⁻¹' {q.left (IsLocalRing.closedPoint k)} := by
    rintro _ ⟨x, rfl⟩
    have h := congrArg (fun m : Z ⟶ P.obj => m.left x) he
    have hs : (toUnit Z).left x = IsLocalRing.closedPoint k := by
      change Z.hom x = IsLocalRing.closedPoint k
      exact Subsingleton.elim _ _
    change φ.left (t.left x) = q.left (IsLocalRing.closedPoint k)
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hs, q, Category.assoc] using h
  have hfin : (Set.range t.left).Finite := (φ.left.finite_preimage_singleton _).subset hr
  have : Finite (Set.range t.left) := hfin
  apply Finite.of_injective (fun x : Z.left =>
    (⟨t.left x, ⟨x, rfl⟩⟩ : Set.range t.left))
  intro x y h
  exact t.left.isClosedEmbedding.injective (congrArg Subtype.val h)

omit [IsHProjective G.hom] [IsCommMonObj G] [LocallyOfFiniteType P.obj.hom] in
/-- If the original Picard morphism of the original pulled-back bundle is
finite, the original map to a separated finite-type target is finite.
Schematic closures of generic points handle all irreducible fibre components. -/
theorem isFinite_of_isFinite_lineBundleClassMorphism_pullback
    [IsProper G.hom]
    (Y : Over (Spec (.of k))) [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : G ⟶ Y) (L : LineBundle Y.left)
    [IsFinite (lineBundleClassMorphism G P R (pullbackClass f.left (classOf Y.left L))).left] :
    IsFinite f.left := by
  have : IsProper (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left Y.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  apply IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace f.left
  intro x hx
  have hy : IsClosed {f.left x} := by simpa using f.left.isClosedMap _ hx
  let b : Spec (.of k) ⟶ Y.left := pointOfClosedPoint Y.hom (f.left x) hy
  have hb : b ≫ Y.hom = 𝟙 _ := pointOfClosedPoint_comp Y.hom (f.left x) hy
  let b' : 𝟙_ (Over (Spec (.of k))) ⟶ Y := Over.homMk b hb
  have : IsClosedImmersion b := isClosedImmersion_of_comp_eq_id Y.hom b hb
  let W := pullback f.left b
  have : IsProper (pullback.snd f.left b) := inferInstance
  have : IsLocallyNoetherian W :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f.left b)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f.left b)
  have : IsNoetherian W :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hfiber : pullback.fst f.left b ≫ G.hom = pullback.snd f.left b := by
    rw [← Over.w f, pullback.condition_assoc, hb, Category.comp_id]
  have hcomp : ∀ C ∈ irreducibleComponents W, C.Finite := by
    intro C hC
    let z : W := hC.1.genericPoint
    let j := W.fromSpecResidueField z
    have : QuasiCompact j := inferInstance
    have : IsIntegral j.image := Scheme.schemeImage_isIntegral j
    let Z : Over (Spec (.of k)) :=
      Over.mk ((j.imageι ≫ pullback.fst f.left b) ≫ G.hom)
    let t : Z ⟶ G := Over.homMk (j.imageι ≫ pullback.fst f.left b) rfl
    have : IsClosedImmersion t.left := by dsimp [t]; infer_instance
    have : IsIntegral Z.left := by change IsIntegral j.image; infer_instance
    have : IsProper Z.hom := by dsimp [Z]; infer_instance
    have ht : t ≫ f = toUnit Z ≫ b' := by
      ext1
      change (j.imageι ≫ pullback.fst f.left b) ≫ f.left =
        ((j.imageι ≫ pullback.fst f.left b) ≫ G.hom) ≫ b
      calc
        _ = j.imageι ≫ pullback.snd f.left b ≫ b := by
          rw [Category.assoc, pullback.condition]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun q => j.imageι ≫ q ≫ b) hfiber.symm
    have : Finite Z.left :=
      finite_integral_parameter_of_finite_phi_pullback G P R Y f L Z t b' ht
    have : Finite j.image := inferInstanceAs (Finite Z.left)
    have hrange : Set.range j.imageι = C := by
      change Set.range j.ker.subschemeι = C
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
      change closure (Set.range (W.fromSpecResidueField z)) = C
      rw [Scheme.range_fromSpecResidueField]
      exact hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    rw [← hrange]
    exact Set.finite_range _
  have : Finite W := Set.finite_univ_iff.mp (by
    rw [← sUnion_irreducibleComponents]
    exact (NoetherianSpace.finite_irreducibleComponents (α := W)).sUnion hcomp)
  have hrange : Set.range b = {f.left x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact pointOfClosedPoint_apply Y.hom (f.left x) hy z
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint k, pointOfClosedPoint_apply Y.hom (f.left x) hy _⟩
  have hfin := Set.finite_range (pullback.fst f.left b)
  rw [Scheme.Pullback.range_fst, hrange] at hfin
  exact hfin

variable [IsSeparated P.obj.hom]

omit [IsAlgClosed k] in
/-- Finiteness of the original Picard morphism persists for its tensor
square. Positive multiplication by two is the independent native supplier,
including characteristic two. -/
theorem isFinite_lineBundleClassMorphism_tensorSquare
    (L : LineBundle G.left)
    [IsFinite (lineBundleClassMorphism G P R (classOf G.left L)).left] :
    IsFinite (lineBundleClassMorphism G P R
      (classOf G.left (tensorPowerLineBundle G.left L 2))).left := by
  let := picardCommGrpObj G.hom P R
  let a := classOf G.left L
  have : IsMonHom (lineBundleClassMorphism G P R a) :=
    isMonHom_lineBundleClassMorphism G P R a
  have : IsFinite ((𝟙 G) ^ 2).left :=
    (Group.Multiplication.multiplication_finite_flat_surjective_of_isHProjective
      (Grp.mk G) 2 (by decide)).1
  have he : lineBundleClassMorphism G P R (2 • a) =
      ((𝟙 G) ^ 2) ≫ lineBundleClassMorphism G P R a := by
    rw [two_nsmul, lineBundleClassMorphism_add, MonObj.pow_comp, Category.id_comp, pow_two]
  rw [classOf_tensorPower]
  change IsFinite (lineBundleClassMorphism G P R (2 • a)).left
  rw [he, Over.comp_left]
  infer_instance

/-- A genuine nonzero original global section and a finite original Picard
morphism make the original line bundle ample. The constructed projective
map and its actual O(1) comparison supply the affine nonvanishing opens. -/
theorem isAmple_of_section_ne_zero_of_isFinite_lineBundleClassMorphism
    (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0)
    [IsFinite (lineBundleClassMorphism G P R (classOf G.left L)).left] : L.IsAmple := by
  obtain ⟨I, hI, f, hf, ⟨e⟩⟩ :=
    exists_projectiveMap_tensorSquare_of_section_ne_zero G L s hs
  let := hI
  let Y : Over (Spec (.of k)) := Over.mk (ProjectiveSpace.toSpec k I)
  have : IsProper Y.hom := by
    change IsProper (ProjectiveSpace.toSpec k I)
    infer_instance
  let f' : G ⟶ Y := Over.homMk f hf
  let N := ProjectiveSpace.twistingLineBundle k I 1
  have hc : pullbackClass f'.left (classOf Y.left N) =
      classOf G.left (tensorPowerLineBundle G.left L 2) :=
    (class_eq_iff G.left _ _).mpr ⟨e⟩
  have : IsFinite (lineBundleClassMorphism G P R
      (pullbackClass f'.left (classOf Y.left N))).left := by
    rw [hc]
    exact isFinite_lineBundleClassMorphism_tensorSquare G P R L
  have : IsFinite f :=
    isFinite_of_isFinite_lineBundleClassMorphism_pullback G P R Y f' N
  exact LineBundle.IsAmple.of_tensorPower L 2 (by decide)
    (ProjectiveSpace.FromSections.isAmple_of_isFinite_projectiveMap
      (tensorPowerLineBundle G.left L 2) f e)

/-- Effective finite-kernel ampleness, for the actual scheme-theoretic
kernel of the original map to the same supplied Picard representative.
No geometry of the dual identity component is required. -/
theorem isAmple_of_section_ne_zero_of_finite_kernel
    (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0)
    (hK : IsFinite (Group.Kernel.group
      (lineBundleClassGroupHom G P R (classOf G.left L))).X.hom) : L.IsAmple := by
  let := picardCommGrpObj G.hom P R
  have : IsFinite (Group.Kernel.group
      (lineBundleClassGroupHom G P R (classOf G.left L))).X.hom := hK
  have : IsFinite (lineBundleClassMorphism G P R (classOf G.left L)).left :=
    Group.Kernel.isFinite_of_isFinite_group
      (lineBundleClassGroupHom G P R (classOf G.left L))
  exact isAmple_of_section_ne_zero_of_isFinite_lineBundleClassMorphism G P R L s hs

/-- The same criterion for the actual scheme kernel after the original
factorization through the actual Picard identity component. The component
need not be known smooth, proper, or of any prescribed dimension. -/
theorem isAmple_of_section_ne_zero_of_finite_identityComponent_kernel
    (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0)
    (hK : IsFinite (Group.Kernel.group
      (lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L))).X.hom) :
    L.IsAmple := by
  let := picardCommGrpObj G.hom P R
  have : IsSeparated (Group.identityComponentOver P.obj).hom := by
    change IsSeparated ((Group.identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  have : IsFinite (Group.Kernel.group
      (lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L))).X.hom := hK
  have : IsFinite
      (lineBundleClassMorphismIdentityComponent G P R (classOf G.left L)).left :=
    Group.Kernel.isFinite_of_isFinite_group
      (lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L))
  have : IsClosedImmersion (Group.identityComponentι P.obj).left := by
    change IsClosedImmersion (Group.identityComponent P.obj).ι
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact Group.isClosed_identityComponent P.obj
  have : IsFinite (lineBundleClassMorphism G P R (classOf G.left L)).left := by
    rw [← lineBundleClassMorphismIdentityComponent_ι, Over.comp_left]
    infer_instance
  exact isAmple_of_section_ne_zero_of_isFinite_lineBundleClassMorphism G P R L s hs

end Picard

end AlgebraicGeometry.Scheme.RelativePicard
