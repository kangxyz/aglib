/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain
public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.Morphisms.Proper.FibreDescent
public import Aglib.AlgebraicGeometry.Surfaces.Birational.ExceptionalConormal
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.Morphisms.Proper.CartierNeighborhood
public import Aglib.AlgebraicGeometry.Surfaces.Birational.CommonDomination
public import Aglib.AlgebraicGeometry.Surfaces.Birational.ExceptionalLocus

/-!
# Actual point blowups in birational surface factorization

The finite-chain decomposition retains a source isomorphism: a source
isomorphism is not itself declared to be a literal point-blowup chain.
Descent of a map contracting the last exceptional fibre uses the original
blowdown and its actual structure-sheaf isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

namespace Blowup.PointBlowupChain

/-- A zero-length actual point chain has an invertible original map. -/
theorem isIso_of_length_eq_zero {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) (hc : c.length = 0) : IsIso f := by
  cases c with
  | refl X => infer_instance
  | cons x hx hd g tail => simp only [length, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false] at hc

/-- A nonempty chain splits at its last actual blowup. The source comparison
is retained explicitly, and the preceding chain has exactly one fewer step. -/
theorem exists_last {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) (hc : c.length ≠ 0) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X) (tail : PointBlowupChain a)
      (x : Z) (_hx : IsClosed ({x} : Set Z))
      (_hd : ringKrullDim (Z.presheaf.stalk x) = 2)
      (e : Y ≅ (blowupDatum (Z.fromSpecResidueField x).ker).Y),
      e.hom ≫ (blowupDatum (Z.fromSpecResidueField x).ker).map ≫ a = f ∧
        tail.length + 1 = c.length := by
  induction c with
  | refl X => exact False.elim (hc rfl)
  | @cons X Y x hx hd g tail ih =>
    by_cases ht : tail.length = 0
    · let : IsIso g := tail.isIso_of_length_eq_zero ht
      refine ⟨X, 𝟙 X, .refl X, x, hx, hd, asIso g, ?_, ?_⟩
      · simp only [asIso_hom, Category.comp_id]
      · simp only [length, ht]
    · obtain ⟨Z, a, d, z, hz, hzd, e, he, hlen⟩ := ih ht
      refine ⟨Z, a ≫ (blowupDatum (X.fromSpecResidueField x).ker).map,
        .cons x hx hd a d, z, hz, hzd, e, ?_, ?_⟩
      · simpa only [Category.assoc] using
          congrArg (fun k => k ≫ (blowupDatum (X.fromSpecResidueField x).ker).map) he
      · simpa only [length] using congrArg (fun n : ℕ => n + 1) hlen

end Blowup.PointBlowupChain

/-- A point outside the actual proper-birational isomorphism locus on a
normal surface has a two-dimensional original local ring. -/
theorem Hom.stalk_dimension_eq_two_of_not_mem_targetIsomorphismLocus
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdim : topologicalKrullDim Y ≤ 2)
    (y : Y) (hy : y ∉ f.targetIsomorphismLocus) :
    ringKrullDim (Y.presheaf.stalk y) = 2 := by
  have hle : Order.coheight y ≤ 2 := by
    rw [topologicalKrullDim_eq_iSup_stalk] at hdim
    have h := (le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) y).trans hdim
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  have hn : ¬Order.coheight y ≤ 1 := by
    intro h
    obtain ⟨U, hyU, hU⟩ :=
      exists_isIso_restrict_of_isProper_birational_at_coheight_le_one f hff hY y h
    exact hy (f.le_targetIsomorphismLocus U hU hyU)
  have heq : Order.coheight y = 2 :=
    le_antisymm hle (not_lt.mp (fun h => hn (ENat.lt_two_iff.mp h)))
  rw [ringKrullDim_stalk_eq_coheight, heq]
  rfl

namespace Blowup

variable {X : Scheme.{u}} (x : X) (B : BlowupDatum (X.fromSpecResidueField x).ker)

/-- The range of the literal exceptional-fibre immersion is the original
point fibre of the specified blowdown. -/
theorem range_exceptionalFst :
    Set.range (pullback.fst B.map (X.fromSpecResidueField x)) = B.map ⁻¹' {x} := by
  rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

/-- Every point of the literal exceptional fibre maps to its original centre. -/
theorem exceptionalFst_map (z : ↑(pullback B.map (X.fromSpecResidueField x))) :
    B.map (pullback.fst B.map (X.fromSpecResidueField x) z) = x := by
  have h := congrArg (fun k => k z)
    (pullback.condition (f := B.map) (g := X.fromSpecResidueField x))
  simpa only [Hom.comp_apply, fromSpecResidueField_apply] using h

/-- Pointwise constancy on the actual exceptional fibre implies constancy
on every fibre of the original point blowdown. -/
theorem constant_on_fibres_of_constant_on_exceptional
    (hx : IsClosed ({x} : Set X)) {T : Scheme.{u}} (q : B.Y ⟶ T)
    (hc : (Set.range (pullback.fst B.map (X.fromSpecResidueField x) ≫ q)).Subsingleton) :
    ∀ z₁ z₂ : B.Y, B.map z₁ = B.map z₂ → q z₁ = q z₂ := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  intro z₁ z₂ hz
  by_cases h₁ : B.map z₁ = x
  · have h₂ : B.map z₂ = x := hz.symm.trans h₁
    have hz₁ : z₁ ∈ Set.range (pullback.fst B.map (X.fromSpecResidueField x)) := by
      rw [range_exceptionalFst]
      exact h₁
    have hz₂ : z₂ ∈ Set.range (pullback.fst B.map (X.fromSpecResidueField x)) := by
      rw [range_exceptionalFst]
      exact h₂
    obtain ⟨e₁, rfl⟩ := hz₁
    obtain ⟨e₂, rfl⟩ := hz₂
    exact hc ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
  · have ha : B.map z₁ ∉ ((X.fromSpecResidueField x).ker.support : Set X) := by
      rw [Hom.support_ker, range_fromSpecResidueField, hx.closure_eq]
      exact h₁
    have hb : B.map z₂ ∉ ((X.fromSpecResidueField x).ker.support : Set X) := by
      rwa [← hz]
    exact congrArg q (B.map_injective_away ha hb hz)

/-- An actual map contracting the literal exceptional fibre descends uniquely
along the specified point blowdown. Normality, local Noetherianity and the
centre's being nongeneric construct the blowdown hypotheses internally. -/
theorem existsUnique_factor_of_constant_on_exceptional
    [IsIntegral X] [IsLocallyNoetherian X] (hX : NormalStalks X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X)
    {T : Scheme.{u}} (q : B.Y ⟶ T)
    (hc : (Set.range (pullback.fst B.map (X.fromSpecResidueField x) ≫ q)).Subsingleton) :
    ∃! q₀ : X ⟶ T, B.map ≫ q₀ = q := by
  have hI := genericPoint_not_mem_pointCentre x hx hne
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsIso B.map.c := isIso_c_of_isProper_birational B.map hX (B.functionFieldMap_isIso hI)
  exact existsUnique_factor_of_isProper_of_isIso_c B.map q
    (constant_on_fibres_of_constant_on_exceptional x B hx q hc)

/-- In an actual square of point blowdowns, a noncontracted source exceptional
fibre forces the original source centre to map to the original target centre. -/
theorem centre_eq_of_exceptional_nonconstant {Y : Scheme.{u}}
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (C : BlowupDatum (Y.fromSpecResidueField y).ker)
    (h : X ⟶ Y) (q : B.Y ⟶ C.Y) (hsq : q ≫ C.map = B.map ≫ h)
    (hc : ¬(Set.range (pullback.fst B.map (X.fromSpecResidueField x) ≫ q)).Subsingleton) :
    h x = y := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  by_contra hxy
  apply hc
  rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
  have him (z : ↑(pullback B.map (X.fromSpecResidueField x))) :
      C.map (q (pullback.fst B.map (X.fromSpecResidueField x) z)) = h x := by
    have hs := congrArg (fun k => k (pullback.fst B.map (X.fromSpecResidueField x) z)) hsq
    simpa only [Hom.comp_apply, exceptionalFst_map] using hs
  apply C.map_injective_away
  · rw [Hom.support_ker, range_fromSpecResidueField, hy.closure_eq]
    change C.map (q (pullback.fst B.map (X.fromSpecResidueField x) a')) ≠ y
    rwa [him]
  · rw [Hom.support_ker, range_fromSpecResidueField, hy.closure_eq]
    change C.map (q (pullback.fst B.map (X.fromSpecResidueField x) b')) ≠ y
    rwa [him]
  · exact (him a').trans (him b').symm

end Blowup

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

namespace Blowup

/-- The actual exceptional map in a commuting square of two original point
blowdowns. Its second projection uses the original residue-field map. -/
def exceptionalMapOfPointSquare {X Y : Scheme.{u}} (x : X) (y : Y)
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (C : BlowupDatum (Y.fromSpecResidueField y).ker)
    (h : X ⟶ Y) (q : B.Y ⟶ C.Y) (hsq : q ≫ C.map = B.map ≫ h)
    (hxy : h x = y) :
    pullback B.map (X.fromSpecResidueField x) ⟶
      pullback C.map (Y.fromSpecResidueField y) := by
  subst y
  refine pullback.lift
    (pullback.fst B.map (X.fromSpecResidueField x) ≫ q)
    (pullback.snd B.map (X.fromSpecResidueField x) ≫ Spec.map (h.residueFieldMap x)) ?_
  simp only [Category.assoc]
  rw [hsq, ← Category.assoc, pullback.condition, Category.assoc,
    h.SpecMap_residueFieldMap_fromSpecResidueField]

@[reassoc]
theorem exceptionalMapOfPointSquare_fst {X Y : Scheme.{u}} (x : X) (y : Y)
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (C : BlowupDatum (Y.fromSpecResidueField y).ker)
    (h : X ⟶ Y) (q : B.Y ⟶ C.Y) (hsq : q ≫ C.map = B.map ≫ h)
    (hxy : h x = y) :
    exceptionalMapOfPointSquare x y B C h q hsq hxy ≫
        pullback.fst C.map (Y.fromSpecResidueField y) =
      pullback.fst B.map (X.fromSpecResidueField x) ≫ q := by
  subst y
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem exceptionalMapOfPointSquare_snd {X Y : Scheme.{u}} (x : X)
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (h : X ⟶ Y)
    (C : BlowupDatum (Y.fromSpecResidueField (h x)).ker)
    (q : B.Y ⟶ C.Y) (hsq : q ≫ C.map = B.map ≫ h) :
    exceptionalMapOfPointSquare x (h x) B C h q hsq rfl ≫
        pullback.snd C.map (Y.fromSpecResidueField (h x)) =
      pullback.snd B.map (X.fromSpecResidueField x) ≫ Spec.map (h.residueFieldMap x) :=
  pullback.lift_snd _ _ _

end Blowup

private theorem isDominant_of_nonconstant_curve
    {E D : Scheme.{u}} [IsIntegral E] [IsIntegral D]
    (g : E ⟶ D) (hd : topologicalKrullDim D ≤ 1)
    (hn : ¬(Set.range g).Subsingleton) : IsDominant g := by
  have hη : g (genericPoint E) = genericPoint D := by
    rcases DimensionOne.point_eq_generic_or_isClosed D hd (g (genericPoint E)) with he | hc
    · exact he
    · apply False.elim
      apply hn
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
      have heq (z : E) : g z = g (genericPoint E) := by
        have hz := specializes_iff_mem_closure.mp
          ((genericPoint_specializes z).map g.continuous)
        simpa only [hc.closure_eq, Set.mem_singleton_iff] using hz
      exact (heq a').trans (heq b').symm
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure D]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint E, hη⟩)

/-- The actual nonconstant map of an integral curve into a normal curve,
cut out in a proper-birational Cartier square, is an isomorphism. The generic
stalk surjectivity comes from the ambient isomorphism and the original closed
immersion, not from a supplied birationality statement for the curve map. -/
theorem isIso_curveMap_of_cartier_square
    {W B E D : Scheme.{u}} [IsIntegral W] [IsIntegral B]
    [IsIntegral E] [IsIntegral D] [IsLocallyNoetherian B]
    (q : W ⟶ B) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (i : E ⟶ W) (j : D ⟶ B) [IsClosedImmersion i] [IsClosedImmersion j]
    (hJ : Modules.Invertible.IsLocallyRankOne B (Hom.idealModule j))
    (hD : NormalStalks D) (hd : topologicalKrullDim D ≤ 1)
    (g : E ⟶ D) (hsq : g ≫ j = i ≫ q)
    (hn : ¬(Set.range g).Subsingleton) : IsIso g := by
  let : IsDominant g := isDominant_of_nonconstant_curve g hd hn
  let : IsProper (g ≫ j) := by rw [hsq]; infer_instance
  let : IsProper g := IsProper.of_comp g j
  let : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian j
  let := isDiscreteValuationRing_stalk_genericPoint_of_cartier j hJ
  obtain ⟨U, hηU, hqU⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_valuationRing q hff (j (genericPoint D))
  let := hqU
  have hηg := map_genericPoint_of_isDominant E g
  have hηi : q (i (genericPoint E)) = j (genericPoint D) := by
    have h := congrArg (fun k => k (genericPoint E)) hsq
    simpa only [Hom.comp_apply, hηg] using h.symm
  have hiU : q (i (genericPoint E)) ∈ U := by rwa [hηi]
  let : IsIso (q.stalkMap (i (genericPoint E))) :=
    (Arrow.isIso_iff_isIso_of_isIso
      (morphismRestrictStalkMap q U ⟨i (genericPoint E), hiU⟩).hom).mp inferInstance
  have hc : Function.Surjective ((g ≫ j).stalkMap (genericPoint E)) := by
    rw [hsq, Hom.stalkMap_comp]
    exact (i.stalkMap_surjective (genericPoint E)).comp
      (ConcreteCategory.bijective_of_isIso (q.stalkMap (i (genericPoint E)))).surjective
  have hg : Function.Surjective (g.stalkMap (genericPoint E)) := by
    rw [Hom.stalkMap_comp] at hc
    exact Function.Surjective.of_comp hc
  have hgff : IsIso (CommRingCat.ofHom (functionFieldMap g)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨(functionFieldMap g).injective, ?_⟩
    let eη := D.presheaf.stalkCongr (.of_eq hηg.symm)
    change Function.Surjective ((g.stalkMap (genericPoint E)).hom ∘ eη.hom.hom)
    exact hg.comp (ConcreteCategory.bijective_of_isIso eη.hom).surjective
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme)
  intro d
  have hd' : Order.coheight d ≤ 1 := by
    rw [topologicalKrullDim_eq_iSup_stalk] at hd
    have h := (le_iSup (fun z : D => ringKrullDim (D.presheaf.stalk z)) d).trans hd
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  exact exists_isIso_restrict_of_isProper_birational_at_coheight_le_one g hgff hD d hd'

/-- An isomorphism of the actual schemes, compatible with their actual
constant-field maps, identifies the original scalar map when both original
global-function structure maps are isomorphisms. -/
theorem isIso_scalarMap_of_schemeIso
    {K L : Type u} [Field K] [Field L] {E D : Scheme.{u}}
    (pE : E ⟶ Spec (.of K)) (pD : D ⟶ Spec (.of L))
    [IsIso pE.appTop] [IsIso pD.appTop]
    (e : E ≅ D) (σ : CommRingCat.of L ⟶ CommRingCat.of K)
    (hsq : e.hom ≫ pD = pE ≫ Spec.map σ) : IsIso σ := by
  let : IsIso ((pE ≫ Spec.map σ).appTop) := by rw [← hsq, Hom.comp_appTop]; infer_instance
  let : IsIso ((Spec.map σ).appTop ≫ pE.appTop) := by
    simpa only [Hom.comp_appTop] using
      (inferInstance : IsIso ((pE ≫ Spec.map σ).appTop))
  let : IsIso ((Spec.map σ).appTop) :=
    IsIso.of_isIso_comp_right _ pE.appTop
  let : IsIso (σ ≫ (ΓSpecIso (.of K)).inv) := by
    rw [ΓSpecIso_inv_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (ΓSpecIso (.of K)).inv

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem projectiveLine_structure_appTop_isIso
    {K : Type u} [Field K] {E : Scheme.{u}} (p : E ⟶ Spec (.of K))
    (ε : Over.mk p ≅ Over.mk
      (AlgebraicGeometry.ProjectiveSpace.toSpec K (ULift.{u} (Fin 2)))) : IsIso p.appTop := by
  let t := AlgebraicGeometry.ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))
  let : IsIso ((ΓSpecIso (.of K)).inv ≫ t.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (AlgebraicGeometry.ProjectiveSpace.globalFunctionsCoefficient_bijective K (ULift.{u} (Fin 2)))
  let : IsIso t.appTop := IsIso.of_isIso_comp_left (ΓSpecIso (.of K)).inv t.appTop
  let e := (Over.forget _).mapIso ε
  have he : e.hom ≫ t = p := ε.hom.w
  rw [← he, Hom.comp_appTop]
  infer_instance

/-- The original map of the two centre fields is an isomorphism, as follows
from the original projective-line constant maps and the actual curve isomorphism. -/
theorem scalarMap_isIso_of_projectiveLineIso
    {K L : Type u} [Field K] [Field L] {E D : Scheme.{u}}
    (pE : E ⟶ Spec (.of K)) (pD : D ⟶ Spec (.of L))
    (εE : Over.mk pE ≅ Over.mk
      (AlgebraicGeometry.ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))))
    (εD : Over.mk pD ≅ Over.mk
      (AlgebraicGeometry.ProjectiveSpace.toSpec L (ULift.{u} (Fin 2))))
    (e : E ≅ D) (σ : CommRingCat.of L ⟶ CommRingCat.of K)
    (hsq : e.hom ≫ pD = pE ≫ Spec.map σ) : IsIso σ := by
  let := projectiveLine_structure_appTop_isIso pE εE
  let := projectiveLine_structure_appTop_isIso pD εD
  exact isIso_scalarMap_of_schemeIso pE pD e σ hsq

/-- The conormal comparison for exceptional lines over their two original
fields. The actual compatible field map is proved invertible from constants;
base change of the original O(1) then supplies the same-field comparison. -/
theorem conormalMap_isIso_of_isProper_birational_projectiveLines
    {K L : Type u} [Field K] [Field L] {W B E D : Scheme.{u}}
    [IsIntegral W] [IsIntegral B] [IsLocallyNoetherian B]
    (q : W ⟶ B) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (i : E ⟶ W) (j : D ⟶ B) [IsClosedImmersion j]
    (hI : Modules.Invertible.IsLocallyRankOne W (Hom.idealModule i))
    (hJ : Modules.Invertible.IsLocallyRankOne B (Hom.idealModule j))
    (e : E ≅ D) (h : e.hom ≫ j = i ≫ q)
    (pE : E ⟶ Spec (.of K)) (pD : D ⟶ Spec (.of L))
    (σ : CommRingCat.of L ⟶ CommRingCat.of K)
    (he : e.hom ≫ pD = pE ≫ Spec.map σ)
    (εE : Over.mk pE ≅ Over.mk
      (AlgebraicGeometry.ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))))
    (εD : Over.mk pD ≅ Over.mk
      (AlgebraicGeometry.ProjectiveSpace.toSpec L (ULift.{u} (Fin 2))))
    (aE : (Modules.pullback εE.hom.left).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf K (ULift.{u} (Fin 2)) 1) ≅
      (Modules.pullback i).obj (Hom.idealModule i))
    (aD : (Modules.pullback εD.hom.left).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf L (ULift.{u} (Fin 2)) 1) ≅
      (Modules.pullback j).obj (Hom.idealModule j)) :
    IsIso ((Modules.pullback i).map (Hom.idealPullbackMap j i q e.hom h)) := by
  let : IsIso σ := scalarMap_isIso_of_projectiveLineIso pE pD εE εD e σ he
  let m := AlgebraicGeometry.ProjectiveSpace.map σ.hom (ULift.{u} (Fin 2))
  let : IsIso m := (AlgebraicGeometry.ProjectiveSpace.isPullback_map σ.hom
    (ULift.{u} (Fin 2))).isIso_fst_of_isIso
  let eE := (Over.forget _).mapIso εE ≪≫ asIso m
  have heE : eE.hom ≫ AlgebraicGeometry.ProjectiveSpace.toSpec L (ULift.{u} (Fin 2)) =
      pE ≫ Spec.map σ := by
    change (εE.hom.left ≫ m) ≫ _ = _
    rw [Category.assoc, AlgebraicGeometry.ProjectiveSpace.map_toSpec, ← Category.assoc]
    exact congrArg (fun t : E ⟶ Spec (.of K) => t ≫ Spec.map σ) εE.hom.w
  let εE' : Over.mk (pE ≫ Spec.map σ) ≅
      Over.mk (AlgebraicGeometry.ProjectiveSpace.toSpec L (ULift.{u} (Fin 2))) :=
    Over.isoMk eE heE
  let aE' : (Modules.pullback εE'.hom.left).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf L (ULift.{u} (Fin 2)) 1) ≅
      (Modules.pullback i).obj (Hom.idealModule i) :=
    ((Modules.pullbackComp εE.hom.left m).app _).symm ≪≫
      (Modules.pullback εE.hom.left).mapIso
        (AlgebraicGeometry.ProjectiveSpace.twistingPullbackIso σ.hom (ULift.{u} (Fin 2)) 1) ≪≫ aE
  exact conormalMap_isIso_of_isProper_birational_projectiveLine q hff i j hI hJ e h
    (pE ≫ Spec.map σ) pD he εE' εD aE' aD

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem preimage_range_eq_of_isIso_restrict
    {W B E D : Scheme.{u}} (q : W ⟶ B) (i : E ⟶ W) (j : D ⟶ B)
    (g : E ⟶ D) [Surjective g] (hsq : g ≫ j = i ≫ q)
    (V : B.Opens) (hV : Set.range j ⊆ V) [IsIso (q ∣_ V)] :
    q ⁻¹' Set.range j = Set.range i := by
  ext w
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨e, rfl⟩ := g.surjective d
    have he : q (i e) = j (g e) :=
      (congrArg (fun k => k e) hsq).symm
    have hwV : q w ∈ V := by rw [← hd]; exact hV ⟨g e, rfl⟩
    have hiV : q (i e) ∈ V := by rw [he]; exact hV ⟨g e, rfl⟩
    have hh : (q ∣_ V) ⟨i e, hiV⟩ = (q ∣_ V) ⟨w, hwV⟩ := by
      apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using he.trans hd
    have hew : i e = w := congrArg Subtype.val ((q ∣_ V).isOpenEmbedding.injective hh)
    exact ⟨e, hew⟩
  · rintro ⟨e, rfl⟩
    exact ⟨g e, congrArg (fun k => k e) hsq⟩

namespace Blowup

/-- An isomorphism neighborhood of the whole target exceptional fibre forces
the original intermediate fibre to be a singleton. The original source
blowdown's surjectivity is retained explicitly. -/
theorem preimage_centre_subsingleton_of_exceptional_isomorphism
    {X Y : Scheme.{u}} (x : X) (y : Y)
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (C : BlowupDatum (Y.fromSpecResidueField y).ker) [Surjective B.map]
    (h : X ⟶ Y) (q : B.Y ⟶ C.Y) (hsq : q ≫ C.map = B.map ≫ h)
    (g : pullback B.map (X.fromSpecResidueField x) ⟶
      pullback C.map (Y.fromSpecResidueField y)) [Surjective g]
    (hg : g ≫ pullback.fst C.map (Y.fromSpecResidueField y) =
      pullback.fst B.map (X.fromSpecResidueField x) ≫ q)
    (V : C.Y.Opens)
    (hV : Set.range (pullback.fst C.map (Y.fromSpecResidueField y)) ⊆ V)
    [IsIso (q ∣_ V)] : (h ⁻¹' {y}).Subsingleton := by
  have hp := preimage_range_eq_of_isIso_restrict q
    (pullback.fst B.map (X.fromSpecResidueField x))
    (pullback.fst C.map (Y.fromSpecResidueField y)) g hg V hV
  have hf (z : X) (hz : h z = y) : z = x := by
    obtain ⟨w, hw⟩ := B.map.surjective z
    have hqw : q w ∈ Set.range (pullback.fst C.map (Y.fromSpecResidueField y)) := by
      rw [range_exceptionalFst]
      change C.map (q w) = y
      have he := congrArg (fun k => k w) hsq
      exact he.trans ((congrArg h hw).trans hz)
    have hwE : w ∈ Set.range (pullback.fst B.map (X.fromSpecResidueField x)) := by
      rw [← hp]
      exact hqw
    obtain ⟨e, rfl⟩ := hwE
    exact hw.symm.trans (exceptionalFst_map x B e)
  intro z hz z' hz'
  exact (hf z hz).trans (hf z' hz').symm

end Blowup

private theorem finite_preimage_singleton_of_surjective_composite
    {Z X Y : Scheme.{u}} (a : Z ⟶ X) [Surjective a] (f : X ⟶ Y) (y : Y)
    (h : ((a ≫ f) ⁻¹' {y}).Subsingleton) : (f ⁻¹' {y}).Finite := by
  apply Set.Subsingleton.finite
  intro x hx x' hx'
  obtain ⟨z, rfl⟩ := a.surjective x
  obtain ⟨z', rfl⟩ := a.surjective x'
  exact congrArg a (h hx hx')

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Blowup.BlowupDatum

variable {X : Scheme.{u}} [IsIntegral X] {I : X.IdealSheafData} (B : BlowupDatum I)

/-- A lift of an actual dominant map through the original blowup is dominant.
The generic fibre of that blowdown has one point, by the original away map. -/
theorem isDominant_lift (hI : genericPoint X ∉ (I.support : Set X))
    {W : Scheme.{u}} [IsIntegral W]
    (f : W ⟶ X) [IsDominant f] (q : W ⟶ B.Y) (hsq : q ≫ B.map = f) : IsDominant q := by
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
  have hb := map_genericPoint_of_isDominant B.Y B.map
  have hq : B.map (q (genericPoint W)) = genericPoint X := by
    have h := congrArg (fun k => k (genericPoint W)) hsq
    exact h.trans (map_genericPoint_of_isDominant W f)
  have hη : q (genericPoint W) = genericPoint B.Y :=
    B.map_injective_away (by rwa [hq]) (by rwa [hb]) (hq.trans hb.symm)
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure B.Y]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint W, hη⟩)

/-- The original lifted function-field map is an isomorphism when the original
composite is birational. The actual blowdown field map is cancelled. -/
theorem functionFieldMap_lift_isIso (hI : genericPoint X ∉ (I.support : Set X))
    {W : Scheme.{u}} [IsIntegral W]
    (f : W ⟶ X) [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (q : W ⟶ B.Y) (hsq : q ≫ B.map = f) :
    let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
    let : IsDominant q := B.isDominant_lift hI f q hsq
    IsIso (CommRingCat.ofHom (functionFieldMap q)) := by
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
  let : IsDominant q := B.isDominant_lift hI f q hsq
  let : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) := B.functionFieldMap_isIso hI
  have hc : IsIso (CommRingCat.ofHom (functionFieldMap (q ≫ B.map))) := by
    simpa only [hsq] using hff
  rw [functionFieldMap_comp, CommRingCat.ofHom_comp] at hc
  let := hc
  exact IsIso.of_isIso_comp_left (CommRingCat.ofHom (functionFieldMap B.map))
    (CommRingCat.ofHom (functionFieldMap q))

end AlgebraicGeometry.Scheme.Blowup.BlowupDatum

namespace AlgebraicGeometry.Scheme

private theorem normalStalks_of_regularStalks {X : Scheme.{u}}
    (hX : RegularStalks X) : NormalStalks X := by
  intro x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

/-- An original stalk of dimension two cannot be the integral scheme's generic field stalk. -/
theorem ne_genericPoint_of_stalk_dimension_two {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

namespace Blowup

open RegularPoint
open OverField.Curve

/-- A nonconstant map on the last exceptional fibre in an original square of
point blowdowns is an isomorphism on a neighborhood of the whole original
target exceptional fibre. Both centre fields and the canonical ideal map
are constructed and compared, rather than supplied as identifications. -/
theorem exists_exceptionalIso_of_pointBlowupSquare_nonconstant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (x : X) (hx : IsClosed ({x} : Set X))
    [IsRegularLocalRing (X.presheaf.stalk x)] (hdx : ringKrullDim (X.presheaf.stalk x) = 2)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hY : RegularStalks Y) (hdy : ringKrullDim (Y.presheaf.stalk y) = 2)
    (h : X ⟶ Y) (q : pointBlowup X x ⟶ pointBlowup Y y)
    [IsProper q] [IsDominant q]
    (hff : let : IsIntegral (pointBlowup X x) :=
        pointBlowup_isIntegral X x hx (ne_genericPoint_of_stalk_dimension_two x hdx)
      let : IsIntegral (pointBlowup Y y) :=
        pointBlowup_isIntegral Y y hy (ne_genericPoint_of_stalk_dimension_two y hdy)
      IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (hsq : q ≫ pointBlowdown Y y = pointBlowdown X x ≫ h)
    (hn : ¬(Set.range (pointExceptionalι X x ≫ q)).Subsingleton) :
    ∃ e : pointExceptionalFibre X x ≅ pointExceptionalFibre Y y,
      e.hom ≫ pointExceptionalι Y y = pointExceptionalι X x ≫ q ∧
      ∃ V : (pointBlowup Y y).Opens,
        Set.range (pointExceptionalι Y y) ⊆ V ∧ IsIso (q ∣_ V) := by
  let : IsIntegral (pointBlowup X x) :=
    pointBlowup_isIntegral X x hx (ne_genericPoint_of_stalk_dimension_two x hdx)
  let : IsIntegral (pointBlowup Y y) :=
    pointBlowup_isIntegral Y y hy (ne_genericPoint_of_stalk_dimension_two y hdy)
  let : IsProper (pointBlowdown Y y) := (pointBlowupDatum Y y).isProper_of_isLocallyNoetherian
  have hxy := centre_eq_of_exceptional_nonconstant x (pointBlowupDatum X x) y hy
    (pointBlowupDatum Y y) h q hsq hn
  subst y
  let : IsRegularLocalRing (Y.presheaf.stalk (h x)) := hY (h x)
  let : IsLocallyNoetherian (pointBlowup Y (h x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointBlowdown Y (h x))
  let E := pointExceptionalFibre X x
  let D := pointExceptionalFibre Y (h x)
  let i := pointExceptionalι X x
  let j := pointExceptionalι Y (h x)
  let pE := pointExceptionalStructureMap X x
  let pD := pointExceptionalStructureMap Y (h x)
  let K := X.residueField x
  let L := Y.residueField (h x)
  let εE₀ := pointExceptionalOverIsoProjectiveP1 X x hx hdx
  let εD₀ := pointExceptionalOverIsoProjectiveP1 Y (h x) hy hdy
  let eE₀ : E ≅ ProjectiveLine.projectiveP1 K := (Over.forget _).mapIso εE₀
  let eD₀ : D ≅ ProjectiveLine.projectiveP1 L := (Over.forget _).mapIso εD₀
  let : IsIntegral E := IsIntegral.of_isIso eE₀.inv
  let : IsIntegral D := IsIntegral.of_isIso eD₀.inv
  have hDsm : SmoothOfRelativeDimension 1 pD := by
    have hw : εD₀.hom.left ≫ (ProjectiveLine.projectiveLineOver L).hom = pD := εD₀.hom.w
    rw [← hw]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1) εD₀.hom.left
      (ProjectiveLine.projectiveLineOver L).hom).mpr
        (ProjectiveLine.projectiveLine_curveProperties L).smooth
  let := hDsm
  let : Smooth pD := SmoothOfRelativeDimension.smooth 1 pD
  have hDnormal : NormalStalks D := smoothFieldNormality L D pD inferInstance
  have hDdim : topologicalKrullDim D ≤ 1 :=
    (smoothFieldDimension L D pD 1 hDsm inferInstance).le
  let : IsClosedImmersion i := pointExceptionalι_isClosedImmersion X x hx
  let : IsClosedImmersion j := pointExceptionalι_isClosedImmersion Y (h x) hy
  let g : E ⟶ D := exceptionalMapOfPointSquare x (h x)
    (pointBlowupDatum X x) (pointBlowupDatum Y (h x)) h q hsq rfl
  have hg : g ≫ j = i ≫ q := exceptionalMapOfPointSquare_fst x (h x)
    (pointBlowupDatum X x) (pointBlowupDatum Y (h x)) h q hsq rfl
  have hgn : ¬(Set.range g).Subsingleton := by
    intro hc
    apply hn
    rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
    have ha := congrArg (fun k => k a') hg
    have hb := congrArg (fun k => k b') hg
    exact ha.symm.trans ((congrArg j (hc ⟨a', rfl⟩ ⟨b', rfl⟩)).trans hb)
  let : IsIso g := isIso_curveMap_of_cartier_square q hff i j
    (pointIdealLine Y (h x) hy).property hDnormal hDdim g hg hgn
  let εE := εE₀ ≪≫ ProjectiveLine.projectiveLineOverIsoNative K
  let εD := εD₀ ≪≫ ProjectiveLine.projectiveLineOverIsoNative L
  have hp : (asIso g).hom ≫ pD = pE ≫ Spec.map (h.residueFieldMap x) :=
    exceptionalMapOfPointSquare_snd x (pointBlowupDatum X x) h
      (pointBlowupDatum Y (h x)) q hsq
  let aE : (Modules.pullback εE.hom.left).obj
      (AlgebraicGeometry.ProjectiveSpace.twistingSheaf K (ULift.{u} (Fin 2)) 1) ≅
        (Modules.pullback i).obj (Hom.idealModule i) :=
    ((Modules.pullbackComp εE₀.hom.left
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso K 2).hom).app _).symm ≪≫
      pointConormalProjectiveP1Iso X x hx hdx
  let aD : (Modules.pullback εD.hom.left).obj
      (AlgebraicGeometry.ProjectiveSpace.twistingSheaf L (ULift.{u} (Fin 2)) 1) ≅
        (Modules.pullback j).obj (Hom.idealModule j) :=
    ((Modules.pullbackComp εD₀.hom.left
      (AlgebraicGeometry.ProjectiveSpace.finUliftIso L 2).hom).app _).symm ≪≫
      pointConormalProjectiveP1Iso Y (h x) hy hdy
  let : IsIso ((Modules.pullback i).map (Hom.idealPullbackMap j i q (asIso g).hom hg)) :=
    conormalMap_isIso_of_isProper_birational_projectiveLines q hff i j
      (pointIdealLine X x hx).property (pointIdealLine Y (h x) hy).property
      (asIso g) hg pE pD (h.residueFieldMap x) hp εE εD aE aD
  refine ⟨asIso g, hg, ?_⟩
  exact exists_isIso_restrict_of_isProper_birational_of_cartier_pullback_isIso q
    (normalStalks_of_regularStalks (RegularPoint.regularStalks_pointBlowup Y hY (h x) hy hdy))
    hff i j ⟨inferInstance, (pointIdealLine X x hx).property⟩
    ⟨inferInstance, (pointIdealLine Y (h x) hy).property⟩ (asIso g) hg


end Blowup

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Blowup

open RegularPoint

/-- An actual finite point-chain resolution of the lift to the target point
blowup can be shortened to length zero. No minimal chain, terminal stage,
exceptional isomorphism or factorization is supplied as input. -/
theorem exists_pointBlowupLift_of_resolution
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hX : RegularStalks X) (hY : RegularStalks Y)
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdy : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hbad : y ∉ f.targetIsomorphismLocus)
    {W : Scheme.{u}} (β : W ⟶ X) (c : PointBlowupChain β)
    (q : W ⟶ pointBlowup Y y) (hsq : q ≫ pointBlowdown Y y = β ≫ f) :
    ∃ f₁ : X ⟶ pointBlowup Y y, f₁ ≫ pointBlowdown Y y = f := by
  classical
  let C := pointBlowupDatum Y y
  have hny := ne_genericPoint_of_stalk_dimension_two y hdy
  have hI := genericPoint_not_mem_pointCentre y hy hny
  let : IsIntegral C.Y := pointBlowup_isIntegral Y y hy hny
  let : IsDominant C.map := pointBlowup_isDominant Y y hy hny
  let : IsProper C.map := C.isProper_of_isLocallyNoetherian
  let P : ℕ → Prop := fun n =>
    ∃ (W₀ : Scheme.{u}) (β₀ : W₀ ⟶ X) (c₀ : PointBlowupChain β₀) (q₀ : W₀ ⟶ C.Y),
      c₀.length = n ∧ q₀ ≫ C.map = β₀ ≫ f
  have hP : ∃ n, P n := ⟨c.length, W, β, c, q, rfl, hsq⟩
  obtain ⟨W₀, β₀, c₀, q₀, hlen₀, hsq₀⟩ := Nat.find_spec hP
  by_cases hzero : c₀.length = 0
  · let : IsIso β₀ := c₀.isIso_of_length_eq_zero hzero
    refine ⟨inv β₀ ≫ q₀, ?_⟩
    rw [Category.assoc, hsq₀, IsIso.inv_hom_id_assoc]
  · obtain ⟨Z, a, d, x, hx, hdx, e, he, hlen⟩ := c₀.exists_last hzero
    let : IsIntegral Z := d.isIntegral inferInstance
    let : IsDominant a := d.isDominant inferInstance
    let : IsProper a := d.isProper inferInstance
    let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian a
    have hZ := d.regularStalks inferInstance hX
    let : IsRegularLocalRing (Z.presheaf.stalk x) := hZ x
    let B := pointBlowupDatum Z x
    have hnx := ne_genericPoint_of_stalk_dimension_two x hdx
    have hIB := genericPoint_not_mem_pointCentre x hx hnx
    let : IsIntegral B.Y := pointBlowup_isIntegral Z x hx hnx
    let : IsDominant B.map := pointBlowup_isDominant Z x hx hnx
    let : IsProper B.map := B.isProper_of_isLocallyNoetherian
    let q' : B.Y ⟶ C.Y := e.inv ≫ q₀
    have hsq' : q' ≫ C.map = B.map ≫ a ≫ f := by
      dsimp only [q']
      rw [Category.assoc, hsq₀, ← he]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    let : IsDominant q' := C.isDominant_lift hI (B.map ≫ a ≫ f) q' hsq'
    let : IsProper (q' ≫ C.map) := by rw [hsq']; infer_instance
    let : IsProper q' := IsProper.of_comp q' C.map
    let : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) := B.functionFieldMap_isIso hIB
    let : IsIso (CommRingCat.ofHom (functionFieldMap a)) := d.functionFieldMap_isIso inferInstance
    let := hff
    have hkff : IsIso (CommRingCat.ofHom (functionFieldMap (B.map ≫ a ≫ f))) := by
      simp only [functionFieldMap_comp, CommRingCat.ofHom_comp]
      infer_instance
    have hqff := C.functionFieldMap_lift_isIso hI (B.map ≫ a ≫ f) hkff q' hsq'
    by_cases hc : (Set.range (pointExceptionalι Z x ≫ q')).Subsingleton
    · obtain ⟨q₁, hq₁, _⟩ := existsUnique_factor_of_constant_on_exceptional x B
        (normalStalks_of_regularStalks hZ) hx hnx q' hc
      let : IsIso B.map.c := isIso_c_of_isProper_birational B.map
        (normalStalks_of_regularStalks hZ) (B.functionFieldMap_isIso hIB)
      obtain ⟨k, hk, huniq⟩ := existsUnique_factor_of_isProper_of_isIso_c B.map
        (B.map ≫ a ≫ f) (fun z z' hz => congrArg (a ≫ f) hz)
      have hq₁c : q₁ ≫ C.map = a ≫ f := by
        apply (huniq (q₁ ≫ C.map) ?_).trans (huniq (a ≫ f) rfl).symm
        rw [← Category.assoc, hq₁]
        exact hsq'
      have hPd : P d.length := ⟨Z, a, d, q₁, rfl, hq₁c⟩
      have hmin := Nat.find_min' hP hPd
      omega
    · obtain ⟨eD, hED, V, hV, hqV⟩ :=
        exists_exceptionalIso_of_pointBlowupSquare_nonconstant x hx hdx y hy hY hdy
          (a ≫ f) q' hqff hsq' hc
      let := hqV
      have hf := preimage_centre_subsingleton_of_exceptional_isomorphism x y B C
        (a ≫ f) q' hsq' eD.hom hED V hV
      obtain ⟨U, hyU, hU⟩ :=
        exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton f
          (normalStalks_of_regularStalks hY) hff y
          (finite_preimage_singleton_of_surjective_composite a f y hf)
      exact False.elim (hbad (f.le_targetIsomorphismLocus U hU hyU))

end AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme.Blowup

open RegularPoint

/-- The already constructed common-domination theorem supplies a concrete
resolution of the original generic lift to an actual point blowup over an
arbitrary affine Noetherian target. -/
theorem exists_pointBlowup_resolution_of_isAffine_target
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian Y] [IsAffine Y]
    (hX : RegularStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdy : ringKrullDim (Y.presheaf.stalk y) = 2) :
    ∃ (W : Scheme.{u}) (β : W ⟶ X) (_c : PointBlowupChain β)
      (q : W ⟶ pointBlowup Y y), q ≫ pointBlowdown Y y = β ≫ f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let C := pointBlowupDatum Y y
  have hny := ne_genericPoint_of_stalk_dimension_two y hdy
  have hI := genericPoint_not_mem_pointCentre y hy hny
  let : IsIntegral C.Y := pointBlowup_isIntegral Y y hy hny
  let : IsDominant C.map := pointBlowup_isDominant Y y hy hny
  let : IsProper C.map := C.isProper_of_isLocallyNoetherian
  let : IsIso (CommRingCat.ofHom (functionFieldMap C.map)) := C.functionFieldMap_isIso hI
  let := hff
  let k : C.Y.functionField ⟶ X.functionField :=
    inv (CommRingCat.ofHom (functionFieldMap C.map)) ≫
      CommRingCat.ofHom (functionFieldMap f)
  let gη : Spec X.functionField ⟶ C.Y :=
    Spec.map k ≫ C.Y.fromSpecStalk (genericPoint C.Y)
  let : IsIso k := by dsimp [k]; infer_instance
  let : IsDominant gη := by dsimp [gη]; infer_instance
  have hg : gη ≫ C.map = X.fromSpecStalk (genericPoint X) ≫ f := by
    dsimp only [gη]
    rw [Category.assoc, fromSpecStalk_genericPoint_naturality C.map,
      ← Spec.map_comp_assoc]
    simp only [k, IsIso.hom_inv_id_assoc]
    exact (fromSpecStalk_genericPoint_naturality f).symm
  let R := Γ(Y, ⊤)
  let : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let pX : X ⟶ Spec (.of R) := f ≫ Y.isoSpec.hom
  let pT : C.Y ⟶ Spec (.of R) := C.map ≫ Y.isoSpec.hom
  let : IsProper pT := by dsimp [pT]; infer_instance
  have hgbase : gη ≫ pT = X.fromSpecStalk (genericPoint X) ≫ pX := by
    simpa only [pT, pX, Category.assoc] using congrArg (fun k => k ≫ Y.isoSpec.hom) hg
  obtain ⟨W, β, c, hout⟩ :=
    CommonDomination.exists_pointBlowupChain_extension_to_proper_target R hX hdX pX pT gη hgbase
  let : IsIntegral W := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  obtain ⟨q, j, _, _, _, _, _, _, hbase, _⟩ := hout
  refine ⟨W, β, c, q, ?_⟩
  apply (cancel_mono Y.isoSpec.hom).mp
  simpa only [pX, pT, Category.assoc] using hbase

/-- Over an affine target, every actual bad closed point has the original
point-blowup lift. The concrete resolving chain is produced internally. -/
theorem exists_pointBlowupLift_of_isAffine_target
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian Y] [IsAffine Y]
    (hX : RegularStalks X) (hY : RegularStalks Y) (hdX : topologicalKrullDim X ≤ 2)
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdy : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hbad : y ∉ f.targetIsomorphismLocus) :
    ∃ f₁ : X ⟶ pointBlowup Y y, f₁ ≫ pointBlowdown Y y = f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨W, β, c, q, hsq⟩ :=
    exists_pointBlowup_resolution_of_isAffine_target hX hdX f hff y hy hdy
  exact exists_pointBlowupLift_of_resolution hX hY f hff y hy hdy hbad β c q hsq

end AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme

private theorem functionFieldMap_restrict_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Surjective f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] [Surjective (f ∣_ U)] :
    IsIso (CommRingCat.ofHom (functionFieldMap (f ∣_ U))) := by
  let : IsDominant U.ι := isDominant_of_isOpenImmersion U.ι
  let : IsDominant (f ⁻¹ᵁ U).ι := isDominant_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  let : IsIso (CommRingCat.ofHom (functionFieldMap U.ι)) := FunctionField.fieldMap_isIso U.ι
  let : IsIso (CommRingCat.ofHom (functionFieldMap (f ⁻¹ᵁ U).ι)) :=
    FunctionField.fieldMap_isIso (f ⁻¹ᵁ U).ι
  let := hff
  have hc' : IsIso (CommRingCat.ofHom (functionFieldMap ((f ⁻¹ᵁ U).ι ≫ f))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  have hc : IsIso (CommRingCat.ofHom (functionFieldMap ((f ∣_ U) ≫ U.ι))) := by
    simpa only [morphismRestrict_ι] using hc'
  rw [functionFieldMap_comp, CommRingCat.ofHom_comp] at hc
  let := hc
  exact IsIso.of_isIso_comp_left (CommRingCat.ofHom (functionFieldMap U.ι)) _

private theorem not_mem_targetIsomorphismLocus_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (y : U.toScheme)
    (hy : U.ι y ∉ f.targetIsomorphismLocus) : y ∉ (f ∣_ U).targetIsomorphismLocus := by
  intro h
  let L := (f ∣_ U).targetIsomorphismLocus
  have hL : IsIso (f ∣_ U ∣_ L) := (f ∣_ U).isIso_restrict_targetIsomorphismLocus
  have hUL : IsIso (f ∣_ U.ι ''ᵁ L) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f U L)).mp hL
  apply hy
  exact f.le_targetIsomorphismLocus _ hUL ⟨y, h, rfl⟩

namespace Blowup

/-- Open restriction preserves the original residue-field point ideal,
through the canonical residue-field map of the open immersion. -/
theorem pointCentre_comap_open {X : Scheme.{u}} (U : X.Opens) (x : U.toScheme)
    (hx : IsClosed ({U.ι x} : Set X)) :
    (X.fromSpecResidueField (U.ι x)).ker.comap U.ι = (U.toScheme.fromSpecResidueField x).ker := by
  let : IsClosedImmersion (X.fromSpecResidueField (U.ι x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have H : IsPullback (U.toScheme.fromSpecResidueField x)
      (Spec.map (U.ι.residueFieldMap x)) U.ι (X.fromSpecResidueField (U.ι x)) :=
    IsPullback.of_vert_isIso_mono ⟨(U.ι.SpecMap_residueFieldMap_fromSpecResidueField x).symm⟩
  calc
    _ = (pullback.fst U.ι (X.fromSpecResidueField (U.ι x))).ker :=
      (IdealSheafData.ker_fst_of_isClosedImmersion _ _).symm
    _ = (U.toScheme.fromSpecResidueField x).ker := by
      simpa only [Hom.ker_comp_of_isIso] using
        congrArg Hom.ker H.isoPullback_hom_fst

/-- A lift on an actual open neighborhood of the entire inverse-image centre
extends to the original blowup. On the complementary open the ideal is the
unit ideal, and the two maps agree by that original universal property. -/
theorem BlowupDatum.exists_lift_of_neighborhood
    {X Y : Scheme.{u}} {I : Y.IdealSheafData} (B : BlowupDatum I)
    (f : X ⟶ Y) (V : X.Opens) (hV : ((I.comap f).support : Set X) ⊆ V)
    (qV : V.toScheme ⟶ B.Y) (hqV : qV ≫ B.map = V.ι ≫ f) :
    ∃ q : X ⟶ B.Y, q ≫ B.map = f := by
  let W := centreComplement (I.comap f)
  have hW : cartierPullback I (W.ι ≫ f) := by
    apply cartier_of_comap_eq_top
    rw [IdealSheafData.comap_comp]
    exact BlowupDatum.comap_eq_top_of_disjoint W (centreComplement_disjoint (I.comap f))
  let qW := B.lift (W.ι ≫ f) hW
  let O : Bool → X.Opens := fun b => if b then V else W
  have hO : IsOpenCover O := by
    apply top_le_iff.mp
    intro x _
    apply Opens.mem_iSup.mpr
    by_cases hx : x ∈ V
    · exact ⟨true, hx⟩
    · exact ⟨false, fun hc => hx (hV hc)⟩
  let a : ∀ b : Bool, (O b).toScheme ⟶ B.Y := fun b => by
    cases b
    · exact qW
    · exact qV
  have ha (b : Bool) : a b ≫ B.map = (O b).ι ≫ f := by
    cases b
    · exact B.lift_map _ _
    · exact hqV
  have hcompat (b b' : Bool) : pullback.fst ((O b).ι) ((O b').ι) ≫ a b =
      pullback.snd ((O b).ι) ((O b').ι) ≫ a b' := by
    cases b with
    | false =>
      have hf := cartierPullback_comp_of_flat I (W.ι ≫ f) hW
        (pullback.fst ((O false).ι) ((O b').ι))
      apply B.hom_ext hf
      · simp only [Category.assoc, ha]
        rfl
      · rw [Category.assoc, ha, ← Category.assoc, ← pullback.condition, Category.assoc]
        rfl
    | true =>
      cases b' with
      | false =>
        have hf := cartierPullback_comp_of_flat I (W.ι ≫ f) hW
          (pullback.snd ((O true).ι) ((O false).ι))
        apply B.hom_ext hf
        · rw [Category.assoc, ha true, ← Category.assoc, pullback.condition, Category.assoc]
          rfl
        · simp only [Category.assoc, ha]
          rfl
      | true =>
        have hh : pullback.fst (O true).ι (O true).ι =
            pullback.snd (O true).ι (O true).ι :=
          (cancel_mono ((O true).ι)).mp pullback.condition
        rw [hh]
  let C := X.openCoverOfIsOpenCover O hO
  refine ⟨C.glueMorphisms a hcompat, ?_⟩
  apply C.hom_ext
  intro b
  rw [← Category.assoc, C.ι_glueMorphisms, ha]
  rfl

end Blowup

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Blowup

open RegularPoint

private theorem exists_pointBlowupLift_on_affineOpen
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (hX : RegularStalks X) (hY : RegularStalks Y) (hdX : topologicalKrullDim X ≤ 2)
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdy : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hbad : y ∉ f.targetIsomorphismLocus)
    (U : Y.Opens) (hU : IsAffineOpen U) (hyU : y ∈ U) :
    ∃ q : (f ⁻¹ᵁ U).toScheme ⟶ pointBlowup Y y,
      q ≫ pointBlowdown Y y = (f ⁻¹ᵁ U).ι ≫ f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let yU : U.toScheme := ⟨y, hyU⟩
  let : Nonempty U := ⟨yU⟩
  let : IsAffine U.toScheme := hU
  let : IsNoetherian U.toScheme := ⟨⟩
  let V := f ⁻¹ᵁ U
  let : Nonempty V := by
    obtain ⟨x, hx⟩ := f.surjective y
    exact ⟨⟨x, by change f x ∈ U; rwa [hx]⟩⟩
  have hyUclosed : IsClosed ({yU} : Set U.toScheme) := by
    have hh : U.ι ⁻¹' ({y} : Set Y) = {yU} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [← hh]
    exact hy.preimage U.ι.continuous
  have hdU : ringKrullDim (U.toScheme.presheaf.stalk yU) = 2 :=
    (ringKrullDim_eq_of_ringEquiv
      (asIso (U.ι.stalkMap yU)).commRingCatIsoToRingEquiv).symm.trans hdy
  let : Surjective (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : Surjective f) U
  let : IsProper (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsProper f) U
  have hffU := functionFieldMap_restrict_isIso f hff U
  have hbadU : yU ∉ (f ∣_ U).targetIsomorphismLocus :=
    not_mem_targetIsomorphismLocus_restrict f U yU hbad
  obtain ⟨qU, hqU⟩ := exists_pointBlowupLift_of_isAffine_target
    (hX.of_isOpenImmersion V.ι) (hY.of_isOpenImmersion U.ι)
    ((V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdX)
    (f ∣_ U) hffU yU hyUclosed hdU hbadU
  let I := (Y.fromSpecResidueField y).ker
  let B := pointBlowupDatum Y y
  let B₀ := pointBlowupDatum U.toScheme yU
  have hI : I.comap U.ι = (U.toScheme.fromSpecResidueField yU).ker :=
    pointCentre_comap_open U yU hy
  let b : B₀.Y ⟶ B.Y := BaseChange.map U.ι hI B B₀
  have hb : b ≫ B.map = B₀.map ≫ U.ι := BaseChange.map_triangle U.ι hI B B₀
  refine ⟨qU ≫ b, ?_⟩
  rw [Category.assoc, hb, ← Category.assoc, hqU]
  exact morphismRestrict_ι f U

/-- A proper birational morphism from a regular surface factors through the
original point blowup at each actual bad closed target point. The affine
resolution is constructed internally, and the resulting map is glued on the
original source with the universal lift off the original centre. -/
theorem exists_pointBlowupLift
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (hX : RegularStalks X) (hY : RegularStalks Y) (hdX : topologicalKrullDim X ≤ 2)
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdy : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hbad : y ∉ f.targetIsomorphismLocus) :
    ∃ f₁ : X ⟶ pointBlowup Y y, f₁ ≫ pointBlowdown Y y = f := by
  obtain ⟨U, hU, hyU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨qU, hqU⟩ :=
    exists_pointBlowupLift_on_affineOpen hX hY hdX f hff y hy hdy hbad U hU hyU
  let I := (Y.fromSpecResidueField y).ker
  let B := pointBlowupDatum Y y
  let V := f ⁻¹ᵁ U
  have hV : ((I.comap f).support : Set X) ⊆ V := by
    let : IsClosedImmersion (Y.fromSpecResidueField y) :=
      isClosed_singleton_iff_isClosedImmersion.mp hy
    intro x hx
    rw [IdealSheafData.support_comap] at hx
    change f x ∈ ((Y.fromSpecResidueField y).ker.support : Set Y) at hx
    rw [Hom.support_ker, range_fromSpecResidueField, hy.closure_eq,
      Set.mem_singleton_iff] at hx
    change f x ∈ U
    rwa [hx]
  exact B.exists_lift_of_neighborhood f V hV qU hqU

end AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme

open Blowup Blowup.RegularPoint

private theorem pointBlowupChain_factorization_induction
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : RegularStalks X) (hdX : topologicalKrullDim X ≤ 2) (n : ℕ) :
    ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
      (_hY : RegularStalks Y) (_hdY : topologicalKrullDim Y ≤ 2)
      (f : X ⟶ Y) [IsProper f] [IsDominant f]
      (_hff : IsIso (CommRingCat.ofHom (functionFieldMap f))),
      contractedCurveCount f = n →
      ∃ (Z : Scheme.{u}) (β : Z ⟶ Y) (_c : PointBlowupChain β) (e : X ≅ Z),
        e.hom ≫ β = f := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y hIY hNY hY hdY f hPf hDf hff hn
    by_cases hIso : IsIso f
    · let := hIso
      exact ⟨Y, 𝟙 Y, .refl Y, asIso f, Category.comp_id f⟩
    · have hbad : ∃ y : Y, y ∉ f.targetIsomorphismLocus := by
        by_contra hall
        have hall' : ∀ y : Y, y ∈ f.targetIsomorphismLocus := by
          simpa only [not_exists, not_not] using hall
        apply hIso
        apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
          (P := .isomorphisms Scheme)
        intro y
        exact ⟨f.targetIsomorphismLocus, hall' y, f.isIso_restrict_targetIsomorphismLocus⟩
      obtain ⟨y, hybad⟩ := hbad
      have hYN := normalStalks_of_regularStalks hY
      have hy := f.isClosed_singleton_of_not_mem_targetIsomorphismLocus hff hYN hdY y hybad
      have hdy := f.stalk_dimension_eq_two_of_not_mem_targetIsomorphismLocus hff hYN hdY y hybad
      obtain ⟨f₁, hf₁⟩ := exists_pointBlowupLift hX hY hdX f hff y hy hdy hybad
      let B := pointBlowupDatum Y y
      have hne := ne_genericPoint_of_stalk_dimension_two y hdy
      have hcentre := genericPoint_not_mem_pointCentre y hy hne
      let : IsIntegral B.Y := pointBlowup_isIntegral Y y hy hne
      let : IsDominant B.map := pointBlowup_isDominant Y y hy hne
      let : IsProper B.map := B.isProper_of_isLocallyNoetherian
      let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
      let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
      let : IsNoetherian B.Y := ⟨⟩
      let : IsDominant f₁ := B.isDominant_lift hcentre f f₁ hf₁
      let : IsProper (f₁ ≫ B.map) := by rw [hf₁]; infer_instance
      let : IsProper f₁ := IsProper.of_comp f₁ B.map
      have hff₁ := B.functionFieldMap_lift_isIso hcentre f hff f₁ hf₁
      have hregB := RegularPoint.regularStalks_pointBlowup Y hY y hy hdy
      have hdimY : ∀ z : Y, ringKrullDim (Y.presheaf.stalk z) ≤ 2 := by
        rw [topologicalKrullDim_eq_iSup_stalk] at hdY
        intro z
        exact (le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) z).trans hdY
      have hdimB : topologicalKrullDim B.Y ≤ 2 := by
        rw [topologicalKrullDim_eq_iSup_stalk]
        exact iSup_le (pointBlowup_stalk_dimension_le_two hY hdimY y hy hdy)
      have hlt : contractedCurveCount f₁ < n := by
        have hc := contractedCurveCount_lt_pointBlowup hY hdX hdY y hy hdy f₁ hff₁
        rwa [hf₁, hn] at hc
      obtain ⟨Z, β, c, e, he⟩ := ih (contractedCurveCount f₁) hlt hregB hdimB f₁ hff₁ rfl
      refine ⟨Z, β ≫ B.map, .cons y hy hdy β c, e, ?_⟩
      rw [← Category.assoc, he, hf₁]

/-- A proper dominant birational morphism between integral Noetherian regular
schemes of dimension at most two factors as an actual point-blowup chain,
up to an explicit isomorphism of its original source. The isomorphism's
composition with the literal chain is exactly the original morphism. -/
theorem exists_pointBlowupChain_factorization
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (hX : RegularStalks X) (hY : RegularStalks Y)
    (hdX : topologicalKrullDim X ≤ 2) (hdY : topologicalKrullDim Y ≤ 2)
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    ∃ (Z : Scheme.{u}) (β : Z ⟶ Y) (_c : PointBlowupChain β) (e : X ≅ Z),
      e.hom ≫ β = f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  exact pointBlowupChain_factorization_induction X hX hdX (contractedCurveCount f)
    hY hdY f hff rfl

private theorem functionFieldMap_isIso_of_birationalOver
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (h : BirationalOver f (𝟙 Y)) :
    IsIso (CommRingCat.ofHom (functionFieldMap f)) := by
  obtain ⟨p, hp⟩ := h
  let : Nonempty p.source := Set.nonempty_coe_sort.mpr p.dense_source.nonempty
  let : Nonempty p.target := Set.nonempty_coe_sort.mpr p.dense_target.nonempty
  let : IsDominant p.source.ι := isDominant_of_isOpenImmersion p.source.ι
  let : IsDominant p.target.ι := isDominant_of_isOpenImmersion p.target.ι
  have hsq : p.source.ι ≫ f = p.iso.hom ≫ p.target.ι := by
    simpa only [PartialIso.IsOver, Category.comp_id] using Eq.symm hp
  let : IsIso (CommRingCat.ofHom (functionFieldMap p.source.ι)) :=
    FunctionField.fieldMap_isIso p.source.ι
  let : IsIso (CommRingCat.ofHom (functionFieldMap p.target.ι)) :=
    FunctionField.fieldMap_isIso p.target.ι
  let : IsIso (CommRingCat.ofHom (functionFieldMap p.iso.hom)) :=
    FunctionField.fieldMap_isIso p.iso.hom
  have hc' : IsIso (CommRingCat.ofHom (functionFieldMap (p.iso.hom ≫ p.target.ι))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  have hc : IsIso (CommRingCat.ofHom (functionFieldMap (p.source.ι ≫ f))) := by
    simpa only [hsq] using hc'
  rw [functionFieldMap_comp, CommRingCat.ofHom_comp] at hc
  let := hc
  exact IsIso.of_isIso_comp_right _ (CommRingCat.ofHom (functionFieldMap p.source.ι))

/-- The same actual factorization with the native dense partial-isomorphism
witness over the original morphism as its birationality premise. -/
theorem exists_pointBlowupChain_factorization_of_birationalOver
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (hX : RegularStalks X) (hY : RegularStalks Y)
    (hdX : topologicalKrullDim X ≤ 2) (hdY : topologicalKrullDim Y ≤ 2)
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (h : BirationalOver f (𝟙 Y)) :
    ∃ (Z : Scheme.{u}) (β : Z ⟶ Y) (_c : PointBlowupChain β) (e : X ≅ Z),
      e.hom ≫ β = f :=
  exists_pointBlowupChain_factorization hX hY hdX hdY f
    (functionFieldMap_isIso_of_birationalOver f h)

end AlgebraicGeometry.Scheme
