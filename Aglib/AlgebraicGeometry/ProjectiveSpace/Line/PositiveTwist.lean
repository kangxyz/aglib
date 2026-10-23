/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Geometry
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Curves.Picard.TorsionSections
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial
public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.RingTheory.MvPolynomial.DegreeOne

/-!
# Positive twists from actual embeddings of the projective line

The original divisor degree classifies actual line bundles on native P1 over
every field. Genus-zero Riemann–Roch and the proved degree-zero section theorem
give injectivity; the actual homogeneous degree-one basis gives degree O(1)=1.

For an actual closed projective embedding, Serre vanishing applied to O(-2)
forces the pullback of O(1) to have strictly positive degree. The resulting
comparison is an actual module-sheaf isomorphism on the original projective
line. No twist comparison, algebraic closure, or representability is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Line

/-- The original native projective line with its fixed lifted coordinate type. -/
abbrev nativeP1 (k : Type u) [Field k] : Scheme.{u} :=
  ProjectiveSpace k (ULift.{u} (Fin 2))

/-- The same native line over its original field. -/
abbrev nativeP1Over (k : Type u) [Field k] : Scheme.OverField.FScheme k :=
  Over.mk (toSpec k (ULift.{u} (Fin 2)))

variable (k : Type u) [Field k]

/-- The canonical original polynomial-line comparison, over the same field. -/
def literalIsoNative : Scheme.ProjectiveLine.projectiveP1 k ≅ nativeP1 k :=
  (Over.forget _).mapIso
    (Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative k)

/-- The proved reciprocal two-chart line compared with the same native projective line. -/
def reciprocalIsoNative : Scheme.PinchedLine.lineGluing k ≅ nativeP1 k :=
  Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k ≪≫ literalIsoNative k

/-- Native P1 is integral, through its original polynomial charts. -/
instance nativeIntegral : IsIntegral (nativeP1 k) :=
  IsIntegral.of_isIso (reciprocalIsoNative k).hom

/-- The original native projective line is Noetherian over every field. -/
instance nativeNoetherian : IsNoetherian (nativeP1 k) := by
  let : CompactSpace (nativeP1 k) := QuasiCompact.compactSpace_of_compactSpace
    (toSpec k (ULift.{u} (Fin 2)))
  exact ⟨⟩

/-- The actual topological dimension of native P1 is one. -/
theorem nativeDimension : topologicalKrullDim (nativeP1 k) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (reciprocalIsoNative k).hom.homeomorph.isHomeomorph).symm.trans
      (Scheme.PinchedLine.line_dimension_eq_one k)

/-- Every original closed stalk of native P1 is a discrete valuation ring. -/
instance nativeClosedDVR (x : Scheme.ClosedPoint (nativeP1 k)) :
    IsDiscreteValuationRing ((nativeP1 k).presheaf.stalk x.val) :=
  Scheme.PinchedLine.closedStalk_dvr_of_isoLine
    (reciprocalIsoNative k).symm x.val x.property

/-- The actual coherent genus of native P1 over the original field is zero. -/
theorem nativeGenusZero : coherentGenus k (nativeP1Over k) = 0 :=
  (coherentGenus_iso
    (Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative k)).symm.trans
      (Scheme.OverField.Curve.ProjectiveLine.projectiveLine_coherentGenus_zero k)

/-- Properness uses the original native structure map. -/
instance nativeProper : IsProper (nativeP1Over k).hom :=
  inferInstanceAs (IsProper (toSpec k (ULift.{u} (Fin 2))))

/-- The original structural constants map of native P1 is bijective. -/
theorem nativeConstants : Function.Bijective (constants (nativeP1Over k)) := by
  let e := Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative k
  have hlocal := @constants_bijective_of_proper_geometricallyIntegral k _
    (Scheme.OverField.Curve.ProjectiveLine.projectiveLineOver k)
    (Scheme.ProjectiveLine.structureMap_proper k)
    (curveProperties_geometricallyIntegral smoothFieldNormality normalComponentsOpen
      (Scheme.OverField.Curve.ProjectiveLine.projectiveLine_curveProperties k))
  have heq : (literalIsoNative k).hom.appTop ∘ constants (nativeP1Over k) =
      constants (Scheme.OverField.Curve.ProjectiveLine.projectiveLineOver k) := by
    funext a
    exact map_constants e.hom a
  have hcomp : Function.Bijective
      ((literalIsoNative k).hom.appTop ∘ constants (nativeP1Over k)) := by
    rw [heq]
    exact hlocal
  let : IsIso (literalIsoNative k).hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso ((literalIsoNative k).op)).isIso_hom
  exact hcomp.of_comp_left
    (ConcreteCategory.bijective_of_isIso (literalIsoNative k).hom.appTop).1

/-- The proved proper-curve product formula for the original native P1 divisors. -/
theorem nativeProductFormula :
    Picard.Degree.PrincipalProductFormula (nativeP1 k) (toSpec k (ULift.{u} (Fin 2))) :=
  Picard.Degree.properCurveProductFormula k (nativeP1 k) (toSpec k (ULift.{u} (Fin 2)))
    (nativeDimension k)

/-- Dimension of actual cohomology with the explicitly constructed original field action. -/
def cohomologyDimension (M : (nativeP1 k).Modules) (q : ℕ) : ℕ := by
  letI := moduleCohomologyModule (nativeP1Over k) M q
  exact Module.finrank k (moduleCohomology k (nativeP1Over k) M q)

/-- The existing residue-weighted Picard degree on the same native projective line. -/
def degreeHom : PicardGroup (nativeP1 k) →+ ℤ :=
  Picard.Degree.picardDegree (nativeP1 k) (toSpec k (ULift.{u} (Fin 2)))
    (nativeDimension k).le (nativeProductFormula k)

/-- Degree of an actual line bundle, retaining the original structural field action. -/
def degree (L : LineBundle (nativeP1 k)) : ℤ := degreeHom k (classOf (nativeP1 k) L)

/-- Genus-zero Riemann–Roch for the actual line bundle and original cohomology modules. -/
theorem riemannRoch (L : LineBundle (nativeP1 k)) :
    (cohomologyDimension k L.val 0 : ℤ) - cohomologyDimension k L.val 1 = degree k L + 1 := by
  let : IsIntegral (nativeP1Over k).left := nativeIntegral k
  let : IsNoetherian (nativeP1Over k).left := nativeNoetherian k
  let (x : ClosedPoint (nativeP1Over k).left) :
      IsDiscreteValuationRing ((nativeP1Over k).left.presheaf.stalk x.val) := nativeClosedDVR k x
  have h := lineBundleRiemannRoch k (nativeP1Over k) (nativeDimension k).le
    (nativeProductFormula k) L inferInstance (nativeConstants k)
  change (cohomologyDimension k L.val 0 : ℤ) - cohomologyDimension k L.val 1 =
    degree k L + 1 - (coherentGenus k (nativeP1Over k) : ℤ) at h
  simpa only [nativeGenusZero, Nat.cast_zero, sub_zero] using h

/-- Degree zero forces an actual native P1 line bundle to be trivial. -/
theorem class_eq_zero_of_degree_eq_zero (L : LineBundle (nativeP1 k)) (hL : degree k L = 0) :
    classOf (nativeP1 k) L = 0 := by
  have hrr := riemannRoch k L
  rw [hL] at hrr
  let := moduleCohomologyModule (nativeP1Over k) L.val 0
  have hpos : 0 < Module.finrank k (moduleCohomology k (nativeP1Over k) L.val 0) := by
    change 0 < cohomologyDimension k L.val 0
    omega
  let : Nontrivial (moduleCohomology k (nativeP1Over k) L.val 0) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k (nativeP1Over k) L.val 0)
  have hsection : moduleH0Equiv (nativeP1Over k) L.val s ≠ 0 := by
    intro h
    exact hs ((moduleH0Equiv (nativeP1Over k) L.val).injective (h.trans (map_zero _).symm))
  obtain ⟨e⟩ := Picard.TorsionSections.lineBundle_trivial_of_nonzero_section
    (nativeP1 k) (toSpec k (ULift.{u} (Fin 2))) (nativeDimension k).le (nativeProductFormula k)
    L hL (moduleH0Equiv (nativeP1Over k) L.val s) hsection
  exact Quotient.sound ⟨e ≪≫ (coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit (nativeP1 k).ringCatSheaf)).symm⟩

/-- The original degree distinguishes all actual line-bundle classes on native P1. -/
theorem degreeHom_injective : Function.Injective (degreeHom k) := by
  have hzero : ∀ a : PicardGroup (nativeP1 k), degreeHom k a = 0 → a = 0 := by
    intro a
    induction a using Quotient.inductionOn with
    | h L => exact class_eq_zero_of_degree_eq_zero k L
  intro a b hab
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hab, sub_self]

section TwistClasses

variable (R : Type u) [CommRing R] (I : Type u)

/-- Actual integer twists, with their native tensor multiplication, define Picard classes. -/
def twistClassHom : ℤ →+ PicardGroup (ProjectiveSpace R I) where
  toFun d := classOf _ (twistingLineBundle R I d)
  map_zero' := Quotient.sound ⟨twistingZeroIso R I ≪≫
    (coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit (ProjectiveSpace R I).ringCatSheaf)).symm⟩
  map_add' a b := Quotient.sound ⟨(twistingTensorIso R I a b).symm⟩

@[simp] theorem twistClassHom_apply (d : ℤ) :
    twistClassHom R I d = classOf _ (twistingLineBundle R I d) := rfl

/-- Integer twist classes are the actual integer multiples of the original O(1) class. -/
theorem twistClassHom_eq_zsmul (d : ℤ) :
    twistClassHom R I d = d • classOf _ (twistingLineBundle R I 1) := by
  simpa only [zsmul_eq_mul, mul_one, Int.cast_id, twistClassHom_apply] using
    map_zsmul (twistClassHom R I) d (1 : ℤ)

end TwistClasses

/-- The original degree-one homogeneous coordinate basis gives degree O(1)=1. -/
theorem degree_twist_one : degree k (twistingLineBundle k (ULift.{u} (Fin 2)) 1) = 1 := by
  let M := twistingSheaf k (ULift.{u} (Fin 2)) 1
  let := moduleCohomologyModule (nativeP1Over k) M 0
  let e : moduleCohomology k (nativeP1Over k) M 0 ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k 1 :=
    (moduleH0Equiv (nativeP1Over k) M).trans
      (twistingGlobalSectionsPolynomialLinearEquiv k (ULift.{u} (Fin 2)) ⟨0⟩ 1)
  have hzero : cohomologyDimension k M 0 = 2 := by
    change Module.finrank k (moduleCohomology k (nativeP1Over k) M 0) = 2
    rw [e.finrank_eq, Module.finrank_eq_card_basis
      (MvPolynomial.homogeneousDegreeOneBasis k (ULift.{u} (Fin 2)))]
    simp only [Fintype.card_ulift, Fintype.card_fin]
  let : Subsingleton (moduleCohomology k (nativeP1Over k) M 1) :=
    twistingCohomology_subsingleton_of_neg_le_degree k (ULift.{u} (Fin 2))
      1 Equiv.ulift 1 1 (by norm_num) one_ne_zero
  have hone : cohomologyDimension k M 1 = 0 := by
    dsimp only [cohomologyDimension]
    exact Module.finrank_zero_of_subsingleton
  have hrr := riemannRoch k (twistingLineBundle k (ULift.{u} (Fin 2)) 1)
  change (cohomologyDimension k M 0 : ℤ) - cohomologyDimension k M 1 = _ at hrr
  rw [hzero, hone] at hrr
  omega

/-- Every integer native twist has its original integer as divisor degree. -/
theorem degree_twist (d : ℤ) :
    degree k (twistingLineBundle k (ULift.{u} (Fin 2)) d) = d := by
  change degreeHom k (twistClassHom k (ULift.{u} (Fin 2)) d) = d
  rw [twistClassHom_eq_zsmul, map_zsmul]
  change d • degree k (twistingLineBundle k (ULift.{u} (Fin 2)) 1) = d
  rw [degree_twist_one, zsmul_eq_mul, mul_one, Int.cast_id]

/-- Every actual line bundle on native P1 is isomorphic to the twist of its actual degree. -/
theorem exists_iso_twist (L : LineBundle (nativeP1 k)) :
    Nonempty (L.val ≅ twistingSheaf k (ULift.{u} (Fin 2)) (degree k L)) := by
  apply (class_eq_iff (nativeP1 k) L (twistingLineBundle k (ULift.{u} (Fin 2)) (degree k L))).mp
  apply degreeHom_injective k
  exact (degree_twist k (degree k L)).symm

/-- A chosen actual module isomorphism supplied by the proved classification. -/
def lineBundleIsoTwist (L : LineBundle (nativeP1 k)) :
    L.val ≅ twistingSheaf k (ULift.{u} (Fin 2)) (degree k L) :=
  (exists_iso_twist k L).some

theorem degree_tensor (L M : LineBundle (nativeP1 k)) :
    degree k (tensorLineBundle (nativeP1 k) L M) = degree k L + degree k M :=
  map_add (degreeHom k) (classOf (nativeP1 k) L) (classOf (nativeP1 k) M)

variable {I : Type u}

/-- The actual pullback of O(n) has n times the degree of the actual pullback of O(1). -/
theorem degree_pullback_twist (t : (nativeP1 k) ⟶ ProjectiveSpace k I) (d : ℤ) :
    degree k (pullbackLineBundle t (twistingLineBundle k I d)) =
      d * degree k (pullbackLineBundle t (twistingLineBundle k I 1)) := by
  let f : ℤ →+ ℤ := (degreeHom k).comp
    ((PullbackTensor.Local.pullbackHom t).comp (twistClassHom k I))
  have h := map_zsmul f d (1 : ℤ)
  simpa only [zsmul_eq_mul, mul_one, Int.cast_id, f, AddMonoidHom.comp_apply,
    twistClassHom_apply, PullbackTensor.Local.pullbackHom_apply, pullbackClass_classOf,
    degree] using h

/-- Closed immersion forces strict positivity, using actual Serre vanishing with O(-2).
The underlying positivity does not require any additional field-action premise. -/
theorem degree_pullback_twist_one_pos [Finite I]
    (t : (nativeP1 k) ⟶ ProjectiveSpace k I) [IsClosedImmersion t] :
    0 < degree k (pullbackLineBundle t (twistingLineBundle k I 1)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Nonempty I := by
    have hx : t (Classical.choice inferInstance) ∈ ⨆ i : I, coordinateOpen k I i := by
      rw [iSup_coordinateOpen_eq_top]
      trivial
    obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let r := Fintype.card I - 1
  have hcard : Fintype.card I = r + 1 := by
    have := Fintype.card_pos (α := I)
    dsimp only [r]
    omega
  let e : I ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcard
  let F := twistingLineBundle k (ULift.{u} (Fin 2)) (-2)
  let : F.val.IsFinitePresentation := lineBundle_isFinitePresentation (nativeP1 k) F
  obtain ⟨B, hB⟩ := embeddedTensorTwist_serreVanishing t r e F.val
    (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation F.val)
  let Q := tensorLineBundle (nativeP1 k)
    (pullbackLineBundle t (twistingLineBundle k I (B : ℤ))) F
  let : Subsingleton (moduleCohomology k (nativeP1Over k) Q.val 1) := hB B le_rfl 1 one_ne_zero
  let := moduleCohomologyModule (nativeP1Over k) Q.val 1
  have hzero : cohomologyDimension k Q.val 1 = 0 := by
    dsimp only [cohomologyDimension]
    exact Module.finrank_zero_of_subsingleton
  have hrr := riemannRoch k Q
  rw [hzero, Nat.cast_zero, sub_zero] at hrr
  change (cohomologyDimension k Q.val 0 : ℤ) =
    degree k (tensorLineBundle (nativeP1 k)
      (pullbackLineBundle t (twistingLineBundle k I (B : ℤ)))
      (twistingLineBundle k (ULift.{u} (Fin 2)) (-2))) + 1 at hrr
  rw [degree_tensor, degree_pullback_twist, degree_twist] at hrr
  by_contra h
  have hmul := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg B) (le_of_not_gt h)
  have hdim := Int.natCast_nonneg (cohomologyDimension k Q.val 0)
  omega

/-- An actual closed immersion from the same native P1 has a positive actual O(d) pullback. -/
theorem exists_positiveTwist_of_isClosedImmersion [Finite I]
    (t : (nativeP1 k) ⟶ ProjectiveSpace k I) [IsClosedImmersion t] :
    ∃ d : ℕ, 0 < d ∧ Nonempty ((Scheme.Modules.pullback t).obj (twistingSheaf k I 1) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) := by
  let L := pullbackLineBundle t (twistingLineBundle k I 1)
  have hpos : 0 < degree k L := degree_pullback_twist_one_pos k t
  have hnat : ((degree k L).toNat : ℤ) = degree k L := Int.toNat_of_nonneg hpos.le
  refine ⟨(degree k L).toNat, by omega, ?_⟩
  rw [hnat]
  exact ⟨lineBundleIsoTwist k L⟩

/-- The original over-k embedding supplies the positive twist without changing its base triangle. -/
theorem exists_positiveTwist [Finite I]
    (t : (nativeP1Over k) ⟶ Over.mk (toSpec k I)) [IsClosedImmersion t.left] :
    ∃ d : ℕ, 0 < d ∧ Nonempty ((Scheme.Modules.pullback t.left).obj (twistingSheaf k I 1) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) :=
  exists_positiveTwist_of_isClosedImmersion k t.left

/-- Transport the proved positive comparison to a specified actual line bundle. -/
theorem exists_positiveTwist_of_comparison [Finite I]
    (t : (nativeP1Over k) ⟶ Over.mk (toSpec k I)) [IsClosedImmersion t.left]
    (L : LineBundle (nativeP1 k))
    (e : (Scheme.Modules.pullback t.left).obj (twistingSheaf k I 1) ≅ L.val) :
    ∃ d : ℕ, 0 < d ∧ Nonempty (L.val ≅ twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ)) := by
  obtain ⟨d, hd, ⟨e'⟩⟩ := exists_positiveTwist k t
  exact ⟨d, hd, ⟨e.symm ≪≫ e'⟩⟩

end AlgebraicGeometry.ProjectiveSpace.Line
