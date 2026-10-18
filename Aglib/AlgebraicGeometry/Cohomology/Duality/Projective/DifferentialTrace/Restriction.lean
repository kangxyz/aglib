/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.DifferentialTrace
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.Naturality
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange

/-!
# The original differential projective trace under open base change

For an actual ring homomorphism whose map on spectra is open, the installed relative
Kähler-differential pullback isomorphism and the original exterior-power descent give the
coefficient arrow on top relative forms. On the same original geometric cohomology map,
the unchanged projective trace commutes with the ring homomorphism. The old normalized
residue class maps to the old residue class with the original coefficient transported.

The proof retains the native geometric Cech map, its product projections and the original
cycles quotient. It computes the enumerated scalar, inverse-ratio product and differential
wedge, and then applies the original Laurent trace normalization. No new trace equivalence
is selected. The coordinate enumeration supplies finiteness internally; arbitrary rings,
dimension zero and zero coefficient rings are included.
-/


noncomputable section

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials HomologicalComplex
open TopologicalSpace

universe u

private def wedgeAt (X : Scheme.{u}) (N : X.Modules) (n : ℕ) (U : X.Opens) :
    Γ(N, U) [⋀^Fin n]→ₗ[Γ(X, U)] Γ(moduleExteriorPower X N n, U) :=
  (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf N n).app (op U)

private theorem wedgeAt_naturality (X : Scheme.{u}) (N : X.Modules) (n : ℕ)
    {U V : X.Opens} (p : U ⟶ V) (s : Fin n → Γ(N, V)) :
    (moduleExteriorPower X N n).presheaf.map p.op (wedgeAt X N n V s) =
      wedgeAt X N n U (fun i => N.presheaf.map p.op (s i)) :=
  SheafOfModulesOfCommRing.exteriorPowerMk_naturality X.sheaf N n p.op s

private def coefficientSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (x : Γ(M, U)) : Γ(N, g ⁻¹ᵁ U) := (φ.app U).hom x

private theorem coefficientSection_add {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (x y : Γ(M, U)) :
    coefficientSection (M := M) (N := N) g φ U (x + y) =
      coefficientSection (M := M) (N := N) g φ U x +
        coefficientSection (M := M) (N := N) g φ U y :=
  map_add (φ.app U).hom x y

private theorem coefficientSection_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (r : Γ(Y, U)) (x : Γ(M, U)) :
    coefficientSection (M := M) (N := N) g φ U (r • x) =
      g.app U r • coefficientSection (M := M) (N := N) g φ U x :=
  (φ.val.app' (op U)).hom.map_smul r x

private def exteriorCoefficientAlternating {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (n : ℕ) :
    PresheafOfModulesOfCommRing.AlternatingMap M.val
      ((Scheme.Modules.pushforward g).obj (moduleExteriorPower X N n)).val n where
  app U := {
    toFun := fun v => wedgeAt X N n (g ⁻¹ᵁ U.unop)
      (coefficientSection (M := M) (N := N) g φ U.unop ∘ v)
    map_update_add' := fun v i x y => by
      change wedgeAt X N n (g ⁻¹ᵁ U.unop)
        (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i (x + y)) =
        wedgeAt X N n (g ⁻¹ᵁ U.unop)
          (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i x) +
          wedgeAt X N n (g ⁻¹ᵁ U.unop)
            (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i y)
      simp only [Function.comp_update]
      rw [coefficientSection_add (M := M) (N := N) g φ]
      exact (wedgeAt X N n (g ⁻¹ᵁ U.unop)).map_update_add _ i _ _
    map_update_smul' := fun v i r x => by
      change wedgeAt X N n (g ⁻¹ᵁ U.unop)
        (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i (r • x)) =
        g.app U.unop r • wedgeAt X N n (g ⁻¹ᵁ U.unop)
          (coefficientSection (M := M) (N := N) g φ U.unop ∘ Function.update v i x)
      simp only [Function.comp_update]
      rw [coefficientSection_smul (M := M) (N := N) g φ]
      exact (wedgeAt X N n (g ⁻¹ᵁ U.unop)).map_update_smul _ i _ _
    map_eq_zero_of_eq' := fun v i j h hij =>
      (wedgeAt X N n (g ⁻¹ᵁ U.unop)).map_eq_zero_of_eq _
          (congrArg (coefficientSection (M := M) (N := N) g φ U.unop) h) hij }
  naturality {U V} p s := by
    change (moduleExteriorPower X N n).presheaf.map
        ((Opens.map g.base).map p.unop).op
        (wedgeAt X N n (g ⁻¹ᵁ U.unop)
          (coefficientSection (M := M) (N := N) g φ U.unop ∘ s)) =
      wedgeAt X N n (g ⁻¹ᵁ V.unop)
        (fun i => coefficientSection (M := M) (N := N) g φ V.unop (M.presheaf.map p (s i)))
    rw [wedgeAt_naturality]
    congr 1
    funext i
    exact (PresheafOfModules.naturality_apply φ.val p (s i)).symm

private def exteriorCoefficientMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (n : ℕ) :
    moduleExteriorPower Y M n ⟶ (Scheme.Modules.pushforward g).obj (moduleExteriorPower X N n) :=
  SheafOfModulesOfCommRing.exteriorPowerDesc Y.sheaf M _ n
    (exteriorCoefficientAlternating (M := M) (N := N) g φ n)

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]

local instance projectiveBaseOpen_isOpen : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
  MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance

/-- The installed differential pullback isomorphism for the original open base square. -/
@[expose] public def differentialBaseOpenPullbackIso :
    (Scheme.Modules.pullback (ProjectiveSpace.map σ ι)).obj
        (relativeDifferentialSheaf (toSpec R ι)) ≅
      relativeDifferentialSheaf (toSpec A ι) := by
  letI : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  exact relativeDifferentialPullbackOpenSquareIso (toSpec R ι) (ProjectiveSpace.map σ ι)
    (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι)

/-- The original module-pullback adjoint of the installed differential isomorphism. -/
@[expose] public def differentialBaseOpenCoefficient :
    relativeDifferentialSheaf (toSpec R ι) ⟶
      (Scheme.Modules.pushforward (ProjectiveSpace.map σ ι)).obj
        (relativeDifferentialSheaf (toSpec A ι)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (ProjectiveSpace.map σ ι)).homEquiv _ _
    (differentialBaseOpenPullbackIso σ ι).hom

/-- The same coefficient arrow is the original open-restriction adjunct. -/
public theorem differentialBaseOpenCoefficient_eq_restrict :
    letI : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
    differentialBaseOpenCoefficient σ ι =
      (Scheme.Modules.restrictAdjunction (ProjectiveSpace.map σ ι)).homEquiv _ _
        (relativeDifferentialOpenSquareIso (toSpec R ι) (ProjectiveSpace.map σ ι)
          (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))
          (ProjectiveSpace.map_toSpec σ ι)).hom := by
  let g := ProjectiveSpace.map σ ι
  let L := Scheme.Modules.restrictAdjunction g
  let L' := Scheme.Modules.pullbackPushforwardAdjunction g
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app L L'
    (relativeDifferentialSheaf (toSpec R ι))
  change L.homEquiv _ _ ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app
    (relativeDifferentialSheaf (toSpec R ι))) =
      L'.unit.app (relativeDifferentialSheaf (toSpec R ι)) at h
  have h' := L.homEquiv_naturality_right
    ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app
      (relativeDifferentialSheaf (toSpec R ι))) (differentialBaseOpenPullbackIso σ ι).hom
  rw [h] at h'
  have hcomp := relativeDifferentialPullbackOpenSquareIso_hom_restrict
    (toSpec R ι) g (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))
      (ProjectiveSpace.map_toSpec σ ι)
  change _ = L.homEquiv _ _ _
  rw [← hcomp]
  exact h'.symm

/-- The actual coefficient arrow carries the original differential to its pullback differential. -/
public theorem differentialBaseOpenCoefficient_d (U : (ProjectiveSpace R ι).Opens)
    (a : Γ(ProjectiveSpace R ι, U)) :
    (differentialBaseOpenCoefficient σ ι).val.app (op U)
        ((relativeDifferentialDerivation (toSpec R ι)).d a) =
      (relativeDifferentialDerivation (toSpec A ι)).d
        ((ProjectiveSpace.map σ ι).app U a) := by
  let g := ProjectiveSpace.map σ ι
  rw [differentialBaseOpenCoefficient_eq_restrict, Adjunction.homEquiv_unit]
  change (relativeDifferentialOpenSquareIso (toSpec R ι) g (toSpec A ι)
      (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι)).hom.val.app
        (op (g ⁻¹ᵁ U))
        ((relativeDifferentialSheaf (toSpec R ι)).val.map
          (homOfLE (g.image_preimage_le U)).op
          ((relativeDifferentialDerivation (toSpec R ι)).d a)) = _
  rw [← relativeDifferentialDerivation_restrict]
  erw [relativeDifferentialOpenSquareIso_hom_d]
  congr 1
  have h := ConcreteCategory.congr_hom (g.app_appIso_inv U) a
  change (g.appIso (g ⁻¹ᵁ U)).inv (g.app U a) =
    (ProjectiveSpace R ι).presheaf.map (homOfLE (g.image_preimage_le U)).op a at h
  rw [← h]
  exact ConcreteCategory.congr_hom (g.appIso (g ⁻¹ᵁ U)).inv_hom_id (g.app U a)

/-- The original exterior-power descent of the actual differential coefficient arrow. -/
public def differentialTopBaseOpenCoefficient (n : ℕ) :
    moduleExteriorPower (ProjectiveSpace R ι) (relativeDifferentialSheaf (toSpec R ι)) n ⟶
      (Scheme.Modules.pushforward (ProjectiveSpace.map σ ι)).obj
        (moduleExteriorPower (ProjectiveSpace A ι) (relativeDifferentialSheaf (toSpec A ι)) n) :=
  exteriorCoefficientMap (M := relativeDifferentialSheaf (toSpec R ι))
    (N := relativeDifferentialSheaf (toSpec A ι))
    (ProjectiveSpace.map σ ι) (differentialBaseOpenCoefficient σ ι) n

/-- The actual exterior coefficient arrow preserves the original wedge of all sections. -/
public theorem differentialTopBaseOpenCoefficient_wedge (n : ℕ)
    (U : (ProjectiveSpace R ι).Opens)
    (s : Fin n → Γ(relativeDifferentialSheaf (toSpec R ι), U)) :
    (differentialTopBaseOpenCoefficient σ ι n).app U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
          (relativeDifferentialSheaf (toSpec R ι)) n).app (op U) s) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace A ι).sheaf
          (relativeDifferentialSheaf (toSpec A ι)) n).app
        (op (ProjectiveSpace.map σ ι ⁻¹ᵁ U))
        (fun i => (differentialBaseOpenCoefficient σ ι).app U (s i)) := by
  change (SheafOfModulesOfCommRing.exteriorPowerDesc (ProjectiveSpace R ι).sheaf
      (relativeDifferentialSheaf (toSpec R ι)) _ n
      (exteriorCoefficientAlternating
        (M := relativeDifferentialSheaf (toSpec R ι))
        (N := relativeDifferentialSheaf (toSpec A ι))
        (ProjectiveSpace.map σ ι) (differentialBaseOpenCoefficient σ ι) n)).val.app (op U)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
          (relativeDifferentialSheaf (toSpec R ι)) n).app (op U) s) = _
  exact SheafOfModulesOfCommRing.exteriorPowerDesc_mk (ProjectiveSpace R ι).sheaf
    (relativeDifferentialSheaf (toSpec R ι))
    ((Scheme.Modules.pushforward (ProjectiveSpace.map σ ι)).obj
      (moduleExteriorPower (ProjectiveSpace A ι) (relativeDifferentialSheaf (toSpec A ι)) n))
    n (exteriorCoefficientAlternating
      (M := relativeDifferentialSheaf (toSpec R ι))
      (N := relativeDifferentialSheaf (toSpec A ι))
      (ProjectiveSpace.map σ ι) (differentialBaseOpenCoefficient σ ι) n) (op U) s

/-- The actual exterior coefficient arrow preserves the original wedge of differentials. -/
public theorem differentialTopBaseOpenCoefficient_wedge_d (n : ℕ)
    (U : (ProjectiveSpace R ι).Opens) (s : Fin n → Γ(ProjectiveSpace R ι, U)) :
    (differentialTopBaseOpenCoefficient σ ι n).app U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
          (relativeDifferentialSheaf (toSpec R ι)) n).app (op U)
            (fun i => (relativeDifferentialDerivation (toSpec R ι)).d (s i))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace A ι).sheaf
          (relativeDifferentialSheaf (toSpec A ι)) n).app
        (op (ProjectiveSpace.map σ ι ⁻¹ᵁ U))
          (fun i => (relativeDifferentialDerivation (toSpec A ι)).d
            ((ProjectiveSpace.map σ ι).app U (s i))) := by
  rw [differentialTopBaseOpenCoefficient_wedge]
  congr 1
  funext i
  exact differentialBaseOpenCoefficient_d σ ι U (s i)

end AlgebraicGeometry.Scheme.Cohomology

end

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open TopologicalSpace Opposite MvPolynomial
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)

private theorem projectiveMap_chart_section (i : ι) (z : coordinateRing R ι i) :
    (ProjectiveSpace.map σ ι).appLE (coordinateOpen R ι i) (coordinateOpen A ι i)
        (by rw [ProjectiveSpace.map_preimage_coordinateOpen])
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i) z) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι A) (MvPolynomial.X i)
        (coordinateRingMap σ ι i z) := by
  have H (x : MvPolynomial ι A) (hx : x = MvPolynomial.gradedMap σ (MvPolynomial.X i)) :
      (ProjectiveSpace.map σ ι).appLE
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i))
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι A) x)
          (by change _ ≤ Proj.basicOpen _ (MvPolynomial.gradedMap σ (MvPolynomial.X i)); rw [← hx])
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i) z) =
        Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι A) x
          (HomogeneousLocalization.map (MvPolynomial.gradedMap σ)
            (P := Submonoid.powers (MvPolynomial.X (R := R) i)) (Q := Submonoid.powers x)
            (by rintro _ ⟨k, rfl⟩; exact ⟨k, by simp [hx]⟩) z) := by
    subst x
    exact ConcreteCategory.congr_hom
      (Proj.awayToSection_comp_appLE (MvPolynomial.gradedMap (ι := ι) σ)
        (by rw [MvPolynomial.irrelevant_map_gradedMap]) (MvPolynomial.isHomogeneous_X R i)) z
  exact H (MvPolynomial.X i) (by simp)

private theorem projectiveMap_chart_ratio (i j : ι) :
    (ProjectiveSpace.map σ ι).appLE (coordinateOpen R ι i) (coordinateOpen A ι i)
        (by rw [ProjectiveSpace.map_preimage_coordinateOpen])
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
          (coordinateRatio R ι i j)) =
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι A) (MvPolynomial.X i)
        (coordinateRatio A ι i j) := by
  rw [projectiveMap_chart_section, coordinateRingMap_ratio]

private theorem projectiveMap_ratio_appLE (i j : ι)
    (U : (ProjectiveSpace R ι).Opens) (V : (ProjectiveSpace A ι).Opens)
    (h : V ≤ ProjectiveSpace.map σ ι ⁻¹ᵁ U)
    (hi : U ≤ coordinateOpen R ι i) (hiA : V ≤ coordinateOpen A ι i) :
    (ProjectiveSpace.map σ ι).appLE U V h (eulerCoordinateRatio R ι i j hi) =
      eulerCoordinateRatio A ι i j hiA := by
  let g := ProjectiveSpace.map σ ι
  let z := Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
    (coordinateRatio R ι i j)
  let hc : coordinateOpen A ι i ≤ g ⁻¹ᵁ coordinateOpen R ι i := by
    rw [ProjectiveSpace.map_preimage_coordinateOpen]
  have h₁ := ConcreteCategory.congr_hom (g.map_appLE h (homOfLE hi).op) z
  have h₂ := ConcreteCategory.congr_hom (g.appLE_map hc (homOfLE hiA).op) z
  have h₃ := congrArg (sectionRestrict (ProjectiveSpace A ι) hiA)
    (projectiveMap_chart_ratio σ ι i j)
  rw [eulerCoordinateRatio_eq_fraction R ι i j hi,
    eulerCoordinateRatio_eq_fraction A ι i j hiA]
  exact h₁.trans (h₂.symm.trans h₃)

private theorem projectiveMap_constant_appLE
    (U : (ProjectiveSpace R ι).Opens) (V : (ProjectiveSpace A ι).Opens)
    (h : V ≤ ProjectiveSpace.map σ ι ⁻¹ᵁ U) (r : R) :
    (ProjectiveSpace.map σ ι).appLE U V h
        (globalRestriction (ProjectiveSpace R ι) U
          (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r)) =
      globalRestriction (ProjectiveSpace A ι) V
        (((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) (σ r)) := by
  let g := ProjectiveSpace.map σ ι
  have hs := moduleSectionsBaseChangeScalars g (toSpec A ι) (toSpec R ι) σ
    (ProjectiveSpace.map_toSpec σ ι)
  have hr := RingHom.congr_fun hs r
  change g.appTop (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r) =
    ((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) (σ r) at hr
  change (ProjectiveSpace A ι).presheaf.map (homOfLE h).op
      (g.app U (globalRestriction (ProjectiveSpace R ι) U
        (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r))) = _
  rw [app_globalRestriction, hr, map_globalRestriction]

private theorem projectiveMap_transition_appLE (i j : ι)
    (U : (ProjectiveSpace R ι).Opens) (V : (ProjectiveSpace A ι).Opens)
    (h : V ≤ ProjectiveSpace.map σ ι ⁻¹ᵁ U)
    (hi : U ≤ coordinateOpen R ι i) (hj : U ≤ coordinateOpen R ι j)
    (hiA : V ≤ coordinateOpen A ι i) (hjA : V ≤ coordinateOpen A ι j) :
    (ProjectiveSpace.map σ ι).appLE U V h (coordinateTransitionOn R ι i j hi hj).val =
      (coordinateTransitionOn A ι i j hiA hjA).val := by
  have hr : eulerCoordinateRatio R ι j i hj = (coordinateTransitionOn R ι i j hi hj).val := by
    simpa only [eulerCoordinateRatio_self, mul_one] using
      eulerCoordinateRatio_transition_reverse R ι i j i hi hj
  have ha : eulerCoordinateRatio A ι j i hjA = (coordinateTransitionOn A ι i j hiA hjA).val := by
    simpa only [eulerCoordinateRatio_self, mul_one] using
      eulerCoordinateRatio_transition_reverse A ι i j i hiA hjA
  rw [← hr, ← ha]
  exact projectiveMap_ratio_appLE σ ι j i U V h hj hjA

end

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
variable {R A : Type u} [CommRing R] [CommRing A]

private theorem forget_homologyπ (S : ShortComplex (ModuleCat.{u} R)) :
    (S.map (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).homologyπ ≫
        (S.mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).hom =
      (S.mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map S.homologyπ := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    Category.assoc]
  change _ ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  rw [← Functor.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
    Functor.map_comp]
  rw [Category.assoc]

private theorem forget_cycles_inv_i (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ) (c : C.cycles n) :
    (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C).iCycles n
        (((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv c) =
      (C.iCycles n) c := by
  let e := (C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  have h := ConcreteCategory.congr_hom
    ((C.sc n).mapCyclesIso_hom_iCycles (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) (e.inv c)
  change (C.iCycles n) (e.hom (e.inv c)) = _ at h
  rw [Iso.inv_hom_id_apply] at h
  exact h.symm

private theorem forget_homologyπ_inv (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ) (c : C.cycles n) :
    ((C.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv
        ((C.homologyπ n) c) =
      (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℕ)).obj C).homologyπ n
        (((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv c) := by
  let e := (C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  let h := (C.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  have hp := ConcreteCategory.congr_hom (forget_homologyπ (C.sc n)) (e.inv c)
  change h.hom (_ ) = (C.homologyπ n) (e.hom (e.inv c)) at hp
  rw [Iso.inv_hom_id_apply] at hp
  have hh := congrArg h.inv hp
  rw [Iso.hom_inv_id_apply] at hh
  exact hh.symm

private theorem additiveCycleTransport_condition
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (D : CochainComplex (ModuleCat.{u} A) ℕ)
    (a : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) (c : C.cycles n) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map (D.sc n).g
      ((a.f n) ((C.iCycles n) c)) = 0 := by
  let k := (ComplexShape.up ℕ).next n
  have h := ConcreteCategory.congr_hom (a.comm n k) ((C.iCycles n) c)
  have hc := ConcreteCategory.congr_hom (C.iCycles_d n k) c
  change (D.d n k) ((a.f n) ((C.iCycles n) c)) =
    (a.f k) ((C.d n k) ((C.iCycles n) c)) at h
  change (C.d n k) ((C.iCycles n) c) = 0 at hc
  rw [hc, map_zero] at h
  exact h

private def additiveCycleTransport
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (D : CochainComplex (ModuleCat.{u} A) ℕ)
    (a : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) (c : C.cycles n) : D.cycles n :=
  (D.sc n).cyclesMk ((a.f n) ((C.iCycles n) c))
    (additiveCycleTransport_condition C D a n c)

private theorem additiveCycleTransport_i
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (D : CochainComplex (ModuleCat.{u} A) ℕ)
    (a : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) (c : C.cycles n) :
    (D.iCycles n) (additiveCycleTransport C D a n c) = (a.f n) ((C.iCycles n) c) :=
  (D.sc n).i_cyclesMk _ _

private theorem additiveCycleTransport_cycles
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (D : CochainComplex (ModuleCat.{u} A) ℕ)
    (a : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) (c : C.cycles n) :
    cyclesMap a n
        (((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv c) =
      ((D.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).inv
        (additiveCycleTransport C D a n c) := by
  let C' := ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C
  let D' := ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj D
  apply (AddCommGrpCat.mono_iff_injective (D'.iCycles n)).mp inferInstance
  have h := ConcreteCategory.congr_hom (cyclesMap_i a n)
    (((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv c)
  change (D'.iCycles n) (cyclesMap a n _) = (a.f n) ((C'.iCycles n) _) at h
  rw [forget_cycles_inv_i] at h
  rw [h, forget_cycles_inv_i, additiveCycleTransport_i]

private theorem additiveCycleTransport_homologyπ
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (D : CochainComplex (ModuleCat.{u} A) ℕ)
    (a : ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj C ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) (c : C.cycles n) :
    homologyMap a n
        (((C.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv
          ((C.homologyπ n) c)) =
      ((D.sc n).mapHomologyIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).inv
        ((D.homologyπ n) (additiveCycleTransport C D a n c)) := by
  rw [forget_homologyπ_inv C n c,
    forget_homologyπ_inv D n (additiveCycleTransport C D a n c)]
  have h := ConcreteCategory.congr_hom (homologyπ_naturality a n)
    (((C.sc n).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv c)
  simp only [ConcreteCategory.comp_apply] at h
  rw [additiveCycleTransport_cycles] at h
  exact h

open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

section
variable {X Y : Scheme.{u}} (p : X ⟶ Y)
    (α : R →+* Γ(Y, ⊤)) (β : A →+* Γ(X, ⊤))
    {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) {ι : Type u} (U : ι → Y.Opens)

private def moduleGeometricAdditiveMap :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
        (moduleCechComplex Y α M U) ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
        (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)) :=
  (moduleCechForgetIso Y α M U).hom ≫
    additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
      (moduleCoefficientPullback (M := M) (N := N) p φ) ≫
    (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).inv

private def moduleGeometricCycle (n : ℕ) (c : (moduleCechComplex Y α M U).cycles n) :
    (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).cycles n :=
  additiveCycleTransport (moduleCechComplex Y α M U)
    (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i))
    (moduleGeometricAdditiveMap p α β φ U) n c

private theorem moduleGeometricCycle_homology (n : ℕ)
    (c : (moduleCechComplex Y α M U).cycles n) :
    (moduleCechAdditiveHomologyIso X β N (fun i => p ⁻¹ᵁ U i) n).hom
        ((moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).homologyπ n
          (moduleGeometricCycle p α β φ U n c)) =
      homologyMap (additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
        (moduleCoefficientPullback (M := M) (N := N) p φ)) n
          ((moduleCechAdditiveHomologyIso Y α M U n).hom
            ((moduleCechComplex Y α M U).homologyπ n c)) := by
  let a := moduleGeometricAdditiveMap p α β φ U
  let f := (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).hom
  have hc : a ≫ f = (moduleCechForgetIso Y α M U).hom ≫
      additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
        (moduleCoefficientPullback (M := M) (N := N) p φ) := by
    simp [a, f, moduleGeometricAdditiveMap, Category.assoc]
  have h := additiveCycleTransport_homologyπ (moduleCechComplex Y α M U)
    (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)) a n c
  have h' := congrArg (homologyMap f n) h
  rw [← ConcreteCategory.comp_apply, ← homologyMap_comp, hc, homologyMap_comp] at h'
  exact h'.symm

variable [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hcover : iSup U = ⊤)
    (haff : ∀ (q : ℕ) (b : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (b k)))
    (haff' : ∀ (q : ℕ) (b : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => p ⁻¹ᵁ U (b k)))
    (I : InjectiveResolution (moduleAddSheaf Y M))
    (J : InjectiveResolution (moduleAddSheaf X N))

private theorem moduleGeometricCycle_cohomology (n : ℕ)
    (c : (moduleCechComplex Y α M U).cycles n) :
    moduleCechCohomologyLinearEquivAll X β (fun i => p ⁻¹ᵁ U i) N
        (p.iSup_preimage_eq_top hcover) haff' J n
        ((moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).homologyπ n
          (moduleGeometricCycle p α β φ U n c)) =
      moduleCohomologyMapAlong p φ n
        (moduleCechCohomologyLinearEquivAll Y α U M hcover haff I n
          ((moduleCechComplex Y α M U).homologyπ n c)) := by
  cases n with
  | zero =>
    exact moduleCechCohomologyLinearEquivZero_geometric p U φ α β hcover _ _
      (moduleGeometricCycle_homology p α β φ U 0 c)
  | succ n =>
    change moduleCechCohomologyAddEquiv (fun i => p ⁻¹ᵁ U i) N J
        (p.iSup_preimage_eq_top hcover) haff' n
        ((moduleCechAdditiveHomologyIso X β N (fun i => p ⁻¹ᵁ U i) (n + 1)).hom
          ((moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).homologyπ (n + 1)
            (moduleGeometricCycle p α β φ U (n + 1) c))) = _
    rw [moduleGeometricCycle_homology]
    exact moduleCechCohomologyAddEquiv_geometric p U M N I J hcover
      (p.iSup_preimage_eq_top hcover) haff haff'
      (moduleCoefficientPullback (M := M) (N := N) p φ) n _

end
end AlgebraicGeometry.Scheme.Cohomology

end

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace TopologicalSpace
open CategoryTheory.Cech AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Cohomology
section
variable {R A : Type u} [CommRing R] [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (α : R →+* Γ(Y, ⊤)) (β : A →+* Γ(X, ⊤))
    {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) {ι : Type u} (U : ι → Y.Opens)

private theorem moduleGeometricCycle_component (n : ℕ)
    (c : (moduleCechComplex Y α M U).cycles n) (a : Fin (n + 1) → ι) :
    Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf X β N).obj (op (tupleOpen (fun i => p ⁻¹ᵁ U i) n b))) a
        ((moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).iCycles n
          (moduleGeometricCycle p α β φ U n c)) =
      N.presheaf.map
        (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).inv.op
          (φ.app (tupleOpen U n a)
            (Pi.π (fun b : Fin (n + 1) → ι =>
              (moduleSectionsPresheaf Y α M).obj (op (tupleOpen U n b))) a
                ((moduleCechComplex Y α M U).iCycles n c))) := by
  let C := moduleCechComplex Y α M U
  let D := moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)
  let f := moduleGeometricAdditiveMap p α β φ U
  rw [show moduleGeometricCycle p α β φ U n c = additiveCycleTransport C D f n c from rfl,
    additiveCycleTransport_i]
  have h : f.f n ≫ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
      (Pi.π (fun b : Fin (n + 1) → ι =>
        (moduleSectionsPresheaf X β N).obj (op (tupleOpen (fun i => p ⁻¹ᵁ U i) n b))) a) =
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (Pi.π (fun b : Fin (n + 1) → ι =>
        (moduleSectionsPresheaf Y α M).obj (op (tupleOpen U n b))) a) ≫
      φ.mapPresheaf.app (op (tupleOpen U n a)) ≫
      N.presheaf.map
        (PreservesProduct.iso (Opens.map p.base) (fun k => U (a k))).inv.op := by
    rw [← moduleCechForgetIso_hom_f_π X β N (fun i => p ⁻¹ᵁ U i) n a]
    change (moduleGeometricAdditiveMap p α β φ U).f n ≫ _ = _
    dsimp only [moduleGeometricAdditiveMap, comp_f]
    simp only [Category.assoc]
    rw [← Category.assoc ((moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).inv.f n)
      ((moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).hom.f n)]
    have he := congrArg (fun m => m.f n)
      (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).inv_hom_id
    simp only [comp_f, id_f] at he
    rw [he, Category.id_comp]
    erw [moduleAdditiveCechGeometricMap_f_π (M := M) (N := N) p φ U n a]
    rw [← Category.assoc]
    erw [moduleCechForgetIso_hom_f_π Y α M U n a]
  exact ConcreteCategory.congr_hom h ((C.iCycles n) c)

end
end AlgebraicGeometry.Scheme.Cohomology


open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace TopologicalSpace
open CategoryTheory.Cech AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicTopology MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
namespace AlgebraicGeometry.Scheme.Cohomology

private theorem moduleCechMap_component {B : Type u} [CommRing B]
    (X : Scheme.{u}) (α : B →+* Γ(X, ⊤))
    {M N : X.Modules} {κ : Type u} (U : κ → X.Opens) (φ : M ⟶ N)
    (q : ℕ) (a : Fin (q + 1) → κ) (x : (moduleCechComplex X α M U).X q) :
    Pi.π (fun b : Fin (q + 1) → κ => (moduleSectionsPresheaf X α N).obj
        (op (tupleOpen U q b))) a ((moduleCechMap X α U φ).f q x) =
      φ.app (tupleOpen U q a)
        (Pi.π (fun b : Fin (q + 1) → κ => (moduleSectionsPresheaf X α M).obj
          (op (tupleOpen U q b))) a x) := by
  have h : (moduleCechMap X α U φ).f q ≫
      Pi.π (fun b : Fin (q + 1) → κ => (moduleSectionsPresheaf X α N).obj
        (op (tupleOpen U q b))) a =
    Pi.π (fun b : Fin (q + 1) → κ => (moduleSectionsPresheaf X α M).obj
      (op (tupleOpen U q b))) a ≫
        ((moduleSectionsPresheafFunctor X α).map φ).app (op (tupleOpen U q a)) := by
    change (Limits.Pi.map (fun b : Fin (q + 1) → κ =>
      ((moduleSectionsPresheafFunctor X α).map φ).app (op (tupleOpen U q b)))) ≫ _ = _
    exact Pi.map_π _ a
  exact ConcreteCategory.congr_hom h x

variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
local notation "P" => ProjectiveSpace R ι
local notation "Ω" => relativeDifferentialSheaf (toSpec R ι)
local notation "K" => moduleExteriorPower P Ω n

private abbrev topOmegaCech :=
  moduleCechComplex P
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K
      (coordinateOpen R ι)
local notation "C" => topOmegaCech R ι n

include e in
private theorem topOmega_qc : (K).IsQuasicoherent := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (SheafOfModules.isQuasicoherent (P).ringCatSheaf).prop_of_iso
    (differentialResidueTwistingIso R ι n e).symm inferInstance

private theorem coordinateTuple_affine (q : ℕ) (a : Fin (q + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => coordinateOpen R ι (a k)) := by
  change IsAffineOpen (tupleOpen (coordinateOpen R ι) q a)
  rw [coordinateTupleOpen_eq, basicOpen_coordinateProduct]
  exact isAffineOpen_coordinateIntersection R ι (coordinateTupleSet a)
    ⟨a 0, (mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩⟩

include e in
private def topOmegaCechComparison :
    letI := moduleCohomologyModuleOfHom P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K n
    (C).homology n ≃ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf P K) n := by
  letI := topOmega_qc R ι n e
  exact moduleCechCohomologyLinearEquivAll P
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) K
    (iSup_coordinateOpen_eq_top R ι) (coordinateTuple_affine R ι)
      (injectiveResolution (moduleAddSheaf P K)) n

private theorem actualCechToTwist_naturality (M : (P).Modules) [M.IsQuasicoherent]
    (d : ℤ) (φ : M ⟶ twistingSheaf R ι d) (q : ℕ)
    (x : (moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        M (coordinateOpen R ι)).homology q) :
    twistingCechCohomologyLinearEquivAll R ι d q
        (homologyMap (moduleCechMap P
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
            (coordinateOpen R ι) φ) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map φ) q
        (moduleCechCohomologyLinearEquivAll P
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
            (coordinateOpen R ι) M
          (iSup_coordinateOpen_eq_top R ι) (coordinateTuple_affine R ι)
            (injectiveResolution (moduleAddSheaf P M)) q x) := by
  cases q with
  | zero =>
    exact moduleCechCohomologyLinearEquivZero_naturality P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) φ x
  | succ q =>
    exact moduleCechCohomologyLinearEquiv_naturality P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) (coordinateTuple_affine R ι)
        (injectiveResolution (moduleAddSheaf P M))
          (injectiveResolution (moduleAddSheaf P (twistingSheaf R ι d))) φ q x

private theorem topOmegaCechComparison_trace (x : (C).homology n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
          (differentialResidueTwistingIso R ι n e).hom) n
            (topOmegaCechComparison R ι n e x)) =
      projectiveTrace R ι n e
        (twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n
          (homologyMap (differentialResidueCechLaurentIso R ι n e).hom n x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := topOmega_qc R ι n e
  have hn := actualCechToTwist_naturality R ι K (-(Fintype.card ι : ℤ))
    (differentialResidueTwistingIso R ι n e).hom n x
  refine (congrArg (projectiveTrace R ι n e) hn).symm.trans ?_
  congr 1
  change twistingCechCohomologyLinearEquivAll R ι _ n
      (homologyMap (moduleCechMap P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (coordinateOpen R ι)
        (differentialResidueTwistingIso R ι n e).hom) n x) =
    twistingCechCohomologyLinearEquivAll R ι _ n
      (homologyMap (twistingCechLaurentIso R ι _).inv n
        (homologyMap (differentialResidueCechLaurentIso R ι n e).hom n x))
  congr 1
  have hc : (differentialResidueCechLaurentIso R ι n e).hom ≫
      (twistingCechLaurentIso R ι (-(Fintype.card ι : ℤ))).inv =
    moduleCechMap P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) (differentialResidueTwistingIso R ι n e).hom := by
    simp [differentialResidueCechLaurentIso, moduleCechMap, Category.assoc]
  have h := congrArg (fun f => homologyMap f n) hc
  rw [homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h x).symm

private theorem differentialLaurent_component_eq
    (x y : (C).X n)
    (h : Pi.π (fun b : Fin (n + 1) → ι => (moduleSectionsPresheaf P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K).obj
        (op (tupleOpen (coordinateOpen R ι) n b))) e.symm x =
      Pi.π (fun b : Fin (n + 1) → ι => (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          K).obj
        (op (tupleOpen (coordinateOpen R ι) n b))) e.symm y) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (differentialResidueCechLaurentIso R ι n e).hom.f n x e.symm =
      (differentialResidueCechLaurentIso R ι n e).hom.f n y e.symm := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  change (twistingCechLaurentTermIso R ι (-(Fintype.card ι : ℤ)) n).hom
      ((moduleCechMap P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (coordinateOpen R ι)
        (differentialResidueTwistingIso R ι n e).hom).f n x) e.symm =
    (twistingCechLaurentTermIso R ι (-(Fintype.card ι : ℤ)) n).hom
      ((moduleCechMap P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (coordinateOpen R ι)
        (differentialResidueTwistingIso R ι n e).hom).f n y) e.symm
  rw [twistingCechLaurentTermIso_hom_apply, twistingCechLaurentTermIso_hom_apply,
    moduleCechMap_component, moduleCechMap_component, h]

private theorem topOmegaCechTrace_depends_enum (c d : (C).cycles n)
    (h : Pi.π (fun b : Fin (n + 1) → ι => (moduleSectionsPresheaf P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K).obj
        (op (tupleOpen (coordinateOpen R ι) n b))) e.symm (((C).iCycles n) c) =
      Pi.π (fun b : Fin (n + 1) → ι => (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          K).obj
        (op (tupleOpen (coordinateOpen R ι) n b))) e.symm (((C).iCycles n) d)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
          (differentialResidueTwistingIso R ι n e).hom) n
            (topOmegaCechComparison R ι n e (((C).homologyπ n) c))) =
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
          (differentialResidueTwistingIso R ι n e).hom) n
            (topOmegaCechComparison R ι n e (((C).homologyπ n) d))) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let f := (differentialResidueCechLaurentIso R ι n e).hom
  rw [topOmegaCechComparison_trace, topOmegaCechComparison_trace]
  have hc := ConcreteCategory.congr_hom (homologyπ_naturality f n) c
  have hd := ConcreteCategory.congr_hom (homologyπ_naturality f n) d
  simp only [ConcreteCategory.comp_apply] at hc hd
  rw [hc, hd, projectiveTrace_laurent_homologyπ, projectiveTrace_laurent_homologyπ]
  have hci := ConcreteCategory.congr_hom (cyclesMap_i f n) c
  have hdi := ConcreteCategory.congr_hom (cyclesMap_i f n) d
  simp only [ConcreteCategory.comp_apply] at hci hdi
  rw [hci, hdi]
  exact congrArg (fun z => z.val.coeff
    (coordinateWeightExponent e.symm coordinateResidueWeight
      (fun i _ => ⟨e i, e.symm_apply_apply i⟩)))
        (differentialLaurent_component_eq R ι n e _ _ h)

end AlgebraicGeometry.Scheme.Cohomology

end

section
private def coefficientAppLE {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U) (x : Γ(M, U)) : Γ(N, V) :=
  N.presheaf.map (homOfLE h).op ((φ.app U).hom x)

private theorem coefficientAppLE_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (r : Γ(Y, U)) (x : Γ(M, U)) :
    coefficientAppLE (M := M) (N := N) g φ U V h (r • x) =
      g.appLE U V h r • coefficientAppLE (M := M) (N := N) g φ U V h x := by
  have hφ := coefficientSection_smul (M := M) (N := N) g φ U r x
  have h₁ := congrArg (N.presheaf.map (homOfLE h).op) hφ
  exact h₁.trans (N.val.map_smul (homOfLE h).op (g.app U r)
    (coefficientSection (M := M) (N := N) g φ U x))

namespace AlgebraicGeometry.Scheme.Cohomology
variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)
  (ι : Type u) [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]

private theorem differentialTopBaseOpenCoefficient_appLE_wedge_d (n : ℕ)
    (U : (ProjectiveSpace R ι).Opens) (V : (ProjectiveSpace A ι).Opens)
    (h : V ≤ ProjectiveSpace.map σ ι ⁻¹ᵁ U) (s : Fin n → Γ(ProjectiveSpace R ι, U)) :
    coefficientAppLE
        (M := moduleExteriorPower (ProjectiveSpace R ι)
          (relativeDifferentialSheaf (toSpec R ι)) n)
        (N := moduleExteriorPower (ProjectiveSpace A ι)
          (relativeDifferentialSheaf (toSpec A ι)) n)
        (ProjectiveSpace.map σ ι) (differentialTopBaseOpenCoefficient σ ι n) U V h
        (wedgeAt (ProjectiveSpace R ι) (relativeDifferentialSheaf (toSpec R ι)) n U
          (fun i => (relativeDifferentialDerivation (toSpec R ι)).d (s i))) =
      wedgeAt (ProjectiveSpace A ι) (relativeDifferentialSheaf (toSpec A ι)) n V
        (fun i => (relativeDifferentialDerivation (toSpec A ι)).d
          ((ProjectiveSpace.map σ ι).appLE U V h (s i))) := by
  have hs := differentialTopBaseOpenCoefficient_wedge_d σ ι n U s
  have hs' := congrArg
    ((moduleExteriorPower (ProjectiveSpace A ι)
      (relativeDifferentialSheaf (toSpec A ι)) n).presheaf.map (homOfLE h).op) hs
  refine hs'.trans ?_
  refine (wedgeAt_naturality (ProjectiveSpace A ι)
    (relativeDifferentialSheaf (toSpec A ι)) n (homOfLE h) _).trans ?_
  congr 1
  funext i
  exact (relativeDifferentialDerivation_restrict (toSpec A ι) (homOfLE h).op
    ((ProjectiveSpace.map σ ι).app U (s i))).symm

private def residueSection (B : Type u) [CommRing B] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (V : (ProjectiveSpace B ι).Opens) (h : ∀ j, V ≤ coordinateOpen B ι (e.symm j))
    (r : B) : Γ(moduleExteriorPower (ProjectiveSpace B ι)
      (relativeDifferentialSheaf (toSpec B ι)) n, V) :=
  (globalRestriction (ProjectiveSpace B ι) V
      (((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom) r) *
        ∏ j : Fin n, (coordinateTransitionOn B ι (e.symm 0) (e.symm j.succ)
          (h 0) (h j.succ)).val) •
    wedgeAt (ProjectiveSpace B ι) (relativeDifferentialSheaf (toSpec B ι)) n V
      (fun j => (relativeDifferentialDerivation (toSpec B ι)).d
        (eulerCoordinateRatio B ι (e.symm 0) (e.symm j.succ) (h 0)))

private theorem differentialTopBaseOpenCoefficient_residueSection (n : ℕ)
    (e : ι ≃ Fin (n + 1))
    (U : (ProjectiveSpace R ι).Opens) (V : (ProjectiveSpace A ι).Opens)
    (h : V ≤ ProjectiveSpace.map σ ι ⁻¹ᵁ U)
    (hR : ∀ j, U ≤ coordinateOpen R ι (e.symm j))
    (hA : ∀ j, V ≤ coordinateOpen A ι (e.symm j)) (r : R) :
    coefficientAppLE
        (M := moduleExteriorPower (ProjectiveSpace R ι)
          (relativeDifferentialSheaf (toSpec R ι)) n)
        (N := moduleExteriorPower (ProjectiveSpace A ι)
          (relativeDifferentialSheaf (toSpec A ι)) n)
        (ProjectiveSpace.map σ ι) (differentialTopBaseOpenCoefficient σ ι n) U V h
          (residueSection ι R n e U hR r) = residueSection ι A n e V hA (σ r) := by
  unfold residueSection
  rw [coefficientAppLE_smul, differentialTopBaseOpenCoefficient_appLE_wedge_d,
    map_mul, map_prod, projectiveMap_constant_appLE]
  congr 1
  · congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact projectiveMap_transition_appLE σ ι (e.symm 0) (e.symm j.succ)
      U V h (hR 0) (hR j.succ) (hA 0) (hA j.succ)
  · congr 1
    funext j
    congr 1
    exact projectiveMap_ratio_appLE σ ι (e.symm 0) (e.symm j.succ) U V h (hR 0) (hA 0)

end AlgebraicGeometry.Scheme.Cohomology

end

section

namespace AlgebraicGeometry.Scheme.Cohomology
variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)
  (ι : Type u) [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
  (n : ℕ) (e : ι ≃ Fin (n + 1))

omit [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))] in
private theorem preimageCoordinateTupleBelow (j : Fin (n + 1)) :
    tupleOpen (fun i => ProjectiveSpace.map σ ι ⁻¹ᵁ coordinateOpen R ι i) n e.symm ≤
      coordinateOpen A ι (e.symm j) := by
  rw [← ProjectiveSpace.map_preimage_coordinateOpen σ ι (e.symm j)]
  exact tupleOpen_le _ n e.symm j

private theorem differentialResidueGeometricCycle_component (r : R) :
    let g := ProjectiveSpace.map σ ι
    let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let β := (toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
    let KA := moduleExteriorPower (ProjectiveSpace A ι)
      (relativeDifferentialSheaf (toSpec A ι)) n
    let W := fun i => g ⁻¹ᵁ coordinateOpen R ι i
    Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf (ProjectiveSpace A ι) β KA).obj
        (op (tupleOpen W n b))) e.symm
        ((moduleCechComplex (ProjectiveSpace A ι) β KA W).iCycles n
          (moduleGeometricCycle g α β (differentialTopBaseOpenCoefficient σ ι n)
            (coordinateOpen R ι) n (differentialResidueCechCycle R ι n e r))) =
      residueSection ι A n e (tupleOpen W n e.symm)
        (preimageCoordinateTupleBelow σ ι n e) (σ r) := by
  dsimp only
  rw [moduleGeometricCycle_component]
  let g := ProjectiveSpace.map σ ι
  let U := tupleOpen (coordinateOpen R ι) n e.symm
  let V := tupleOpen (fun i => g ⁻¹ᵁ coordinateOpen R ι i) n e.symm
  let h : V ≤ g ⁻¹ᵁ U := leOfHom
    (PreservesProduct.iso (Opens.map g.base) (fun k => coordinateOpen R ι (e.symm k))).inv
  change coefficientAppLE
      (M := moduleExteriorPower (ProjectiveSpace R ι)
        (relativeDifferentialSheaf (toSpec R ι)) n)
      (N := moduleExteriorPower (ProjectiveSpace A ι)
        (relativeDifferentialSheaf (toSpec A ι)) n)
      g (differentialTopBaseOpenCoefficient σ ι n) U V h _ = _
  rw [differentialResidueCechCycle_component]
  exact differentialTopBaseOpenCoefficient_residueSection σ ι n e U V h
    (tupleOpen_le (coordinateOpen R ι) n e.symm)
      (preimageCoordinateTupleBelow σ ι n e) r

end AlgebraicGeometry.Scheme.Cohomology

end

section

namespace AlgebraicGeometry.Scheme.Cohomology
section
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
local notation "P" => ProjectiveSpace R ι
local notation "Ω" => relativeDifferentialSheaf (toSpec R ι)
local notation "K" => moduleExteriorPower P Ω n

private theorem differentialTrace_injective :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    Function.Injective (fun x : Sheaf.H.{u + 1} (moduleAddSheaf P K) n =>
      projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
          (differentialResidueTwistingIso R ι n e).hom) n x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  dsimp only
  intro x y h
  have h' := (projectiveTraceLinearEquiv R ι n e).injective h
  let E := (SheafOfModules.toSheaf (P).ringCatSheaf).mapIso
    (differentialResidueTwistingIso R ι n e)
  have hx := congrArg (Sheaf.H.map E.inv n) h'
  have hid : (SheafOfModules.toSheaf (P).ringCatSheaf).map (𝟙 K) =
      𝟙 (moduleAddSheaf P K) := (SheafOfModules.toSheaf (P).ringCatSheaf).map_id K
  simpa only [← Sheaf.H.map_comp_apply, E, Functor.mapIso_inv, ← Functor.map_comp,
    Iso.hom_inv_id, hid, Sheaf.H.map_id_apply] using hx

private theorem topOmegaCechTrace_of_component
    (W : ι → (P).Opens) (hW : W = coordinateOpen R ι)
    (hcover : iSup W = ⊤)
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => W (a k)))
    (hchart : ∀ j, tupleOpen W n e.symm ≤ coordinateOpen R ι (e.symm j))
    (c : (moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K W).cycles n)
    (r : R)
    (hc : Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K).obj
          (op (tupleOpen W n b))) e.symm
            ((moduleCechComplex P
              ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
                K W).iCycles n c) =
      residueSection ι R n e (tupleOpen W n e.symm) hchart r) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI : (K).IsQuasicoherent := topOmega_qc R ι n e
    projectiveTrace R ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
        (differentialResidueTwistingIso R ι n e).hom) n
        (moduleCechCohomologyLinearEquivAll P
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) W K
            hcover haff (injectiveResolution (moduleAddSheaf P K)) n
              ((moduleCechComplex P
                ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
                  K W).homologyπ n c))) = r := by
  subst W
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : (K).IsQuasicoherent := topOmega_qc R ι n e
  have hd := differentialResidueCechCycle_component R ι n e r
  have hcd : Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K).obj
          (op (tupleOpen (coordinateOpen R ι) n b))) e.symm
            ((topOmegaCech R ι n).iCycles n c) =
      Pi.π (fun b : Fin (n + 1) → ι =>
        (moduleSectionsPresheaf P
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K).obj
            (op (tupleOpen (coordinateOpen R ι) n b))) e.symm
              ((topOmegaCech R ι n).iCycles n
                (differentialResidueCechCycle R ι n e r)) := hc.trans hd.symm
  exact (topOmegaCechTrace_depends_enum R ι n e c
    (differentialResidueCechCycle R ι n e r) hcd).trans
      (differentialResidueCohomologyClass_trace R ι n e r)

end
end AlgebraicGeometry.Scheme.Cohomology

end

section

namespace AlgebraicGeometry.Scheme.Cohomology
variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)
  (ι : Type u) [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
  (n : ℕ) (e : ι ≃ Fin (n + 1))

private theorem differentialResidue_baseOpen_trace (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveTrace A ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
        (differentialResidueTwistingIso A ι n e).hom) n
        (moduleCohomologyMapAlong (M := moduleExteriorPower (ProjectiveSpace R ι)
          (relativeDifferentialSheaf (toSpec R ι)) n)
          (N := moduleExteriorPower (ProjectiveSpace A ι)
            (relativeDifferentialSheaf (toSpec A ι)) n)
          (ProjectiveSpace.map σ ι) (differentialTopBaseOpenCoefficient σ ι n) n
            (differentialResidueCohomologyClass R ι n e r))) = σ r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := topOmega_qc R ι n e
  let := topOmega_qc A ι n e
  let g := ProjectiveSpace.map σ ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let β := (toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  let KR := moduleExteriorPower (ProjectiveSpace R ι)
    (relativeDifferentialSheaf (toSpec R ι)) n
  let KA := moduleExteriorPower (ProjectiveSpace A ι)
    (relativeDifferentialSheaf (toSpec A ι)) n
  let W := fun i => g ⁻¹ᵁ coordinateOpen R ι i
  have hW : W = coordinateOpen A ι := funext (ProjectiveSpace.map_preimage_coordinateOpen σ ι)
  have haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι),
      IsAffineOpen (∏ᶜ fun k => W (a k)) := by
    intro q a
    rw [hW]
    exact coordinateTuple_affine A ι q a
  let c := moduleGeometricCycle (M := KR) (N := KA) g α β
    (differentialTopBaseOpenCoefficient σ ι n) (coordinateOpen R ι) n
      (differentialResidueCechCycle R ι n e r)
  have hc := moduleGeometricCycle_cohomology (M := KR) (N := KA) g α β
    (differentialTopBaseOpenCoefficient σ ι n) (coordinateOpen R ι)
    (iSup_coordinateOpen_eq_top R ι) (coordinateTuple_affine R ι) haff
    (injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) KR))
    (injectiveResolution (moduleAddSheaf (ProjectiveSpace A ι) KA)) n
    (differentialResidueCechCycle R ι n e r)
  change _ = moduleCohomologyMapAlong (M := KR) (N := KA) g
    (differentialTopBaseOpenCoefficient σ ι n) n
    (differentialResidueCohomologyClass R ι n e r) at hc
  rw [← hc]
  exact topOmegaCechTrace_of_component A ι n e W hW
    (g.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) haff
    (preimageCoordinateTupleBelow σ ι n e) c (σ r)
      (differentialResidueGeometricCycle_component σ ι n e r)

@[expose] public section

/-- The actual differential coefficient pullback carries the same normalized residue class. -/
theorem differentialResidueCohomologyClass_baseOpen (r : R) :
    moduleCohomologyMapAlong (M := moduleExteriorPower (ProjectiveSpace R ι)
      (relativeDifferentialSheaf (toSpec R ι)) n)
      (N := moduleExteriorPower (ProjectiveSpace A ι)
        (relativeDifferentialSheaf (toSpec A ι)) n)
      (ProjectiveSpace.map σ ι) (differentialTopBaseOpenCoefficient σ ι n) n
        (differentialResidueCohomologyClass R ι n e r) =
      differentialResidueCohomologyClass A ι n e (σ r) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  apply differentialTrace_injective A ι n e
  exact (differentialResidue_baseOpen_trace σ ι n e r).trans
    (differentialResidueCohomologyClass_trace A ι n e (σ r)).symm

/-- The actual open base map carries the original projective differential trace through `σ`. -/
theorem projectiveTrace_differential_baseOpen
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (moduleExteriorPower (ProjectiveSpace R ι)
        (relativeDifferentialSheaf (toSpec R ι)) n)) n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveTrace A ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace A ι).ringCatSheaf).map
        (differentialResidueTwistingIso A ι n e).hom) n
        (moduleCohomologyMapAlong (M := moduleExteriorPower (ProjectiveSpace R ι)
          (relativeDifferentialSheaf (toSpec R ι)) n)
          (N := moduleExteriorPower (ProjectiveSpace A ι)
            (relativeDifferentialSheaf (toSpec A ι)) n)
          (ProjectiveSpace.map σ ι) (differentialTopBaseOpenCoefficient σ ι n) n x)) =
      σ (projectiveTrace R ι n e
        (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
          (differentialResidueTwistingIso R ι n e).hom) n x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  dsimp only
  let r := projectiveTrace R ι n e
    (Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      (differentialResidueTwistingIso R ι n e).hom) n x)
  have hx : x = differentialResidueCohomologyClass R ι n e r := by
    apply differentialTrace_injective R ι n e
    exact (differentialResidueCohomologyClass_trace R ι n e r).symm
  have htrace := differentialResidue_baseOpen_trace σ ι n e r
  dsimp only at htrace
  rw [← hx] at htrace
  exact htrace

end
end AlgebraicGeometry.Scheme.Cohomology

end

