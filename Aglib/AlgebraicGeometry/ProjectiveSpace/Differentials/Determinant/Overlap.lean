/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Determinant.Frames
public import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Actual projective differential determinant overlaps

The original Euler and differential frames evaluate the original determinant chart maps on
arbitrary original wedges. The same transported Euler middle frame and the original target
generator have the same transition factor. Changing the original pivot adds a vector in the
actual Euler differential image; the resulting extra alternating term vanishes above the
actual rank. This proves equality of the original chart maps through the native over-site
restriction composition isomorphisms on every common open.

The coefficient determinant and tensor orientation remain those of `Frames`. The ring is any
commutative ring, with a supplied coordinate order `e : ι ≃ Fin (n + 1)`. Dimension zero and
the zero ring are included. Global gluing and the original Laurent trace transport are later
owners.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped MonoidalCategory TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveSpace

private theorem overSections_ext {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) (s t : M.sections)
    (h : ∀ W : U.toScheme.Opens,
      s.val (op (U.overEquivalence.inverse.obj W)) =
        t.val (op (U.overEquivalence.inverse.obj W))) : s = t := by
  apply PresheafOfModules.sections_ext
  intro V
  let e := U.overEquivalence.unitIso.app V.unop
  have hs := s.property e.hom.op
  have ht := t.property e.hom.op
  exact hs.symm.trans ((congrArg (M.val.map e.hom.op)
    (h (U.overEquivalence.functor.obj V.unop))).trans ht)

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original relative differential of an original coordinate ratio on every over-open. -/
def determinantRatioDifferentialOverSection (i j : ι) :
    ((Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).over
      (coordinateOpen R ι i)).sections where
  val V := (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
    (eulerCoordinateRatio R ι i j (leOfHom V.unop.hom))
  property {V W} f := by
    let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
    exact (d.d_map f.unop.left.op
      (eulerCoordinateRatio R ι i j (leOfHom V.unop.hom))).symm.trans
        (congrArg d.d (eulerCoordinateRatio_restrict R ι i j
          (leOfHom f.unop.left) (leOfHom V.unop.hom)))

/-- The Euler middle generator as a section over coordinate chart `i`. -/
def determinantMiddleGeneratorOverSection (i j : ι) :
    ((eulerMiddle R ι).over (coordinateOpen R ι i)).sections where
  val V := eulerMiddleGenerator R ι i j (leOfHom V.unop.hom)
  property {V _W} f := eulerMiddleGenerator_restrict R ι i j
    (leOfHom f.unop.left) (leOfHom V.unop.hom)

/-- The Euler kernel generator as a section of the Euler middle term over coordinate chart `i`. -/
def determinantKernelGeneratorOverSection (i j : ι) :
    ((eulerMiddle R ι).over (coordinateOpen R ι i)).sections where
  val V := eulerKernelGenerator R ι i j (leOfHom V.unop.hom)
  property {V _W} f := eulerKernelGenerator_restrict R ι i j
    (leOfHom f.unop.left) (leOfHom V.unop.hom)

theorem determinantOmegaOrderedOverFreeIso_section (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (i : ι) (a : Fin n) :
    SheafOfModules.sectionsMap (determinantOmegaOrderedOverFreeIso R ι n e i).hom
      (SheafOfModules.freeSection (ULift.up a)) =
      determinantRatioDifferentialOverSection R ι i (e.symm ((e i).succAbove a)) := by
  apply overSections_ext (coordinateOpen R ι i)
  intro W
  exact determinantOmegaOrderedOverFreeIso_hom_freeSection R ι n e i a W

theorem determinantOmegaOrderedOverFreeIso_hom_ratio (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (i : ι) (a : Fin n)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    (determinantOmegaOrderedOverFreeIso R ι n e i).hom.val.app
      (op (Over.mk (homOfLE hi)))
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over
        (coordinateOpen R ι i)) (ULift.up a)).val (op (Over.mk (homOfLE hi)))) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) hi) :=
  congrArg (fun s => s.val (op (Over.mk (homOfLE hi))))
    (determinantOmegaOrderedOverFreeIso_section R ι n e i a)


/-- The original middle polynomial frame transported to the original coordinate-open scheme. -/
def determinantMiddleCoordinateFreeIso (i : ι) :
    SheafOfModules.free (R := (coordinateOpen R ι i).toScheme.ringCatSheaf) ι ≅
      (eulerMiddle R ι).restrict (coordinateOpen R ι i).ι := by
  let q := (coordinateOpenIsoSpecPolynomial R ι i).hom
  let F := Scheme.Modules.restrictFunctor q
  letI : PreservesColimitsOfSize.{u, u} F := inferInstance
  exact SheafOfModules.mapFreeIso F ι (Scheme.Modules.restrictUnitIso q).symm ≪≫
    F.mapIso (eulerMiddlePolynomialFreeIso R ι i).symm ≪≫
      determinantCoordinateTransport R ι i (eulerMiddle R ι)

theorem determinantMiddleCoordinateFreeIso_hom_freeSection (i j : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (determinantMiddleCoordinateFreeIso R ι i).hom.val.app (op W)
      ((SheafOfModules.freeSection (R := (coordinateOpen R ι i).toScheme.ringCatSheaf) j).val
        (op W)) = eulerMiddleGenerator R ι i j ((coordinateOpen R ι i).ι_image_le W) := by
  let Z := (coordinateOpen R ι i).toScheme
  let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
  let q := (coordinateOpenIsoSpecPolynomial R ι i).hom
  let F := Scheme.Modules.restrictFunctor q
  let : PreservesColimitsOfSize.{u, u} F := inferInstance
  let η := (Scheme.Modules.restrictUnitIso q).symm
  let a := SheafOfModules.mapFreeIso F ι η
  have hu : η.hom.val.app (op W) (1 : Γ(Z, W)) = (1 : Γ(Spec S, q ''ᵁ W)) := by
    change (q.appIso W).inv 1 = 1
    exact (q.appIso W).inv.hom.map_one
  have he := congrArg (fun f => f.val.app (op W) (1 : Γ(Z, W)))
    (SheafOfModules.ιFree_mapFreeIso_hom F ι η j)
  change a.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W)) =
    (F.map (SheafOfModules.ιFree (R := (Spec S).ringCatSheaf) j)).val.app (op W)
      (η.hom.val.app (op W) (1 : Γ(Z, W))) at he
  have he' : a.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W)) =
      (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val (op (q ''ᵁ W)) :=
    he.trans (congrArg
      ((F.map (SheafOfModules.ιFree (R := (Spec S).ringCatSheaf) j)).val.app (op W)) hu)
  let g := eulerPolynomialChart R ι i
  let M := eulerMiddle R ι
  let h := determinantCoordinateChart_image R ι i W
  have hp : ((F.map (eulerMiddlePolynomialFreeIso R ι i).inv).val.app (op W))
      (a.hom.val.app (op W)
        ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W))) =
      eulerMiddleGenerator R ι i j (eulerPolynomialChart_image_le R ι i (q ''ᵁ W)) :=
    (congrArg ((F.map (eulerMiddlePolynomialFreeIso R ι i).inv).val.app (op W)) he').trans
      (eulerMiddlePolynomialFreeIso_inv_freeSection R ι i j (q ''ᵁ W))
  change (determinantCoordinateTransport R ι i M).hom.val.app (op W)
    (((F.map (eulerMiddlePolynomialFreeIso R ι i).inv).val.app (op W))
      (a.hom.val.app (op W)
        ((SheafOfModules.freeSection (R := Z.ringCatSheaf) j).val (op W)))) = _
  exact (congrArg ((determinantCoordinateTransport R ι i M).hom.val.app (op W)) hp).trans
    ((determinantCoordinateTransport_hom_app R ι i M W _).trans
      (eulerMiddleGenerator_restrict R ι i j h.le
        (eulerPolynomialChart_image_le R ι i (q ''ᵁ W))))

/-- The free trivialization of the Euler middle term on the over-site of coordinate chart `i`. -/
def determinantMiddleOverFreeIso (i : ι) :
    SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf.over
      (coordinateOpen R ι i)) ι ≅ (eulerMiddle R ι).over (coordinateOpen R ι i) :=
  freeIsoOverOfRestrictFreeIso (coordinateOpen R ι i)
    (determinantMiddleCoordinateFreeIso R ι i)

theorem determinantMiddleOverFreeIso_section (i j : ι) :
    SheafOfModules.sectionsMap (determinantMiddleOverFreeIso R ι i).hom
      (SheafOfModules.freeSection j) = determinantMiddleGeneratorOverSection R ι i j := by
  apply overSections_ext (coordinateOpen R ι i)
  intro W
  exact (freeIsoOverOfRestrictFreeIso_hom_freeSection (coordinateOpen R ι i)
    (determinantMiddleCoordinateFreeIso R ι i) j W).trans
      (determinantMiddleCoordinateFreeIso_hom_freeSection R ι i j W)

/-- The over-site trivialization of the Euler middle term indexed by `ULift (Fin (n + 1))` via
`e`. -/
def determinantMiddleOrderedOverFreeIso (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    SheafOfModules.free (R := (ProjectiveSpace R ι).ringCatSheaf.over
      (coordinateOpen R ι i)) (ULift.{u} (Fin (n + 1))) ≅
      (eulerMiddle R ι).over (coordinateOpen R ι i) :=
  (SheafOfModules.freeFunctor (R := (ProjectiveSpace R ι).ringCatSheaf.over
    (coordinateOpen R ι i))).mapIso ((e.trans Equiv.ulift.symm).symm.toIso) ≪≫
      determinantMiddleOverFreeIso R ι i

theorem determinantMiddleOrderedOverFreeIso_section (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i : ι) (a : Fin (n + 1)) :
    SheafOfModules.sectionsMap (determinantMiddleOrderedOverFreeIso R ι n e i).hom
      (SheafOfModules.freeSection (ULift.up a)) =
      determinantMiddleGeneratorOverSection R ι i (e.symm a) := by
  dsimp only [determinantMiddleOrderedOverFreeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [SheafOfModules.freeFunctor_map, SheafOfModules.sectionsMap_comp,
    SheafOfModules.sectionMap_freeMap_freeSection]
  exact determinantMiddleOverFreeIso_section R ι i (e.symm a)

theorem determinantMiddleOrderedOverFreeIso_hom_generator (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (i : ι) (a : Fin (n + 1))
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    (determinantMiddleOrderedOverFreeIso R ι n e i).hom.val.app
      (op (Over.mk (homOfLE hi)))
      ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf.over
        (coordinateOpen R ι i)) (ULift.up a)).val (op (Over.mk (homOfLE hi)))) =
      eulerMiddleGenerator R ι i (e.symm a) hi :=
  congrArg (fun s => s.val (op (Over.mk (homOfLE hi))))
    (determinantMiddleOrderedOverFreeIso_section R ι n e i a)



private theorem alternating_above_basis {S : Type*} [CommRing S]
    {A B : Type*} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (n : ℕ) (b : Module.Basis (Fin n) S A)
    (F : A [⋀^Fin (n + 1)]→ₗ[S] B) (s : Fin (n + 1) → A) : F s = 0 := by
  let : Subsingleton (⋀[S]^(n + 1) A) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt (R := S) b b.span_eq (n + 1) (by simp)
  let q := exteriorPower.alternatingMapLinearEquiv F
  exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti F s).symm.trans
    ((congrArg q (Subsingleton.elim (exteriorPower.ιMulti S (n + 1) s) 0)).trans q.map_zero)

private theorem pivot_form_independent {S : Type*} [CommRing S]
    {A B : Type*} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (n : ℕ) (b : Module.Basis (Fin n) S A) (η : A →ₗ[S] B)
    (F : B [⋀^Fin (n + 1)]→ₗ[S] S) (p q : B) (v : A) (h : q - p = η v)
    (s : Fin n → A) : F.curryLeft q (η ∘ s) = F.curryLeft p (η ∘ s) := by
  have hz := alternating_above_basis n b (F.compLinearMap η) (Matrix.vecCons v s)
  have hc : (F.compLinearMap η).curryLeft v s = F.curryLeft (η v) (η ∘ s) :=
    congrArg (fun G => G s) (AlternatingMap.curryLeft_compLinearMap η F v)
  have hd : F.curryLeft (q - p) (η ∘ s) = 0 :=
    (congrArg (fun x => F.curryLeft x (η ∘ s)) h).trans (hc.symm.trans hz)
  have hs := congrArg (fun G => G (η ∘ s)) (F.curryLeft.map_sub q p)
  exact sub_eq_zero.mp (hs.symm.trans hd)

private theorem basis_determinant_scale {S : Type*} [CommRing S]
    {B : Type*} [AddCommGroup B] [Module S B] (m : ℕ)
    (b c : Module.Basis (Fin m) S B) (r : S) (h : ∀ a, c a = r • b a)
    (s : Fin m → B) : b.det s = r ^ m * c.det s := by
  classical
  have hc : (fun a => c a) = (fun a => r • b a) := funext h
  have hv : b.det c = r ^ m := by
    change b.det (fun a => c a) = _
    rw [hc, b.det.map_smul_univ (fun _ => r) b, b.det_self]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact (congrArg (fun F => F s) (b.det.eq_smul_basis_det c)).trans
    (by rw [hv])

attribute [local irreducible] determinantOmegaOrderedOverFreeIso
  determinantMiddleOrderedOverFreeIso

private theorem overFreeSectionsBasis_apply (X : Scheme.{u}) (M : X.Modules) (m : ℕ)
    (U : X.Opens) (f : SheafOfModules.free (R := X.ringCatSheaf.over U)
      (ULift.{u} (Fin m)) ≅ M.over U) (V : (Over U)ᵒᵖ) (a : Fin m) :
    ((SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) m V).map
      (((SheafOfModules.evaluation (X.ringCatSheaf.over U) V).mapIso f).toLinearEquiv)) a =
      f.hom.val.app V
      ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up a)).val V) := by
  rw [Module.Basis.map_apply]
  exact congrArg (((SheafOfModules.evaluation (X.ringCatSheaf.over U) V).mapIso f).toLinearEquiv)
    (SheafOfModulesOfCommRing.freeFinSectionsBasis_apply (X.sheaf.over U) m V a)

private theorem overFreeOriginalSectionsBasis_apply (X : Scheme.{u}) (M : X.Modules)
    (m : ℕ) (U T : X.Opens) (h : T ≤ U)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin m)) ≅ M.over U)
    (a : Fin m) (t : Γ(M, T))
    (ht : f.hom.val.app (op (Over.mk (homOfLE h)))
      ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up a)).val
        (op (Over.mk (homOfLE h)))) = t) :
    (show Module.Basis (Fin (m)) Γ(X, T) Γ(M, T) from
    (show Module.Basis (Fin (m)) ((X.sheaf.over U).obj.obj
      (op (Over.mk (homOfLE h))))
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE h)))).obj ((M).over U)) from
    (SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) (m)
      (op (Over.mk (homOfLE h)))).map
        (((SheafOfModules.evaluation (X.ringCatSheaf.over U)
          (op (Over.mk (homOfLE h)))).mapIso f).toLinearEquiv))) a = t := by
  exact congrArg (β := Γ(M, T))
    (fun x : (SheafOfModules.evaluation (X.ringCatSheaf.over U)
      (op (Over.mk (homOfLE h)))).obj (M.over U) => x)
    ((overFreeSectionsBasis_apply X M m U f (op (Over.mk (homOfLE h))) a).trans ht)

/-- The original differential frame evaluated on an original subopen, in the displayed order. -/
def determinantOmegaSectionsBasis (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    Module.Basis (Fin n) Γ(ProjectiveSpace R ι, T)
      Γ(Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι), T) :=
  (fun (X : Scheme.{u}) (M : X.Modules) (U T : X.Opens) (h : T ≤ U)
      (f : SheafOfModules.free (R := X.ringCatSheaf.over U)
        (ULift.{u} (Fin (n))) ≅ M.over U) =>
    (show Module.Basis (Fin (n)) Γ(X, T) Γ(M, T) from
    (show Module.Basis (Fin (n)) ((X.sheaf.over U).obj.obj
      (op (Over.mk (homOfLE h))))
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE h)))).obj ((M).over U)) from
    (SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) (n)
      (op (Over.mk (homOfLE h)))).map
        (((SheafOfModules.evaluation (X.ringCatSheaf.over U)
          (op (Over.mk (homOfLE h)))).mapIso f).toLinearEquiv))))
    (ProjectiveSpace R ι) (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
      (coordinateOpen R ι i) T hi
      (determinantOmegaOrderedOverFreeIso R ι n e i)

theorem determinantOmegaSectionsBasis_apply (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) (a : Fin (n)) :
    determinantOmegaSectionsBasis R ι n e i hi a =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) hi) := by
  simpa only [determinantOmegaSectionsBasis] using
    overFreeOriginalSectionsBasis_apply (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
      (n) (coordinateOpen R ι i) T hi (determinantOmegaOrderedOverFreeIso R ι n e i) a _
      (determinantOmegaOrderedOverFreeIso_hom_ratio R ι n e i a hi)

/-- The same original Euler middle frame evaluated on an original subopen. -/
def determinantMiddleSectionsBasis (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    Module.Basis (Fin (n + 1)) Γ(ProjectiveSpace R ι, T) Γ(eulerMiddle R ι, T) :=
  (fun (X : Scheme.{u}) (M : X.Modules) (U T : X.Opens) (h : T ≤ U)
      (f : SheafOfModules.free (R := X.ringCatSheaf.over U)
        (ULift.{u} (Fin (n + 1))) ≅ M.over U) =>
    (show Module.Basis (Fin (n + 1)) Γ(X, T) Γ(M, T) from
    (show Module.Basis (Fin (n + 1)) ((X.sheaf.over U).obj.obj
      (op (Over.mk (homOfLE h))))
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (homOfLE h)))).obj ((M).over U)) from
    (SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) (n + 1)
      (op (Over.mk (homOfLE h)))).map
        (((SheafOfModules.evaluation (X.ringCatSheaf.over U)
          (op (Over.mk (homOfLE h)))).mapIso f).toLinearEquiv))))
    (ProjectiveSpace R ι) (eulerMiddle R ι) (coordinateOpen R ι i) T hi
      (determinantMiddleOrderedOverFreeIso R ι n e i)

theorem determinantMiddleSectionsBasis_apply (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) (a : Fin (n + 1)) :
    determinantMiddleSectionsBasis R ι n e i hi a =
      eulerMiddleGenerator R ι i (e.symm a) hi := by
  simpa only [determinantMiddleSectionsBasis] using
    overFreeOriginalSectionsBasis_apply (ProjectiveSpace R ι) (eulerMiddle R ι)
      (n + 1) (coordinateOpen R ι i) T hi (determinantMiddleOrderedOverFreeIso R ι n e i) a _
      (determinantMiddleOrderedOverFreeIso_hom_generator R ι n e i a hi)



theorem determinantEulerDifferential_coordinate_ratio (i j : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (eulerDifferential R ι).val.app (op ((coordinateOpen R ι i).ι ''ᵁ W))
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j ((coordinateOpen R ι i).ι_image_le W))) =
      eulerKernelGenerator R ι i j ((coordinateOpen R ι i).ι_image_le W) := by
  let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
  let E := eulerMiddle R ι
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  let q := (coordinateOpenIsoSpecPolynomial R ι i).hom
  let g := eulerPolynomialChart R ι i
  let h := determinantCoordinateChart_image R ι i W
  let hp := eulerPolynomialChart_image_le R ι i (q ''ᵁ W)
  let t := eulerCoordinateRatio R ι i j hp
  have hd : Ω.val.map (eqToHom h).op (d.d t) =
      d.d (eulerCoordinateRatio R ι i j ((coordinateOpen R ι i).ι_image_le W)) :=
    (d.d_map (eqToHom h).op t).symm.trans
      (congrArg d.d (eulerCoordinateRatio_restrict R ι i j h.le hp))
  have hn := PresheafOfModules.naturality_apply (eulerDifferential R ι).val
    (eqToHom h).op (d.d t)
  have he := eulerDifferential_d_ratio R ι i j (q ''ᵁ W)
  have hk := eulerKernelGenerator_restrict R ι i j h.le hp
  exact (congrArg ((eulerDifferential R ι).val.app
    (op ((coordinateOpen R ι i).ι ''ᵁ W))) hd).symm.trans
      (hn.trans ((congrArg (E.val.map (eqToHom h).op) he).trans hk))

theorem determinantEulerDifferential_ratio_section (i j : ι) :
    SheafOfModules.sectionsMap ((eulerDifferential R ι).over (coordinateOpen R ι i))
      (determinantRatioDifferentialOverSection R ι i j) =
      determinantKernelGeneratorOverSection R ι i j := by
  apply overSections_ext (coordinateOpen R ι i)
  intro W
  exact determinantEulerDifferential_coordinate_ratio R ι i j W

theorem determinantEulerDifferential_ratio (i j : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    (eulerDifferential R ι).val.app (op T)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i j hi)) = eulerKernelGenerator R ι i j hi :=
  congrArg (fun s => s.val (op (Over.mk (homOfLE hi))))
    (determinantEulerDifferential_ratio_section R ι i j)

theorem determinantEulerPivot_augmentation (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    (eulerAugmentation R ι).val.app (op T) (eulerMiddleGenerator R ι i i hi) =
      (1 : Γ(ProjectiveSpace R ι, T)) :=
  (eulerAugmentation_generator R ι i i hi).trans (eulerCoordinateRatio_self R ι i hi)

/-- The difference of the original Euler pivots is the original differential image. -/
theorem determinantEulerPivot_difference (i k : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (hk : T ≤ coordinateOpen R ι k) :
    eulerMiddleGenerator R ι k k hk - eulerMiddleGenerator R ι i i hi =
      (eulerDifferential R ι).val.app (op T)
        ((coordinateTransitionOn R ι i k hi hk).val •
          (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
            (eulerCoordinateRatio R ι i k hi)) := by
  let u := coordinateTransitionOn R ι i k hi hk
  let d := Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)
  have hR : (eulerDifferential R ι).val.app (op T)
      (u.val • d.d (eulerCoordinateRatio R ι i k hi)) =
      u.val • eulerKernelGenerator R ι i k hi :=
    (((eulerDifferential R ι).val.app (op T)).hom.map_smul u.val
      (d.d (eulerCoordinateRatio R ι i k hi))).trans
        (congrArg (fun a => u.val • a) (determinantEulerDifferential_ratio R ι i k hi))
  apply Eq.trans _ hR.symm
  rw [eulerMiddleGenerator_transition R ι i k k hi hk]
  change u.val • eulerMiddleGenerator R ι i k hi - eulerMiddleGenerator R ι i i hi =
    u.val • (eulerMiddleGenerator R ι i k hi -
      eulerCoordinateRatio R ι i k hi • eulerMiddleGenerator R ι i i hi)
  rw [smul_sub, smul_smul, eulerCoordinateRatio_transition_inverse R ι i k hi hk]
  change u.val • eulerMiddleGenerator R ι i k hi - eulerMiddleGenerator R ι i i hi =
    u.val • eulerMiddleGenerator R ι i k hi -
      (u.val * u.inv) • eulerMiddleGenerator R ι i i hi
  rw [u.val_inv, one_smul]


private theorem basis_det_pivot {S : Type u} [CommRing S]
    {B : Type u} [AddCommGroup B] [Module S B] (n : ℕ)
    (b : Module.Basis (Fin (n + 1)) S B) (p : Fin (n + 1)) (h : Fin n → S) :
    b.det (Fin.cases (b p) (fun a => b (p.succAbove a) - h a • b p)) =
      (-1 : S) ^ p.val := by
  classical
  have H : b.toMatrix (Fin.cases (b p)
      (fun a => b (p.succAbove a) - h a • b p)) = determinantPivotFirstMatrix n p h := by
    ext r c
    refine Fin.cases ?_ (fun a => ?_) c
    · simp [Module.Basis.toMatrix_apply, determinantPivotFirstMatrix, Finsupp.single_apply, eq_comm]
    · simp [Module.Basis.toMatrix_apply, determinantPivotFirstMatrix, Finsupp.single_apply, eq_comm]
  change (b.toMatrix _).det = _
  rw [H, determinantPivotFirstMatrix_det]

/-- The original target tensor generator retains the original transition unit to its full power. -/
theorem differentialDeterminantTargetGenerator_transition (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (i k : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (hk : T ≤ coordinateOpen R ι k) :
    differentialDeterminantTargetGenerator R ι n e k hk =
      (coordinateTransitionOn R ι i k hi hk).val ^ (n + 1) •
        differentialDeterminantTargetGenerator R ι n e i hi := by
  let X := ProjectiveSpace R ι
  let L := twistingSheaf R ι (-(n + 1 : ℤ))
  let M := determinantCoefficientSheaf R ι n
  let m : Γ(M, T) := (determinantCoefficientSection R ι n e).val (op T)
  let η := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
    (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L) ⊗
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))
  have hL : twistingGenerator R ι (-(n + 1 : ℤ)) k hk =
      (coordinateTransitionOn R ι i k hi hk).val ^ (n + 1) •
        twistingGenerator R ι (-(n + 1 : ℤ)) i hi := by
    simpa only [neg_neg, zpow_add, zpow_natCast, zpow_one, Units.val_mul,
      Units.val_pow_eq_pow_val, pow_succ] using
      twistingGenerator_transition R ι (-(n + 1 : ℤ)) i k hi hk
  change η.app (op T) (twistingGenerator R ι (-(n + 1 : ℤ)) k hk ⊗ₜ[Γ(X, T)] m) =
    (coordinateTransitionOn R ι i k hi hk).val ^ (n + 1) •
      η.app (op T) (twistingGenerator R ι (-(n + 1 : ℤ)) i hi ⊗ₜ[Γ(X, T)] m)
  exact (congrArg (fun s : Γ(L, T) => η.app (op T) (s ⊗ₜ[Γ(X, T)] m)) hL).trans (by
    rw [← TensorProduct.smul_tmul', (η.app (op T)).hom.map_smul])

private theorem overFreeSectionsBasis_det (X : Scheme.{u}) (M : X.Modules) (m : ℕ)
    (U : X.Opens) (f : SheafOfModules.free (R := X.ringCatSheaf.over U)
      (ULift.{u} (Fin m)) ≅ M.over U) (V : (Over U)ᵒᵖ)
    (s : Fin m → (SheafOfModules.evaluation (X.ringCatSheaf.over U) V).obj (M.over U)) :
    ((SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) m V).map
      (((SheafOfModules.evaluation (X.ringCatSheaf.over U) V).mapIso f).toLinearEquiv)).det s =
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) m V).det
        (fun a => f.inv.val.app V (s a)) := by
  rw [Module.Basis.det_map]
  rfl

theorem determinantOmegaOverIso_mk (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    let U := coordinateOpen R ι i
    let V := op (Over.mk (homOfLE hi))
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    ∀ s : Fin n → (SheafOfModules.evaluation ((ProjectiveSpace R ι).ringCatSheaf.over U) V).obj
      (Ω.over U),
    (determinantOmegaOverIso R ι n e i).hom.val.app V
      ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf Ω n).app
        (op T) s) = (determinantOmegaSectionsBasis R ι n e i hi).det s := by
  intro U V Ω s
  exact (moduleExteriorTopOverIso_mk (ProjectiveSpace R ι) Ω n U
    (determinantOmegaOrderedOverFreeIso R ι n e i).symm V s).trans
      (overFreeSectionsBasis_det (ProjectiveSpace R ι) Ω n U
        (determinantOmegaOrderedOverFreeIso R ι n e i) V s).symm


private theorem overUnitIso_inv_scalar (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U))
    (f : M ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (V : (Over U)ᵒᵖ)
    (t : M.val.obj V)
    (ht : f.hom.val.app V t = (1 : (X.sheaf.over U).obj.obj V))
    (c : (X.sheaf.over U).obj.obj V) : f.inv.val.app V c = c • t := by
  have hv : f.inv.val.app V (1 : (X.sheaf.over U).obj.obj V) = t :=
    (congrArg (f.inv.val.app V) ht).symm.trans
      (ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app V) f.hom_inv_id) t)
  have hs := (f.inv.val.app V).hom.map_smul c (1 : (X.sheaf.over U).obj.obj V)
  have hs' : f.inv.val.app V c = c • f.inv.val.app V (1 : (X.sheaf.over U).obj.obj V) := by
    simpa only [smul_eq_mul, mul_one] using hs
  exact hs'.trans (congrArg (c • ·) hv)

/-- The existing actual chart isomorphism evaluates arbitrary original wedges by its original
frame. -/
theorem differentialDeterminantChartIso_mk (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    let U := coordinateOpen R ι i
    let V := op (Over.mk (homOfLE hi))
    let Ω := Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
    ∀ s : Fin n → (SheafOfModules.evaluation ((ProjectiveSpace R ι).ringCatSheaf.over U) V).obj
      (Ω.over U),
    (differentialDeterminantChartIso R ι n e i).hom.val.app V
      ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf Ω n).app
        (op T) s) =
      ((-1 : Γ(ProjectiveSpace R ι, T)) ^ (e i).val *
        (determinantOmegaSectionsBasis R ι n e i hi).det s) •
          differentialDeterminantTargetGenerator R ι n e i hi := by
  intro U V Ω s
  let w := (SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf Ω n).app
    (op T) s
  let f := differentialDeterminantTargetOverIso R ι n e i
  let t := differentialDeterminantTargetGenerator R ι n e i hi
  let b := determinantOmegaSectionsBasis R ι n e i hi
  have hf : f.inv.val.app V (b.det s) = b.det s • t :=
    overUnitIso_inv_scalar (ProjectiveSpace R ι) U _ f V t
      (differentialDeterminantTargetOverIso_generator R ι n e i V) (b.det s)
  let c := determinantOmegaOverIso R ι n e i ≪≫ f.symm
  have hc : c.hom.val.app V w = b.det s • t :=
    (congrArg (f.inv.val.app V) (determinantOmegaOverIso_mk R ι n e i hi s)).trans hf
  let z : ℤ := (-1) ^ (e i).val
  have hz : ((z • c.hom).val.app V) w = z • (c.hom.val.app V w) := by
    change (((SheafOfModules.forget ((ProjectiveSpace R ι).ringCatSheaf.over U)).map
      (z • c.hom)).app V) w = _
    erw [Functor.map_zsmul, PresheafOfModules.zsmul_app]
    rfl
  change ((z • c.hom).val.app V) w = _
  exact hz.trans ((congrArg (fun x => z • x) hc).trans (by
    rw [← Int.cast_smul_eq_zsmul Γ(ProjectiveSpace R ι, T)]
    simp only [z, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul]
    rfl))

/-- The pivot-first scalar form of the same original transported Euler middle frame. -/
def determinantEulerPivotForm (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    Γ(Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι), T)
      [⋀^Fin n]→ₗ[Γ(ProjectiveSpace R ι, T)] Γ(ProjectiveSpace R ι, T) :=
  ((determinantMiddleSectionsBasis R ι n e i hi).det.curryLeft
    (eulerMiddleGenerator R ι i i hi)).compLinearMap
      ((eulerDifferential R ι).val.app (op T)).hom

theorem determinantEulerPivotForm_basis (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    determinantEulerPivotForm R ι n e i hi (determinantOmegaSectionsBasis R ι n e i hi) =
      (-1 : Γ(ProjectiveSpace R ι, T)) ^ (e i).val := by
  let b := determinantMiddleSectionsBasis R ι n e i hi
  let h := fun a : Fin n => eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a)) hi
  have hp : eulerMiddleGenerator R ι i i hi = b (e i) := by
    rw [determinantMiddleSectionsBasis_apply]
    simp only [Equiv.symm_apply_apply]
  have hk (a : Fin n) : (eulerDifferential R ι).val.app (op T)
      (determinantOmegaSectionsBasis R ι n e i hi a) =
      b ((e i).succAbove a) - h a • b (e i) := by
    rw [determinantOmegaSectionsBasis_apply, determinantEulerDifferential_ratio]
    change eulerMiddleGenerator R ι i (e.symm ((e i).succAbove a)) hi -
      h a • eulerMiddleGenerator R ι i i hi = _
    rw [determinantMiddleSectionsBasis_apply, determinantMiddleSectionsBasis_apply]
    simp only [Equiv.symm_apply_apply]
  change b.det (Matrix.vecCons (eulerMiddleGenerator R ι i i hi)
    (fun a => (eulerDifferential R ι).val.app (op T)
      (determinantOmegaSectionsBasis R ι n e i hi a))) = _
  have H : Matrix.vecCons (eulerMiddleGenerator R ι i i hi)
      (fun a => (eulerDifferential R ι).val.app (op T)
        (determinantOmegaSectionsBasis R ι n e i hi a)) =
      Fin.cases (b (e i)) (fun a => b ((e i).succAbove a) - h a • b (e i)) := by
    funext a
    exact Fin.cases hp (fun a => hk a) a
  exact (congrArg b.det H).trans (basis_det_pivot n b (e i) h)

theorem determinantEulerPivotForm_apply (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (s : Fin n → Γ(Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι), T)) :
    determinantEulerPivotForm R ι n e i hi s =
      (-1 : Γ(ProjectiveSpace R ι, T)) ^ (e i).val *
        (determinantOmegaSectionsBasis R ι n e i hi).det s := by
  exact (congrArg (fun F => F s)
    ((determinantEulerPivotForm R ι n e i hi).eq_smul_basis_det
      (determinantOmegaSectionsBasis R ι n e i hi))).trans (by
        rw [determinantEulerPivotForm_basis, AlternatingMap.smul_apply, smul_eq_mul])


/-- Above-rank vanishing and the original pivot difference give the same-frame transition law. -/
theorem determinantEulerPivotForm_transition (n : ℕ) (e : ι ≃ Fin (n + 1)) (i k : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (hk : T ≤ coordinateOpen R ι k)
    (s : Fin n → Γ(Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι), T)) :
    determinantEulerPivotForm R ι n e i hi s =
      (coordinateTransitionOn R ι i k hi hk).val ^ (n + 1) *
        determinantEulerPivotForm R ι n e k hk s := by
  let b := determinantMiddleSectionsBasis R ι n e i hi
  let c := determinantMiddleSectionsBasis R ι n e k hk
  let u := coordinateTransitionOn R ι i k hi hk
  let η := ((eulerDifferential R ι).val.app (op T)).hom
  let p := eulerMiddleGenerator R ι i i hi
  let q := eulerMiddleGenerator R ι k k hk
  have hbc (a : Fin (n + 1)) : c a = u.val • b a :=
    (determinantMiddleSectionsBasis_apply R ι n e k hk a).trans
      ((eulerMiddleGenerator_transition R ι i k (e.symm a) hi hk).trans
        (congrArg (u.val • ·) (determinantMiddleSectionsBasis_apply R ι n e i hi a).symm))
  have hp := pivot_form_independent n (determinantOmegaSectionsBasis R ι n e i hi) η
    b.det p q (u.val •
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι i k hi))
      (determinantEulerPivot_difference R ι i k hi hk) s
  change b.det (Matrix.vecCons q (η ∘ s)) =
    b.det (Matrix.vecCons p (η ∘ s)) at hp
  change b.det (Matrix.vecCons p (η ∘ s)) =
    u.val ^ (n + 1) * c.det (Matrix.vecCons q (η ∘ s))
  exact hp.symm.trans (basis_determinant_scale (n + 1) b c u.val hbc _)

/-- The original chart maps agree on every original wedge on a common subopen. -/
theorem differentialDeterminantChartIso_mk_overlap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (i k : ι) {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (hk : T ≤ coordinateOpen R ι k)
    (s : Fin n → Γ(Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι), T)) :
    (differentialDeterminantChartIso R ι n e i).hom.val.app
        (op (Over.mk (homOfLE hi)))
        ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
          (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).app (op T) s) =
      (differentialDeterminantChartIso R ι n e k).hom.val.app
        (op (Over.mk (homOfLE hk)))
        ((SheafOfModulesOfCommRing.exteriorPowerMk (ProjectiveSpace R ι).sheaf
          (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).app
            (op T) s) := by
  rw [differentialDeterminantChartIso_mk, differentialDeterminantChartIso_mk,
    ← determinantEulerPivotForm_apply, ← determinantEulerPivotForm_apply,
    determinantEulerPivotForm_transition R ι n e i k hi hk,
    differentialDeterminantTargetGenerator_transition R ι n e i k hi hk, smul_smul]
  rw [mul_comm]

/-- The original chart isomorphism on any smaller open, with the native over-composition
isomorphisms retained. -/
def differentialDeterminantChartIsoOn (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i) :
    (moduleExteriorPower (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).over T ≅
      (differentialDeterminantTarget R ι n).over T :=
  ((SheafOfModules.overFunctorMap (ProjectiveSpace R ι).ringCatSheaf
    (homOfLE hi)).app _).symm ≪≫
  (SheafOfModules.overMap (ProjectiveSpace R ι).ringCatSheaf (homOfLE hi)).mapIso
    (differentialDeterminantChartIso R ι n e i) ≪≫
  ((SheafOfModules.overFunctorMap (ProjectiveSpace R ι).ringCatSheaf (homOfLE hi)).app _)

private theorem chartIsoOn_hom_app (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (V : (Over T)ᵒᵖ) (s : ((moduleExteriorPower (ProjectiveSpace R ι)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n).over T).val.obj V) :
    (differentialDeterminantChartIsoOn R ι n e i hi).hom.val.app V s =
      (differentialDeterminantChartIso R ι n e i).hom.val.app
        (op ((Over.map (homOfLE hi)).obj V.unop)) s := by
  rfl

/-- Literal original chart arrows agree after actual native restriction to every common open. -/
theorem differentialDeterminantChartIsoOn_eq (n : ℕ) (e : ι ≃ Fin (n + 1)) (i k : ι)
    {T : (ProjectiveSpace R ι).Opens} (hi : T ≤ coordinateOpen R ι i)
    (hk : T ≤ coordinateOpen R ι k) :
    differentialDeterminantChartIsoOn R ι n e i hi =
      differentialDeterminantChartIsoOn R ι n e k hk := by
  apply Iso.ext
  apply (cancel_epi (moduleExteriorPowerOverIso (ProjectiveSpace R ι)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n T).hom).mp
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext
    ((ProjectiveSpace R ι).sheaf.over T)
    ((Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).over T)
    ((differentialDeterminantTarget R ι n).over T) n
  intro V s
  change (differentialDeterminantChartIsoOn R ι n e i hi).hom.val.app V
      ((moduleExteriorPowerOverIso (ProjectiveSpace R ι)
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n T).hom.val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk ((ProjectiveSpace R ι).sheaf.over T)
          ((Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).over T) n).app
            V s)) =
    (differentialDeterminantChartIsoOn R ι n e k hk).hom.val.app V
      ((moduleExteriorPowerOverIso (ProjectiveSpace R ι)
        (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)) n T).hom.val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk ((ProjectiveSpace R ι).sheaf.over T)
          ((Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).over T) n).app
            V s))
  rw [moduleExteriorPowerOverIso_hom_mk, chartIsoOn_hom_app, chartIsoOn_hom_app]
  exact differentialDeterminantChartIso_mk_overlap R ι n e i k
    ((leOfHom V.unop.hom).trans hi) ((leOfHom V.unop.hom).trans hk) s


end AlgebraicGeometry.ProjectiveSpace
