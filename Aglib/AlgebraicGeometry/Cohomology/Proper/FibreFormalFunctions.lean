/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreIdempotents
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningSectionsReduction
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Nilpotent
public import Aglib.AlgebraicGeometry.FundamentalGroup.SectionLifting
public import Mathlib.RingTheory.Etale.Pi

/-!
# Actual idempotent images on proper ideal thickenings

Finite étale invariance along the actual nilpotent thickenings supplies compatible
finite-order lifts of an original idempotent. The canonical formal-functions
comparison then supplies an original cohomology class representing its first
geometric coordinate. The native degree-zero structure-unit comparisons turn this
into an actual global function with the required restriction.

Only one quotient coordinate is lifted from completion; neither a completed class
nor an idempotent representative in the original ring is asserted to lift.
The ordinary ring-stalk comparison is provided by the upper `Stalk` leaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

universe u v w

private theorem exists_original_coordinate
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (Q : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (uMap : ∀ n : ℕ, M →ₗ[R] Q.obj (op n))
    (hu : ∀ {m n : ℕ} (h : m ≤ n),
      (AdicCompletion.towerTransition Q h).comp (uMap n) = uMap m)
    (hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) ≤ (uMap n).ker)
    (hsurj : Function.Surjective (AdicCompletion.completionToSections I Q uMap hu hpow))
    (s : ModuleCat.sectionsSubmodule Q) (n : ℕ) :
    ∃ a : M, uMap n a = s.val (op n) := by
  obtain ⟨x, rfl⟩ := hsurj s
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (p := (I ^ n • ⊤ : Submodule R M)) (AdicCompletion.eval I M n x)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.completionToSections_apply, ← ha,
    AdicCompletion.quotientToTower_mk]

/-- Every coordinate of an actual compatible proper thickening family is the
literal geometric restriction of an original cohomology class. -/
theorem exists_original_geometric_coordinate
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) (hF : affineLocallyFiniteType X F) (p : ℕ)
    (s : ModuleCat.sectionsSubmodule
      (properIdealThickeningCohomologyTower f F hF I p)) (n : ℕ) :
    ∃ x : (moduleCohomologyFunctorOfHom X (affineFormalFunctionsScalar f) p).obj F,
      moduleCohomologyPullback (idealThickeningι f (I ^ n)) F p x = s.val (op n) := by
  let α := affineFormalFunctionsScalar f
  let e := properIdealQuotientThickeningSectionsEquiv (CommRingCat.of A) f F hF I p
  let t := e.symm s
  obtain ⟨x, hx⟩ := exists_original_coordinate I
    (idealPowerQuotientCohomology X α F I p)
    (idealPowerCohomologyReductionMap X α F I p)
    (idealPowerCohomologyReductionMap_compatible X α F I p)
    (fun n => idealPowerQuotientReduction_pow_le_ker X α F I n p)
    (moduleCohomologyFormalFunctions_bijective I f F hF p).2 t n
  refine ⟨x, ?_⟩
  have he := properIdealQuotientThickeningSectionsEquiv_reduction
    (CommRingCat.of A) f F hF I p t x n hx.symm
  change (e (e.symm s)).val (op n) = _ at he
  rw [e.apply_symm_apply] at he
  exact he.symm

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The universal idempotent of the actual relative two-point algebra. -/
def twoPointIdempotent (A : Type u) [CommRing A] : Bool → A :=
  fun b => if b then 0 else 1

theorem twoPointIdempotent_idempotent (A : Type u) [CommRing A] :
    IsIdempotentElem (twoPointIdempotent A) := by
  ext b
  cases b <;> simp [twoPointIdempotent]

/-- The ring map determined by an original idempotent and the original constants. -/
def twoPointRingHom (α : A →+* B) (e : B) (he : IsIdempotentElem e) :
    (Bool → A) →+* B where
  toFun v := α (v false) * e + α (v true) * (1 - e)
  map_zero' := by simp
  map_one' := by simp
  map_add' v w := by
    simp only [Pi.add_apply, map_add]
    ring
  map_mul' v w := by
    simp only [Pi.mul_apply, map_mul]
    have he2 : e ^ 2 = e := by simpa only [pow_two] using he.eq
    ring_nf
    simp only [he2]
    ring

theorem twoPointRingHom_idempotent (α : A →+* B) (e : B) (he : IsIdempotentElem e) :
    twoPointRingHom α e he (twoPointIdempotent A) = e := by
  simp [twoPointRingHom, twoPointIdempotent]

theorem twoPointRingHom_constants (α : A →+* B) (e : B) (he : IsIdempotentElem e) :
    (twoPointRingHom α e he).comp (algebraMap A (Bool → A)) = α := by
  ext a
  change α a * e + α a * (1 - e) = α a
  ring

/-- The actual finite étale two-point cover over the specified ring. -/
def twoPointCover (A : Type u) [CommRing A] : FiniteEtale (Spec (.of A)) := by
  refine ⟨Over.mk (Spec.algebraMap A (Bool → A)), ?_, ?_⟩
  · change IsFinite (Spec.algebraMap A (Bool → A))
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · change Etale (Spec.algebraMap A (Bool → A))
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)

variable {S : Scheme.{u}} (p : S ⟶ Spec (.of A))

/-- An original idempotent is an actual map to the relative two-point spectrum. -/
def idempotentTwoPointMap (e : Γ(S, ⊤)) (he : IsIdempotentElem e) :
    S ⟶ Spec (.of (Bool → A)) :=
  (ΓSpec.adjunction.homEquiv S (op (.of (Bool → A))))
    (CommRingCat.ofHom
      (twoPointRingHom (affineFormalFunctionsScalar p) e he)).op

theorem idempotentTwoPointMap_over (e : Γ(S, ⊤)) (he : IsIdempotentElem e) :
    idempotentTwoPointMap p e he ≫ Spec.algebraMap A (Bool → A) = p := by
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of A)).inv).mp
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rw [idempotentTwoPointMap, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  apply CommRingCat.hom_ext
  exact twoPointRingHom_constants (affineFormalFunctionsScalar p) e he

/-- Reading the universal idempotent along the original map recovers the original section. -/
theorem idempotentTwoPointMap_value (e : Γ(S, ⊤)) (he : IsIdempotentElem e) :
    (idempotentTwoPointMap p e he).appTop
      ((Scheme.ΓSpecIso (.of (Bool → A))).inv (twoPointIdempotent A)) = e :=
  (ConcreteCategory.congr_hom
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom (twoPointRingHom (affineFormalFunctionsScalar p) e he)))
    (twoPointIdempotent A)).trans
      (twoPointRingHom_idempotent (affineFormalFunctionsScalar p) e he)

private theorem finiteEtale_baseChange_first {X T : Scheme.{u}} (j : T ⟶ X)
    {C D : FiniteEtale X} (s : C ⟶ D) :
    ((baseChange j).map s).hom.left ≫ pullback.fst D.obj.hom j =
      pullback.fst C.obj.hom j ≫ s.hom.left := pullback.lift_fst _ _ _

private theorem finiteEtale_baseChange_second {X T : Scheme.{u}} (j : T ⟶ X)
    {C D : FiniteEtale X} (s : C ⟶ D) :
    ((baseChange j).map s).hom.left ≫ pullback.snd D.obj.hom j =
      pullback.snd C.obj.hom j := pullback.lift_snd _ _ _

/-- Faithfulness of the actual finite-étale base change gives uniqueness of actual sections. -/
theorem finiteEtale_section_ext {X T : Scheme.{u}} (j : T ⟶ X)
    [(baseChange j).Faithful] (C : FiniteEtale X)
    (s t : X ⟶ C.obj.left) (hs : s ≫ C.obj.hom = 𝟙 X)
    (ht : t ≫ C.obj.hom = 𝟙 X) (h : j ≫ s = j ≫ t) : s = t := by
  let s' : SectionLifting.identityCover X ⟶ C := ⟨Over.homMk s hs⟩
  let t' : SectionLifting.identityCover X ⟶ C := ⟨Over.homMk t ht⟩
  have hm : (baseChange j).map s' = (baseChange j).map t' := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · erw [finiteEtale_baseChange_first, finiteEtale_baseChange_first]
      change pullback.fst (𝟙 X) j ≫ s = pullback.fst (𝟙 X) j ≫ t
      have hi : pullback.fst (𝟙 X) j = pullback.snd (𝟙 X) j ≫ j := by
        simpa using (pullback.condition (f := 𝟙 X) (g := j))
      rw [hi, Category.assoc, Category.assoc, h]
    · erw [finiteEtale_baseChange_second, finiteEtale_baseChange_second]
  exact congrArg (fun k : SectionLifting.identityCover X ⟶ C => k.hom.left)
    ((baseChange j).map_injective hm)

/-- The actual fullness supplier lifts maps to a finite étale cover over a fixed base. -/
def finiteEtaleLiftMap {X T Z : Scheme.{u}} (j : T ⟶ X)
    [(baseChange j).Full] (q : X ⟶ Z) (C : FiniteEtale Z)
    (s : T ⟶ C.obj.left) (hs : s ≫ C.obj.hom = j ≫ q) : X ⟶ C.obj.left :=
  SectionLifting.liftedSection j ((baseChange q).obj C)
    (pullback.lift s j hs) (pullback.lift_snd _ _ _) ≫ pullback.fst C.obj.hom q

theorem finiteEtaleLiftMap_over {X T Z : Scheme.{u}} (j : T ⟶ X)
    [(baseChange j).Full] (q : X ⟶ Z) (C : FiniteEtale Z)
    (s : T ⟶ C.obj.left) (hs : s ≫ C.obj.hom = j ≫ q) :
    finiteEtaleLiftMap j q C s hs ≫ C.obj.hom = q := by
  have h := congrArg (fun m => m ≫ q)
    (SectionLifting.liftedSection_isSection j ((baseChange q).obj C)
      (pullback.lift s j hs) (pullback.lift_snd _ _ _))
  simpa only [finiteEtaleLiftMap, Category.assoc, pullback.condition,
    baseChange_obj_hom, Category.id_comp] using h


theorem finiteEtaleLiftMap_restrict {X T Z : Scheme.{u}} (j : T ⟶ X)
    [(baseChange j).Full] (q : X ⟶ Z) (C : FiniteEtale Z)
    (s : T ⟶ C.obj.left) (hs : s ≫ C.obj.hom = j ≫ q) :
    j ≫ finiteEtaleLiftMap j q C s hs = s := by
  have h := congrArg (fun m => m ≫ pullback.fst C.obj.hom q)
    (SectionLifting.liftedSection_restrict j ((baseChange q).obj C)
      (pullback.lift s j hs) (pullback.lift_snd _ _ _))
  simpa [finiteEtaleLiftMap, FiniteEtale.forget, Category.assoc] using h


/-- Uniqueness retains the original map to the fixed finite étale cover. -/
theorem finiteEtaleLiftMap_unique {X T Z : Scheme.{u}} (j : T ⟶ X)
    [(baseChange j).Faithful] (q : X ⟶ Z) (C : FiniteEtale Z)
    (s t : X ⟶ C.obj.left) (hs : s ≫ C.obj.hom = q)
    (ht : t ≫ C.obj.hom = q) (h : j ≫ s = j ≫ t) : s = t := by
  have he := finiteEtale_section_ext j ((baseChange q).obj C)
    (pullback.lift s (𝟙 X) (by simpa [FiniteEtale.forget] using hs))
    (pullback.lift t (𝟙 X) (by simpa [FiniteEtale.forget] using ht))
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (by
      apply pullback.hom_ext <;> simp [h])
  simpa [FiniteEtale.forget] using
    congrArg (fun k => k ≫ pullback.fst C.obj.hom q) he

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.FiniteEtale
universe u

private theorem quotient_factor_kernel {A : Type u} [CommRing A]
    {I J : Ideal A} (h : I ≤ J) :
    RingHom.ker (Ideal.Quotient.factor h) = J.map (Ideal.Quotient.mk I) := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_quotient_iff_mem h]

private theorem first_power_factor_kernel_nilpotent {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n)))) := by
  rw [quotient_factor_kernel]
  refine ⟨n + 1, ?_⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

/-- The original transition between actual ideal thickenings is Cartesian over the
original quotient-factor map. -/
theorem idealThickeningMap_isPullback {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {J K : Ideal A} (h : J ≤ K) :
    IsPullback (idealThickeningMap f h) (idealThickeningStructure f K)
      (idealThickeningStructure f J)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  have hw : idealThickeningMap f h ≫ idealThickeningStructure f J =
      idealThickeningStructure f K ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
    pullback.lift_snd _ _ _
  apply ((IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).paste_horiz_iff hw).mp
  simpa only [idealThickeningMap_ι, idealThickeningBaseMap_comp] using
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))))

private theorem finiteEtale_baseChange_isEquivalence_of_isIso
    {X T : Scheme.{u}} (j : T ⟶ X) [IsIso j] : (baseChange j).IsEquivalence := by
  let : (baseChange j).Full := baseChange_full_of_isIso j
  let : (baseChange j).Faithful := baseChange_faithful_of_isIso j
  let e : baseChange (inv j) ⋙ baseChange j ≅ 𝟭 (FiniteEtale T) :=
    (baseChangeComp (inv j) j).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.hom_inv_id j)) ≪≫ baseChangeId T
  let : (baseChange j).EssSurj :=
    ⟨fun C => ⟨(baseChange (inv j)).obj C, ⟨e.app C⟩⟩⟩
  exact { }

/-- The actual first thickening and every positive ideal-power thickening have
equivalent finite étale categories under their literal transition. -/
theorem firstThickening_baseChange_isEquivalence {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (I : Ideal A) (n : ℕ) :
    (baseChange (idealThickeningMap f
      (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n)))).IsEquivalence := by
  let h := Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))
  let π := idealThickeningStructure f (I ^ (n + 1))
  let : (baseChange (pullback.fst π q)).IsEquivalence :=
    FiniteEtale.Nilpotent.specMap_pullback_baseChange_isEquivalence
      (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)
      (first_power_factor_kernel_nilpotent I n) π
  let hb := idealThickeningMap_isPullback f h
  let e := hb.isoPullback
  let : (baseChange e.hom).IsEquivalence := finiteEtale_baseChange_isEquivalence_of_isIso _
  have he : e.hom ≫ pullback.fst π q = idealThickeningMap f h := hb.isoPullback_hom_fst
  rw [← he]
  exact Functor.isEquivalence_of_iso (baseChangeComp (pullback.fst π q) e.hom).symm

/-- Literal transition composition follows from the original closed-immersion projection. -/
theorem idealThickeningMap_comp {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I J K : Ideal A}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    idealThickeningMap f hJK ≫ idealThickeningMap f hIJ =
      idealThickeningMap f (hIJ.trans hJK) := by
  apply (cancel_mono (idealThickeningι f I)).mp
  simp only [Category.assoc, idealThickeningMap_ι]

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.FiniteEtale
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (e : Γ(idealThickeningSpace f I, ⊤)) (he : IsIdempotentElem e)

/-- Lift the same original two-point map to every positive ideal-power thickening. -/
def positiveThickeningTwoPointMap (n : ℕ) :
    idealThickeningSpace f (I ^ (n + 1)) ⟶ Spec (.of (Bool → A)) := by
  let j := idealThickeningMap f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))
  let q := idealThickeningι f (I ^ (n + 1)) ≫ f
  let : (baseChange j).IsEquivalence := firstThickening_baseChange_isEquivalence f I n
  let s := idempotentTwoPointMap (idealThickeningι f I ≫ f) e he
  exact finiteEtaleLiftMap j q (twoPointCover A) s (by
    change s ≫ Spec.algebraMap A (Bool → A) = j ≫ q
    rw [idempotentTwoPointMap_over]
    dsimp [j, q]
    rw [← Category.assoc, idealThickeningMap_ι])

theorem positiveThickeningTwoPointMap_over (n : ℕ) :
    positiveThickeningTwoPointMap f I e he n ≫ Spec.algebraMap A (Bool → A) =
      idealThickeningι f (I ^ (n + 1)) ≫ f := by
  let j := idealThickeningMap f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))
  let : (baseChange j).IsEquivalence := firstThickening_baseChange_isEquivalence f I n
  exact finiteEtaleLiftMap_over j _ (twoPointCover A) _ _

theorem positiveThickeningTwoPointMap_restrict (n : ℕ) :
    idealThickeningMap f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n)) ≫
      positiveThickeningTwoPointMap f I e he n =
        idempotentTwoPointMap (idealThickeningι f I ≫ f) e he := by
  let j := idealThickeningMap f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))
  let : (baseChange j).IsEquivalence := firstThickening_baseChange_isEquivalence f I n
  exact finiteEtaleLiftMap_restrict j _ (twoPointCover A) _ _

/-- Compatibility is forced by faithfulness along the same first thickening. -/
theorem positiveThickeningTwoPointMap_compatible {m n : ℕ} (h : m ≤ n) :
    idealThickeningMap f
      (Ideal.pow_le_pow_right (I := I) (Nat.add_le_add_right h 1)) ≫
        positiveThickeningTwoPointMap f I e he n =
      positiveThickeningTwoPointMap f I e he m := by
  let j := idealThickeningMap f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero m))
  let : (baseChange j).IsEquivalence := firstThickening_baseChange_isEquivalence f I m
  apply finiteEtaleLiftMap_unique j (idealThickeningι f (I ^ (m + 1)) ≫ f)
    (twoPointCover A)
  · change (idealThickeningMap f
        (Ideal.pow_le_pow_right (I := I) (Nat.add_le_add_right h 1)) ≫
        positiveThickeningTwoPointMap f I e he n) ≫
          Spec.algebraMap A (Bool → A) = _
    rw [Category.assoc, positiveThickeningTwoPointMap_over,
      ← Category.assoc, idealThickeningMap_ι]
  · exact positiveThickeningTwoPointMap_over f I e he m
  · rw [← Category.assoc, idealThickeningMap_comp,
      positiveThickeningTwoPointMap_restrict, positiveThickeningTwoPointMap_restrict]

/-- The actual universal idempotent, read on a positive geometric thickening. -/
def positiveThickeningIdempotent (n : ℕ) : Γ(idealThickeningSpace f (I ^ (n + 1)), ⊤) :=
  (positiveThickeningTwoPointMap f I e he n).appTop
    ((Scheme.ΓSpecIso (.of (Bool → A))).inv (twoPointIdempotent A))

theorem positiveThickeningIdempotent_idempotent (n : ℕ) :
    IsIdempotentElem (positiveThickeningIdempotent f I e he n) := by
  change IsIdempotentElem ((positiveThickeningTwoPointMap f I e he n).appTop
    ((Scheme.ΓSpecIso (.of (Bool → A))).inv (twoPointIdempotent A)))
  exact ((twoPointIdempotent_idempotent A).map
    (Scheme.ΓSpecIso (.of (Bool → A))).inv.hom).map
      (positiveThickeningTwoPointMap f I e he n).appTop.hom

theorem positiveThickeningIdempotent_restrict (n : ℕ) :
    (idealThickeningMap f
      (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))).appTop
        (positiveThickeningIdempotent f I e he n) = e := by
  have h := congrArg (fun q =>
    q.appTop ((Scheme.ΓSpecIso (.of (Bool → A))).inv (twoPointIdempotent A)))
      (positiveThickeningTwoPointMap_restrict f I e he n)
  rw [Scheme.Hom.comp_appTop] at h
  exact h.trans (idempotentTwoPointMap_value (idealThickeningι f I ≫ f) e he)

/-- The actual section family is compatible under the original geometric restrictions. -/
theorem positiveThickeningIdempotent_compatible {m n : ℕ} (h : m ≤ n) :
    (idealThickeningMap f
      (Ideal.pow_le_pow_right (I := I) (Nat.add_le_add_right h 1))).appTop
        (positiveThickeningIdempotent f I e he n) =
      positiveThickeningIdempotent f I e he m := by
  have hh := congrArg (fun q =>
    q.appTop ((Scheme.ΓSpecIso (.of (Bool → A))).inv (twoPointIdempotent A)))
      (positiveThickeningTwoPointMap_compatible f I e he h)
  rw [Scheme.Hom.comp_appTop] at hh
  exact hh

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

namespace AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
universe u v

/-- The actual coefficient map on a pullback triangle preserves the original structure units. -/
theorem pullbackTriangleCoefficientMap_unit
    {X Y Z : Scheme.{u}} (p : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X) (h : j ≫ p = q) :
    pullbackTriangleCoefficientMap (SheafOfModules.unit X.ringCatSheaf) p j q h ≫
      (Scheme.Modules.pushforward j).map (pullbackUnitIso q).hom =
    (pullbackUnitIso p).hom ≫
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
  let O := SheafOfModules.unit X.ringCatSheaf
  have hunit := pullbackUnitIso_homEquiv j
  rw [Adjunction.homEquiv_unit] at hunit
  have hc :
      (Scheme.Modules.pullbackComp j p).hom.app O ≫
        (Scheme.Modules.pullbackCongr h).hom.app O ≫ (pullbackUnitIso q).hom =
      (Scheme.Modules.pullback j).map (pullbackUnitIso p).hom ≫ (pullbackUnitIso j).hom := by
    rw [pullbackUnitIso_congr, pullbackUnitIso_comp]
  rw [pullbackTriangleCoefficientMap, Category.assoc, ← Functor.map_comp,
    Category.assoc, hc, Functor.map_comp, ← Category.assoc]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality
    (pullbackUnitIso p).hom
  change (pullbackUnitIso p).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) =
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.pullback j).map (pullbackUnitIso p).hom) at hn
  exact (congrArg (fun k => k ≫ (Scheme.Modules.pushforward j).map
      (pullbackUnitIso j).hom) hn.symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => (pullbackUnitIso p).hom ≫ k) hunit))

theorem unitSections_map_unitToPushforward {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf)) 0) :
    unitSections Z
      (moduleCohomologyMapAlong j
        (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) 0 x) =
      j.appTop (unitSections Y x) := by
  change Sheaf.H.equiv₀ _ isTerminalTop _ = _
  rw [moduleCohomologyMapAlong_equiv₀, pushforwardSectionsIso_hom_app_apply]
  rfl

theorem unitSections_map_pullbackUnitIso {X Y : Scheme.{u}} (p : Y ⟶ X)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y
      ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf))) 0) :
    unitSections Y (Sheaf.H.map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map (pullbackUnitIso p).hom) 0 x) =
      pullbackUnitSections p x := by
  change Sheaf.H.equiv₀ _ isTerminalTop _ = _
  rw [← Sheaf.H.equiv₀_naturality]
  rfl

/-- Native H0 of the original triangle coefficient map is actual restriction of functions. -/
theorem pullbackUnitSections_triangle
    {X Y Z : Scheme.{u}} (p : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X) (h : j ≫ p = q)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y
      ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf))) 0) :
    pullbackUnitSections q
      (moduleCohomologyMapAlong j
        (pullbackTriangleCoefficientMap (SheafOfModules.unit X.ringCatSheaf) p j q h) 0 x) =
      j.appTop (pullbackUnitSections p x) := by
  rw [← unitSections_map_pullbackUnitIso,
    ← moduleCohomologyMapAlong_postcomp, pullbackTriangleCoefficientMap_unit,
    moduleCohomologyMapAlong_precomp, unitSections_map_unitToPushforward,
    unitSections_map_pullbackUnitIso]

/-- The canonical degree-zero comparison is an actual equivalence of additive groups. -/
def pullbackUnitH0Equiv {X Y : Scheme.{u}} (p : Y ⟶ X) :
    Sheaf.H.{u + 1} (moduleAddSheaf Y
      ((Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf))) 0 ≃+
      Γ(Y, ⊤) :=
  AddEquiv.ofBijective (pullbackUnitSections p) (pullbackUnitSections_bijective p)

/-- Extend an actual compatible positive-coordinate family to the original all-natural tower.
The zeroth coordinate is its original transition from stage one. -/
def sectionsOfPositiveFamily {R : Type u} [CommRing R]
    (Q : ℕᵒᵖ ⥤ ModuleCat.{v} R) (t : ∀ n : ℕ, Q.obj (op (n + 1)))
    (ht : ∀ {m n : ℕ} (h : m ≤ n),
      Q.map (homOfLE (Nat.add_le_add_right h 1)).op (t n) = t m) :
    ModuleCat.sectionsSubmodule Q := by
  let s (n : ℕ) : Q.obj (op n) :=
    match n with
    | 0 => Q.map (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)).op (t 0)
    | n + 1 => t n
  refine ⟨fun j => s j.unop, ?_⟩
  intro j k a
  obtain ⟨n⟩ := j
  obtain ⟨m⟩ := k
  have h : m ≤ n := leOfHom a.unop
  have ha : a = (homOfLE h).op := Subsingleton.elim _ _
  subst a
  change Q.map (homOfLE h).op (s n) = s m
  cases n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst m
      have hi : (homOfLE h).op = 𝟙 (op (0 : ℕ)) := Subsingleton.elim _ _
      rw [hi, Q.map_id]
      rfl
  | succ n =>
      cases m with
      | zero =>
          have hf : (homOfLE h).op =
              (homOfLE (Nat.succ_le_succ (Nat.zero_le n))).op ≫
                (homOfLE (Nat.zero_le 1)).op := Subsingleton.elim _ _
          rw [hf, Q.map_comp]
          change Q.map (homOfLE (Nat.zero_le 1)).op
            (Q.map (homOfLE (Nat.add_le_add_right (Nat.zero_le n) 1)).op (t n)) =
              Q.map (homOfLE (Nat.zero_le 1)).op (t 0)
          rw [ht (Nat.zero_le n)]
      | succ m =>
          exact ht (Nat.le_of_succ_le_succ h)

theorem sectionsOfPositiveFamily_one {R : Type u} [CommRing R]
    (Q : ℕᵒᵖ ⥤ ModuleCat.{v} R) (t : ∀ n : ℕ, Q.obj (op (n + 1)))
    (ht : ∀ {m n : ℕ} (h : m ≤ n),
      Q.map (homOfLE (Nat.add_le_add_right h 1)).op (t n) = t m) :
    (sectionsOfPositiveFamily Q t ht).val (op 1) = t 0 := rfl

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f] (I : Ideal A)
  (e : Γ(idealThickeningSpace f I, ⊤)) (he : IsIdempotentElem e)

/-- The actual lifted function on a positive thickening, in its native H0 coordinates. -/
def positiveThickeningH0Class (n : ℕ) :
    idealThickeningCohomology f (SheafOfModules.unit X.ringCatSheaf) (I ^ (n + 1)) 0 :=
  (pullbackUnitH0Equiv (idealThickeningι f (I ^ (n + 1)))).symm
    (positiveThickeningIdempotent f I e he n)

theorem positiveThickeningH0Class_compatible {m n : ℕ} (h : m ≤ n) :
    (properIdealThickeningCohomologyTower f (SheafOfModules.unit X.ringCatSheaf)
      (affineLocallyFiniteType_unit X) I 0).map
        (homOfLE (Nat.add_le_add_right h 1)).op
          (positiveThickeningH0Class f I e he n) =
      positiveThickeningH0Class f I e he m := by
  apply (pullbackUnitH0Equiv (idealThickeningι f (I ^ (m + 1)))).injective
  change (pullbackUnitH0Equiv (idealThickeningι f (I ^ (m + 1))))
      (idealThickeningCohomologyMap f (SheafOfModules.unit X.ringCatSheaf)
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) 0
        (positiveThickeningH0Class f I e he n)) = _
  rw [idealThickeningCohomologyMap_apply]
  change pullbackUnitSections (idealThickeningι f (I ^ (m + 1)))
      (moduleCohomologyMapAlong
        (idealThickeningMap f (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))
        (idealThickeningCoefficientMap f (SheafOfModules.unit X.ringCatSheaf)
          (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) 0
        (positiveThickeningH0Class f I e he n)) = _
  rw [idealThickeningCoefficientMap, pullbackUnitSections_triangle]
  change (idealThickeningMap f
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).appTop
      ((pullbackUnitH0Equiv _)
        ((pullbackUnitH0Equiv _).symm (positiveThickeningIdempotent f I e he n))) =
    (pullbackUnitH0Equiv _)
      ((pullbackUnitH0Equiv _).symm (positiveThickeningIdempotent f I e he m))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact positiveThickeningIdempotent_compatible f I e he h

/-- An actual idempotent on the first closed subscheme produces a compatible family
in the original geometric H0 tower, including its zeroth coordinate. -/
def idempotentThickeningH0Family :
    ModuleCat.sectionsSubmodule
      (properIdealThickeningCohomologyTower f (SheafOfModules.unit X.ringCatSheaf)
        (affineLocallyFiniteType_unit X) I 0) :=
  sectionsOfPositiveFamily _ (positiveThickeningH0Class f I e he)
    (positiveThickeningH0Class_compatible f I e he)

include he in
/-- Proper formal functions gives an arbitrary original global function restricting
to the given idempotent on the actual ideal thickening. -/
theorem exists_section_restrict_eq_of_isIdempotentElem [IsNoetherianRing A] :
    ∃ a : Γ(X, ⊤), (idealThickeningι f I).appTop a = e := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let s := idempotentThickeningH0Family f I e he
  obtain ⟨x, hx⟩ := exists_original_geometric_coordinate I f O
    (affineLocallyFiniteType_unit X) 0 s 1
  let a := unitSections X x
  have h1 : (idealThickeningι f (I ^ 1)).appTop a =
      positiveThickeningIdempotent f I e he 0 := by
    have h := congrArg (pullbackUnitSections (idealThickeningι f (I ^ 1))) hx
    rw [pullbackUnitSections_moduleCohomologyPullback] at h
    change (idealThickeningι f (I ^ 1)).appTop a =
      (pullbackUnitH0Equiv (idealThickeningι f (I ^ 1)))
        ((pullbackUnitH0Equiv (idealThickeningι f (I ^ 1))).symm
          (positiveThickeningIdempotent f I e he 0)) at h
    rw [AddEquiv.apply_symm_apply] at h
    exact h
  refine ⟨a, ?_⟩
  have h := positiveThickeningIdempotent_restrict f I e he 0
  rw [← h1] at h
  change (idealThickeningMap f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero 0))).appTop
    ((idealThickeningι f (I ^ 1)).appTop a) = e at h
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, idealThickeningMap_ι] at h
  exact h

end AlgebraicGeometry.Scheme.Cohomology.ProperFibreFormalFunctions
