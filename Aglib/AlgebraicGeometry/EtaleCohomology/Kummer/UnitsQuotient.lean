/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Nsmul
public import Aglib.GroupTheory.QuotientGroup.Nsmul
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerPreimage
public import Aglib.AlgebraicGeometry.Picard.Torsion

/-!
# The original units and Picard Kummer exact sequence

For every scheme and every positive invertible level, the original connecting map induces
`0 → Γ(Y, 𝒪_Y)^×/n → H^1(Y, μ_n) → Pic(Y)[n] → 0`. Its maps are constructed on the actual
unit quotient, original Ext cohomology and original Picard torsion subgroup. No curve,
properness or global-unit root hypothesis is imposed. Pullback squares retain the actual
section ring maps, coefficient inclusion and boundary. The curve specialization of Stacks,
Tag 03RR, is a separate consumer.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

variable (Y : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]

/-- `H^0(Y, 𝔾_m) ≃+ Γ(Y, 𝒪_Y)^×`: degree-zero cohomology is the group of global sections. -/
def gmZeroAddEquiv : Sheaf.H.{w} (gm Y) 0 ≃+ Additive Γ(Y, ⊤)ˣ :=
  (Sheaf.H.equiv₀ (gm Y) (etaleTerminalIsTerminal Y)).trans
    (unitsSections Y (op (etaleTerminal Y)))

variable (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Y, ⊤)))

/-- The Kummer boundary `Γ(Y, 𝒪_Y)^× → H^1(Y, μ_n)` on global units. -/
def unitsBoundary : Additive Γ(Y, ⊤)ˣ →+ Sheaf.H.{w} (mu Y n) 1 :=
  (boundary Y n hn hinv 0).comp (gmZeroAddEquiv Y).symm.toAddMonoidHom

/-- The kernel of the units boundary consists exactly of the `n`-th powers. -/
theorem unitsBoundary_eq_zero_iff (a : Additive Γ(Y, ⊤)ˣ) :
    unitsBoundary Y n hn hinv a = 0 ↔ ∃ b, n • b = a := by
  have hker := AddEquiv.ker_comp_eq_range_nsmul_of_exact (gmZeroAddEquiv Y).symm
    (Sheaf.H.map (power Y n) 0) (boundary Y n hn hinv 0) n
    (Sheaf.H.map_nsmul_id (gm Y) 0 n)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (shortExact Y n hn hinv) 0 1 rfl))
  exact SetLike.ext_iff.mp hker a

/-- Equality of additive subgroups: the kernel of the units boundary is `n Γ(Y, 𝒪_Y)^×`. -/
theorem unitsBoundary_ker :
    (unitsBoundary Y n hn hinv).ker =
      (nsmulAddMonoidHom (α := Additive Γ(Y, ⊤)ˣ) n).range := by
  ext a
  exact unitsBoundary_eq_zero_iff Y n hn hinv a

/-- The Kummer map `Γ(Y, 𝒪_Y)^×/n → H^1(Y, μ_n)`. -/
def unitsQuotientBoundary :
    Additive Γ(Y, ⊤)ˣ ⧸ (nsmulAddMonoidHom (α := Additive Γ(Y, ⊤)ˣ) n).range →+
      Sheaf.H.{w} (mu Y n) 1 :=
  QuotientAddGroup.lift _ (unitsBoundary Y n hn hinv) (unitsBoundary_ker Y n hn hinv).symm.le

@[simp] theorem unitsQuotientBoundary_mk (a : Additive Γ(Y, ⊤)ˣ) :
    unitsQuotientBoundary Y n hn hinv (QuotientAddGroup.mk a) = unitsBoundary Y n hn hinv a :=
  rfl

/-- **`Γ(Y, 𝒪_Y)^×/n` injects into `H^1(Y, μ_n)`** on every scheme on which `n > 0` is
invertible. -/
theorem unitsQuotientBoundary_injective :
    Function.Injective (unitsQuotientBoundary Y n hn hinv) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).mpr (unitsBoundary_ker Y n hn hinv).symm

/-- The map `H^1(Y, μ_n) → Pic(Y)`: the inclusion `μ_n → 𝔾_m` on `H^1`, followed by the inverse
of `Picard.picardCohomologyEquiv : Pic(Y) ≃+ H^1(Y, 𝔾_m)`. -/
def rootsPicardMap : Sheaf.H.{w} (mu Y n) 1 →+ PicardGroup Y :=
  (Picard.picardCohomologyEquiv Y).symm.toAddMonoidHom.comp (Sheaf.H.map (inclusion Y n) 1)

/-- **Exactness at `H^1(Y, μ_n)`**: the kernel of `H^1(Y, μ_n) → Pic(Y)` is the image of
`Γ(Y, 𝒪_Y)^×/n`. -/
theorem exact_unitsQuotientBoundary_rootsPicardMap :
    Function.Exact (unitsQuotientBoundary Y n hn hinv) (rootsPicardMap Y n) := by
  have h : Function.Exact (boundary Y n hn hinv 0) (Sheaf.H.map (inclusion Y n) 1) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₁' (shortExact Y n hn hinv) 0 1 rfl)
  intro x
  constructor
  · intro hx
    have hmap : Sheaf.H.map (inclusion Y n) 1 x = 0 := by
      have h' := congrArg (Picard.picardCohomologyEquiv Y) hx
      rw [map_zero] at h'
      change Picard.picardCohomologyEquiv Y ((Picard.picardCohomologyEquiv Y).symm
        (Sheaf.H.map (inclusion Y n) 1 x)) = 0 at h'
      rwa [AddEquiv.apply_symm_apply] at h'
    obtain ⟨c, rfl⟩ := (h x).mp hmap
    refine ⟨QuotientAddGroup.mk (gmZeroAddEquiv Y c), ?_⟩
    change boundary Y n hn hinv 0 ((gmZeroAddEquiv Y).symm (gmZeroAddEquiv Y c)) = _
    rw [AddEquiv.symm_apply_apply]
  · rintro ⟨a, rfl⟩
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      change (Picard.picardCohomologyEquiv Y).symm (Sheaf.H.map (inclusion Y n) 1
        (boundary Y n hn hinv 0 ((gmZeroAddEquiv Y).symm a))) = 0
      rw [h.apply_apply_eq_zero, map_zero]

include hn hinv in
/-- **The image of `H^1(Y, μ_n) → Pic(Y)` is the `n`-torsion `Pic(Y)[n]`.** -/
theorem range_rootsPicardMap :
    (rootsPicardMap Y n).range = Torsion.picardTorsion Y n := by
  have h : Function.Exact (Sheaf.H.map (inclusion Y n) 1) (Sheaf.H.map (power Y n) 1) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' (shortExact Y n hn hinv) 1)
  ext c
  rw [AddMonoidHom.mem_range, Torsion.picardTorsion, AddMonoidHom.mem_ker,
    nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    apply (Picard.picardCohomologyEquiv Y).injective
    change Picard.picardCohomologyEquiv Y (n • (Picard.picardCohomologyEquiv Y).symm
      (Sheaf.H.map (inclusion Y n) 1 x)) = Picard.picardCohomologyEquiv Y 0
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero,
      ← Sheaf.H.map_nsmul_id_apply (gm Y) 1 n]
    exact h.apply_apply_eq_zero x
  · intro hc
    have hpow : Sheaf.H.map (power Y n) 1 (Picard.picardCohomologyEquiv Y c) = 0 := by
      change Sheaf.H.map (n • 𝟙 (gm Y)) 1 (Picard.picardCohomologyEquiv Y c) = 0
      rw [Sheaf.H.map_nsmul_id_apply, ← map_nsmul, hc, map_zero]
    obtain ⟨x, hx⟩ := (h _).mp hpow
    refine ⟨x, ?_⟩
    change (Picard.picardCohomologyEquiv Y).symm (Sheaf.H.map (inclusion Y n) 1 x) = c
    rw [hx, AddEquiv.symm_apply_apply]

/-- The original Picard image with its actual torsion codomain. -/
def rootsPicardTorsionMap : Sheaf.H.{w} (mu Y n) 1 →+ Torsion.picardTorsion Y n :=
  (rootsPicardMap Y n).codRestrict _ (fun x => by
    rw [← range_rootsPicardMap Y n hn hinv]
    exact ⟨x, rfl⟩)

/-- Forgetting the torsion membership recovers the whole original Picard map. -/
theorem rootsPicardTorsionMap_subtype :
    (Torsion.picardTorsion Y n).subtype.comp (rootsPicardTorsionMap Y n hn hinv) =
      rootsPicardMap Y n := rfl

/-- Every actual torsion Picard class is an original Kummer image. -/
theorem rootsPicardTorsionMap_surjective :
    Function.Surjective (rootsPicardTorsionMap Y n hn hinv) := by
  intro c
  have hc : (c : PicardGroup Y) ∈ (rootsPicardMap Y n).range := by
    rw [range_rootsPicardMap Y n hn hinv]
    exact c.property
  obtain ⟨x, hx⟩ := hc
  exact ⟨x, Subtype.ext hx⟩

/-- Exactness with the actual torsion codomain, retaining independent Ext and scheme universes. -/
theorem exact_unitsQuotientBoundary_rootsPicardTorsionMap :
    Function.Exact (unitsQuotientBoundary Y n hn hinv) (rootsPicardTorsionMap Y n hn hinv) := by
  intro x
  constructor
  · intro hx
    exact (exact_unitsQuotientBoundary_rootsPicardMap Y n hn hinv x).mp
      (congrArg Subtype.val hx)
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    exact (exact_unitsQuotientBoundary_rootsPicardMap Y n hn hinv).apply_apply_eq_zero a

section Pullback

variable {X S T : Scheme.{u}}

/-- Pullback of global units by the actual global-section ring map. -/
def unitsPullback (f : S ⟶ X) : Additive Γ(X, ⊤)ˣ →+ Additive Γ(S, ⊤)ˣ :=
  (Units.map f.appTop.hom.toMonoidHom).toAdditive

/-- Global-unit pullback preserves identity. -/
@[simp] theorem unitsPullback_id : unitsPullback (𝟙 X) = AddMonoidHom.id _ := by
  ext a
  rfl

/-- Global-unit pullback preserves composition. -/
theorem unitsPullback_comp (f : S ⟶ X) (g : T ⟶ S) :
    (unitsPullback g).comp (unitsPullback f) = unitsPullback (g ≫ f) := rfl

/-- The original quotient map on units induced by geometric pullback. -/
def unitsQuotientPullback (f : S ⟶ X) (n : ℕ) :
    Additive Γ(X, ⊤)ˣ ⧸ (nsmulAddMonoidHom (α := Additive Γ(X, ⊤)ˣ) n).range →+
      Additive Γ(S, ⊤)ˣ ⧸ (nsmulAddMonoidHom (α := Additive Γ(S, ⊤)ˣ) n).range :=
  QuotientAddGroup.nsmulMap (unitsPullback f) n

/-- The whole unit-quotient construction preserves identity. -/
@[simp] theorem unitsQuotientPullback_id (n : ℕ) :
    unitsQuotientPullback (𝟙 X) n = AddMonoidHom.id _ := by
  rw [unitsQuotientPullback, unitsPullback_id, QuotientAddGroup.nsmulMap_id]

/-- The whole unit-quotient construction preserves composition. -/
theorem unitsQuotientPullback_comp (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    (unitsQuotientPullback g n).comp (unitsQuotientPullback f n) =
      unitsQuotientPullback (g ≫ f) n := by
  rw [unitsQuotientPullback, unitsQuotientPullback, QuotientAddGroup.nsmulMap_comp,
    unitsPullback_comp]
  rfl

/-- Quotient pullback retains the literal global-unit representative. -/
@[simp] theorem unitsQuotientPullback_mk (f : S ⟶ X) (n : ℕ) (a : Additive Γ(X, ⊤)ˣ) :
    unitsQuotientPullback f n (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (unitsPullback f a) := rfl

/-- The original Picard pullback restricted to actual `n`-torsion. -/
def picardTorsionPullback (f : S ⟶ X) (n : ℕ) :
    Torsion.picardTorsion X n →+ Torsion.picardTorsion S n :=
  ((PullbackTensor.Local.pullbackHom f).comp (Torsion.picardTorsion X n).subtype).codRestrict _
    (fun c => by
      change n • (PullbackTensor.Local.pullbackHom f) (c : PicardGroup X) = 0
      have hc : n • (c : PicardGroup X) = 0 := c.property
      rw [← map_nsmul, hc, map_zero])

/-- Forgetting torsion membership recovers original Picard pullback. -/
theorem picardTorsionPullback_subtype (f : S ⟶ X) (n : ℕ) :
    (Torsion.picardTorsion S n).subtype.comp (picardTorsionPullback f n) =
      (PullbackTensor.Local.pullbackHom f).comp (Torsion.picardTorsion X n).subtype := rfl

/-- Torsion Picard pullback preserves identity. -/
@[simp] theorem picardTorsionPullback_id (n : ℕ) :
    picardTorsionPullback (𝟙 X) n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  exact pullbackClass_id (c : PicardGroup X)

/-- Torsion Picard pullback preserves composition. -/
theorem picardTorsionPullback_comp (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    (picardTorsionPullback g n).comp (picardTorsionPullback f n) =
      picardTorsionPullback (g ≫ f) n := by
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  exact (pullbackClass_comp g f (c : PicardGroup X)).symm

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The whole degree-zero Gm comparison is natural for the actual global-unit pullback. -/
theorem gmZeroAddEquiv_naturality (f : S ⟶ X) :
    (gmZeroAddEquiv S).toAddMonoidHom.comp (Picard.gmCohomologyPullback f 0) =
      (unitsPullback f).comp (gmZeroAddEquiv X).toAddMonoidHom := by
  let c := torsorAdjunctionCoefficient f (q := gmUnit f)
  have hsec : globalSectionsPullback f (gm X) ≫ (globalSections S).map c =
      (globalSections X).map (gmUnit f) ≫
        (directImageGlobalSectionsIso f).hom.app (gm S) := by
    dsimp only [globalSectionsPullback]
    rw [Category.assoc, ← (directImageGlobalSectionsIso f).hom.naturality,
      ← Category.assoc, Functor.comp_map, ← Functor.map_comp]
    have hc : (inverseImageAdjunction f).unit.app (gm X) ≫
        (directImage f).map c = gmUnit f :=
      by
        have he := ((inverseImageAdjunction f).homEquiv _ _).apply_symm_apply (gmUnit f)
        rw [Adjunction.homEquiv_apply] at he
        exact he
    rw [hc]
  apply AddMonoidHom.ext
  intro x
  change unitsSections S (op (etaleTerminal S))
      (Sheaf.H.equiv₀ (gm S) (etaleTerminalIsTerminal S)
        (Sheaf.H.map c 0 (cohomologyPullback f (gm X) 0 x))) = _
  rw [← Sheaf.H.equiv₀_naturality, cohomologyPullback_equiv₀]
  change unitsSections S (op (etaleTerminal S))
      ((globalSectionsPullback f (gm X) ≫ (globalSections S).map c)
        (Sheaf.H.equiv₀ (gm X) (etaleTerminalIsTerminal X) x)) = _
  rw [hsec]
  apply Additive.toMul.injective
  change (unitsSections S (op (etaleTerminal S))
      ((gm S).obj.map (siteBaseChangeTerminalIso f).inv.op
        ((gmUnit f).hom.app (op (etaleTerminal X))
          (Sheaf.H.equiv₀ (gm X) (etaleTerminalIsTerminal X) x)))).toMul = _
  let t : S ⟶ CategoryTheory.Limits.pullback (C := Scheme.{u}) (𝟙 X) f :=
    (siteBaseChangeTerminalIso f).inv.left
  have ht : t ≫ CategoryTheory.Limits.pullback.fst (𝟙 X) f = f := by
    have hs : t ≫ CategoryTheory.Limits.pullback.snd (𝟙 X) f = 𝟙 S :=
      (siteBaseChangeTerminalIso f).inv.w
    calc
      t ≫ CategoryTheory.Limits.pullback.fst (𝟙 X) f =
          t ≫ (CategoryTheory.Limits.pullback.fst (𝟙 X) f ≫ 𝟙 X) := by
            rw [Category.comp_id]
      _ = t ≫ CategoryTheory.Limits.pullback.snd (𝟙 X) f ≫ f :=
        congrArg (fun a : CategoryTheory.Limits.pullback (C := Scheme.{u}) (𝟙 X) f ⟶ X =>
          t ≫ a) CategoryTheory.Limits.pullback.condition
      _ = f := by rw [← Category.assoc, hs, Category.id_comp]
  calc
    _ = Units.map (siteBaseChangeTerminalIso f).inv.left.appTop.hom.toMonoidHom
        (unitsSections S ((siteBaseChange f).op.obj (op (etaleTerminal X)))
          ((gmUnit f).hom.app (op (etaleTerminal X))
            (Sheaf.H.equiv₀ (gm X) (etaleTerminalIsTerminal X) x))).toMul :=
      unitsSections_naturality S (siteBaseChangeTerminalIso f).inv.op _
    _ = Units.map (siteBaseChangeTerminalIso f).inv.left.appTop.hom.toMonoidHom
        (Units.map (CategoryTheory.Limits.pullback.fst (𝟙 X) f).appTop.hom.toMonoidHom
          (gmZeroAddEquiv X x).toMul) :=
      congrArg (Units.map (siteBaseChangeTerminalIso f).inv.left.appTop.hom.toMonoidHom)
        (gmUnit_sections f (op (etaleTerminal X)) _)
    _ = _ := by
      apply Units.ext
      exact congrArg (fun q : S ⟶ X => q.appTop (gmZeroAddEquiv X x).toMul.val) ht

/-- The original roots-to-Picard homomorphism commutes with geometric pullback. -/
theorem rootsPicardMap_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPicardMap S n).comp (rootsCohomologyPullback f n hn hinv 1) =
      (PullbackTensor.Local.pullbackHom f).comp (rootsPicardMap X n) := by
  apply AddMonoidHom.ext
  intro x
  apply (Picard.picardCohomologyEquiv S).injective
  change Picard.picardCohomologyEquiv S ((Picard.picardCohomologyEquiv S).symm
      (Sheaf.H.map (inclusion S n) 1 (rootsCohomologyPullback f n hn hinv 1 x))) = _
  rw [AddEquiv.apply_symm_apply, rootsCohomologyPullback_inclusion]
  change _ = Picard.picardCohomologyEquiv S (pullbackClass f
    ((Picard.picardCohomologyEquiv X).symm (Sheaf.H.map (inclusion X n) 1 x)))
  rw [← Picard.picardCohomologyEquiv_pullback, AddEquiv.apply_symm_apply]

/-- The connecting homomorphism on actual global units commutes with pullback. -/
theorem unitsBoundary_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsCohomologyPullback f n hn hinv 1).comp (unitsBoundary X n hn hinv) =
      (unitsBoundary S n hn (levelInvertible f n hinv)).comp (unitsPullback f) := by
  apply AddMonoidHom.ext
  intro a
  change rootsCohomologyPullback f n hn hinv 1
      (boundary X n hn hinv 0 ((gmZeroAddEquiv X).symm a)) = _
  rw [boundary_pullback]
  have h := DFunLike.congr_fun (gmZeroAddEquiv_naturality f) ((gmZeroAddEquiv X).symm a)
  change gmZeroAddEquiv S (Picard.gmCohomologyPullback f 0 ((gmZeroAddEquiv X).symm a)) =
    unitsPullback f (gmZeroAddEquiv X ((gmZeroAddEquiv X).symm a)) at h
  rw [AddEquiv.apply_symm_apply] at h
  change _ = boundary S n hn (levelInvertible f n hinv) 0
    ((gmZeroAddEquiv S).symm (unitsPullback f a))
  rw [← h, AddEquiv.symm_apply_apply]

/-- The injection from the actual quotient of units is natural before evaluation. -/
theorem unitsQuotientBoundary_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsCohomologyPullback f n hn hinv 1).comp (unitsQuotientBoundary X n hn hinv) =
      (unitsQuotientBoundary S n hn (levelInvertible f n hinv)).comp
        (unitsQuotientPullback f n) := by
  apply AddMonoidHom.ext
  intro a
  induction a using QuotientAddGroup.induction_on with
  | H a => exact DFunLike.congr_fun (unitsBoundary_pullback f n hn hinv) a

/-- The surjection to the actual Picard torsion subgroup is natural before evaluation. -/
theorem rootsPicardTorsionMap_pullback (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPicardTorsionMap S n hn (levelInvertible f n hinv)).comp
        (rootsCohomologyPullback f n hn hinv 1) =
      (picardTorsionPullback f n).comp (rootsPicardTorsionMap X n hn hinv) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (rootsPicardMap_pullback f n hn hinv) x

end Pullback

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
