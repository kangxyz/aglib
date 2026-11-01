/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.AffineStein.Reduced
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantUnitOfStructureIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleNoetherian
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.SurjectiveMonomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Noetherian.StrongSerre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.ConstructibleTarget
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme

/-! # Constructibility of original proper direct images in degree zero

For a reduced source and an affine target, the actual affinization has a
finite second map by reduced proper H0 finiteness. Its first map preserves
finite constant coefficients by the original structure-sheaf unit theorem.
The native reduction inclusion removes reducedness, and actual etale open
base change gives affine locality. Finally the finite constant cogenerator
monomorphism and strong Serre closure handle every constructible coefficient.
No higher proper base change or positive-degree constructibility is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Reduced proper sources over an affine Noetherian target have constructible
original direct images of finite constant coefficients. -/
theorem isConstructible_properDirectImage_constant_of_isAffine_of_isReduced
    {X S : Scheme.{u}} [IsReduced X] [IsAffine S] [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (A : Type u) [AddCommGroup A] [Finite A] :
    Constructible.IsConstructible ((directImage f).obj (ConstantFinite.coefficient A X)) := by
  let q := X.toSpecΓ
  let k := Spec.map f.appTop ≫ S.isoSpec.inv
  have hk : IsFinite k := by
    let : IsFinite (Spec.map f.appTop) :=
      (IsFinite.SpecMap_iff f.appTop).mpr
        (AffineStein.finite_coefficient_of_isReduced f ⊤ (isAffineOpen_top S))
    dsimp only [k]
    infer_instance
  let : IsFinite k := hk
  have hfac : q ≫ k = f := by
    dsimp only [q, k]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    change f ≫ S.isoSpec.hom ≫ S.isoSpec.inv = f
    simp
  have : IsProper (q ≫ k) := by rw [hfac]; infer_instance
  let : IsProper q := IsProper.of_comp q k
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let : IsIso q.c := isIso_c_toSpecΓ_of_qcqs X
  let C := Spec Γ(X, ⊤)
  have : IsIso ((inverseImageAdjunction q).unit.app (ConstantFinite.coefficient A C)) :=
    finiteConstant_adjunctionUnit_isIso_of_structureIso q A
  let e : ConstantFinite.coefficient A C ≅
      (directImage q).obj (ConstantFinite.coefficient A X) :=
    asIso ((inverseImageAdjunction q).unit.app (ConstantFinite.coefficient A C)) ≪≫
      (directImage q).mapIso ((inverseImageConstantIso q).app (ConstantFinite.value A))
  have hC : Constructible.IsConstructible
      ((directImage k).obj (ConstantFinite.coefficient A C)) :=
    Finite.isConstructible_directImage_of_isNoetherian k
      (Constructible.isConstructible_constant C (ConstantFinite.value A))
  let E := (directImage k).mapIso e ≪≫
    (directImageCompIso k q).app (ConstantFinite.coefficient A X)
  rw [← hfac]
  exact (Constructible.isConstructible_iff_of_iso E).mp hC

/-- The source reduction removes the reducedness hypothesis without a
nilpotence bound: its original finite-monomorphism unit is an isomorphism. -/
theorem isConstructible_properDirectImage_constant_of_isAffine
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (A : Type u) [AddCommGroup A] [Finite A] :
    Constructible.IsConstructible ((directImage f).obj (ConstantFinite.coefficient A X)) := by
  let i := X.nilradical.subschemeι
  let : IsReduced X.nilradical.subscheme := by
    apply IdealSheafData.subscheme_reduced_of_radical
    rw [← IdealSheafData.vanishingIdeal_support, support_nilradical,
      IdealSheafData.vanishingIdeal_top]
  let : Surjective i := ⟨by
    apply Set.range_eq_univ.mp
    rw [IdealSheafData.range_subschemeι, support_nilradical]
    rfl⟩
  let F := ConstantFinite.coefficient A X
  have : IsIso ((inverseImageAdjunction i).unit.app F) :=
    Finite.surjectiveFiniteMono_unit_app_isIso i F
  let e := (directImage f).mapIso (asIso ((inverseImageAdjunction i).unit.app F)) ≪≫
    (directImageCompIso f i).app ((inverseImage i).obj F) ≪≫
    (directImage (i ≫ f)).mapIso ((inverseImageConstantIso i).app (ConstantFinite.value A))
  exact (Constructible.isConstructible_iff_of_iso e).mpr
    (isConstructible_properDirectImage_constant_of_isAffine_of_isReduced (i ≫ f) A)

/-- Finite constant coefficients have constructible original direct image
under every proper morphism to a Noetherian scheme. -/
theorem isConstructible_properDirectImage_constant
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (A : Type u) [AddCommGroup A] [Finite A] :
    Constructible.IsConstructible ((directImage f).obj (ConstantFinite.coefficient A X)) := by
  apply Constructible.isConstructible_of_affineOpenPullbacks
  intro U
  let : IsAffine U.1.toScheme := U.property
  let : IsNoetherian U.1.toScheme := ⟨⟩
  let p := pullback.fst U.1.ι f
  let a := pullback.snd U.1.ι f
  let e := (etaleBaseChangeIso f U.1.ι).app (ConstantFinite.coefficient A X) ≪≫
    (directImage p).mapIso ((inverseImageConstantIso a).app (ConstantFinite.value A))
  exact (Constructible.isConstructible_iff_of_iso e).mpr
    (isConstructible_properDirectImage_constant_of_isAffine p A)

/-- Proper ordinary direct image preserves original constructible abelian
coefficients on a Noetherian target. This is degree zero only. -/
theorem isConstructible_properDirectImage
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] {F : AbelianSheaf.{u, u + 1} X}
    (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage f).obj F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let t := Constructible.FiniteCogenerators.Global.finiteConstantProductEmbeddingOfConstructible
    X F hF
  let B := fun i : t.index => (directImage (t.morphism i)).obj
    (ConstantFinite.coefficient (t.value i) (t.source i))
  have hB (i : t.index) : Constructible.IsConstructible ((directImage f).obj (B i)) :=
    (Constructible.isConstructible_iff_of_iso
      ((directImageCompIso f (t.morphism i)).app
        (ConstantFinite.coefficient (t.value i) (t.source i)))).mpr
      (isConstructible_properDirectImage_constant (t.morphism i ≫ f) (t.value i))
  have hprod := Constructible.FiniteCogenerators.isConstructible_finiteProduct
    (fun i => (directImage f).obj (B i)) hB
  have htarget : Constructible.IsConstructible ((directImage f).obj (∏ᶜ B)) :=
    (Constructible.isConstructible_iff_of_iso (PreservesProduct.iso (directImage f) B)).mpr hprod
  exact Constructible.isConstructible_of_mono_of_noetherian ((directImage f).map t.map) htarget

end AlgebraicGeometry.Scheme.EtaleCohomology
