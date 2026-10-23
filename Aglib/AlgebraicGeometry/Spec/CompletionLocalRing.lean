/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.CompletionResidueFiber
public import Aglib.AlgebraicGeometry.Properties.Regular.ClosedPoints
public import Aglib.RingTheory.AdicCompletion.FiniteTypeLocalComparison
public import Aglib.RingTheory.AdicCompletion.RingEquiv
public import Aglib.RingTheory.AdicCompletion.RegularLocalRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Completed local rings after base completion

The canonical Spec stalk/localization isomorphisms transport the actual
localized completion comparison to the original tensor-coefficient spectrum
map. Its equation on completion images is the equation of that map's actual
stalk homomorphism. The affine pullback and literal residue-fibre comparison
retain the original point correspondence. An original affine open chart
and its canonical base-change stalk square extend the comparison to arbitrary
schemes, at actual closed-fibre points of the literal completion pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.LocalRing

universe u

section CompletionTransport

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Changing only an ideal's equality presentation identifies the actual
completions, without changing a coefficient. -/
def completionIdealEquiv (I J : Ideal R) (hIJ : I = J) :
    AdicCompletion I R ≃+* AdicCompletion J R := by
  subst J
  exact RingEquiv.refl _

/-- Equality transport retains the original completion coefficient map. -/
theorem completionIdealEquiv_algebraMap (I J : Ideal R) (hIJ : I = J) (r : R) :
    completionIdealEquiv I J hIJ (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (AdicCompletion J R) r := by
  subst J
  rfl

variable [IsLocalRing R] [IsLocalRing S]

/-- The original maximal-adic completion map, with a shared native ring and
algebra presentation for the stalk comparisons below. -/
def maximalCompletionMap (R : Type*) [CommRing R] [IsLocalRing R] :
    R →+* AdicCompletion (IsLocalRing.maximalIdeal R) R :=
  algebraMap R _

/-- The shared maximal-adic completion map is the native algebra map. -/
theorem maximalCompletionMap_eq (R : Type*) [CommRing R] [IsLocalRing R] :
    maximalCompletionMap R =
      algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := rfl

/-- Transport the actual maximal-adic completion through a local-ring
equivalence, using the existing finite-quotient completion equivalence. -/
def completionCongr (e : R ≃+* S) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S :=
  (AdicCompletion.congrRingEquiv e (IsLocalRing.maximalIdeal R)).trans
    (completionIdealEquiv _ _
      (IsLocalRing.map_maximalIdeal_of_surjective (e : R →+* S) e.surjective))

/-- Completion transport acts on original elements by the original ring
equivalence, rather than by an independently chosen completion map. -/
theorem completionCongr_algebraMap (e : R ≃+* S) (r : R) :
    completionCongr e (maximalCompletionMap R r) = maximalCompletionMap S (e r) := by
  simp only [completionCongr, RingEquiv.trans_apply, maximalCompletionMap,
    AdicCompletion.congrRingEquiv_algebraMap, completionIdealEquiv_algebraMap]

end CompletionTransport

/-- Use the actual scheme's native local-stalk structure at a prime-spectrum
point, with its scheme point presentation fixed explicitly. -/
local instance specStalkIsLocalRing (R : CommRingCat.{u}) (p : PrimeSpectrum R) :
    IsLocalRing ((Spec R).presheaf.stalk p) :=
  (Spec R).toLocallyRingedSpace.isLocalRing (p : Spec R)

/-- Compose the three actual completion comparisons through one shared
typed equivalence presentation. -/
def completionComposite
    {P Q R S : Type*} [Mul P] [Add P] [Mul Q] [Add Q] [Mul R] [Add R] [Mul S] [Add S]
    (e₁ : P ≃+* Q) (e₂ : Q ≃+* R) (e₃ : R ≃+* S) : P ≃+* S :=
  e₁.trans (e₂.trans e₃)

/-- The original-element equation for specified completion and coefficient
maps, retained as one regular proposition at all comparison boundaries. -/
def CompletionImageEq {U V P S : Type*} [Mul P] [Add P] [Mul S] [Add S]
    (e : P ≃+* S) (source : U → P) (target : V → S) (original : U → V) (a : U) : Prop :=
  e (source a) = target (original a)

/-- Recover the literal original-element equality from its shared
proposition presentation, at abstract map and ring heads. -/
theorem CompletionImageEq.eq {U V P S : Type*} [Mul P] [Add P] [Mul S] [Add S]
    {e : P ≃+* S} {source : U → P} {target : V → S} {original : U → V} {a : U}
    (h : CompletionImageEq e source target original a) :
    e (source a) = target (original a) := h

private theorem completionComposite_imageEq
    {U V : Type*}
    {P Q R S : Type*} [Mul P] [Add P] [Mul Q] [Add Q] [Mul R] [Add R] [Mul S] [Add S]
    (e₁ : P ≃+* Q) (e₂ : Q ≃+* R) (e₃ : R ≃+* S)
    (source : U → P) (target : V → S) (original : U → V)
    (a : U) (b : Q) (c : R)
    (h₁ : e₁ (source a) = b) (h₂ : e₂ b = c) (h₃ : e₃ c = target (original a)) :
    CompletionImageEq (completionComposite e₁ e₂ e₃) source target original a := by
  change (e₁.trans (e₂.trans e₃)) (source a) = target (original a)
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h₁, h₂, h₃]

section SpecStalks

variable (R : CommRingCat.{u}) (p : PrimeSpectrum R)

/-- Complete the canonical Spec stalk/localization isomorphism. -/
def specStalkCompletionEquiv :=
  completionCongr (Spec.stalkIso R p).commRingCatIsoToRingEquiv

/-- The completed canonical stalk isomorphism retains its original stalk
map on every coefficient. -/
theorem specStalkCompletionEquiv_algebraMap (s : (Spec R).presheaf.stalk p) :
    specStalkCompletionEquiv R p
        (maximalCompletionMap ((Spec R).presheaf.stalk p) s) =
      AdicCompletion.atPrimeCompletionMap p.asIdeal ((Spec.stalkIso R p).hom s) :=
  completionCongr_algebraMap (Spec.stalkIso R p).commRingCatIsoToRingEquiv s

/-- The inverse completed stalk isomorphism also retains the original
localization-to-stalk map on every original local element. -/
theorem specStalkCompletionEquiv_symm_algebraMap (s : Localization.AtPrime p.asIdeal) :
    (specStalkCompletionEquiv R p).symm (AdicCompletion.atPrimeCompletionMap p.asIdeal s) =
      maximalCompletionMap ((Spec R).presheaf.stalk p) ((Spec.stalkIso R p).inv s) := by
  apply (specStalkCompletionEquiv R p).injective
  rw [RingEquiv.apply_symm_apply, specStalkCompletionEquiv_algebraMap,
    CommRingCat.hom_inv_apply]

end SpecStalks

section TensorStalks

variable {A : Type u} [CommRing A] (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]

/-- The spectrum map of the original tensor inclusion, using the same
underlying ring homomorphism as the localized completion comparison. -/
def tensorCompletionSpecMap :
    Spec (.of (AdicCompletion I A ⊗[A] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (AdicCompletion.tensorComparisonRingHom I B))

/-- The original spectrum map contracts the actual prime through the same
original coefficient ring homomorphism. -/
theorem tensorCompletionSpecMap_apply
    (q : Spec (.of (AdicCompletion I A ⊗[A] B))) :
    tensorCompletionSpecMap I B q =
      (show Spec (.of B) from PrimeSpectrum.comap (AdicCompletion.tensorComparisonRingHom I B)
        (show PrimeSpectrum (AdicCompletion I A ⊗[A] B) from q)) :=
  Spec.map_apply (CommRingCat.ofHom (AdicCompletion.tensorComparisonRingHom I B)) q

/-- The original tensor-coefficient spectrum map is over the original base. -/
@[reassoc]
theorem tensorCompletionSpecMap_base :
    tensorCompletionSpecMap I B ≫ Spec.algebraMap A B =
      Spec.algebraMap A (AdicCompletion I A ⊗[A] B) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hbase : (AdicCompletion.tensorComparisonRingHom I B).comp (algebraMap A B) =
      algebraMap A (AdicCompletion I A ⊗[A] B) := by
    rw [AdicCompletion.tensorComparisonRingHom_eq, AlgHom.toRingHom_eq_coe]
    exact (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)).comp_algebraMap
  exact congrArg (fun f : A →+* AdicCompletion I A ⊗[A] B ↦
    Spec.map (CommRingCat.ofHom f)) hbase

variable (hI : I.FG) (q : PrimeSpectrum (AdicCompletion I A ⊗[A] B))
  (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q.asIdeal)

/-- At an actual closed-fibre prime, the original tensor spectrum map
identifies the completions of its source and target stalks. -/
def tensorStalkCompletionsEquiv :=
  completionComposite
    (specStalkCompletionEquiv (.of B) (q.comap (AdicCompletion.tensorComparisonRingHom I B)))
    (AdicCompletion.tensorLocalCompletionsEquiv I B hI q.asIdeal hclosed)
    (specStalkCompletionEquiv (.of (AdicCompletion I A ⊗[A] B)) q).symm

/-- The Spec stalk completion comparison is induced by the original
`Spec.map` stalk homomorphism on every original stalk element. -/
theorem tensorStalkCompletionsEquiv_algebraMap
    (s : (Spec (.of B)).presheaf.stalk
      (show Spec (.of B) from q.comap (AdicCompletion.tensorComparisonRingHom I B))) :
    CompletionImageEq (tensorStalkCompletionsEquiv I B hI q hclosed)
      (maximalCompletionMap ((Spec (.of B)).presheaf.stalk
        (show Spec (.of B) from q.comap (AdicCompletion.tensorComparisonRingHom I B))))
      (maximalCompletionMap ((Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk q))
      ((tensorCompletionSpecMap I B).stalkMap q).hom s := by
  have hstalk :
      (Spec.stalkIso (.of (AdicCompletion I A ⊗[A] B)) q).inv
          (Localization.localRingHom
            (q.comap (AdicCompletion.tensorComparisonRingHom I B)).asIdeal q.asIdeal
            (AdicCompletion.tensorComparisonRingHom I B) rfl
            ((Spec.stalkIso (.of B)
              (q.comap (AdicCompletion.tensorComparisonRingHom I B))).hom s)) =
        (tensorCompletionSpecMap I B).stalkMap q s := by
    exact congrArg (fun g :
      (Spec (.of B)).presheaf.stalk
          (q.comap (AdicCompletion.tensorComparisonRingHom I B)) ⟶
        (Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk q ↦ g s)
      (Scheme.localRingHom_comp_stalkIso
        (CommRingCat.ofHom (AdicCompletion.tensorComparisonRingHom I B)) q)
  let toTargetStalk :=
    (specStalkCompletionEquiv (.of (AdicCompletion I A ⊗[A] B)) q).symm
  let localComparison := AdicCompletion.tensorLocalCompletionsEquiv I B hI q.asIdeal hclosed
  have hsource := specStalkCompletionEquiv_algebraMap (.of B)
    (q.comap (AdicCompletion.tensorComparisonRingHom I B)) s
  have hlocal := AdicCompletion.tensorLocalCompletionsEquiv_algebraMap I B hI q.asIdeal
    hclosed ((Spec.stalkIso (.of B)
      (q.comap (AdicCompletion.tensorComparisonRingHom I B))).hom s)
  have htarget := specStalkCompletionEquiv_symm_algebraMap
    (.of (AdicCompletion I A ⊗[A] B)) q
    (Localization.localRingHom
      (q.comap (AdicCompletion.tensorComparisonRingHom I B)).asIdeal q.asIdeal
      (AdicCompletion.tensorComparisonRingHom I B) rfl
      ((Spec.stalkIso (.of B)
        (q.comap (AdicCompletion.tensorComparisonRingHom I B))).hom s))
  have htargetMap := congrArg
    (maximalCompletionMap
      ((Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk
        (show Spec (.of (AdicCompletion I A ⊗[A] B)) from q))) hstalk
  have htargetComplete := htarget.trans htargetMap
  exact completionComposite_imageEq
    (specStalkCompletionEquiv (.of B) (q.comap (AdicCompletion.tensorComparisonRingHom I B)))
    localComparison toTargetStalk
    (maximalCompletionMap ((Spec (.of B)).presheaf.stalk
      (show Spec (.of B) from q.comap (AdicCompletion.tensorComparisonRingHom I B))))
    (maximalCompletionMap ((Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk q))
    ((tensorCompletionSpecMap I B).stalkMap q).hom
    s _ _ hsource hlocal htargetComplete

end TensorStalks

section AffinePullback

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

/-- The canonical affine presentation of the actual completion base change. -/
def completionTensorSpecIso :
    pullback (Spec.algebraMap A B)
        (Spec.algebraMap A (AdicCompletion I A)) ≅
      Spec (.of (AdicCompletion I A ⊗[A] B)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A (AdicCompletion I A) B

/-- The tensor presentation retains the original projection to `Spec B`. -/
@[reassoc (attr := simp)]
theorem completionTensorSpecIso_hom_fst :
    (completionTensorSpecIso A B I).hom ≫ tensorCompletionSpecMap I B =
      pullback.fst (Spec.algebraMap A B)
        (Spec.algebraMap A (AdicCompletion I A)) := by
  have hprojection :
      (pullbackSpecIso A (AdicCompletion I A) B).hom ≫ tensorCompletionSpecMap I B =
        pullback.snd (Spec.algebraMap A (AdicCompletion I A)) (Spec.algebraMap A B) := by
    rw [tensorCompletionSpecMap, AdicCompletion.tensorComparisonRingHom_eq,
      AlgHom.toRingHom_eq_coe]
    exact pullbackSpecIso_hom_snd A (AdicCompletion I A) B
  dsimp only [completionTensorSpecIso, Iso.trans_hom]
  rw [Category.assoc, hprojection]
  exact pullbackSymmetry_hom_comp_snd _ _

/-- The tensor presentation retains the original projection to the completed base. -/
@[reassoc (attr := simp)]
theorem completionTensorSpecIso_hom_snd :
    (completionTensorSpecIso A B I).hom ≫
        Spec.algebraMap (AdicCompletion I A) (AdicCompletion I A ⊗[A] B) =
      pullback.snd (Spec.algebraMap A B)
        (Spec.algebraMap A (AdicCompletion I A)) := by
  simp only [completionTensorSpecIso, Iso.trans_hom, Category.assoc,
    Spec.algebraMap, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

variable [IsNoetherianRing A] [IsLocalRing A]

/-- The canonical map from the literal completed residue fibre to the actual
tensor spectrum, with no choice of an affine point. -/
def completionResidueFiberTensorMap :
    pullback (pullback.snd (Spec.algebraMap A B) (completionSpecMap A))
        (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ⟶
      Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) :=
  pullback.fst _ _ ≫ (completionTensorSpecIso A B (IsLocalRing.maximalIdeal A)).hom

/-- The original point under the tensor spectrum projection is exactly the
point corresponding through the canonical literal residue-fibre isomorphism. -/
@[reassoc]
theorem completionResidueFiberTensorMap_projection :
    completionResidueFiberTensorMap A B ≫
        tensorCompletionSpecMap (IsLocalRing.maximalIdeal A) B =
      (completionResidueFiberIso (Spec.algebraMap A B)).hom ≫
        pullback.fst (Spec.algebraMap A B) (residueSpecMap A) := by
  rw [completionResidueFiberTensorMap, Category.assoc,
    completionTensorSpecIso_hom_fst]
  exact (completionResidueFiberIso_hom_fst (Spec.algebraMap A B)).symm

/-- The same residue-fibre point retains its original residue-base map. -/
@[reassoc]
theorem completionResidueFiberTensorMap_base :
    completionResidueFiberTensorMap A B ≫
        Spec.algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B) =
      (completionResidueFiberIso (Spec.algebraMap A B)).hom ≫
        pullback.snd (Spec.algebraMap A B) (residueSpecMap A) ≫ residueSpecMap A := by
  rw [← tensorCompletionSpecMap_base, ← Category.assoc,
    completionResidueFiberTensorMap_projection, Category.assoc, pullback.condition]

/-- An actual point of the literal completed closed fibre satisfies the
closed-fibre ideal condition required by the stalk completion comparison. -/
theorem completionResidueFiberTensorMap_closed
    (y : (pullback (pullback.snd (Spec.algebraMap A B) (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u})) :
    (IsLocalRing.maximalIdeal A).map
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) ≤
      (completionResidueFiberTensorMap A B y).asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  let tensorPoint : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) :=
    completionResidueFiberTensorMap A B y
  let residuePoint : Spec (.of (IsLocalRing.ResidueField A)) :=
    pullback.snd (Spec.algebraMap A B) (residueSpecMap A)
      ((completionResidueFiberIso (Spec.algebraMap A B)).hom y)
  have hy :
      Spec.algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B) tensorPoint =
        residueSpecMap A residuePoint := by
    have h := congrArg
      (fun g : (pullback (pullback.snd (Spec.algebraMap A B) (completionSpecMap A))
        (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u}) ⟶
          Spec (.of A) ↦ g y) (completionResidueFiberTensorMap_base A B)
    simpa only [Scheme.Hom.comp_apply, tensorPoint, residuePoint] using h
  have hmem : IsLocalRing.residue A a ∈
      (show PrimeSpectrum (IsLocalRing.ResidueField A) from residuePoint).asIdeal := by
    rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha]
    exact Ideal.zero_mem _
  have hmembership := congrArg
    (fun p : Spec (.of A) ↦ a ∈ (show PrimeSpectrum A from p).asIdeal) hy
  exact hmembership.symm.mp hmem

/-- The actual completed residue-fibre point gives the Spec stalk comparison
with the closed-fibre condition proved from its original residue map. -/
def completionResidueFiberStalkCompletionsEquiv
    (y : (pullback (pullback.snd (Spec.algebraMap A B) (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u})) :=
  tensorStalkCompletionsEquiv (IsLocalRing.maximalIdeal A) B
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
    (completionResidueFiberTensorMap A B y) (completionResidueFiberTensorMap_closed A B y)

end AffinePullback


local instance originalStalkIsLocalRing (X : Scheme.{u}) (x : X) :
    IsLocalRing (X.presheaf.stalk x) :=
  X.toLocallyRingedSpace.isLocalRing x

section OriginalAffineChart

variable {A : Type u} [CommRing A] (I : Ideal A) (B : Type u)
  [CommRing B] [Algebra A B]

/-- The original tensor maps form the actual affine base-change square. -/
theorem tensorCompletion_isPullback :
    IsPullback (tensorCompletionSpecMap I B)
      (Spec.algebraMap (AdicCompletion I A) (AdicCompletion I A ⊗[A] B))
      (Spec.algebraMap A B) (Spec.algebraMap A (AdicCompletion I A)) := by
  have H := (isPullback_SpecMap_of_isPushout
    _ _ _ _
    (CommRingCat.isPushout_tensorProduct A (AdicCompletion I A) B)).flip
  simpa only [tensorCompletionSpecMap, AdicCompletion.tensorComparisonRingHom_eq,
    AlgHom.toRingHom_eq_coe] using H

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (uB : Spec (.of B) ⟶ X) (huB : uB ≫ f = Spec.algebraMap A B)

/-- The original affine chart, pulled back along the original completion map. -/
def completionAffineChartMap :
    Spec (.of (AdicCompletion I A ⊗[A] B)) ⟶
      pullback f (Spec.algebraMap A (AdicCompletion I A)) :=
  pullback.lift (tensorCompletionSpecMap I B ≫ uB)
    (Spec.algebraMap (AdicCompletion I A) (AdicCompletion I A ⊗[A] B)) (by
      rw [Category.assoc, huB]
      exact (tensorCompletion_isPullback I B).w)

@[reassoc]
theorem completionAffineChartMap_fst :
    completionAffineChartMap I B f uB huB ≫
        pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) =
      tensorCompletionSpecMap I B ≫ uB := pullback.lift_fst _ _ _

@[reassoc]
theorem completionAffineChartMap_snd :
    completionAffineChartMap I B f uB huB ≫
        pullback.snd f (Spec.algebraMap A (AdicCompletion I A)) =
      Spec.algebraMap (AdicCompletion I A) (AdicCompletion I A ⊗[A] B) :=
  pullback.lift_snd _ _ _

/-- The chart square is the literal base change of its original open immersion. -/
theorem completionAffineChartMap_isPullback :
    IsPullback (completionAffineChartMap I B f uB huB) (tensorCompletionSpecMap I B)
      (pullback.fst f (Spec.algebraMap A (AdicCompletion I A))) uB := by
  have H : IsPullback
      (completionAffineChartMap I B f uB huB ≫
        pullback.snd f (Spec.algebraMap A (AdicCompletion I A)))
      (tensorCompletionSpecMap I B) (Spec.algebraMap A (AdicCompletion I A)) (uB ≫ f) := by
    rw [completionAffineChartMap_snd, huB]
    exact (tensorCompletion_isPullback I B).flip
  exact H.of_right (completionAffineChartMap_fst I B f uB huB)
    (IsPullback.of_hasPullback f (Spec.algebraMap A (AdicCompletion I A))).flip

/-- Its structural map to the original affine base is unchanged. -/
@[reassoc]
theorem completionAffineChartMap_base :
    completionAffineChartMap I B f uB huB ≫
        pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) ≫ f =
      Spec.algebraMap A (AdicCompletion I A ⊗[A] B) := by
  rw [← Category.assoc, completionAffineChartMap_fst, Category.assoc, huB,
    tensorCompletionSpecMap_base]

variable [IsOpenImmersion uB]

/-- The original global projection and tensor-Spec projection have canonically
isomorphic stalk-map arrows, using only the original open-immersion square. -/
def completionAffineChartStalkArrowIso (q : PrimeSpectrum (AdicCompletion I A ⊗[A] B))
    (z : (pullback f (Spec.algebraMap A (AdicCompletion I A)) : Scheme.{u}))
    (hz : completionAffineChartMap I B f uB huB q = z) :=
  Scheme.stalkMapIsoOfIsPullback (completionAffineChartMap_isPullback I B f uB huB)
    (show Spec (.of (AdicCompletion I A ⊗[A] B)) from q) z hz

/-- Every original point covered by the affine chart has an actual tensor
chart point over it; the projection equation is retained. -/
theorem exists_completionAffineChartPoint
    (z : (pullback f (Spec.algebraMap A (AdicCompletion I A)) : Scheme.{u}))
    (hz : pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) z ∈ Set.range uB) :
    ∃ q : PrimeSpectrum (AdicCompletion I A ⊗[A] B),
      completionAffineChartMap I B f uB huB q = z := by
  have hz' : z ∈ Set.range
      (pullback.fst (pullback.fst f (Spec.algebraMap A (AdicCompletion I A))) uB) := by
    rw [IsOpenImmersion.range_pullbackFst uB]
    exact hz
  obtain ⟨v, hv⟩ := hz'
  let H := completionAffineChartMap_isPullback I B f uB huB
  refine ⟨H.isoPullback.inv v, ?_⟩
  exact (congrArg (fun g :
    (pullback (pullback.fst f (Spec.algebraMap A (AdicCompletion I A))) uB : Scheme.{u}) ⟶
      (pullback f (Spec.algebraMap A (AdicCompletion I A)) : Scheme.{u}) ↦ g v)
        H.isoPullback_inv_fst).trans hv

variable (hI : I.FG) (q : PrimeSpectrum (AdicCompletion I A ⊗[A] B))
  (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q.asIdeal)
  (z : (pullback f (Spec.algebraMap A (AdicCompletion I A)) : Scheme.{u}))
  (hz : completionAffineChartMap I B f uB huB q = z)

/-- The source component of the canonical stalk-arrow comparison, with
both original native stalk ring objects stated explicitly. -/
def completionAffineChartSourceStalkIso :
    X.presheaf.stalk (pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) z) ≅
      (Spec (.of B)).presheaf.stalk (tensorCompletionSpecMap I B q) :=
  asIso (completionAffineChartStalkArrowIso I B f uB huB q z hz).hom.left

/-- The target component of the canonical stalk-arrow comparison, with
both original native stalk ring objects stated explicitly. -/
def completionAffineChartTargetStalkIso :
    (pullback f (Spec.algebraMap A (AdicCompletion I A)) : Scheme.{u}).presheaf.stalk z ≅
      (Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk
        (show Spec (.of (AdicCompletion I A ⊗[A] B)) from q) :=
  asIso (completionAffineChartStalkArrowIso I B f uB huB q z hz).hom.right

/-- The two explicitly presented native stalk isomorphisms retain the
original global projection and original tensor spectrum stalk maps. -/
theorem completionAffineChartStalkSquare :
    (completionAffineChartSourceStalkIso I B f uB huB q z hz).hom ≫
        (tensorCompletionSpecMap I B).stalkMap q =
      (pullback.fst f (Spec.algebraMap A (AdicCompletion I A))).stalkMap z ≫
        (completionAffineChartTargetStalkIso I B f uB huB q z hz).hom :=
  (completionAffineChartStalkArrowIso I B f uB huB q z hz).hom.w

/-- Construct the global projection's completed-stalk equivalence at an
actual tensor chart point through its two canonical native stalk isomorphisms. -/
def completionAffineChartStalkEquiv :=
  completionComposite
    (completionCongr
      (completionAffineChartSourceStalkIso I B f uB huB q z hz).commRingCatIsoToRingEquiv)
    (tensorStalkCompletionsEquiv I B hI q hclosed)
    (completionCongr
      (completionAffineChartTargetStalkIso I B f uB huB q z hz).commRingCatIsoToRingEquiv).symm

include hI hclosed hz

/-- The completed chart comparison acts by the actual original global
projection stalk map on every original stalk coefficient. -/
theorem completionAffineChartStalkEquiv_algebraMap
    (s : X.presheaf.stalk
      (pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) z)) :
    CompletionImageEq (completionAffineChartStalkEquiv I B f uB huB hI q hclosed z hz)
      (maximalCompletionMap _) (maximalCompletionMap _)
      ((pullback.fst f (Spec.algebraMap A (AdicCompletion I A))).stalkMap z).hom s := by
  let sourceIso := completionAffineChartSourceStalkIso I B f uB huB q z hz
  let targetIso := completionAffineChartTargetStalkIso I B f uB huB q z hz
  let targetCompletion := completionCongr targetIso.commRingCatIsoToRingEquiv
  let tensorCompletion := tensorStalkCompletionsEquiv I B hI q hclosed
  have hsource := completionCongr_algebraMap sourceIso.commRingCatIsoToRingEquiv s
  have htensor := (tensorStalkCompletionsEquiv_algebraMap I B hI q hclosed
    (sourceIso.hom s)).eq
  have harrow := congrArg
    (fun g : X.presheaf.stalk
      (pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) z) ⟶
        (Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk
          (show Spec (.of (AdicCompletion I A ⊗[A] B)) from q) ↦ g s)
      (completionAffineChartStalkSquare I B f uB huB q z hz)
  have htarget := completionCongr_algebraMap targetIso.commRingCatIsoToRingEquiv
    ((pullback.fst f (Spec.algebraMap A (AdicCompletion I A))).stalkMap z s)
  have htargetMap := congrArg (maximalCompletionMap
    ((Spec (.of (AdicCompletion I A ⊗[A] B))).presheaf.stalk
      (show Spec (.of (AdicCompletion I A ⊗[A] B)) from q))) harrow
  have htargetComplete := htarget.trans htargetMap.symm
  have hinverse : targetCompletion.symm
      (maximalCompletionMap _ ((tensorCompletionSpecMap I B).stalkMap q (sourceIso.hom s))) =
      maximalCompletionMap _
        ((pullback.fst f (Spec.algebraMap A (AdicCompletion I A))).stalkMap z s) :=
    (congrArg targetCompletion.symm htargetComplete).symm.trans
      (targetCompletion.symm_apply_apply _)
  exact completionComposite_imageEq (completionCongr sourceIso.commRingCatIsoToRingEquiv)
    tensorCompletion targetCompletion.symm
    (maximalCompletionMap
      (X.presheaf.stalk (pullback.fst f (Spec.algebraMap A (AdicCompletion I A)) z)))
    (maximalCompletionMap
      ((pullback f (Spec.algebraMap A (AdicCompletion I A)) : Scheme.{u}).presheaf.stalk z))
    ((pullback.fst f (Spec.algebraMap A (AdicCompletion I A))).stalkMap z).hom
    s _ _ hsource htensor hinverse

end OriginalAffineChart

section GlobalComparison

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- At every actual closed-fibre point, the literal completion-base-change
projection identifies completed original stalks and retains its stalk map. -/
theorem exists_completionBaseChangeStalkEquiv
    (z : (pullback f (completionSpecMap A) : Scheme.{u}))
    (hz : IsLocalRing.maximalIdeal A ≤
      (show PrimeSpectrum A from f (pullback.fst f (completionSpecMap A) z)).asIdeal) :
    ∃ e : AdicCompletion
        (IsLocalRing.maximalIdeal
          (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z)))
        (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z)) ≃+*
      AdicCompletion
        (IsLocalRing.maximalIdeal ((pullback f (completionSpecMap A)).presheaf.stalk z))
        ((pullback f (completionSpecMap A)).presheaf.stalk z),
      ∀ s, CompletionImageEq e (maximalCompletionMap _) (maximalCompletionMap _)
        ((pullback.fst f (completionSpecMap A)).stalkMap z).hom s := by
  let 𝒰 := X.affineOpenCover
  let i := 𝒰.idx (pullback.fst f (completionSpecMap A) z)
  let B : Type u := 𝒰.X i
  let : CommRing B := inferInstanceAs (CommRing (𝒰.X i))
  let uB : Spec (.of B) ⟶ X := 𝒰.f i
  let φ : A →+* B := (Spec.preimage (uB ≫ f)).hom
  let : Algebra A B := φ.toAlgebra
  have huB : uB ≫ f = Spec.algebraMap A B := (Spec.map_preimage _).symm
  let : IsOpenImmersion uB := 𝒰.map_prop i
  obtain ⟨q, hq⟩ := exists_completionAffineChartPoint (IsLocalRing.maximalIdeal A) B
    f uB huB z (𝒰.covers (pullback.fst f (completionSpecMap A) z))
  have hclosed : (IsLocalRing.maximalIdeal A).map
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    let qPoint : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) := q
    have hpoint :
        f (pullback.fst f (completionSpecMap A)
          (completionAffineChartMap (IsLocalRing.maximalIdeal A) B f uB huB q)) =
        Spec.algebraMap A
          (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B) qPoint := by
      let t : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) ⟶
          (pullback f (completionSpecMap A) : Scheme.{u}) :=
        completionAffineChartMap (IsLocalRing.maximalIdeal A) B f uB huB
      let β : (pullback f (completionSpecMap A) : Scheme.{u}) ⟶ X :=
        pullback.fst f (completionSpecMap A)
      have hbase : t ≫ β ≫ f =
          Spec.algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B) :=
        completionAffineChartMap_base (IsLocalRing.maximalIdeal A) B f uB huB
      have h := congrArg (fun g : Spec (.of
        (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] B)) ⟶ Spec (.of A) ↦ g qPoint)
          hbase
      have hcomp : (t ≫ β ≫ f) qPoint = f (β (t qPoint)) :=
        (Scheme.Hom.comp_apply t (β ≫ f) qPoint).trans
          (Scheme.Hom.comp_apply β f (t qPoint))
      exact hcomp.symm.trans h
    have hpointZ := (congrArg (fun v : (pullback f (completionSpecMap A) : Scheme.{u}) ↦
      f (pullback.fst f (completionSpecMap A) v)) hq).symm.trans hpoint
    have hmembership := congrArg
      (fun p : Spec (.of A) ↦ a ∈ (show PrimeSpectrum A from p).asIdeal) hpointZ
    exact hmembership.mp (hz ha)
  let e := completionAffineChartStalkEquiv (IsLocalRing.maximalIdeal A) B f uB huB
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing q hclosed z hq
  have he := completionAffineChartStalkEquiv_algebraMap (IsLocalRing.maximalIdeal A) B
    f uB huB (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing q hclosed z hq
  exact ⟨e, he⟩

/-- The actual completed residue-fibre point projects to the original point
specified by the canonical residue-fibre isomorphism. -/
theorem completionResidueFiberPoint_projection
    (y : (pullback (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u})) :
    pullback.fst f (completionSpecMap A)
        (pullback.fst (pullback.snd f (completionSpecMap A))
          (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y) =
      pullback.fst f (residueSpecMap A) ((completionResidueFiberIso f).hom y) := by
  have h := congrArg (fun g : (pullback (pullback.snd f (completionSpecMap A))
    (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u}) ⟶ X ↦ g y)
      (completionResidueFiberIso_hom_fst f)
  simpa only [Scheme.Hom.comp_apply] using h.symm

/-- An actual literal completed residue-fibre point lies in the original
closed fibre, with no additional field-base assumption. -/
theorem completionResidueFiberPoint_closed
    (y : (pullback (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u})) :
    IsLocalRing.maximalIdeal A ≤
      (show PrimeSpectrum A from f (pullback.fst f (completionSpecMap A)
        (pullback.fst (pullback.snd f (completionSpecMap A))
          (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y))).asIdeal := by
  intro a ha
  let z := pullback.fst (pullback.snd f (completionSpecMap A))
    (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y
  let xResidue := pullback.fst f (residueSpecMap A) ((completionResidueFiberIso f).hom y)
  let residuePoint : Spec (.of (IsLocalRing.ResidueField A)) :=
    pullback.snd f (residueSpecMap A) ((completionResidueFiberIso f).hom y)
  have hx : xResidue = pullback.fst f (completionSpecMap A) z :=
    (completionResidueFiberPoint_projection A f y).symm
  have hb : f xResidue = residueSpecMap A residuePoint := by
    have h := congrArg (fun g : (pullback f (residueSpecMap A) : Scheme.{u}) ⟶ Spec (.of A) ↦
      g ((completionResidueFiberIso f).hom y))
        (pullback.condition (f := f) (g := residueSpecMap A))
    simpa only [Scheme.Hom.comp_apply, xResidue, residuePoint] using h
  have hpoint := (congrArg f hx).symm.trans hb
  have hmem : IsLocalRing.residue A a ∈
      (show PrimeSpectrum (IsLocalRing.ResidueField A) from residuePoint).asIdeal := by
    rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha]
    exact Ideal.zero_mem _
  have hmembership := congrArg
    (fun p : Spec (.of A) ↦ a ∈ (show PrimeSpectrum A from p).asIdeal) hpoint
  exact hmembership.symm.mp hmem

/-- The actual residue-fibre point supplies the global completed-stalk
comparison for the original completion-base-change projection. -/
theorem exists_completionResidueFiberStalkEquiv
    (y : (pullback (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u})) :
    let z := pullback.fst (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y
    ∃ e : AdicCompletion
        (IsLocalRing.maximalIdeal
          (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z)))
        (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z)) ≃+*
      AdicCompletion
        (IsLocalRing.maximalIdeal ((pullback f (completionSpecMap A)).presheaf.stalk z))
        ((pullback f (completionSpecMap A)).presheaf.stalk z),
      ∀ s, CompletionImageEq e (maximalCompletionMap _) (maximalCompletionMap _)
        ((pullback.fst f (completionSpecMap A)).stalkMap z).hom s :=
  exists_completionBaseChangeStalkEquiv A f
    (pullback.fst (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y)
    (completionResidueFiberPoint_closed A f y)

end GlobalComparison

section Regularity

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]

/-- Local finite type over the original Noetherian local base and its actual
Noetherian completion supplies both original stalks' Noetherianity. The
actual completed-stalk comparison then identifies their regularity. -/
theorem isRegularLocalRing_completionBaseChange_iff
    (z : (pullback f (completionSpecMap A) : Scheme.{u}))
    (hz : IsLocalRing.maximalIdeal A ≤
      (show PrimeSpectrum A from f (pullback.fst f (completionSpecMap A) z)).asIdeal) :
    IsRegularLocalRing (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z)) ↔
      IsRegularLocalRing ((pullback f (completionSpecMap A) : Scheme.{u}).presheaf.stalk z) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.isNoetherianRing A (IsLocalRing.maximalIdeal A)
  let : IsLocallyNoetherian (pullback f (completionSpecMap A) : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (completionSpecMap A))
  obtain ⟨e, _he⟩ := exists_completionBaseChangeStalkEquiv A f z hz
  constructor
  · intro h
    have hcomplete := (AdicCompletion.isRegularLocalRing_iff_maximalCompletion
      (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z))).mp h
    let := hcomplete
    have htarget := IsRegularLocalRing.of_ringEquiv e
    exact (AdicCompletion.isRegularLocalRing_iff_maximalCompletion
      ((pullback f (completionSpecMap A) : Scheme.{u}).presheaf.stalk z)).mpr htarget
  · intro h
    have hcomplete := (AdicCompletion.isRegularLocalRing_iff_maximalCompletion
      ((pullback f (completionSpecMap A) : Scheme.{u}).presheaf.stalk z)).mp h
    let := hcomplete
    have hsource := IsRegularLocalRing.of_ringEquiv e.symm
    exact (AdicCompletion.isRegularLocalRing_iff_maximalCompletion
      (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z))).mpr hsource

/-- At the actual point of the literal completed residue fibre, regularity
is equivalent at the two original corresponding stalks. The fibre supplies
the closed-fibre condition through its original residue map. -/
theorem isRegularLocalRing_completionResidueFiber_iff
    (y : (pullback (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) : Scheme.{u})) :
    let z := pullback.fst (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y
    IsRegularLocalRing (X.presheaf.stalk (pullback.fst f (completionSpecMap A) z)) ↔
      IsRegularLocalRing ((pullback f (completionSpecMap A) : Scheme.{u}).presheaf.stalk z) :=
  isRegularLocalRing_completionBaseChange_iff A f
    (pullback.fst (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)) y)
    (completionResidueFiberPoint_closed A f y)

end Regularity

section ProperRegularity

open IsLocalRing

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

private theorem completionSpecMap_closedPoint :
    completionSpecMap A
        (show Spec (.of (AdicCompletion (maximalIdeal A) A)) from
          closedPoint (AdicCompletion (maximalIdeal A) A)) =
      (show Spec (.of A) from closedPoint A) :=
  IsLocalRing.comap_closedPoint (algebraMap A (AdicCompletion (maximalIdeal A) A))

omit [IsNoetherianRing A] in
private theorem residueSpecMap_closedPoint :
    residueSpecMap A
        (show Spec (.of (ResidueField A)) from closedPoint (ResidueField A)) =
      (show Spec (.of A) from closedPoint A) :=
  IsLocalRing.comap_closedPoint (IsLocalRing.residue A)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- Properness lets the original closed-fibre stalk equivalence detect
regularity at every actual point on both original schemes. -/
theorem regularStalks_completionBaseChange_iff :
    RegularStalks X ↔ RegularStalks (pullback f (completionSpecMap A) : Scheme.{u}) := by
  constructor
  · intro hX
    apply Scheme.regularStalks_of_regular_closedFibre (pullback.snd f (completionSpecMap A))
    intro z hz
    let β : (pullback f (completionSpecMap A) : Scheme.{u}) ⟶ X :=
      pullback.fst f (completionSpecMap A)
    let p : (pullback f (completionSpecMap A) : Scheme.{u}) ⟶
        Spec (.of (AdicCompletion (maximalIdeal A) A)) :=
      pullback.snd f (completionSpecMap A)
    have htri : f (β z) = completionSpecMap A (p z) := by
      have h := congrArg
        (fun g : (pullback f (completionSpecMap A) : Scheme.{u}) ⟶ Spec (.of A) ↦ g z)
        (pullback.condition (f := f) (g := completionSpecMap A))
      exact (Scheme.Hom.comp_apply β f z).symm.trans
        (h.trans (Scheme.Hom.comp_apply p (completionSpecMap A) z))
    have hbase : f (β z) = (show Spec (.of A) from closedPoint A) :=
      htri.trans ((congrArg (completionSpecMap A) hz).trans (completionSpecMap_closedPoint A))
    have hclosed : maximalIdeal A ≤ (show PrimeSpectrum A from f (β z)).asIdeal :=
      (congrArg (fun x : Spec (.of A) ↦ (show PrimeSpectrum A from x).asIdeal) hbase).symm.le
    exact (isRegularLocalRing_completionBaseChange_iff A f z hclosed).mp (hX (β z))
  · intro hXhat
    apply Scheme.regularStalks_of_regular_closedFibre f
    intro x hx
    have hrange : x ∈ Set.range (pullback.fst f (residueSpecMap A)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨closedPoint (ResidueField A), (residueSpecMap_closedPoint A).trans hx.symm⟩
    obtain ⟨u, hu⟩ := hrange
    let E := completionResidueFiberIso f
    let y := E.inv u
    let z := pullback.fst (pullback.snd f (completionSpecMap A))
      (residueSpecMap (AdicCompletion (maximalIdeal A) A)) y
    have hEu : E.hom y = u :=
      (Scheme.Hom.comp_apply E.inv E.hom u).symm.trans
        (congrArg
          (fun g : (pullback f (residueSpecMap A) : Scheme.{u}) ⟶
            (pullback f (residueSpecMap A) : Scheme.{u}) ↦ g u) E.inv_hom_id)
    have hpoint : pullback.fst f (completionSpecMap A) z = x :=
      (completionResidueFiberPoint_projection A f y).trans
        ((congrArg (pullback.fst f (residueSpecMap A)) hEu).trans hu)
    have hregular := (isRegularLocalRing_completionResidueFiber_iff A f y).mpr (hXhat z)
    exact hpoint ▸ hregular

end ProperRegularity

end AlgebraicGeometry.Scheme.LocalRing
