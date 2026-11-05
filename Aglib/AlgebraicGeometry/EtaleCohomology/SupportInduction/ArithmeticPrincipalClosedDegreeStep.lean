/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticDegreeProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.PrincipalClosedSupport
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Aglib.CategoryTheory.Limits.Shapes.PullbackPastingIso

/-! # The genuine lower-rank principal closed induction step

The original injective coefficient and original class are fixed. A single
closed injective and its actual coefficient monomorphism produce the literal
residual class on the principal quotient. The coefficient dimension drops,
and the full smaller-rank induction hypothesis produces a pointed target
neighborhood killing that residual. Canonical Cartesian pasting and the
uniform closed-residual return kill the original class on the whole target
refinement, with the same mark.

The lower-degree open-summand vanishing is explicit and uses only r < q.
The only supplied class zero is the already obtained original principal-open zero.
No residual zero, target neighborhood, or target-local-zero producer is an
extra input. The smaller-rank hypothesis remains explicit: this is the
successor branch, not a claim of completed strong induction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  HasExt.standard HasDerivedCategory.standard

/-- Apply the actual smaller-rank property to the genuine residual on the
literal principal quotient, then return to the unchanged original class.
The source, whole section, pointed field, original injective and its maps are
retained throughout. No affineness of the total source family is assumed. -/
theorem exists_arithmetic_principalClosed_degree_refinement_of_lower_rank
    (q : ℕ) (hq : 0 < q) (d : ℕ)
    (ih : ∀ r < d + 1, ArithmeticPointedCurveModuleEffacement.{u} q r)
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    (hd : ringKrullDim S ≤ (d + 1 : ℕ))
    {G Y : Scheme.{u}} (p : G ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of R) ⟶ G) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (f : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      IsAffine (pullback p f : Scheme.{u}))
    (β : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    (a : Y ⟶ G) (b : Y ⟶ Spec (CommRingCat.of S)) (H : IsPullback a b p β)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (CommRingCat.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (s : S) (hs : s ≠ 0)
    (hopen : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen S s).ι b) _ q c = 0)
    (hlower : ∀ (U : G.Etale),
      let t := pullback.snd U.hom a
      let j' := pullback.snd (principalSupportOpen S s).ι b
      let bU := pullback.fst (principalSupportOpen S s).ι b
      let j₂ := pullback.snd j' t
      let bU₂ := pullback.fst j' t ≫ bU
      ∀ r : ℕ, 1 ≤ r → r < q →
        IsZero ((higherDirectImage j₂ r).obj ((inverseImage bU₂).obj
          ((SheafOfModules.toSheaf (constantRing (principalSupportOpen S s).toScheme
            (ULift.{u + 1} (ZMod n)))).obj
            ((moduleInverseImage (principalSupportOpen S s).ι
              (ULift.{u + 1} (ZMod n))).obj I)))))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ∃ (U : G.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  let Q := S ⧸ Ideal.span {s}
  let j := (principalSupportOpen S s).ι
  let i := principalSupportClosedMap S s
  let : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {s})))
      Ideal.Quotient.mk_surjective
  let : Algebra ℤ Q := Ring.toIntAlgebra Q
  let : Algebra.FiniteType ℤ Q := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ S) (inferInstance : Algebra.FiniteType S Q)
  have hQdim : ringKrullDim Q ≤ (d : ℕ) :=
    Algebra.finite_domain_principalComplement_le_predecessor S S s hs d hd
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : Smooth b := MorphismProperty.of_isPullback H inferInstance
  obtain ⟨K, hK, α, hα, hreturn⟩ :=
    exists_uniform_closed_residual_degree_refinement_return j i
      (principalSupport_complement S s) n hn I
  let : Injective K := hK
  let j' := pullback.snd j b
  let bU := pullback.fst j b
  let i' := pullback.snd i b
  let bZ := pullback.fst i b
  have hi : IsPullback bZ i' i b := IsPullback.of_hasPullback i b
  have hclosedFamily : IsPullback (i' ≫ a) bZ p (i ≫ β) :=
    hi.flip.paste_horiz H
  let cZ := Sheaf.H.map
    (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm
      (ULift.{u + 1} (ZMod n)) I K α) q
    (cohomologyPullback.{u, u + 2, u + 2} i' _ q c)
  obtain ⟨U, xU, hxU, hzero⟩ :=
    ih d (Nat.lt_succ_self d) R Q hQdim p σ hσ haff
      (i ≫ β) (i' ≫ a) bZ hclosedFamily n hn hunit K cZ Ω x
  let t := pullback.snd U.hom a
  let : Etale U.hom := U.prop
  let : Etale t := inferInstanceAs (Etale (pullback.snd U.hom a))
  let : Smooth (t ≫ b) := inferInstance
  let v := pullback.fst j' t
  let j₂ := pullback.snd j' t
  let t' := pullback.fst i' t
  let i₂ := pullback.snd i' t
  have hj₂ : IsPullback (v ≫ bU) j₂ j (t ≫ b) :=
    (IsPullback.of_hasPullback j' t).paste_horiz (IsPullback.of_hasPullback j b)
  have hi₂ : IsPullback (t' ≫ bZ) i₂ i (t ≫ b) :=
    (IsPullback.of_hasPullback i' t).paste_horiz hi
  have ho : v ≫ j' = j₂ ≫ t := pullback.condition
  have hz : i₂ ≫ t = t' ≫ i' := pullback.condition.symm
  have hresidual : cohomologyPullback.{u, u + 2, u + 2} t' _ q cZ = 0 := by
    let E := ((IsPullback.of_hasPullback U.hom a).flip).familyPullbackIso i'
    exact TwoFieldEffacement.original_class_zero_of_map_law E.hom
      (pullback.snd U.hom (i' ≫ a)) t'
      (((IsPullback.of_hasPullback U.hom a).flip).familyPullbackIso_hom_snd i')
      _ q cZ hzero
  refine ⟨U, xU, hxU, ?_⟩
  exact hreturn b j' i' bZ hi t v t' j₂ i₂ (v ≫ bU) hj₂ hi₂ ho hz
    inferInstance q hq (hlower U) c hopen hresidual

end AlgebraicGeometry.Scheme.EtaleCohomology
