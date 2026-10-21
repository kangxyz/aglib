/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreIdempotents
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreFormalFunctions
public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.RingTheory.LocalRing.EtaleLift
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Connectedness from actual global-section idempotents

A nontrivial clopen decomposition gives a product decomposition of actual
structural sections. Its characteristic idempotent excludes such a decomposition
when every global idempotent is zero or one. Proper formal functions supplies
actual closed-fibre idempotent image witnesses over a Noetherian affine base.

Flat change of base preserves an isomorphism of the actual structure-sheaf map
for a quasi-compact quasi-separated morphism. The proof retains the original
section pushout comparison on an affine basis. Idempotents already in the
ordinary fibre-section image are trivial when the structure-sheaf map is an
isomorphism. Finite etale residue lifts discharge the finite separable field
tests after flat transport to the actual stalk spectrum, giving geometric
connectedness for a proper surjective morphism to a locally Noetherian target
with this sheaf isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- Trivial idempotents in the actual structural section ring give connectedness. -/
theorem connectedSpace_of_globalSections_idempotents (X : Scheme.{u}) [Nonempty X]
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace X := by
  classical
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro S hS
  by_cases hS0 : S = ∅
  · exact Or.inl hS0
  by_cases hS1 : S = Set.univ
  · exact Or.inr hS1
  let U : X.Opens := ⟨S, hS.2⟩
  let V : X.Opens := ⟨Sᶜ, hS.1.isOpen_compl⟩
  have hdisj : U ⊓ V = ⊥ := by
    ext x
    simp [U, V]
  have hcover : U ⊔ V = ⊤ := by
    ext x
    simp [U, V]
  let : Nonempty U := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS0
    exact ⟨⟨x, hx⟩⟩
  let : Nonempty V := by
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem S).mp hS1
    exact ⟨⟨x, hx⟩⟩
  let : Nontrivial Γ(X, U) := Scheme.component_nontrivial _ _
  let : Nontrivial Γ(X, V) := Scheme.component_nontrivial _ _
  let iso : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hdisj).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  let e : Γ(X, ⊤) ≃+* (Γ(X, U) × Γ(X, V)) :=
    ((X.presheaf.mapIso (eqToIso hcover).op) ≪≫ iso).commRingCatIsoToRingEquiv
  have hid : IsIdempotentElem ((1, 0) : Γ(X, U) × Γ(X, V)) := by
    rw [IsIdempotentElem]
    ext <;> simp
  rcases h (e.symm (1, 0)) (hid.map e.symm) with he | he
  · have h10 : (1 : Γ(X, U)) = 0 := by
      simpa using congrArg (fun a => (e a).1) he
    exact (one_ne_zero h10).elim
  · have h01 : (0 : Γ(X, V)) = 1 := by
      simpa using congrArg (fun a => (e a).2) he
    exact (zero_ne_one h01).elim

/-- An idempotent in the actual ordinary fibre-section image is zero or one when
the original structure-sheaf map is invertible. -/
theorem eq_zero_or_one_of_idempotent_stalkToFibreSections_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) [IsIso f.c]
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e)
    (himage : ∃ a, Cohomology.ProperFibreIdempotents.stalkToFibreSections f y a = e) :
    e = 0 ∨ e = 1 := by
  by_cases he0 : e = 0
  · exact Or.inl he0
  let : Nontrivial Γ(f.fiber y, ⊤) := ⟨⟨e, 0, he0⟩⟩
  obtain ⟨a, ha⟩ := himage
  obtain ⟨c, hc⟩ :=
    Cohomology.ProperFibreIdempotents.exists_residue_constant_of_stalk f y a
  have hce : Cohomology.ProperFibreIdempotents.fibreConstants f y c = e :=
    hc.symm.trans ha
  have hcid : IsIdempotentElem c := by
    change c * c = c
    apply (Cohomology.ProperFibreIdempotents.fibreConstants f y).hom.injective
    rw [map_mul, hce]
    exact he.eq
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcid with hc0 | hc1
  · left
    rw [← hce, hc0, map_zero]
  · right
    rw [← hce, hc1, map_one]

/-- The actual section map of a flat base change is invertible on each affine
chart lying over an affine target chart. -/
theorem isIso_app_pullback_snd_of_flat_of_isIso_c
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsIso f.c]
    (U : Y.Opens) (hU : IsAffineOpen U) (V : T.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) : IsIso ((pullback.snd f g).app V) := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  let H : IsPullback a b f g := IsPullback.of_hasPullback f g
  have hUV : b ⁻¹ᵁ V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro z hz
    change f (a z) ∈ U
    have hpoint : f (a z) = g (b z) :=
      congrArg (fun k : pullback f g ⟶ Y => k z) H.w
    rw [hpoint]
    exact hVU hz
  have hUY : b ⁻¹ᵁ V = a ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ b ⁻¹ᵁ V :=
    le_antisymm (le_inf hUV le_rfl) inf_le_right
  let comparison := AlgebraicGeometry.pushoutSection H hVU le_rfl hUY
  let : IsIso comparison :=
    AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
      H hVU le_rfl hUY hU hV (f.isCompact_preimage hU.isCompact)
        (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let : IsIso (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    infer_instance
  have hcomp : pushout.inr (f.appLE U (f ⁻¹ᵁ U) le_rfl) (g.appLE U V hVU) ≫
      comparison = b.app V := by
    dsimp only [comparison, AlgebraicGeometry.pushoutSection]
    rw [pushout.inr_desc]
    exact b.appLE_eq_app
  change IsIso (b.app V)
  rw [← hcomp]
  infer_instance

/-- Flat change of base preserves the actual structure-sheaf isomorphism for
a quasi-compact quasi-separated morphism. -/
theorem isIso_c_pullback_snd_of_flat_of_isIso_c
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsIso f.c] :
    IsIso (pullback.snd f g).c := by
  let b := pullback.snd f g
  let B := {V : T.Opens // IsAffineOpen V ∧
    ∃ U : Y.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U}
  have hB : Opens.IsBasis (Set.range (fun V : B => V.val)) := by
    have hrange : Set.range (fun V : B => V.val) =
        {V : T.Opens | IsAffineOpen V ∧ ∃ U : Y.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U} := by
      ext V
      constructor
      · rintro ⟨W, rfl⟩
        exact W.property
      · intro hV
        exact ⟨⟨V, hV⟩, rfl⟩
    rw [hrange]
    apply Opens.isBasis_iff_nbhd.mpr
    intro W x hx
    obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top (g x))
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (show x ∈ W ⊓ g ⁻¹ᵁ U from ⟨hx, hxU⟩)
    exact ⟨V, ⟨hV, U, hU, hVW.trans inf_le_right⟩, hxV, hVW.trans inf_le_left⟩
  let F : T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} b.base).obj
      (pullback f g).sheaf := ⟨b.c⟩
  have : IsIso F := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := fun V : B => V.val) hB ?_
    intro V
    obtain ⟨U, hU, hVU⟩ := V.property.2
    exact isIso_app_pullback_snd_of_flat_of_isIso_c f g U hU V.val V.property.1 hVU
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map F))

/-- Purely inseparable change of field preserves connectedness through the actual
closed bijective projection. -/
theorem connectedSpace_fieldBaseChange_of_isPurelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X] :
    ConnectedSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : UniversallyInjective g := by
    apply ((tfae_universallyInjective g).out 2 1).mp
    intro L _ r s hrs
    obtain ⟨r', rfl⟩ := Spec.map_surjective r
    obtain ⟨s', rfl⟩ := Spec.map_surjective s
    change Spec.map r' ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map s' ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) at hrs
    rw [← Spec.map_comp, ← Spec.map_comp] at hrs
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply IsPurelyInseparable.injective_comp_algebraMap k K L
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hrs)
  let : IsIntegralHom g := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr inferInstance)
  let : Surjective g := ⟨fun x =>
    ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let p := pullback.fst q g
  let : UniversallyInjective p := MorphismProperty.pullback_fst q g inferInstance
  let : Surjective p := MorphismProperty.pullback_fst q g inferInstance
  let e := (Equiv.ofBijective p ⟨p.injective, p.surjective⟩).toHomeomorphOfContinuousClosed
    p.continuous p.isClosedMap
  exact e.connectedSpace_iff.mpr inferInstance

private theorem exists_finite_intermediateField_idempotent_tensor_preimage
    (k K B : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [CommRing B] [Algebra k B] (e : K ⊗[k] B) (he : IsIdempotentElem e) :
    ∃ L : IntermediateField k K, Module.Finite k L ∧
      ∃ t : L ⊗[k] B, IsIdempotentElem t ∧
        Algebra.TensorProduct.map L.val (AlgHom.id k B) t = e := by
  obtain ⟨A, hA, t, ht⟩ := TensorProduct.Algebra.exists_of_fg e
  let : Module.Finite k A := by
    obtain ⟨s, hs⟩ := hA
    rw [← hs]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  let L : IntermediateField k K := A.toIntermediateField' A.isField_of_algebraic
  let : Module.Finite k L := inferInstanceAs (Module.Finite k A)
  let tL : L ⊗[k] B := t
  have hlinear (z : L ⊗[k] B) :
      Algebra.TensorProduct.map L.val (AlgHom.id k B) z =
        LinearMap.rTensor B L.val.toLinearMap z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hpre : Algebra.TensorProduct.map L.val (AlgHom.id k B) tL = e := by
    rw [hlinear]
    exact ht
  have hinj : Function.Injective (Algebra.TensorProduct.map L.val (AlgHom.id k B)) := by
    intro z w hzw
    apply Module.Flat.rTensor_preserves_injective_linearMap L.val.toLinearMap L.val.injective
    exact (hlinear z).symm.trans (hzw.trans (hlinear w))
  refine ⟨L, inferInstance, tL, ?_, hpre⟩
  change tL * tL = tL
  apply hinj
  rw [map_mul, hpre]
  exact he.eq

/-- Actual idempotent structural sections are trivial on a preconnected scheme. -/
theorem globalSections_idempotents_of_preconnectedSpace (X : Scheme.{u})
    [PreconnectedSpace X] (e : Γ(X, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinter : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
    rw [← X.basicOpen_mul, he.mul_one_sub_self, X.basicOpen_zero]
  have hcover : X.basicOpen e ⊔ X.basicOpen (1 - e) = ⊤ := by
    have hs : e + (1 - e) = 1 := by ring
    have h := X.basicOpen_add_le e (1 - e)
    rw [hs, X.basicOpen_one] at h
    exact top_unique h
  have hcompl : (X.basicOpen e : Set X)ᶜ = (X.basicOpen (1 - e) : Set X) := by
    ext x
    constructor
    · intro hx
      have hxT : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e) := by rw [hcover]; trivial
      exact (show x ∈ X.basicOpen e ∨ x ∈ X.basicOpen (1 - e) from hxT).resolve_left hx
    · intro hx hxE
      have hxI : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := ⟨hxE, hx⟩
      rw [hinter] at hxI
      exact hxI
  have hclopen : IsClopen (X.basicOpen e : Set X) := by
    refine ⟨?_, (X.basicOpen e).isOpen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (X.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h0 | h1
  · left
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ e 0
    intro x hx
    rw [map_zero]
    have hxF : x ∈ X.basicOpen (1 - e) := by
      change x ∈ (X.basicOpen (1 - e) : Set X)
      rw [← hcompl, h0]
      simp
    have hu := (X.mem_basicOpen_top (1 - e) x).mp hxF
    have hv := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp
      (he.one_sub.map (X.presheaf.germ ⊤ x hx).hom)
    rw [map_sub, map_one] at hv
    exact sub_eq_self.mp hv
  · right
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ e 1
    intro x hx
    rw [map_one]
    have hxE : x ∈ X.basicOpen e := by
      change x ∈ (X.basicOpen e : Set X)
      rw [h1]
      trivial
    exact (IsIdempotentElem.iff_eq_one_of_isUnit
      ((X.mem_basicOpen_top e x).mp hxE)).mp (he.map (X.presheaf.germ ⊤ x hx).hom)

/-- A field point surjective on stalks has the original residue field as its field. -/
theorem isIso_descResidueField_stalkClosedPointTo_of_surjectiveOnStalks
    {Y : Scheme.{u}} (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Y) [SurjectiveOnStalks s] :
    IsIso (Y.descResidueField (Scheme.stalkClosedPointTo s)) := by
  have hs : Function.Surjective (Scheme.stalkClosedPointTo s) := by
    change Function.Surjective (fun a => (stalkClosedPointIso (CommRingCat.of K)).hom
      (s.stalkMap (IsLocalRing.closedPoint K) a))
    exact (ConcreteCategory.bijective_of_isIso
      (stalkClosedPointIso (CommRingCat.of K)).hom).2.comp
        (s.stalkMap_surjective (IsLocalRing.closedPoint K))
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(Y.descResidueField (Scheme.stalkClosedPointTo s)).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := hs a
  refine ⟨Y.residue _ b, ?_⟩
  exact ConcreteCategory.congr_hom
    (Scheme.residue_descResidueField (Scheme.stalkClosedPointTo s)) b

/-- The actual closed-field-point base change is the original residue fibre,
through the original residue map and canonical iterated pullback comparison. -/
theorem connectedSpace_pullback_of_fieldPoint_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Y) [SurjectiveOnStalks s]
    [ConnectedSpace (f.fiber (s (IsLocalRing.closedPoint K)))] :
    ConnectedSpace (pullback f s : Scheme.{u}) := by
  let y := s (IsLocalRing.closedPoint K)
  let φ := Y.descResidueField (Scheme.stalkClosedPointTo s)
  let : IsIso φ :=
    isIso_descResidueField_stalkClosedPointTo_of_surjectiveOnStalks K s
  let g := Spec.map φ
  let p := pullback.fst (f.fiberToSpecResidueField y) g
  let : IsIso p := inferInstance
  have hlocal : ConnectedSpace (pullback (f.fiberToSpecResidueField y) g : Scheme.{u}) :=
    (asIso p).hom.homeomorph.connectedSpace_iff.mpr inferInstance
  let comparison : (pullback (f.fiberToSpecResidueField y) g : Scheme.{u}) ≃ₜ
      (pullback f (g ≫ Y.fromSpecResidueField y) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) g).hom.homeomorph
  have hcomp : ConnectedSpace (pullback f (g ≫ Y.fromSpecResidueField y) : Scheme.{u}) :=
    comparison.connectedSpace_iff.mp hlocal
  have hs : g ≫ Y.fromSpecResidueField y = s :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y s
  exact hs ▸ hcomp

private theorem exists_finite_etale_residue_quotient
    (R : Type u) [CommRing R] [IsLocalRing R]
    (L : Type u) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [FiniteDimensional (IsLocalRing.ResidueField R) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        ∃ φ : A →+* L, Function.Surjective φ ∧
          φ.comp (algebraMap R A) =
            (algebraMap (IsLocalRing.ResidueField R) L).comp (IsLocalRing.residue R) := by
  obtain ⟨A, hA, hAlg, hfin, hetale, ⟨e⟩⟩ :=
    IsLocalRing.exists_finite_etale_residue_lift R L
  let : CommRing A := hA
  let : Algebra R A := hAlg
  let φ : A →+* L := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      A →ₐ[R] IsLocalRing.ResidueField R ⊗[R] A).toRingHom
  refine ⟨A, hA, hAlg, hfin, hetale, φ, ?_, ?_⟩
  · exact e.surjective.comp (Algebra.TensorProduct.includeRight_surjective A
      (IsLocalRing.residue_surjective (R := R)))
  · ext r
    change e ((Algebra.TensorProduct.includeRight :
      A →ₐ[R] IsLocalRing.ResidueField R ⊗[R] A) (algebraMap R A r)) = _
    calc
      _ = e (algebraMap R (IsLocalRing.ResidueField R ⊗[R] A) r) :=
        congrArg e ((Algebra.TensorProduct.includeRight :
          A →ₐ[R] IsLocalRing.ResidueField R ⊗[R] A).commutes r)
      _ = e (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField R ⊗[R] A) (IsLocalRing.residue R r)) := by
        congr 1
      _ = _ := e.commutes _

/-- Under the actual structure-sheaf isomorphism, a global-function image that
is idempotent on the literal residue-quotient fibre is zero or one. -/
theorem eq_zero_or_one_of_idempotent_residueFibre_globalImage
    (R : Type u) [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f.c]
    (e : Γ(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))), ⊤))
    (he : IsIdempotentElem e)
    (himage : ∃ a : Γ(X, ⊤),
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop a = e) :
    e = 0 ∨ e = 1 := by
  let q := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let i := pullback.fst f q
  let p := pullback.snd f q
  let c : IsLocalRing.ResidueField R →+* Γ(pullback f q, ⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))).inv.hom
  let aMap : CommRingCat.of R ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let : IsIso aMap := inferInstance
  obtain ⟨a, ha⟩ := himage
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso aMap).2 a
  have htriangle : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ i.appTop =
      CommRingCat.ofHom (IsLocalRing.residue R) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))).inv ≫ p.appTop := by
    rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have hce : c (IsLocalRing.residue R b) = e := by
    have h := ConcreteCategory.congr_hom htriangle b
    change i.appTop (aMap b) = c (IsLocalRing.residue R b) at h
    rw [hb, ha] at h
    exact h.symm
  by_cases he0 : e = 0
  · exact Or.inl he0
  let : Nontrivial Γ(pullback f q, ⊤) := ⟨⟨e, 0, he0⟩⟩
  have hc : IsIdempotentElem (IsLocalRing.residue R b) := by
    change IsLocalRing.residue R b * IsLocalRing.residue R b = IsLocalRing.residue R b
    apply c.injective
    rw [map_mul, hce]
    exact he.eq
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hc with hc0 | hc1
  · left
    rw [← hce, hc0, map_zero]
  · right
    rw [← hce, hc1, map_one]

/-- Under the actual structure-sheaf isomorphism, a global-function image that
is idempotent on the literal pullback by any field-valued base map is zero or one. -/
theorem eq_zero_or_one_of_idempotent_fieldFibre_globalImage
    (R K : Type u) [CommRing R] [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f.c] (φ : R →+* K)
    (e : Γ(pullback f (Spec.map (CommRingCat.ofHom (φ))), ⊤))
    (he : IsIdempotentElem e)
    (himage : ∃ a : Γ(X, ⊤),
      (pullback.fst f (Spec.map (CommRingCat.ofHom (φ)))).appTop a = e) :
    e = 0 ∨ e = 1 := by
  let q := Spec.map (CommRingCat.ofHom (φ))
  let i := pullback.fst f q
  let p := pullback.snd f q
  let c : K →+* Γ(pullback f q, ⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (K))).inv.hom
  let aMap : CommRingCat.of R ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let : IsIso aMap := inferInstance
  obtain ⟨a, ha⟩ := himage
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso aMap).2 a
  have htriangle : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ i.appTop =
      CommRingCat.ofHom (φ) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (K))).inv ≫ p.appTop := by
    rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have hce : c (φ b) = e := by
    have h := ConcreteCategory.congr_hom htriangle b
    change i.appTop (aMap b) = c (φ b) at h
    rw [hb, ha] at h
    exact h.symm
  by_cases he0 : e = 0
  · exact Or.inl he0
  let : Nontrivial Γ(pullback f q, ⊤) := ⟨⟨e, 0, he0⟩⟩
  have hc : IsIdempotentElem (φ b) := by
    change φ b * φ b = φ b
    apply c.injective
    rw [map_mul, hce]
    exact he.eq
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hc with hc0 | hc1
  · left
    rw [← hce, hc0, map_zero]
  · right
    rw [← hce, hc1, map_one]

private theorem isPushout_appTop_of_qcqs_flat
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [IsAffine Y] [IsAffine T] :
    IsPushout f.appTop g.appTop (pullback.fst f g).appTop (pullback.snd f g).appTop := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  let H : IsPullback a b f g := IsPullback.of_hasPullback f g
  have hUST : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ⊤ := by simp
  have hUSX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hUY : (⊤ : (pullback f g).Opens) = a ⁻¹ᵁ ⊤ ⊓ b ⁻¹ᵁ ⊤ := by simp
  have hc : IsCompact (X := X) (⊤ : X.Opens) := by
    simpa only [Scheme.Hom.preimage_top] using
      f.isCompact_preimage (isAffineOpen_top Y).isCompact
  have hq : IsQuasiSeparated (α := X) (⊤ : X.Opens) := by
    simpa only [Scheme.Hom.preimage_top] using
      f.isQuasiSeparated_preimage (isAffineOpen_top Y).isQuasiSeparated
  let : IsIso (AlgebraicGeometry.pushoutSection H hUST hUSX hUY) :=
    AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
      H hUST hUSX hUY (isAffineOpen_top Y) (isAffineOpen_top T) hc hq
  have hp := (AlgebraicGeometry.isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (inferInstance : IsIso (AlgebraicGeometry.pushoutSection H hUST hUSX hUY))
  have happ {S Z : Scheme.{u}} (p : S ⟶ Z) (h : ⊤ ≤ p ⁻¹ᵁ ⊤) :
      p.appLE ⊤ ⊤ h = p.appTop := by
    simpa only [Scheme.Hom.preimage_top] using (p.appLE_eq_app (U := ⊤))
  change IsPushout (f.appLE ⊤ ⊤ hUSX) (g.appLE ⊤ ⊤ hUST)
    (a.appLE ⊤ ⊤ (by simp)) (b.appLE ⊤ ⊤ (by simp)) at hp
  rw [happ f hUSX, happ g hUST, happ a (by simp), happ b (by simp)] at hp
  exact hp

private theorem exists_fieldBaseChangeSectionsRingEquiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact q] [QuasiSeparated q] :
    let α := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    letI : Algebra k Γ(X, ⊤) := α.toAlgebra
    ∃ e : K ⊗[k] Γ(X, ⊤) ≃+*
        Γ(pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤),
      ∀ (r : K) (s : Γ(X, ⊤)), e (r ⊗ₜ[k] s) =
        (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r) *
        (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop s := by
  let α := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let : Algebra k Γ(X, ⊤) := α.toAlgebra
  let δ : CommRingCat.of k ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap k K)
  let g := Spec.map δ
  let : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let leftProjection := pullback.fst q g
  let rightProjection := pullback.snd q g
  let ck : CommRingCat.of k ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop
  let cK : CommRingCat.of K ⟶ Γ(pullback q g, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ rightProjection.appTop
  have Hfield : IsPushout ck δ leftProjection.appTop cK := by
    apply (isPushout_appTop_of_qcqs_flat q g).of_iso
      (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of K)) (Iso.refl _)
    · simp [ck]
    · exact Scheme.ΓSpecIso_naturality δ
    · simp [leftProjection]
    · simp [cK, rightProjection]
  let Htensor : IsPushout δ ck
      (CommRingCat.ofHom (S := K ⊗[k] Γ(X, ⊤)) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct k K Γ(X, ⊤)
  let comparison : CommRingCat.of (K ⊗[k] Γ(X, ⊤)) ≅ Γ(pullback q g, ⊤) :=
    Htensor.isoPushout ≪≫ Hfield.flip.isoPushout.symm
  have hleft : CommRingCat.ofHom (S := K ⊗[k] Γ(X, ⊤))
      Algebra.TensorProduct.includeLeftRingHom ≫ comparison.hom = cK := by
    dsimp only [comparison, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, Htensor.inl_isoPushout_hom, Hfield.flip.inl_isoPushout_inv]
  have hright : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
      comparison.hom = leftProjection.appTop := by
    dsimp only [comparison, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, Htensor.inr_isoPushout_hom, Hfield.flip.inr_isoPushout_inv]
  let e := comparison.commRingCatIsoToRingEquiv
  refine ⟨e, ?_⟩
  intro r s
  have hr : e (r ⊗ₜ[k] (1 : Γ(X, ⊤))) = cK r :=
    ConcreteCategory.congr_hom hleft r
  have hs : e ((1 : K) ⊗ₜ[k] s) = leftProjection.appTop s :=
    ConcreteCategory.congr_hom hright s
  calc
    _ = e ((r ⊗ₜ[k] (1 : Γ(X, ⊤))) * ((1 : K) ⊗ₜ[k] s)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = e (r ⊗ₜ[k] (1 : Γ(X, ⊤))) * e ((1 : K) ⊗ₜ[k] s) := map_mul e _ _
    _ = _ := by rw [hr, hs]; rfl

private theorem geometricallyConnected_of_connected_finiteSeparable_baseChanges
    (k : Type u) [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact q] [QuasiSeparated q] [Nonempty X]
    (hfinite : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
      [Algebra.IsSeparable k L],
      ConnectedSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
        Scheme.{u})) : GeometricallyConnected q := by
  let B := Γ(X, ⊤)
  let α := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let : Algebra k B := α.toAlgebra
  let S := SeparableClosure k
  let gS := Spec.map (CommRingCat.ofHom (algebraMap k S))
  let XS := pullback q gS
  let qS := pullback.snd q gS
  let : Surjective gS := ⟨fun x =>
    ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let : Surjective (pullback.fst q gS) := MorphismProperty.pullback_fst q gS inferInstance
  let : Nonempty XS := by
    obtain ⟨z, _⟩ := (pullback.fst q gS).surjective (Nonempty.some (inferInstance : Nonempty X))
    exact ⟨z⟩
  have hS : ConnectedSpace XS := by
    apply connectedSpace_of_globalSections_idempotents XS
    intro e he
    obtain ⟨E, _⟩ := exists_fieldBaseChangeSectionsRingEquiv k S q
    let t : S ⊗[k] B := E.symm e
    obtain ⟨L, hLfinite, tL, htL, hmap⟩ :=
      exists_finite_intermediateField_idempotent_tensor_preimage k S B t (he.map E.symm)
    let : Module.Finite k L := hLfinite
    let : Algebra.IsSeparable k L := inferInstance
    let gL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let : ConnectedSpace (pullback q gL : Scheme.{u}) := hfinite L
    obtain ⟨EL, _⟩ := exists_fieldBaseChangeSectionsRingEquiv k L q
    rcases globalSections_idempotents_of_preconnectedSpace
      (pullback q gL) (EL tL) (htL.map EL) with h0 | h1
    · left
      have htL0 : tL = 0 := EL.injective (by simpa only [map_zero] using h0)
      have ht0 : t = 0 := by rw [← hmap, htL0, map_zero]
      have hh := congrArg E ht0
      simpa only [t, RingEquiv.apply_symm_apply, map_zero] using hh
    · right
      have htL1 : tL = 1 := EL.injective (by simpa only [map_one] using h1)
      have ht1 : t = 1 := by rw [← hmap, htL1, map_one]
      have hh := congrArg E ht1
      simpa only [t, RingEquiv.apply_symm_apply, map_one] using hh
  let A := AlgebraicClosure k
  let : IsPurelyInseparable S A := inferInstance
  let : ConnectedSpace XS := hS
  let gA := Spec.map (CommRingCat.ofHom (algebraMap S A))
  have hNested : ConnectedSpace (pullback qS gA : Scheme.{u}) :=
    connectedSpace_fieldBaseChange_of_isPurelyInseparable S A qS
  let comparison : (pullback qS gA : Scheme.{u}) ≃ₜ
      (pullback q (gA ≫ gS) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso q gS gA).hom.homeomorph
  have hcomp : ConnectedSpace (pullback q (gA ≫ gS) : Scheme.{u}) :=
    comparison.connectedSpace_iff.mp hNested
  have hmaps : gA ≫ gS = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    dsimp only [gA, gS]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq k S A).symm
  have hA : ConnectedSpace
      (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k A))) : Scheme.{u}) :=
    hmaps ▸ hcomp
  exact Geometrically.geometricallyConnected_of_connected_algebraicClosure k q hA

private def surjectiveBaseChangeKernelQuotientIso
    (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    pullback f (Spec.map (CommRingCat.ofHom φ)) ≅
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)))) := by
  let quotientIso := (φ.quotientKerEquivOfSurjective hφ).toCommRingCatIso
  let baseMap := Spec.map quotientIso.hom
  let sourceMap := Spec.map (CommRingCat.ofHom φ)
  let quotientMap := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)))
  have hfactor : sourceMap = baseMap ≫ quotientMap := by
    dsimp only [sourceMap, baseMap, quotientMap]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hφ r).symm
  let hom := pullback.map f sourceMap f quotientMap (𝟙 X) baseMap
    (𝟙 (Spec (CommRingCat.of R))) (by simp)
    (by simpa only [Category.comp_id] using hfactor)
  exact asIso hom

private theorem surjectiveBaseChangeKernelQuotientIso_hom_fst
    (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    (surjectiveBaseChangeKernelQuotientIso R S φ hφ f).hom ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ)))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom φ)) := by
  simp [surjectiveBaseChangeKernelQuotientIso, pullback.map]

/-- Every idempotent on the actual closed field fibre of a proper morphism over a
Noetherian affine base is the restriction of an arbitrary original global function. -/
theorem exists_section_restrict_eq_of_isIdempotentElem_fieldFibre
    (R K : Type u) [CommRing R] [IsNoetherianRing R] [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (φ : R →+* K)
    (hφ : Function.Surjective φ)
    (e : Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤))
    (he : IsIdempotentElem e) :
    ∃ a : Γ(X, ⊤), (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appTop a = e := by
  let E := surjectiveBaseChangeKernelQuotientIso R K φ hφ f
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom φ))
  let iI := pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ))))
  let eI := E.inv.appTop e
  obtain ⟨a, ha⟩ :=
    Cohomology.ProperFibreFormalFunctions.exists_section_restrict_eq_of_isIdempotentElem
      f (RingHom.ker φ) eI (he.map E.inv.appTop.hom)
  change iI.appTop a = eI at ha
  refine ⟨a, ?_⟩
  have htriangle : iI.appTop ≫ E.hom.appTop = i.appTop := by
    rw [← Scheme.Hom.comp_appTop]
    exact congrArg (fun t => t.appTop)
      (surjectiveBaseChangeKernelQuotientIso_hom_fst R K φ hφ f)
  have hinv : E.inv.appTop ≫ E.hom.appTop =
      𝟙 Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) := by
    have h := congrArg (fun t => t.appTop) E.hom_inv_id
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] using h
  have h := ConcreteCategory.congr_hom htriangle a
  change E.hom.appTop (iI.appTop a) = i.appTop a at h
  rw [ha] at h
  have heI : E.hom.appTop eI = e := ConcreteCategory.congr_hom hinv e
  exact h.symm.trans heI

/-- A proper surjective morphism with its actual structure-sheaf map invertible has
connected closed field fibres over a Noetherian affine base. -/
theorem connectedSpace_fieldFibre_of_isProper_of_isIso_c
    (R K : Type u) [CommRing R] [IsNoetherianRing R] [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Surjective f] [IsIso f.c]
    (φ : R →+* K) (hφ : Function.Surjective φ) :
    ConnectedSpace (pullback f (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u}) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  let : Surjective (pullback.snd f g) := MorphismProperty.pullback_snd f g inferInstance
  let : Nonempty (pullback f g : Scheme.{u}) := by
    obtain ⟨z, _⟩ := (pullback.snd f g).surjective
      (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))
    exact ⟨z⟩
  apply connectedSpace_of_globalSections_idempotents (pullback f g)
  intro e he
  exact eq_zero_or_one_of_idempotent_fieldFibre_globalImage R K f φ e he
    (exists_section_restrict_eq_of_isIdempotentElem_fieldFibre R K f φ hφ e he)

/-- Properness over a locally Noetherian target, surjectivity, and the actual
structure-sheaf isomorphism imply geometric connectedness of every actual fibre. -/
theorem geometricallyConnected_of_isProper_of_isIso_c
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [IsProper f] [Surjective f] [IsIso f.c] : GeometricallyConnected f := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr
  intro y
  let R := Y.presheaf.stalk y
  let k := IsLocalRing.ResidueField R
  let j := Y.fromSpecStalk y
  let b := pullback.snd f j
  let : Flat j := fromSpecStalk_flat Y y
  let : IsIso b.c := isIso_c_pullback_snd_of_flat_of_isIso_c f j
  let q := f.fiberToSpecResidueField y
  let : IsProper q := MorphismProperty.pullback_snd f (Y.fromSpecResidueField y)
    inferInstance
  let : Surjective q := MorphismProperty.pullback_snd f (Y.fromSpecResidueField y)
    inferInstance
  let : Nonempty (f.fiber y) := by
    obtain ⟨z, _⟩ := q.surjective
      (Nonempty.some (inferInstance : Nonempty (Spec (Y.residueField y))))
    exact ⟨z⟩
  apply geometricallyConnected_of_connected_finiteSeparable_baseChanges k q
  intro L _ _ _ _
  obtain ⟨A, hA, hAlg, hfin, hetale, φ, hφ, hscalar⟩ :=
    exists_finite_etale_residue_quotient R L
  let : CommRing A := hA
  let : Algebra R A := hAlg
  let : Module.Finite R A := hfin
  let : Algebra.Etale R A := hetale
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let c := pullback.snd b g
  let : IsIso c.c := isIso_c_pullback_snd_of_flat_of_isIso_c b g
  let h := Spec.map (CommRingCat.ofHom φ)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hC : ConnectedSpace (pullback c h : Scheme.{u}) :=
    connectedSpace_fieldFibre_of_isProper_of_isIso_c A L c φ hφ
  let comparisonA : (pullback c h : Scheme.{u}) ≃ₜ (pullback b (h ≫ g) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso b g h).hom.homeomorph
  have hmaps : h ≫ g = ρ ≫ r := by
    dsimp only [h, g, ρ, r]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext hscalar
  have hB : ConnectedSpace (pullback b (ρ ≫ r) : Scheme.{u}) :=
    hmaps ▸ comparisonA.connectedSpace_iff.mp hC
  let comparisonB : (pullback b (ρ ≫ r) : Scheme.{u}) ≃ₜ
      (pullback f ((ρ ≫ r) ≫ j) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso f j (ρ ≫ r)).hom.homeomorph
  have hbaseMap : (ρ ≫ r) ≫ j = ρ ≫ Y.fromSpecResidueField y := by
    exact Category.assoc _ _ _
  have hF : ConnectedSpace (pullback f (ρ ≫ Y.fromSpecResidueField y) : Scheme.{u}) :=
    hbaseMap ▸ comparisonB.connectedSpace_iff.mp hB
  let comparisonQ : (pullback q ρ : Scheme.{u}) ≃ₜ
      (pullback f (ρ ≫ Y.fromSpecResidueField y) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) ρ).hom.homeomorph
  exact comparisonQ.connectedSpace_iff.mpr hF

/-- A proper dominant birational morphism of integral schemes onto a normal locally
Noetherian target has geometrically connected actual fibres. -/
theorem geometricallyConnected_of_isProper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) : GeometricallyConnected f := by
  let : IsIso f.c := isIso_c_of_isProper_birational f hY hff
  exact geometricallyConnected_of_isProper_of_isIso_c f

end AlgebraicGeometry.Scheme
