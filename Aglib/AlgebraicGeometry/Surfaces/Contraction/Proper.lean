/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.ProperProjective
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.OpenRestriction
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.ProperGluing

/-!
# The actual base neighbourhood for a proper surface contraction

The image of the original exceptional curve is a closed point of the original
base. An affine neighbourhood of that point and its complement form the actual
base cover used by the proper gluing construction. Their inverse images retain
the original exceptional immersion and unchanged complement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.Proper

/-- A nonempty closed subscheme with constant image under a proper map has
closed singleton image in the original base. -/
theorem image_isClosed {D X S : Scheme.{u}} [Nonempty D]
    (f : X ⟶ S) [IsProper f] (i : D ⟶ X) [IsClosedImmersion i]
    (s : S) (hs : ∀ d : D, f (i d) = s) : IsClosed ({s} : Set S) := by
  have hrange : f '' Set.range i = ({s} : Set S) := by
    ext y
    constructor
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
      exact hs d
    · intro hy
      have hys : y = s := hy
      subst y
      let d : D := Classical.choice inferInstance
      exact ⟨i d, ⟨d, rfl⟩, hs d⟩
  rw [← hrange]
  exact f.isClosedMap _ i.isClosedEmbedding.isClosed_range

/-- Choose the original affine-base neighbourhood and its complementary base
open. Their inverse images cover the source with the original exceptional
complement, and the same curve factors through the first inverse image. -/
theorem exists_affine_base_cover {k : Type u} [Field k] {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f]
    (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
    (s : S) (hs : ∀ d, f (i d) = s) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (Z : S.Opens),
      s ∈ V ∧ (Z : Set S) = ({s} : Set S)ᶜ ∧ V ⊔ Z = ⊤ ∧
      Set.range i ⊆ Set.range (f ⁻¹ᵁ V).ι ∧
      f ⁻¹ᵁ Z ≤ exceptionalComplement i ∧
      (f ⁻¹ᵁ V) ⊔ exceptionalComplement i = ⊤ := by
  obtain ⟨V, hV, hsV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  let Z : S.Opens := ⟨({s} : Set S)ᶜ, (image_isClosed f i s hs).isOpen_compl⟩
  have hbase : V ⊔ Z = ⊤ := by
    apply le_antisymm le_top
    intro y _
    change y ∈ V ∨ y ≠ s
    by_cases hy : y = s
    · exact Or.inl (by rw [hy]; exact hsV)
    · exact Or.inr hy
  have hrange : Set.range i ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rintro _ ⟨d, rfl⟩
    have hdV : i d ∈ f ⁻¹ᵁ V := by
      change f (i d) ∈ V
      rw [hs d]
      exact hsV
    exact ⟨⟨i d, hdV⟩, rfl⟩
  have haway : f ⁻¹ᵁ Z ≤ exceptionalComplement i := by
    intro x hx
    change f x ≠ s at hx
    change x ∉ Set.range i
    rintro ⟨d, hd⟩
    exact hx ((congrArg f hd).symm.trans (hs d))
  have hcover : (f ⁻¹ᵁ V) ⊔ exceptionalComplement i = ⊤ := by
    apply le_antisymm le_top
    intro x _
    change f x ∈ V ∨ x ∉ Set.range i
    by_cases hx : x ∈ Set.range i
    · obtain ⟨d, rfl⟩ := hx
      exact Or.inl ((hs d).symm ▸ hsV)
    · exact Or.inr hx
  exact ⟨V, hV, Z, hsV, rfl, hbase, hrange, haway, hcover⟩

/-- A contraction with a two-dimensional point stalk and the stated original
complement preserves dimension two. The argument transports stalks through the
actual complement maps and uses the stalk formula for scheme dimension. -/
theorem dimension_eq_two_of_point_complement
    {X Y : Scheme.{u}} (hX : topologicalKrullDim X ≤ 2)
    {k : Type u} [Field k] (c : Spec (.of k) ⟶ Y)
    (hc : ringKrullDim (Y.presheaf.stalk (c (IsLocalRing.closedPoint k))) = 2)
    (b : X ⟶ Y) (C : Y.Opens) (hC : (C : Set Y) = (Set.range c)ᶜ)
    [IsIso (b ∣_ C)] : topologicalKrullDim Y = 2 := by
  have hXD : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk] at hX
    intro x
    exact (le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) x).trans hX
  have hYD : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2 := by
    intro y
    by_cases hy : y ∈ Set.range c
    · obtain ⟨z, rfl⟩ := hy
      have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      subst z
      exact hc.le
    · have hyC : y ∈ C := (Set.ext_iff.mp hC y).mpr hy
      let yC : C.toScheme := ⟨y, hyC⟩
      let g : C.toScheme ⟶ X := inv (b ∣_ C) ≫ (b ⁻¹ᵁ C).ι
      let : IsOpenImmersion g := inferInstance
      calc
        ringKrullDim (Y.presheaf.stalk y) =
            ringKrullDim (C.toScheme.presheaf.stalk yC) :=
          ringKrullDim_eq_of_ringEquiv (asIso (C.ι.stalkMap yC)).commRingCatIsoToRingEquiv
        _ = ringKrullDim (X.presheaf.stalk (g yC)) :=
          (ringKrullDim_eq_of_ringEquiv (asIso (g.stalkMap yC)).commRingCatIsoToRingEquiv).symm
        _ ≤ 2 := hXD (g yC)
  rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
  apply le_antisymm (iSup_le hYD)
  rw [← hc]
  exact le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) (c (IsLocalRing.closedPoint k))

/-- The same complement isomorphism is birational over the original target.
Its density is derived from the two-dimensional point stalk and surjectivity,
rather than from a separately supplied birational identification. -/
theorem birationalOver_of_point_complement
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {k : Type u} [Field k] (c : Spec (.of k) ⟶ Y)
    (hc : ringKrullDim (Y.presheaf.stalk (c (IsLocalRing.closedPoint k))) = 2)
    (b : X ⟶ Y) [Surjective b] (C : Y.Opens)
    (hC : (C : Set Y) = (Set.range c)ᶜ) [IsIso (b ∣_ C)] :
    BirationalOver b (𝟙 Y) := by
  have hne : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) = 2 → y ≠ genericPoint Y := by
    intro y hdim h
    subst y
    change ringKrullDim Y.functionField = 2 at hdim
    rw [ringKrullDim_eq_zero_of_field] at hdim
    norm_num at hdim
  have hcg := hne (c (IsLocalRing.closedPoint k)) hc
  have hηC : genericPoint Y ∈ C := by
    apply (Set.ext_iff.mp hC _).mpr
    rintro ⟨z, hz⟩
    exact hcg ((congrArg c (Subsingleton.elim (IsLocalRing.closedPoint k) z)).trans hz)
  have hs : (b ⁻¹ᵁ C : Set X).Nonempty := by
    obtain ⟨x, hx⟩ := b.surjective (genericPoint Y)
    refine ⟨x, ?_⟩
    change b x ∈ C
    rw [hx]
    exact hηC
  let P : X.PartialIso Y :=
    { source := b ⁻¹ᵁ C
      dense_source := (b ⁻¹ᵁ C).isOpen.dense hs
      target := C
      dense_target := C.isOpen.dense ⟨genericPoint Y, hηC⟩
      iso := asIso (b ∣_ C) }
  refine ⟨P, ?_⟩
  simpa only [PartialIso.IsOver, P, asIso_hom, Category.comp_id] using
    morphismRestrict_ι b C

/-- An actual finite projective embedding on the specified inverse-image
neighbourhood gives a contraction over the original base. All global ideal,
blowup and complement comparisons refer to the original exceptional immersion. -/
theorem exists_cartier_contraction_of_local_projective_embedding
    {k : Type u} [Field k] {X S : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [IsNoetherian S]
    (hX : RegularStalks X) (f : X ⟶ S) [IsProper f]
    (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (Hom.idealModule i))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (V : S.Opens) (hV : IsAffineOpen V) (Z : S.Opens)
    (hbase : V ⊔ Z = ⊤) (haway : f ⁻¹ᵁ Z ≤ exceptionalComplement i)
    (hcover : (f ⁻¹ᵁ V) ⊔ exceptionalComplement i = ⊤)
    (hrange : Set.range i ⊆ Set.range (f ⁻¹ᵁ V).ι)
    {I : Type u} [Finite I]
    (p : (f ⁻¹ᵁ V).toScheme ⟶ ProjectiveSpace Γ(S, V) I) [IsClosedImmersion p]
    (hp : p ≫ toSpec Γ(S, V) I = (f ∣_ V) ≫ hV.isoSpec.hom) :
    ∃ (Y : Scheme.{u}) (b : X ⟶ Y) (c : Spec (.of k) ⟶ Y)
      (s : Y ⟶ S) (hf : Blowup.cartierPullback c.ker b),
      Surjective b ∧ IsProper b ∧ IsClosedImmersion c ∧ IsProper s ∧ IsNoetherian Y ∧
      RegularStalks Y ∧ IsIntegral Y ∧
      ringKrullDim (Y.presheaf.stalk (c (IsLocalRing.closedPoint k))) = 2 ∧
      IsIso ((Blowup.blowupDatum c.ker).lift b hf) ∧ c.ker.comap b = i.ker ∧
      i ≫ b = toSpec k (ULift.{u} (Fin 2)) ≫ c ∧ b ≫ s = f ∧
      ∃ (C : Y.Opens) (ε : (exceptionalComplement i).toScheme ≅ C.toScheme),
        (C : Set Y) = (Set.range c)ᶜ ∧
        b ⁻¹ᵁ C = exceptionalComplement i ∧ IsIso (b ∣_ C) ∧
        ε.hom ≫ C.ι = (exceptionalComplement i).ι ≫ b := by
  let U := f ⁻¹ᵁ V
  let W := exceptionalComplement i
  let : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let d : ProjectiveSpace k (ULift.{u} (Fin 2)) := Classical.choice inferInstance
  obtain ⟨u, _⟩ := hrange ⟨d, rfl⟩
  let : Nonempty U.toScheme := ⟨u⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let iU := OpenRestriction.map i U.ι hrange
  let : IsClosedImmersion iU := inferInstance
  have hi : iU ≫ U.ι = i := OpenRestriction.map_comp i U.ι hrange
  have hIU := OpenRestriction.isLocallyRankOne_ideal i U.ι hrange hI
  let eIU := OpenRestriction.conormalTwistIso i U.ι hrange eI
  obtain ⟨T, c, ρ, t, hfc, hcs, hcp, hρ, htp, hTN, hTR, hTI, hpt,
      hbl, hker, hexc, htri, _, C, ε, hC, hpre, _, hε⟩ :=
    exists_cartier_contraction_of_projective_embedding (hX.of_isOpenImmersion U.ι)
      ((f ∣_ V) ≫ hV.isoSpec.hom) p hp iU hIU eIU
  let : IsNoetherian T := hTN
  let : IsIntegral T := hTI
  let : Surjective c := hcs
  let : IsProper c := hcp
  let : IsProper t := htp
  let : IsClosedImmersion ρ := hρ
  let q : T ⟶ V.toScheme := t ≫ hV.isoSpec.inv
  let : IsProper q := inferInstance
  have hcq : c ≫ q = f ∣_ V := by
    calc
      c ≫ q = (c ≫ t) ≫ hV.isoSpec.inv := (Category.assoc _ _ _).symm
      _ = ((f ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.isoSpec.inv :=
        congrArg (fun g => g ≫ hV.isoSpec.inv) htri
      _ = f ∣_ V := by rw [Category.assoc, hV.isoSpec.hom_inv_id, Category.comp_id]
  have hW : U.ι ⁻¹ᵁ W = exceptionalComplement iU := by
    apply Opens.ext
    exact OpenRestriction.preimage_complement i U.ι hrange
  let : IsOpenImmersion ((W.ι ∣_ U) ≫ c) :=
    ProperGluing.overlap_isOpenImmersion_of_complement U W c
      (exceptionalComplement iU) C hW ε hε
  have Hoverlap := ProperGluing.overlap_isPullback_of_complement U W c
    (exceptionalComplement iU) C hW ε hε hpre
  have hcompl : Set.range ((W.ι ∣_ U) ≫ c) = (Set.range ρ)ᶜ :=
    (ProperGluing.overlap_range_of_complement U W c
      (exceptionalComplement iU) C hW ε hε).trans hC
  let Y := ProperGluing.obj f V W c
  let b : X ⟶ Y := ProperGluing.contraction f V W c hcover
  let ρ' : Spec (.of k) ⟶ Y := ProperGluing.point f V W c ρ
  let s : Y ⟶ S := ProperGluing.structureMap f V W c q hcq
  let R : Y.Opens := (ProperGluing.rightι f V W c).opensRange
  let hf : Blowup.cartierPullback ρ'.ker b :=
    ProperGluing.pointIdeal_cartierPullback f V W c ρ hcover i iU
      (toSpec k (ULift.{u} (Fin 2))) hi hexc hker hcompl hI
  have hYpt : ringKrullDim (Y.presheaf.stalk (ρ' (IsLocalRing.closedPoint k))) = 2 := by
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso ((ProperGluing.leftι f V W c).stalkMap
        (ρ (IsLocalRing.closedPoint k)))).commRingCatIsoToRingEquiv).trans hpt
  have hbpre : b ⁻¹ᵁ R = W := by
    have H := OpenReplacement.OfOpens.isPullback_right U W hcover c Hoverlap
    have Hrange : W = b ⁻¹ᵁ R := by
      simpa only [Opens.opensRange_ι] using
        (Hom.opensRange_of_isPullback W.ι (𝟙 W.toScheme) b
          (ProperGluing.rightι f V W c) H.flip)
    exact Hrange.symm
  refine ⟨Y, b, ρ', s, hf,
    ProperGluing.contraction_surjective f V W c hcover,
    ProperGluing.contraction_isProper f V W c hcover Hoverlap,
    ProperGluing.point_isClosedImmersion f V W c ρ hcompl,
    ProperGluing.structureMap_isProper f V W c q hcq hcover Z hbase haway,
    ProperGluing.isNoetherian_obj f V W c,
    ProperGluing.regularStalks_obj f V W c hX hTR,
    ProperGluing.isIntegral_obj f V W c hcover hX hTR, hYpt,
    ProperGluing.contraction_isBlowup f V W c ρ hcover Hoverlap hcompl hf hfc hbl,
    ProperGluing.pointIdeal_comap_contraction f V W c ρ hcover i iU
      (toSpec k (ULift.{u} (Fin 2))) hi hexc hker hcompl,
    ?_, ProperGluing.contraction_structureMap f V W c q hcq hcover,
    R, ProperGluing.complementIso f V W c, ?_, hbpre,
    ProperGluing.contraction_isIso_restrict f V W c hcover Hoverlap,
    ProperGluing.complementIso_hom f V W c hcover⟩
  · calc
      i ≫ b = (iU ≫ U.ι) ≫ b := congrArg (fun g => g ≫ b) hi.symm
      _ = (iU ≫ c) ≫ ProperGluing.leftι f V W c := by
        rw [Category.assoc, ProperGluing.left_contraction, ← Category.assoc]
      _ = toSpec k (ULift.{u} (Fin 2)) ≫ ρ' := by
        rw [hexc, Category.assoc]
        rfl
  · exact ProperGluing.range_right_eq_compl_point f V W c ρ hcompl

end AlgebraicGeometry.Scheme.Surfaces.Contraction.Proper
