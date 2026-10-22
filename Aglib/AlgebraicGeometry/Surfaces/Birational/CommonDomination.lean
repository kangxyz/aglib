/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Integral.GenericSection
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Actual regular-source common domination of proper targets

The original dominant generic map lifts through the actual Chow modification.
Its finite projective coordinates extend successively along the native point
chains, with original function-field maps retained. Native finite products
assemble the actual target map. Normality of the regular final source extends
its original generic lift through the finite Chow map, recovering a morphism
to the original proper target. Original base and generic triangles are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.CommonDomination

/-- An original dominant field-valued generic map lands in every actual dense
open of the integral target. -/
theorem genericMap_range_subset_denseOpen {K : Type u} [Field K]
    {T : Scheme.{u}} [IsIntegral T] (g : Spec (.of K) ⟶ T) [IsDominant g]
    (V : T.Opens) (hV : Dense (V : Set T)) : Set.range g ⊆ V := by
  rintro _ ⟨x, rfl⟩
  have hx : x = genericPoint (Spec (.of K)) := Subsingleton.elim _ _
  rw [hx, Scheme.map_genericPoint_of_isDominant (Spec (.of K)) g]
  exact ((genericPoint_spec T).mem_open_set_iff V.isOpen).mpr
    (by simpa only [Set.univ_inter] using hV.nonempty)

/-- Lift the original generic map through the actual restriction isomorphism,
retaining the supplied modification and its literal dense open. -/
def genericLiftOfIsoOnDenseOpen {K : Type u} [Field K]
    {T Z : Scheme.{u}} [IsIntegral T] (p : Z ⟶ T)
    (V : T.Opens) (hV : Dense (V : Set T)) [IsIso (p ∣_ V)]
    (g : Spec (.of K) ⟶ T) [IsDominant g] : Spec (.of K) ⟶ Z :=
  IsOpenImmersion.lift V.ι g (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨g x, genericMap_range_subset_denseOpen g V hV ⟨x, rfl⟩⟩, rfl⟩) ≫
    inv (p ∣_ V) ≫ (p ⁻¹ᵁ V).ι

@[reassoc (attr := simp)]
theorem genericLiftOfIsoOnDenseOpen_comp {K : Type u} [Field K]
    {T Z : Scheme.{u}} [IsIntegral T] (p : Z ⟶ T)
    (V : T.Opens) (hV : Dense (V : Set T)) [IsIso (p ∣_ V)]
    (g : Spec (.of K) ⟶ T) [IsDominant g] :
    genericLiftOfIsoOnDenseOpen p V hV g ≫ p = g := by
  simp only [genericLiftOfIsoOnDenseOpen, Category.assoc]
  rw [← morphismRestrict_ι p V, IsIso.inv_hom_id_assoc]
  exact IsOpenImmersion.lift_fac V.ι g _

/-- The actual Chow producer supplies its own modification and an original
generic lift; no modification, coordinate or model family is given as input. -/
theorem exists_chowModification_with_genericLift
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (pX : X ⟶ Spec (.of R)) (pT : T ⟶ Spec (.of R)) [IsProper pT]
    (gη : Spec X.functionField ⟶ T) [IsDominant gη]
    (hg : gη ≫ pT = X.fromSpecStalk (genericPoint X) ≫ pX) :
    ∃ (m : ℕ) (σ : Fin m → Type u) (_ : ∀ i, Fintype (σ i))
      (Z : Scheme.{u}) (p : Z ⟶ T) (q : Z ⟶ (Chow.projectiveProductOver R σ).left)
      (V : T.Opens) (w : p ≫ pT = q ≫ (Chow.projectiveProductOver R σ).hom)
      (gZ : Spec X.functionField ⟶ Z),
      IsProper p ∧ Surjective p ∧ IsFinite q ∧ Dense (V : Set T) ∧
        IsIso (p ∣_ V) ∧ IsClosedImmersion (pullback.lift p q w) ∧
        gZ ≫ p = gη ∧ gZ ≫ q ≫ (Chow.projectiveProductOver R σ).hom =
          X.fromSpecStalk (genericPoint X) ≫ pX := by
  obtain ⟨m, σ, hσ, Z, p, q, V, w, hp, hsurj, hq, hV, hi, hclosed⟩ :=
    Chow.exists_finite_projective_product_modification R pT
  let : IsIso (p ∣_ V) := hi
  let gZ := genericLiftOfIsoOnDenseOpen p V hV gη
  refine ⟨m, σ, hσ, Z, p, q, V, w, gZ, hp, hsurj, hq, hV, hi, hclosed,
    genericLiftOfIsoOnDenseOpen_comp p V hV gη, ?_⟩
  calc
    gZ ≫ q ≫ (Chow.projectiveProductOver R σ).hom = gZ ≫ (p ≫ pT) :=
      congrArg (fun a ↦ gZ ≫ a) w.symm
    _ = (gZ ≫ p) ≫ pT := (Category.assoc _ _ _).symm
    _ = gη ≫ pT := congrArg (fun a ↦ a ≫ pT)
      (genericLiftOfIsoOnDenseOpen_comp p V hV gη)
    _ = _ := hg


private theorem generic_triangle_comp
    {X Y Z T : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f] [IsDominant g]
    (a : Y ⟶ T) (aη : Spec X.functionField ⟶ T)
    (ha : Y.fromSpecStalk (genericPoint Y) ≫ a =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫ aη) :
    Z.fromSpecStalk (genericPoint Z) ≫ (g ≫ a) =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap (g ≫ f))) ≫ aη := by
  calc
    _ = (Z.fromSpecStalk (genericPoint Z) ≫ g) ≫ a :=
      (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap g)) ≫
        Y.fromSpecStalk (genericPoint Y) ≫ a := by
      rw [Scheme.fromSpecStalk_genericPoint_naturality, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap g)) ≫
        Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫ aη := by rw [ha]
    _ = _ := by
      rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]
      exact (Category.assoc _ _ _).symm

private theorem finiteProduct_map_with_original_generic
    {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (pX : X ⟶ S)
    {n : ℕ} (P : Fin n → Over S)
    (aη : Spec X.functionField ⟶ (finiteProductOver P).left)
    (haη : aη ≫ (finiteProductOver P).hom =
      X.fromSpecStalk (genericPoint X) ≫ pX)
    (a : ∀ i, Y ⟶ (P i).left)
    (ha : ∀ i, a i ≫ (P i).hom = f ≫ pX)
    (hgen : ∀ i, Y.fromSpecStalk (genericPoint Y) ≫ a i =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫ aη ≫
        (finiteProductOverπ P i).left) :
    ∃ h : Y ⟶ (finiteProductOver P).left,
      h ≫ (finiteProductOver P).hom = f ≫ pX ∧
        Y.fromSpecStalk (genericPoint Y) ≫ h =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫ aη ∧
        ∀ i, h ≫ (finiteProductOverπ P i).left = a i := by
  let A : Over S := Over.mk (f ≫ pX)
  let ai (i : Fin n) : A ⟶ P i := Over.homMk (a i) (ha i)
  let h : A ⟶ finiteProductOver P := finiteProductOverLift P ai
  have hπ (i : Fin n) : h.left ≫ (finiteProductOverπ P i).left = a i :=
    congrArg (fun k ↦ k.left) (finiteProductOverLift_π P ai i)
  let G : Over S := Over.mk (Y.fromSpecStalk (genericPoint Y) ≫ f ≫ pX)
  let e : G ⟶ A := Over.homMk (Y.fromSpecStalk (genericPoint Y)) rfl
  let g₀ : Over.mk (X.fromSpecStalk (genericPoint X) ≫ pX) ⟶ finiteProductOver P :=
    Over.homMk aη haη
  have hfield : Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫
      (X.fromSpecStalk (genericPoint X) ≫ pX) =
        Y.fromSpecStalk (genericPoint Y) ≫ f ≫ pX := by
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ pX)
      (Scheme.fromSpecStalk_genericPoint_naturality f).symm
  let γ : G ⟶ Over.mk (X.fromSpecStalk (genericPoint X) ≫ pX) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f))) hfield
  have hh : e ≫ h = γ ≫ g₀ := by
    apply finiteProductOver_hom_ext P
    intro i
    apply Over.OverMorphism.ext
    change Y.fromSpecStalk (genericPoint Y) ≫ h.left ≫
        (finiteProductOverπ P i).left =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫ aη ≫
        (finiteProductOverπ P i).left
    rw [hπ]
    exact hgen i
  refine ⟨h.left, h.w, ?_, hπ⟩
  have hv := congrArg (fun k ↦ k.left) hh
  change Y.fromSpecStalk (genericPoint Y) ≫ h.left =
    Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f)) ≫ aη at hv
  exact hv

private theorem normalStalks_of_regularStalks {X : Scheme.{u}}
    (hX : RegularStalks X) : NormalStalks X := by
  intro x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩


private theorem exists_finiteProjectiveFamily_extension
    (R : Type u) [CommRing R] (n : ℕ) :
    ∀ (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]
      (_hX : RegularStalks X) (_hd : topologicalKrullDim X ≤ 2)
      (pX : X ⟶ Spec (.of R)) (σ : Fin n → Type u)
      (_hσ : ∀ i, Finite (σ i))
      (g : ∀ i, Spec X.functionField ⟶ ProjectiveSpace R (Option (σ i)))
      (_hg : ∀ i, g i ≫ ProjectiveSpace.toSpec R (Option (σ i)) =
        X.fromSpecStalk (genericPoint X) ≫ pX),
      ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (c : Blowup.PointBlowupChain β),
        let : IsIntegral Y := c.isIntegral inferInstance
        let : IsDominant β := c.isDominant inferInstance
        ∃ a : ∀ i, Y ⟶ ProjectiveSpace R (Option (σ i)),
          (∀ i, a i ≫ ProjectiveSpace.toSpec R (Option (σ i)) = β ≫ pX) ∧
          (∀ i, Y.fromSpecStalk (genericPoint Y) ≫ a i =
            Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ g i) := by
  induction n with
  | zero =>
    intro X hN hI hX hd pX σ hσ g hg
    refine ⟨X, 𝟙 X, Blowup.PointBlowupChain.refl X, ?_⟩
    refine ⟨fun i ↦ i.elim0, ?_, ?_⟩ <;> intro i <;> exact i.elim0
  | succ n ih =>
    intro X hN hI hX hd pX σ hσ g hg
    let (i : Fin (n + 1)) : Finite (σ i) := hσ i
    obtain ⟨Y₁, β₁, c₁, hout₁⟩ :=
      RationalCoordinates.exists_pointBlowupChain_projectiveExtension
        (R := R) (X := X) (I := Option (σ 0)) hX hd pX (g 0) (hg 0)
    let : IsIntegral Y₁ := c₁.isIntegral inferInstance
    let : IsDominant β₁ := c₁.isDominant inferInstance
    obtain ⟨a₀, hproper₁, _, hreg₁, hdim₁, hbase₀, hgen₀⟩ := hout₁
    let : IsProper β₁ := hproper₁
    let : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian β₁
    let : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace β₁
    let : IsNoetherian Y₁ := ⟨⟩
    have hd₁ : topologicalKrullDim Y₁ ≤ 2 := by
      rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
      exact iSup_le hdim₁
    let p₁ := β₁ ≫ pX
    let g₁ (i : Fin n) :=
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β₁)) ≫ g i.succ
    have hg₁ (i : Fin n) : g₁ i ≫ ProjectiveSpace.toSpec R (Option (σ i.succ)) =
        Y₁.fromSpecStalk (genericPoint Y₁) ≫ p₁ := by
      calc
        _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β₁)) ≫
            X.fromSpecStalk (genericPoint X) ≫ pX := by
          rw [Category.assoc, hg]
        _ = (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β₁)) ≫
            X.fromSpecStalk (genericPoint X)) ≫ pX := (Category.assoc _ _ _).symm
        _ = (Y₁.fromSpecStalk (genericPoint Y₁) ≫ β₁) ≫ pX :=
          congrArg (fun k ↦ k ≫ pX)
            (Scheme.fromSpecStalk_genericPoint_naturality β₁).symm
        _ = _ := Category.assoc _ _ _
    obtain ⟨Y₂, β₂, c₂, hout₂⟩ := ih Y₁ hreg₁ hd₁ p₁
      (fun i ↦ σ i.succ) (fun i ↦ hσ i.succ) g₁ hg₁
    let : IsIntegral Y₂ := c₂.isIntegral inferInstance
    let : IsDominant β₂ := c₂.isDominant inferInstance
    obtain ⟨atail, hbaseTail, hgenTail⟩ := hout₂
    let β := β₂ ≫ β₁
    let c := c₁.comp c₂
    refine ⟨Y₂, β, c, ?_⟩
    let a : ∀ i : Fin (n + 1), Y₂ ⟶ ProjectiveSpace R (Option (σ i)) :=
      Fin.cases (β₂ ≫ a₀) atail
    refine ⟨a, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero =>
        change (β₂ ≫ a₀) ≫ ProjectiveSpace.toSpec R (Option (σ 0)) =
          (β₂ ≫ β₁) ≫ pX
        simpa only [Category.assoc] using congrArg (fun k ↦ β₂ ≫ k) hbase₀
      | succ i =>
        change atail i ≫ ProjectiveSpace.toSpec R (Option (σ i.succ)) =
          (β₂ ≫ β₁) ≫ pX
        simpa only [p₁, Category.assoc] using hbaseTail i
    · intro i
      cases i using Fin.cases with
      | zero =>
        change Y₂.fromSpecStalk (genericPoint Y₂) ≫ (β₂ ≫ a₀) =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap (β₂ ≫ β₁))) ≫ g 0
        exact generic_triangle_comp β₁ β₂ a₀ (g 0) hgen₀
      | succ i =>
        change Y₂.fromSpecStalk (genericPoint Y₂) ≫ atail i =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap (β₂ ≫ β₁))) ≫ g i.succ
        calc
          _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β₂)) ≫ g₁ i :=
            hgenTail i
          _ = _ := by
            dsimp only [g₁]
            rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]
            exact (Category.assoc _ _ _).symm


theorem exists_pointBlowupChain_extension_to_proper_target
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X T : Scheme.{u}} [IsNoetherian X] [IsIntegral X] [IsIntegral T]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (pX : X ⟶ Spec (.of R)) (pT : T ⟶ Spec (.of R)) [IsProper pT]
    (gη : Spec X.functionField ⟶ T) [IsDominant gη]
    (hgη : gη ≫ pT = X.fromSpecStalk (genericPoint X) ≫ pX) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (c : Blowup.PointBlowupChain β),
      let : IsIntegral Y := c.isIntegral inferInstance
      let : IsDominant β := c.isDominant inferInstance
      ∃ (h : Y ⟶ T) (j : Spec X.functionField ⟶ Y),
        IsProper β ∧ BirationalOver β (𝟙 X) ∧ IsNoetherian Y ∧
        RegularStalks Y ∧ topologicalKrullDim Y ≤ 2 ∧ IsDominant h ∧
        h ≫ pT = β ≫ pX ∧
        Y.fromSpecStalk (genericPoint Y) ≫ h =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ gη ∧
        j ≫ β = X.fromSpecStalk (genericPoint X) ∧ j ≫ h = gη := by
  obtain ⟨m, σ, hσ, Z, p, q, V, w, gZ, _, _, hq, _, _, _,
      hgZp, hgZbase⟩ := exists_chowModification_with_genericLift R pX pT gη hgη
  let (i : Fin m) : Fintype (σ i) := hσ i
  let : IsFinite q := hq
  let P : Fin m → Over (Spec (.of R)) :=
    fun i ↦ Over.mk (ProjectiveSpace.toSpec R (Option (σ i)))
  let gP := gZ ≫ q
  have hgP : gP ≫ (finiteProductOver P).hom =
      X.fromSpecStalk (genericPoint X) ≫ pX := by
    simpa only [gP, Category.assoc] using hgZbase
  let gi (i : Fin m) := gP ≫ (finiteProductOverπ P i).left
  have hgi (i : Fin m) : gi i ≫ ProjectiveSpace.toSpec R (Option (σ i)) =
      X.fromSpecStalk (genericPoint X) ≫ pX := by
    change (gP ≫ (finiteProductOverπ P i).left) ≫ (P i).hom = _
    rw [Category.assoc, finiteProductOverπ_hom]
    exact hgP
  obtain ⟨Y, β, c, hout⟩ := exists_finiteProjectiveFamily_extension R m X hX hd pX σ
    (fun _ ↦ inferInstance) gi hgi
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  obtain ⟨a, ha, hgen⟩ := hout
  obtain ⟨hP, hPbase, hPgen, _⟩ :=
    finiteProduct_map_with_original_generic β pX P gP hgP a ha hgen
  let : IsProper β := c.isProper inferInstance
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace β
  let : IsNoetherian Y := ⟨⟩
  have hregY := c.regularStalks inferInstance hX
  have hdimX : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk] at hd
    intro x
    exact (le_iSup (fun z : X ↦ ringKrullDim (X.presheaf.stalk z)) x).trans hd
  have hdimY := c.stalk_dimension_le_two inferInstance hX hdimX
  have hdY : topologicalKrullDim Y ≤ 2 := by
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk]
    exact iSup_le hdimY
  have hnormalY := normalStalks_of_regularStalks hregY
  let gZY := Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ gZ
  have hgZY : gZY ≫ q = Y.fromSpecStalk (genericPoint Y) ≫ hP := by
    calc
      _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ gP :=
        Category.assoc _ _ _
      _ = _ := hPgen.symm
  let l := integralGenericLift Y hnormalY hP q gZY hgZY
  have hlq := integralGenericLift_over Y hnormalY hP q gZY hgZY
  have hlg := integralGenericLift_generic Y hnormalY hP q gZY hgZY
  let h := l ≫ p
  have hbase : h ≫ pT = β ≫ pX := by
    calc
      _ = l ≫ (p ≫ pT) := Category.assoc _ _ _
      _ = l ≫ q ≫ (finiteProductOver P).hom := congrArg (fun k ↦ l ≫ k) w
      _ = (l ≫ q) ≫ (finiteProductOver P).hom := (Category.assoc _ _ _).symm
      _ = hP ≫ (finiteProductOver P).hom :=
        congrArg (fun k ↦ k ≫ (finiteProductOver P).hom) hlq
      _ = _ := hPbase
  have hgeneric : Y.fromSpecStalk (genericPoint Y) ≫ h =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ gη := by
    calc
      _ = (Y.fromSpecStalk (genericPoint Y) ≫ l) ≫ p := (Category.assoc _ _ _).symm
      _ = gZY ≫ p := congrArg (fun k ↦ k ≫ p) hlg
      _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ (gZ ≫ p) :=
        Category.assoc _ _ _
      _ = _ := congrArg (fun k ↦
        Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ k) hgZp
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)) :=
    c.functionFieldMap_isIso inferInstance
  let e := asIso (CommRingCat.ofHom (Scheme.functionFieldMap β))
  let j := Spec.map e.inv ≫ Y.fromSpecStalk (genericPoint Y)
  have hinv : Spec.map e.inv ≫ Spec.map e.hom = 𝟙 (Spec X.functionField) := by
    calc
      _ = Spec.map (e.hom ≫ e.inv) := (Spec.map_comp e.hom e.inv).symm
      _ = Spec.map (𝟙 (CommRingCat.of X.functionField)) := congrArg Spec.map e.hom_inv_id
      _ = 𝟙 (Spec (CommRingCat.of X.functionField)) := by simp
      _ = _ := rfl
  have hjβ : j ≫ β = X.fromSpecStalk (genericPoint X) := by
    calc
      _ = Spec.map e.inv ≫ (Y.fromSpecStalk (genericPoint Y) ≫ β) := Category.assoc _ _ _
      _ = Spec.map e.inv ≫ Spec.map e.hom ≫ X.fromSpecStalk (genericPoint X) :=
        congrArg (fun k ↦ Spec.map e.inv ≫ k)
          (Scheme.fromSpecStalk_genericPoint_naturality β)
      _ = (Spec.map e.inv ≫ Spec.map e.hom) ≫ X.fromSpecStalk (genericPoint X) :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 (Spec X.functionField) ≫ X.fromSpecStalk (genericPoint X) :=
        congrArg (fun k ↦ k ≫ X.fromSpecStalk (genericPoint X)) hinv
      _ = _ := Category.id_comp _
  have hjh : j ≫ h = gη := by
    calc
      _ = Spec.map e.inv ≫ (Y.fromSpecStalk (genericPoint Y) ≫ h) := Category.assoc _ _ _
      _ = Spec.map e.inv ≫ Spec.map e.hom ≫ gη :=
        congrArg (fun k ↦ Spec.map e.inv ≫ k) hgeneric
      _ = (Spec.map e.inv ≫ Spec.map e.hom) ≫ gη := (Category.assoc _ _ _).symm
      _ = 𝟙 (Spec X.functionField) ≫ gη := congrArg (fun k ↦ k ≫ gη) hinv
      _ = _ := Category.id_comp _
  let : IsDominant (j ≫ h) := hjh.symm ▸ (inferInstance : IsDominant gη)
  have hdom : IsDominant h := IsDominant.of_comp j h
  exact ⟨Y, β, c, h, j, inferInstance, c.birationalOver inferInstance,
    inferInstance, hregY, hdY, hdom, hbase, hgeneric, hjβ, hjh⟩

theorem exists_proper_pointBlowupChain_commonDomination
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X T : Scheme.{u}} [IsNoetherian X] [IsIntegral X] [IsIntegral T]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (pX : X ⟶ Spec (.of R)) [IsProper pX]
    (pT : T ⟶ Spec (.of R)) [IsProper pT]
    (gη : Spec X.functionField ⟶ T) [IsDominant gη]
    (hgη : gη ≫ pT = X.fromSpecStalk (genericPoint X) ≫ pX) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (c : Blowup.PointBlowupChain β),
      let : IsIntegral Y := c.isIntegral inferInstance
      let : IsDominant β := c.isDominant inferInstance
      ∃ (h : Y ⟶ T) (j : Spec X.functionField ⟶ Y),
        IsProper β ∧ BirationalOver β (𝟙 X) ∧ IsNoetherian Y ∧
        RegularStalks Y ∧ topologicalKrullDim Y ≤ 2 ∧ IsProper h ∧ Surjective h ∧
        h ≫ pT = β ≫ pX ∧
        Y.fromSpecStalk (genericPoint Y) ≫ h =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ gη ∧
        j ≫ β = X.fromSpecStalk (genericPoint X) ∧ j ≫ h = gη := by
  obtain ⟨Y, β, c, hout⟩ :=
    exists_pointBlowupChain_extension_to_proper_target R hX hd pX pT gη hgη
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  obtain ⟨h, j, hpβ, hbir, hN, hreg, hdim, hdom, hbase, hgeneric, hjβ, hjh⟩ := hout
  let : IsProper β := hpβ
  let : IsDominant h := hdom
  let : IsProper (h ≫ pT) := hbase.symm ▸ (inferInstance : IsProper (β ≫ pX))
  let : IsProper h := IsProper.of_comp h pT
  let : Surjective h :=
    surjective_of_isDominant_of_isClosed_range h h.isClosedMap.isClosed_range
  exact ⟨Y, β, c, h, j, hpβ, hbir, hN, hreg, hdim, inferInstance, inferInstance,
    hbase, hgeneric, hjβ, hjh⟩

end AlgebraicGeometry.Scheme.CommonDomination
