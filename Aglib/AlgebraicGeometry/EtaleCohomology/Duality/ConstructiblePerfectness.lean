/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.GenericOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.Constructible.FiniteSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.OpenPerfectness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PerfectnessExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph

/-!
# Constructible curve duality on the original coefficient objects

The geometric reduction selects the actual stratum containing the original
generic point from the SAME global finite locally closed partition. Its
original inclusion is a nonempty dense open; its complement is finite and
consists of closed points. The original module inverse image is retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u r

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- A constructible module on an integral Noetherian scheme of dimension at
most one is finite-type locally constant on an actual nonempty dense open
stratum of its original partition, with a finite closed-point complement.
The coefficient ring is arbitrary and no lisse-locus model is introduced. -/
theorem exists_dense_open_finiteTypeLocallyConstant
    {R : Type r} [CommRing R] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) {F : ModuleSheaf R X} (hF : IsConstructible F) :
    ∃ (V : Scheme.{u}) (g : V ⟶ X), IsOpenImmersion g ∧ DenseRange g ∧ Nonempty V ∧
      IsFiniteTypeLocallyConstant ((moduleInverseImage R g).obj F) ∧
      (Set.range g)ᶜ.Finite ∧ ∀ x ∈ (Set.range g)ᶜ, IsClosed ({x} : Set X) := by
  let : NoetherianSpace X := inferInstance
  let : CompactSpace X := inferInstance
  let : QuasiSeparatedSpace X := inferInstance
  obtain ⟨t⟩ := nonempty_constructiblePartition hF
  obtain ⟨a, hη, hg, hdense, hnonempty⟩ :=
    t.toFiniteLocallyClosedPartition.exists_generic_open_stratum
  let V := t.stratum a
  let g : V ⟶ X := t.inclusion a
  let : IsOpenImmersion g := hg
  have hηg : genericPoint X ∈ Set.range g := hη
  have hclosed : IsClosed ((Set.range g)ᶜ) := g.isOpenEmbedding.isOpen_range.isClosed_compl
  have hne : (Set.range g)ᶜ ≠ Set.univ := by
    intro h
    have hx : genericPoint X ∈ (Set.range g)ᶜ := by rw [h]; trivial
    exact hx hηg
  have hfinite := Scheme.DimensionOne.finite_of_isClosed_of_ne_univ X hdim hclosed hne
  have hpoints : ∀ x ∈ (Set.range g)ᶜ, IsClosed ({x} : Set X) := by
    intro x hx
    rcases Scheme.DimensionOne.point_eq_generic_or_isClosed X hdim x with he | hc
    · subst x
      exact (hx hηg).elim
    · exact hc
  exact ⟨V, g, hg, hdense, hnonempty, t.locally_constant a, hfinite, hpoints⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

private theorem original_range_comp_complement
    {A B C : Type*} (f : A → B) (g : B → C) (hg : Function.Injective g)
    (D : Set C) (hD : Set.range g = Dᶜ) :
    Set.range (g ∘ f) = (D ∪ g '' (Set.range f)ᶜ)ᶜ := by
  ext z
  change (∃ a, g (f a) = z) ↔
    ¬ (z ∈ D ∨ ∃ b, b ∉ Set.range f ∧ g b = z)
  constructor
  · rintro ⟨a, rfl⟩ (hz | ⟨b, hb, he⟩)
    · have h : g (f a) ∈ Dᶜ := by
        rw [← hD]
        exact ⟨f a, rfl⟩
      exact h hz
    · exact hb ⟨a, (hg he).symm⟩
  · intro hz
    have hzg : z ∈ Set.range g := by
      rw [hD]
      exact fun h => hz (Or.inl h)
    obtain ⟨b, hb⟩ := hzg
    have hbf : b ∈ Set.range f := by
      by_contra h
      exact hz (Or.inr ⟨b, h, hb⟩)
    obtain ⟨a, ha⟩ := hbf
    exact ⟨a, (congrArg g ha).trans hb⟩

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Curves.FiniteClosedSupport Scheme.OverField
open CategoryTheory.Limits CategoryTheory.Abelian

universe wU wX wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule
  moduleSheaf_hasFiniteBiproducts

/-- The original compact-support trace pairing has both bijective adjoints
for every constructible native coefficient on the given finite-complement open
of the same smooth proper geometrically connected curve. The modulus may be
composite or one, and the original source, compact and abelian worlds remain
independent. The actual generic-stratum counit/unit localization is used. -/
theorem moduleDualityMap_isPerfPair_of_constructible
    {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
    (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
    [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv F r hr).IsPerfPair := by
  let : Nonempty U := nonempty_of_curve_finite_complement X hX D hfin hclosed j hD
  let : IsIntegral X.left := hX.isIntegral
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : IsNoetherian X.left := Curve.curveProperties_isNoetherian hX
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let : NoetherianSpace U := j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : CompactSpace U := NoetherianSpace.compactSpace U
  let : IsNoetherian U := ⟨⟩
  let Λ := ULift.{u + 1} (ZMod n)
  have hdim : topologicalKrullDim U ≤ 1 :=
    Curves.dimension_le_one_of_etale j hX.topologicalKrullDim_eq_one.le
  obtain ⟨V, g, hg, _, hV, hgF, hTfin, hTclosed⟩ :=
    Constructible.Modules.exists_dense_open_finiteTypeLocallyConstant hdim hF
  let : IsOpenImmersion g := hg
  let : Nonempty V := hV
  let : HasExt.{u + 2} (ModuleSheaf V Λ) := SheafOfModules.hasExt (constantRing V Λ)
  let T : Set U := (Set.range g)ᶜ
  let i := inclusion U T
  let : IsClosedImmersion i := inclusion_isClosedImmersion U T hTfin hTclosed
  let P := (moduleInverseImage g Λ).obj F
  let M := (moduleInverseImage i Λ).obj F
  have hP : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence V Λ).inverse.obj P) :=
    (Constructible.Modules.isFiniteTypeLocallyConstant_iff_of_iso
      ((moduleInverseImageValuedIso Λ g).app F)).mpr hgF
  have hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme U T) Λ).inverse.obj M) :=
    (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleInverseImageValuedIso Λ i).app F)).mpr
        (Constructible.Modules.isConstructible_pullback i hF)
  let E : Set X.left := D ∪ j '' T
  have hEfin : E.Finite := hfin.union (hTfin.image j)
  have hEclosed : ∀ x ∈ E, IsClosed ({x} : Set X.left) := by
    intro x hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hclosed x hx
    · exact modulePoint_image_isClosed hX j ⟨y, hTclosed y hy⟩
  have hE : Set.range (g ≫ j) = Eᶜ :=
    original_range_comp_complement g j j.isOpenEmbedding.injective D hD
  have hcomp : Set.range g = (Set.range i)ᶜ := by
    rw [range_inclusion]
    simp only [T, compl_compl]
  let S := moduleLocalizationShortComplex g Λ i hcomp F
  have hS : S.ShortExact := moduleLocalization_shortExact g Λ i hcomp F
  have hA (q : ℕ) (hq : q ≤ 2) :
      (moduleDualityMap.{u, wU, wX, wA}
        X hX D hfin hclosed j hD n hn hunit hinv S.X₁ q hq).IsPerfPair := by
    apply (moduleDualityMap_lowerShriek_isPerfPair_iff
      X hX D hfin hclosed j hD g E hEfin hEclosed hE n hn hunit hinv P q hq).mpr
    exact moduleDualityMap_isPerfPair_of_finiteLocallyConstant.{u, u + 2, wX, wA}
      X hX E hEfin hEclosed (g ≫ j) hE n hn hunit hinv P hP q hq
  have hQ (q : ℕ) (hq : q ≤ 2) :
      (moduleDualityMap.{u, wU, wX, wA}
        X hX D hfin hclosed j hD n hn hunit hinv S.X₃ q hq).IsPerfPair :=
    moduleDualityMap_finiteSupport_isPerfPair.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv T hTfin hTclosed M hM q hq
  have hCA : Subsingleton (Ext.{wX} (moduleUnit X.left Λ)
      ((moduleLowerShriek j Λ).obj S.X₁) 3) := by
    let : Subsingleton (Ext.{wX} (moduleUnit X.left Λ)
        ((moduleLowerShriek (g ≫ j) Λ).obj P) 3) :=
      moduleCompactExt_high_subsingleton_of_finiteLocallyConstant.{u, wX, wA}
        X hX E hEfin hEclosed (g ≫ j) hE n hn hunit P hP 3 (by decide)
    exact (moduleLowerShriekCompAddEquiv g j Λ P 3).injective.subsingleton
  have hEQ : Subsingleton (Ext.{wU} S.X₃ (moduleRootsOfUnity U n) 3) :=
    (moduleFiniteSupport_concentration.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv T hTfin hTclosed M hM).2 3 (by decide)
  exact moduleDualityMap_middle_isPerfPair_of_shortExact.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv hS hA hQ hCA hEQ r hr

end AlgebraicGeometry.Scheme.EtaleCohomology
