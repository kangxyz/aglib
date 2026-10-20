/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.Closed
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/



/-!
# Actual closed-point divisors and principal divisors

C1, K2-018 `lem:k2018-geometric-exact-order`, frozen basis `7f86e4a`.
The divisor group is the free abelian group on actual closed scheme points.
Orders are mathlib's local-ring length orders in the actual function field.
Finite support is proved from a nonempty open on which the rational function
is a unit and Noetherian finiteness of the codimension-one complement.
Regularity is needed for the DVR interpretation, not for this construction.
On an arbitrary-dimensional scheme this is only the closed-point restriction of
the codimension-one order divisor. It is the usual curve divisor when closed
points are exactly the codimension-one points; that identification is not assumed
for, or proved by, the general finite-support construction.
The local-to-global kernel theorem is proved by actual sheaf gluing. The
constant-kernel application is conditional on surjectivity of the actual global
constant map; the proper-global-functions theorem is supplied only in the
higher curve adapter.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Order Set

namespace AlgebraicGeometry.Scheme.OverField.Curve.Divisors
universe u

/-- The free abelian group of divisors on actual closed points. -/
abbrev Divisor (X : Scheme.{u}) := ClosedPoint X →₀ ℤ

/-- The actual free abelian divisor group is torsion-free. -/
theorem divisor_isAddTorsionFree (X : Scheme.{u}) : IsAddTorsionFree (Divisor X) :=
  inferInstance

variable (X : Scheme.{u}) [IsIntegral X] [hNoeth : IsNoetherian X]

/-- Integer local order on units of the actual function field. -/
def localOrder (x : ClosedPoint X) : Additive X.functionFieldˣ →+ ℤ where
  toFun f := X.ord (f.toMul : X.functionField) x.val
  map_zero' := by
    have h := Scheme.ord_mul (x := x.val) (f := (1 : X.functionField))
      (g := 1) one_ne_zero one_ne_zero
    simp only [one_mul] at h
    exact add_eq_left.mp h.symm
  map_add' f g := Scheme.ord_mul (Units.ne_zero _) (Units.ne_zero _)

/-- The codimension-one support of a nonzero rational function is finite. -/
theorem finite_order_support (f : X.functionFieldˣ) :
    (Function.support fun x : X => X.ord (f : X.functionField) x).Finite := by
  obtain ⟨U, _, s, hU, hs, hu⟩ := exists_isUnit_germ_eq X (f : X.functionField) f.ne_zero
  let : Nonempty U := hU
  have hc : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  let : QuasiSober ↥((U : Set X)ᶜ) := hc.isClosedEmbedding_subtypeVal.quasiSober
  have hp : closure ((U : Set X)ᶜ) ≠ Set.univ := by
    rw [hc.closure_eq]
    intro he
    have hm : hU.some.val ∈ (U : Set X)ᶜ := he ▸ Set.mem_univ _
    exact hm hU.some.property
  apply (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hp).subset
  intro x hx
  have hn : X.ord (f : X.functionField) x ≠ 0 := hx
  refine ⟨?_, ?_⟩
  · intro hxU
    exact hn (hs ▸ Scheme.ord_of_isUnit hu hxU)
  · by_contra h
    exact hn (Scheme.ord_eq_zero_of_coheight_neq_one h _)

/-- Finite support after restriction to the actual closed points. -/
theorem finite_closedPoint_order_support (f : X.functionFieldˣ) :
    (Function.support fun x : ClosedPoint X => X.ord (f : X.functionField) x.val).Finite :=
  (finite_order_support X f).preimage_embedding ⟨Subtype.val, Subtype.val_injective⟩

/-- The actual principal divisor homomorphism. -/
def principal : Additive X.functionFieldˣ →+ Divisor X where
  toFun f := Finsupp.ofSupportFinite (fun x => localOrder X x f)
    (finite_closedPoint_order_support X f.toMul)
  map_zero' := by ext x; exact (localOrder X x).map_zero
  map_add' f g := by ext x; exact (localOrder X x).map_add f g

@[simp] theorem principal_apply (f : Additive X.functionFieldˣ) (x : ClosedPoint X) :
    principal X f x = X.ord (f.toMul : X.functionField) x.val := rfl

theorem principal_mul (f g : X.functionFieldˣ) :
    principal X (Additive.ofMul (f * g)) =
      principal X (Additive.ofMul f) + principal X (Additive.ofMul g) :=
  (principal X).map_add _ _

theorem principal_pow (f : X.functionFieldˣ) (n : ℕ) :
    principal X (Additive.ofMul (f ^ n)) = n • principal X (Additive.ofMul f) :=
  (principal X).map_nsmul _ _

/-- On a DVR stalk the convention assigns a uniformizer order `+1`. -/
theorem order_uniformizer (x : ClosedPoint X) (hx : Order.coheight x.val = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (t : X.presheaf.stalk x.val) (ht : Irreducible t) :
    X.ord (algebraMap (X.presheaf.stalk x.val) X.functionField t) x.val = 1 := by
  have hn : algebraMap (X.presheaf.stalk x.val) X.functionField t ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (X.presheaf.stalk x.val)
      X.functionField).ne ht.ne_zero
  rw [Scheme.ord_eq_iff hx hn]
  exact Ring.ordFrac_irreducible ht



omit hNoeth in
attribute [local instance] specializationOrder in
-- Retain noetherianity in the divisor-curve interface used for finite principal support; this
-- dimension-one dichotomy itself is order-theoretic.
/-- On an integral scheme of dimension at most one, every point is generic or closed. -/
@[nolint unusedArguments]
theorem point_eq_generic_or_isClosed [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    x = genericPoint X ∨ IsClosed ({x} : Set X) := by
  have hd : krullDim X ≤ 1 := by
    rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  rcases krullDim_le_one_iff.mp hd x with hx | hx
  · right
    rw [← closure_eq_iff_isClosed]
    apply Set.Subset.antisymm
    · intro y hy
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have he : x = y := le_antisymm (hx hxy) hxy
      exact he ▸ Set.mem_singleton x
    · exact subset_closure
  · left
    exact le_antisymm (genericPoint_specializes x) (hx (genericPoint_specializes x))

omit hNoeth in
-- Retain noetherianity in the divisor-curve codimension interface; the codimension calculation
-- itself uses the actual DVR stalk dimension.
/-- An actual DVR stalk has codimension one, by the stalk/coheight theorem. -/
@[nolint unusedArguments]
theorem coheight_eq_one_of_dvr [IsNoetherian X] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
  Order.coheight x = 1 := by
  have h : (Order.coheight x : WithBot ℕ∞) = 1 := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  exact WithBot.coe_injective h

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

omit hNoeth in
-- Retain noetherianity in the divisor-curve section-extension interface; this gluing argument
-- only uses integrality and the specified stalk representatives.
/-- A rational function lying in every actual stalk ring extends globally.
The proof constructs local sections, proves compatibility by fraction-field
injectivity, and applies the structure sheaf gluing theorem. -/
@[nolint unusedArguments]
theorem exists_globalSection_of_mem_stalk [IsNoetherian X] (f : X.functionField)
    (hf : ∀ x : X, ∃ r : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField r = f) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = f := by
  choose r hr using hf
  choose U hx s hs using fun x => X.presheaf.exists_germ_eq (r x)
  let (x : X) : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  have he (x : X) : X.germToFunctionField (U x) (s x) = f := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (hx x), hs x, hr x]
  have hc : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro x y
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    change X.presheaf.germ (U x ⊓ U y) z hz
      (X.presheaf.map ((U x).infLELeft (U y)).op (s x)) =
      X.presheaf.germ (U x ⊓ U y) z hz
      (X.presheaf.map ((U x).infLERight (U y)).op (s y))
    apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    rw [Scheme.algebraMap_germ_eq_germToFunctionField X hz.1,
      Scheme.algebraMap_germ_eq_germToFunctionField X hz.2, he, he]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover s hc
  refine ⟨g, ?_⟩
  have := he (genericPoint X)
  rw [← hg] at this
  change X.presheaf.germ (U (genericPoint X)) (genericPoint X) _
    (X.presheaf.map (homOfLE le_top).op g) = f at this
  rw [X.presheaf.germ_res_apply] at this
  exact this


/-- A rational unit represented by units at every stalk extends to a global unit. -/
theorem exists_globalUnit_of_mem_stalk_units (f : X.functionFieldˣ)
    (hf : ∀ x : X, ∃ r : X.presheaf.stalk x, IsUnit r ∧
      algebraMap (X.presheaf.stalk x) X.functionField r = f) :
    ∃ s : Γ(X, ⊤)ˣ,
      Units.map (X.germToFunctionField ⊤).hom.toMonoidHom s = f := by
  obtain ⟨s, hs⟩ := exists_globalSection_of_mem_stalk X (f : X.functionField)
    (fun x => let ⟨r, _, hr⟩ := hf x; ⟨r, hr⟩)
  have hu : IsUnit s := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨r, hr, he⟩ := hf x
    have hg : X.presheaf.germ ⊤ x hx s = r := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      rw [Scheme.algebraMap_germ_eq_germToFunctionField X hx, hs, he]
    exact hg ▸ hr
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  apply Units.ext
  change X.germToFunctionField ⊤ (u : Γ(X, ⊤)) = (f : X.functionField)
  rw [hu, hs]



/-- Zero local order is exactly membership in the units of the actual DVR stalk. -/
theorem order_zero_iff_stalk_unit (x : X) (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (f : X.functionFieldˣ) :
    X.ord (f : X.functionField) x = 0 ↔
      ∃ r : X.presheaf.stalk x, IsUnit r ∧
        algebraMap (X.presheaf.stalk x) X.functionField r = f := by
  rw [Scheme.ord_eq_iff hx f.ne_zero]
  change Ring.ordFrac (X.presheaf.stalk x) (f : X.functionField) = 1 ↔ _
  change (f : X.functionField) ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk x)) ↔ _
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid]
  rfl




/-- Zero principal divisor is equivalent to extension as a global unit. -/
theorem principal_eq_zero_iff_globalUnit
    (hpoints : ∀ x : X, x = genericPoint X ∨ IsClosed ({x} : Set X))
    (hcodim : ∀ x : ClosedPoint X, Order.coheight x.val = 1)
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (f : X.functionFieldˣ) :
    principal X (Additive.ofMul f) = 0 ↔
    ∃ s : Γ(X, ⊤)ˣ, Units.map (X.germToFunctionField ⊤).hom.toMonoidHom s = f := by
  constructor
  · intro hf
    apply exists_globalUnit_of_mem_stalk_units X f
    intro x
    rcases hpoints x with rfl | hx
    · refine ⟨(f : X.functionField), f.isUnit, ?_⟩
      simp [RingHom.algebraMap_toAlgebra]
    · let y : ClosedPoint X := ⟨x, hx⟩
      let : IsDiscreteValuationRing (X.presheaf.stalk x) :=
        inferInstanceAs (IsDiscreteValuationRing (X.presheaf.stalk y.val))
      have hz : X.ord (f : X.functionField) x = 0 :=
        congrArg (fun D : Divisor X => D y) hf
      exact (order_zero_iff_stalk_unit X x (hcodim y) f).mp hz
  · rintro ⟨s, rfl⟩
    ext x
    exact Scheme.ord_of_isUnit s.isUnit (show x.val ∈ (⊤ : X.Opens) from trivial)


variable {k : Type u} [Field k]

/-- Apply an actual global-functions surjectivity theorem to the proved divisor kernel. -/
theorem kernel_eq_constants_from_global_functions
    (p : X ⟶ Spec (.of k))
    (hconstants : Function.Surjective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
    (hpoints : ∀ x : X, x = genericPoint X ∨ IsClosed ({x} : Set X))
    (hcodim : ∀ x : ClosedPoint X, Order.coheight x.val = 1)
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (f : X.functionFieldˣ) :
    principal X (Additive.ofMul f) = 0 ↔
    ∃ a : kˣ, Units.map (Scheme.functionFieldConstants X p).toMonoidHom a = f := by
  rw [principal_eq_zero_iff_globalUnit X hpoints hcodim]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha⟩ := hconstants (s : Γ(X, ⊤))
    have hn : a ≠ 0 := by
      intro h
      subst a
      have hz : (s : Γ(X, ⊤)) = 0 := by simpa using ha.symm
      exact s.ne_zero hz
    refine ⟨Units.mk0 a hn, ?_⟩
    apply Units.ext
    change Scheme.functionFieldConstants X p a = (f : X.functionField)
    change X.germToFunctionField ⊤
      ((((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom) a) = _
    rw [ha]
    exact congrArg (fun v : X.functionFieldˣ => (v : X.functionField)) hs
  · rintro ⟨a, rfl⟩
    refine ⟨Units.map (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toMonoidHom) a, ?_⟩
    rfl

end AlgebraicGeometry.Scheme.OverField.Curve.Divisors
