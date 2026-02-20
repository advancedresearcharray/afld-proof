/-
  Fermat Bridge — Formal Properties

  The Fermat bridge is the key mechanism in libdimfold that achieves
  lossless dimensional folding. It works by:

  1. Encoding real-valued data as elements of (Z/pZ)* for a prime p
  2. Permuting via exponentiation by a primitive root g
  3. The permutation is a bijection (group automorphism of (Z/pZ)*)
  4. The discrete log inverts it exactly

  The mathematical foundation is:
  - (Z/pZ)* is cyclic of order p-1 (for prime p)
  - Fermat's Little Theorem: a^(p-1) ≡ 1 mod p for a ≢ 0
  - A primitive root g generates all of (Z/pZ)*
  - The map a ↦ g^a is a bijection on {0,...,p-2}

  This file proves these properties using mathlib's ZMod infrastructure.

  Kilpatrick, AFLD formalization, 2026
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic

open Subgroup

namespace AFLD.FermatBridge

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Part 1: (Z/pZ)* is cyclic of order p-1

    This is the structural foundation: the multiplicative group of
    nonzero elements mod p is cyclic. Every element satisfies a^(p-1) = 1. -/

/-- (Z/pZ)* is cyclic for prime p -/
theorem units_cyclic : IsCyclic (ZMod p)ˣ :=
  ZMod.isCyclic_units_prime hp.out

/-- |(Z/pZ)*| = p - 1 -/
theorem units_card : Fintype.card (ZMod p)ˣ = p - 1 :=
  ZMod.card_units p

/-- Fermat's Little Theorem: a^(p-1) = 1 for all units a ∈ (Z/pZ)* -/
theorem fermat (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 :=
  ZMod.units_pow_card_sub_one_eq_one p a

/-- Fermat's Little Theorem (element form): a^(p-1) = 1 for nonzero a -/
theorem fermat' {a : ZMod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one ha

/-! ### Part 2: Primitive root and the permutation map

    A primitive root g generates all of (Z/pZ)*. The map k ↦ g^k
    gives a bijection on {0,...,p-2} → (Z/pZ)*. This is the Fermat
    bridge permutation used in libdimfold. -/

/-- A primitive root (generator) of (Z/pZ)* exists -/
theorem exists_generator : ∃ g : (ZMod p)ˣ, ∀ a : (ZMod p)ˣ, a ∈ zpowers g :=
  IsCyclic.exists_generator

/-- A generator has order p-1 -/
theorem generator_order (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) :
    orderOf g = p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, units_card]

/-! ### Part 3: Injectivity and bijectivity of the power map

    The power map k ↦ g^k is injective on {0,...,p-2} (follows from
    g having order p-1). Combined with a cardinality argument, this
    gives bijectivity. This is the mathematical core of why the Fermat
    bridge in libdimfold achieves lossless compression. -/

/-- The power map from a generator is injective on Fin(p-1) -/
theorem pow_injective (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) :
    Function.Injective (fun k : Fin (p - 1) => g ^ k.val) := by
  intro a b hab
  have hord := generator_order p g hg
  ext
  exact pow_injOn_Iio_orderOf
    (by rw [Set.mem_Iio, hord]; exact a.isLt)
    (by rw [Set.mem_Iio, hord]; exact b.isLt)
    hab

/-- The power map from a generator is bijective: Fin(p-1) ≃ (Z/pZ)*.
    This is the formal statement that the Fermat bridge permutation is
    invertible — encode (exponentiation) and decode (discrete log) are
    mutual inverses. -/
theorem pow_bijective (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) :
    Function.Bijective (fun k : Fin (p - 1) => g ^ k.val) := by
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨pow_injective p g hg, by
      simp [Nat.totient_prime hp.out]⟩

/-! ### Part 4: Round-trip identity

    The key property for lossless folding: for any unit a ∈ (Z/pZ)*,
    there exists a unique k such that g^k = a, and this k can be
    recovered (the discrete log). The round-trip encode → decode is
    the identity on {0,...,p-2}. -/

/-- For every unit, a unique exponent exists (discrete log) -/
theorem discrete_log_unique (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g)
    (a : (ZMod p)ˣ) : ∃! k : Fin (p - 1), g ^ k.val = a := by
  have hbij := pow_bijective p g hg
  exact ⟨hbij.surjective a |>.choose, hbij.surjective a |>.choose_spec,
    fun k hk => hbij.injective (hk.trans (hbij.surjective a |>.choose_spec).symm)⟩

/-- Round-trip: the Fermat bridge equiv.
    This packages the bijection as a proper equivalence, establishing
    that Fin(p-1) and (Z/pZ)* are in exact correspondence via the
    power map. In libdimfold, this means:
    - quantized value k → g^k mod p (encode)
    - g^k mod p → k via discrete log (decode)
    - decode(encode(k)) = k for all k ∈ {0,...,p-2}  -/
noncomputable def bridgeEquiv (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) :
    Fin (p - 1) ≃ (ZMod p)ˣ :=
  Equiv.ofBijective _ (pow_bijective p g hg)

/-- The bridge equivalence sends k to g^k -/
theorem bridgeEquiv_apply (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) (k : Fin (p - 1)) :
    bridgeEquiv p g hg k = g ^ k.val := rfl

/-- The inverse (discrete log) recovers the original exponent -/
theorem bridgeEquiv_symm_apply (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) (k : Fin (p - 1)) :
    (bridgeEquiv p g hg).symm (g ^ k.val) = k :=
  (bridgeEquiv p g hg).symm_apply_apply k

/-- The encode-decode round-trip is the identity -/
theorem bridge_roundtrip (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ zpowers g) (a : (ZMod p)ˣ) :
    g ^ ((bridgeEquiv p g hg).symm a).val = a :=
  (bridgeEquiv p g hg).apply_symm_apply a

end AFLD.FermatBridge
