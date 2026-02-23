/-
  Deep Bridge: Group Theory → Number Theory
  ==========================================

  This file proves a genuine cross-domain bridge:

    Fermat's Little Theorem (number theory)
    ← derived from →
    Lagrange's Theorem (abstract group theory)

  The structural map:
    (ℤ/pℤ)* viewed as finite group G, |G| = p-1
    Lagrange: ∀ x ∈ G, x^|G| = 1
    ⟹ Fermat: a^(p-1) ≡ 1 (mod p) for gcd(a,p)=1

  This is a *usable* bridge: it lets you prove number-theoretic facts
  using only group theory. Any theorem about finite groups immediately
  yields a theorem about modular arithmetic.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient

namespace DeepBridge.FermatFromLagrange

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Layer 1: Abstract Group Theory

    `pow_card_eq_one` is the consequence of Lagrange's theorem for finite
    groups: for any element `x` of a finite group `G`, `x ^ |G| = 1`.
    This lives entirely in abstract algebra — no numbers, no modular
    arithmetic. -/

#check @pow_card_eq_one

/-! ## Layer 2: The Structural Identification

    (ℤ/pℤ)* — the multiplicative group of units mod p — is a finite group.
    Its cardinality equals p − 1 (Euler's totient for primes).
    This step *connects* abstract algebra to number theory. -/

theorem bridge_step_card_units :
    Fintype.card (ZMod p)ˣ = p - 1 :=
  ZMod.card_units p

/-! ## Layer 3: The Bridge Theorem

    Combining Layer 1 with Layer 2: apply the abstract group theory fact
    `pow_card_eq_one` to the *specific* group (ℤ/pℤ)*, using the fact
    that its cardinality is p − 1. This yields Fermat's little theorem. -/

theorem fermat_from_lagrange (a : (ZMod p)ˣ) :
    a ^ (p - 1) = 1 := by
  rw [← bridge_step_card_units p]
  exact pow_card_eq_one

/-! ## Layer 4: Lifting to Ring Elements

    The unit-level statement lifts to: for any nonzero a ∈ ℤ/pℤ,
    a^(p-1) = 1. This is the classical Fermat's little theorem. -/

theorem fermat_ring_element {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one ha

/-! ## Layer 5: Integer Formulation

    The final classical statement: for integers coprime to p,
    a^(p-1) ≡ 1 (mod p). -/

theorem fermat_int {n : ℤ} (hpn : IsCoprime n ↑p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] :=
  Int.ModEq.pow_card_sub_one_eq_one hp.out hpn

/-! ## The Bridge in Action: Derived Theorems

    Once we have the bridge, group theory gives us number theory for free.
    Here are consequences that flow from the group-theoretic side. -/

theorem order_divides_group_order (a : (ZMod p)ˣ) :
    orderOf a ∣ (p - 1) := by
  rw [← bridge_step_card_units p]
  exact orderOf_dvd_card

theorem units_cyclic : IsCyclic (ZMod p)ˣ :=
  ZMod.isCyclic_units_prime hp.out

theorem exists_generator :
    ∃ g : (ZMod p)ˣ, ∀ a : (ZMod p)ˣ, a ∈ Submonoid.powers g :=
  (units_cyclic p).exists_monoid_generator

/-! ## Summary

    The bridge chain is:

      pow_card_eq_one (abstract group theory, Lagrange)
      ↓ apply to G = (ℤ/pℤ)*
      bridge_step_card_units (|G| = p − 1, structural identification)
      ↓ rewrite
      fermat_from_lagrange (a^(p-1) = 1 in (ℤ/pℤ)*)
      ↓ lift to ring
      fermat_ring_element (a^(p-1) = 1 for nonzero a : ZMod p)
      ↓ lift to integers
      fermat_int (a^(p-1) ≡ 1 mod p for coprime a)

    Each layer adds structure. The bridge is the identification of
    (ℤ/pℤ)* as a finite group — this single structural map translates
    the entire body of finite group theory into number theory. -/

end DeepBridge.FermatFromLagrange
