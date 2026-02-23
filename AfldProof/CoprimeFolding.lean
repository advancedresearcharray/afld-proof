/-
  Bridge C: Coprimality Controls Dimensional Folding Quality

  When folding D*d items into a d × D grid, coprimality of D and d
  guarantees zero aliasing: the Chinese Remainder Theorem provides
  a bijective decomposition.  The number of "quality" (coprime) indices
  is exactly φ(D)·φ(d) = φ(D·d).

  This bridge connects:
    - Applied math / data science: dimensional folding / index aliasing
    - Number theory: coprimality, Euler's totient, CRT
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace NewBridge.CoprimeFolding

/-! ### Core: CRT gives alias-free folding

    When gcd(D,d) = 1, the ring isomorphism ZMod(D*d) ≃+* ZMod D × ZMod d
    means the folding map k ↦ (k mod D, k mod d) is a bijection.
    No two distinct source indices map to the same (target, source) pair. -/

theorem alias_free_folding (D d : ℕ) (hcop : Nat.Coprime D d) :
    ∃ _f : ZMod (D * d) ≃+* ZMod D × ZMod d, True :=
  ⟨ZMod.chineseRemainder hcop, trivial⟩

/-! ### The folding is invertible: given any target pair, there is a unique source -/

noncomputable def fold (D d : ℕ) (hcop : Nat.Coprime D d) :
    ZMod (D * d) ≃+* ZMod D × ZMod d :=
  ZMod.chineseRemainder hcop

noncomputable def unfold (D d : ℕ) (hcop : Nat.Coprime D d) :
    ZMod D × ZMod d ≃+* ZMod (D * d) :=
  (ZMod.chineseRemainder hcop).symm

theorem fold_unfold_id (D d : ℕ) (hcop : Nat.Coprime D d) (x : ZMod (D * d)) :
    (unfold D d hcop) ((fold D d hcop) x) = x :=
  (ZMod.chineseRemainder hcop).symm_apply_apply x

theorem unfold_fold_id (D d : ℕ) (hcop : Nat.Coprime D d)
    (p : ZMod D × ZMod d) :
    (fold D d hcop) ((unfold D d hcop) p) = p :=
  (ZMod.chineseRemainder hcop).apply_symm_apply p

/-! ### Full coverage: the folding hits every target pair exactly once -/

theorem full_coverage (D d : ℕ) (hcop : Nat.Coprime D d)
    (target : ZMod D × ZMod d) :
    ∃! x : ZMod (D * d), (fold D d hcop) x = target :=
  ⟨(unfold D d hcop) target,
   (ZMod.chineseRemainder hcop).apply_symm_apply target,
   fun y hy => by
     exact (ZMod.chineseRemainder hcop).injective
       (hy.trans ((ZMod.chineseRemainder hcop).apply_symm_apply target).symm)⟩

/-! ### Cardinality: the source space has exactly D*d elements -/

theorem source_card (D d : ℕ) [NeZero D] [NeZero d] [NeZero (D * d)] :
    Fintype.card (ZMod (D * d)) = D * d :=
  ZMod.card (D * d)

theorem target_card (D d : ℕ) [NeZero D] [NeZero d] :
    Fintype.card (ZMod D × ZMod d) = D * d := by
  rw [Fintype.card_prod, ZMod.card D, ZMod.card d]

/-! ### Quality indices: coprime residues decompose multiplicatively

    The "quality" indices are those coprime to the modulus.
    By totient multiplicativity, the count of quality indices
    in the folded space equals the product of quality indices
    in each dimension. -/

theorem quality_count_multiplicative (D d : ℕ) (hcop : Nat.Coprime D d) :
    Nat.totient (D * d) = Nat.totient D * Nat.totient d :=
  Nat.totient_mul hcop

/-! ### The bridge: zero aliasing ↔ coprimality

    Aliasing occurs when two distinct source indices map to the same target.
    The fold map is injective (zero aliasing) precisely because CRT
    provides a ring isomorphism when gcd(D,d) = 1. -/

theorem zero_aliasing_iff_injective (D d : ℕ) (hcop : Nat.Coprime D d) :
    Function.Injective (fold D d hcop) :=
  (ZMod.chineseRemainder hcop).injective

/-! ### Folding preserves additive structure (ring homomorphism)

    This is the key structural property: the folding doesn't just
    preserve set-level bijection, it preserves the arithmetic.
    Addition in the source space corresponds to componentwise
    addition in the target space. -/

theorem fold_add (D d : ℕ) (hcop : Nat.Coprime D d)
    (x y : ZMod (D * d)) :
    (fold D d hcop) (x + y) = (fold D d hcop) x + (fold D d hcop) y :=
  map_add (ZMod.chineseRemainder hcop) x y

theorem fold_mul (D d : ℕ) (hcop : Nat.Coprime D d)
    (x y : ZMod (D * d)) :
    (fold D d hcop) (x * y) = (fold D d hcop) x * (fold D d hcop) y :=
  map_mul (ZMod.chineseRemainder hcop) x y

/-! ### Composition: if we fold D₁·D₂·d with all pairwise coprime,
    we can fold in stages -/

theorem staged_folding (D₁ D₂ d : ℕ)
    (h₁₂ : Nat.Coprime D₁ D₂) (h₁d : Nat.Coprime D₁ d) (h₂d : Nat.Coprime D₂ d) :
    Nat.totient (D₁ * D₂ * d) = Nat.totient D₁ * Nat.totient D₂ * Nat.totient d := by
  rw [Nat.totient_mul (Nat.Coprime.mul_left h₁d h₂d)]
  rw [Nat.totient_mul h₁₂]

end NewBridge.CoprimeFolding
