/-
  PseudoSquares.lean -- PrimeAtlas pt1: deterministic primality of the partial sieve's survivors
  by the pseudosquares test (engine_pt_pss.h, pss_prove), instead of BPSW.

  lpw_sorenson  -- Lukes-Patterson-Williams with Sorenson's sieve bound (Sorenson 2006, Lemma 3.1):
                   n odd, prime factors > s, n < L*s, conditions (3)-(4) => n is a prime power.
  prime_of_pss  -- with s >= n^(1/4) (pt1's B = isqrt(isqrt(top))): not a square, not a cube
                   => n is prime.
  pss_complete  -- a prime passes: the test never rejects a prime.
  pssProve_sound, pssProve_complete -- the same for the C routine pss_prove as written (bases and
                   L_p from engine_pt_pss.h, the tail past n_bases, return values 1 / 0 / -1).
  table_*       -- the C table checked by decide: bases are the 74 primes up to 373 in order,
                   L_p non-decreasing, every L_p a pseudosquare except three typos (p = 229,
                   353, 359), each below the corrected value, so the table errs on the safe side.
  Assumption, explicit as hypothesis hL: L bounds the pseudosquares L_p from below (the published
  table, OEIS A002189); Lean does not recompute the table.
  Proof with orders in ZMod r, Euler's criterion and quadratic reciprocity (Mathlib), and a 2-adic
  argument: two prime factors with v2(r-1) = v2(n-1) force v2(n-1) larger, unless a third factor
  exists, which bounds r*d below L.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.IntervalCases

namespace PseudoSquares

/-! ### 2-adic bookkeeping -/

lemma odd_coprime_two_pow {t : ℕ} (ht : Odd t) (e : ℕ) : Nat.Coprime t (2 ^ e) :=
  Nat.Coprime.pow_right e (Nat.coprime_two_right.2 ht)

/-- If `d ∣ 2^e m` (`m` odd) and `2^e ∤ d`, then `d ∣ 2^(e-1) m`. -/
lemma dvd_half {d e m : ℕ} (he : 1 ≤ e) (hm : Odd m) (hd : d ∣ 2 ^ e * m)
    (hn : ¬ 2 ^ e ∣ d) : d ∣ 2 ^ (e - 1) * m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hd0 : d ≠ 0 := by
    rintro rfl; rw [zero_dvd_iff] at hd; simp [hm0] at hd
  obtain ⟨a, d', hd', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd0
  have h1 : d' ∣ 2 ^ e * m := dvd_trans (Dvd.intro_left _ rfl) hd
  have h2 : d' ∣ m := (odd_coprime_two_pow hd' e).dvd_of_dvd_mul_left h1
  have ha : a < e := by
    by_contra h
    exact hn (dvd_trans (pow_dvd_pow 2 (by omega)) (Dvd.intro _ rfl))
  exact mul_dvd_mul (pow_dvd_pow 2 (by omega)) h2

lemma le_of_two_pow_dvd {e f t : ℕ} (ht : Odd t) (h : 2 ^ e ∣ 2 ^ f * t) : e ≤ f := by
  have : 2 ^ e ∣ 2 ^ f :=
    (Nat.Coprime.symm (odd_coprime_two_pow ht e)).dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this

/-! ### Orders in `ZMod r` -/

section orders
variable {r : ℕ} [hr : Fact r.Prime]

lemma one_ne_neg_one (hr2 : r ≠ 2) : (1 : ZMod r) ≠ -1 := by
  have : Fact (2 < r) := ⟨lt_of_le_of_ne hr.out.two_le (Ne.symm hr2)⟩
  exact fun h => ZMod.neg_one_ne_one h.symm

lemma ord_dvd_sub_one {q : ZMod r} (hq : q ≠ 0) : orderOf q ∣ r - 1 :=
  orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hq)

lemma two_pow_split {e m : ℕ} (he : 1 ≤ e) : 2 ^ e * m = 2 ^ (e - 1) * m * 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

/-- A base with `b^((n-1)/2) = -1 (mod r)` forces `v₂(r - 1) ≥ v₂(n - 1)`. -/
lemma claim1 (hr2 : r ≠ 2) {b : ZMod r} {e m f t : ℕ} (he : 1 ≤ e) (hm : Odd m) (ht : Odd t)
    (hr1 : r - 1 = 2 ^ f * t) (hb : b ^ (2 ^ (e - 1) * m) = -1) : e ≤ f := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hpos : 2 ^ (e - 1) * m ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; simp at hm
      positivity
    rw [zero_pow hpos] at hb
    exact one_ne_zero (neg_eq_zero.1 hb.symm)
  have hsq : b ^ (2 ^ e * m) = 1 := by rw [two_pow_split he, pow_mul, hb]; norm_num
  have ho : orderOf b ∣ 2 ^ e * m := orderOf_dvd_of_pow_eq_one hsq
  have hno : ¬ orderOf b ∣ 2 ^ (e - 1) * m := by
    intro h
    have := (orderOf_dvd_iff_pow_eq_one.1 h)
    rw [hb] at this
    exact one_ne_neg_one hr2 this.symm
  have h2e : 2 ^ e ∣ orderOf b := by
    by_contra hc; exact hno (dvd_half he hm ho hc)
  have hor : orderOf b ∣ 2 ^ f * t := hr1 ▸ ord_dvd_sub_one hb0
  exact le_of_two_pow_dvd ht (dvd_trans h2e hor)

/-- The quadratic character of `q` modulo a prime factor `r` of `n`:
`q^((r-1)/2) = -1` exactly when `q^((n-1)/2) = -1` and `v₂(r - 1) = v₂(n - 1)`. -/
lemma claim2 (hr2 : r ≠ 2) {q : ZMod r} {e m f t : ℕ} (hq0 : q ≠ 0) (he : 1 ≤ e) (hm : Odd m)
    (ht : Odd t) (hf : 1 ≤ f) (hr1 : r - 1 = 2 ^ f * t) (hef : e ≤ f)
    (hε : q ^ (2 ^ (e - 1) * m) = 1 ∨ q ^ (2 ^ (e - 1) * m) = -1) :
    q ^ (2 ^ (f - 1) * t) = -1 ↔ (q ^ (2 ^ (e - 1) * m) = -1 ∧ f = e) := by
  have hon : orderOf q ∣ 2 ^ e * m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [two_pow_split he, pow_mul]
    rcases hε with h | h <;> rw [h] <;> norm_num
  have hor : orderOf q ∣ 2 ^ f * t := hr1 ▸ ord_dvd_sub_one hq0
  have key : q ^ (2 ^ (f - 1) * t) = -1 ↔ 2 ^ f ∣ orderOf q := by
    constructor
    · intro h
      by_contra hc
      have := orderOf_dvd_iff_pow_eq_one.1 (dvd_half hf ht hor hc)
      rw [h] at this
      exact one_ne_neg_one hr2 this.symm
    · intro h2
      have hsq : q ^ (2 ^ (f - 1) * t) * q ^ (2 ^ (f - 1) * t) = 1 := by
        rw [← pow_add, ← two_mul, ← mul_assoc, ← pow_succ']
        rw [show f - 1 + 1 = f by omega, ← hr1]
        exact ZMod.pow_card_sub_one_eq_one hq0
      rcases mul_self_eq_one_iff.1 hsq with h1 | h1
      · exfalso
        have hd := dvd_trans h2 (orderOf_dvd_iff_pow_eq_one.2 h1)
        have := le_of_two_pow_dvd ht hd
        omega
      · exact h1
  rw [key]
  rcases hε with h | h
  · have hd : orderOf q ∣ 2 ^ (e - 1) * m := orderOf_dvd_iff_pow_eq_one.2 h
    constructor
    · intro h2
      have := le_of_two_pow_dvd hm (dvd_trans h2 hd)
      omega
    · rintro ⟨h', -⟩
      rw [h] at h'
      exact absurd h' (one_ne_neg_one hr2)
  · have h2e : 2 ^ e ∣ orderOf q := by
      by_contra hc
      have := orderOf_dvd_iff_pow_eq_one.1 (dvd_half he hm hon hc)
      rw [h] at this
      exact one_ne_neg_one hr2 this.symm
    constructor
    · intro h2
      exact ⟨h, le_antisymm (le_of_two_pow_dvd hm (dvd_trans h2 hon)) hef⟩
    · rintro ⟨-, hfe⟩
      rw [hfe]; exact h2e

end orders

/-! ### The character at a prime factor of `n` -/

lemma cast_mod_of_dvd {x n r : ℕ} (hrn : r ∣ n) : ((x % n : ℕ) : ZMod r) = (x : ZMod r) := by
  rw [ZMod.natCast_eq_natCast_iff']; exact Nat.mod_mod_of_dvd x hrn

lemma cast_n_sub_one {n r : ℕ} (hrn : r ∣ n) (hn : 1 ≤ n) : ((n - 1 : ℕ) : ZMod r) = -1 := by
  rw [Nat.cast_sub hn, (ZMod.natCast_eq_zero_iff n r).2 hrn]; simp

lemma half_of {x f t : ℕ} (hf : 1 ≤ f) (hx1 : 1 ≤ x) (hxt : x - 1 = 2 ^ f * t) :
    x / 2 = 2 ^ (f - 1) * t := by
  have h := two_pow_split (m := t) hf
  rw [h] at hxt
  omega

/-- For a prime factor `x` of `n` (with `x - 1 = 2^f t`), every base `q ≤ p` is a unit mod `x`,
`f ≥ e = v₂(n - 1)`, and `(q | x) = -1` exactly when `q^((n-1)/2) ≡ -1 (mod n)` and `f = e`. -/
theorem factor_char {n p e m x f t : ℕ} [hx : Fact x.Prime] (hn : 3 ≤ n) (hxn : x ∣ n) (hx2 : x ≠ 2)
    (he : 1 ≤ e) (hm : Odd m) (hexp : (n - 1) / 2 = 2 ^ (e - 1) * m)
    (ht : Odd t) (hf : 1 ≤ f) (hxt : x - 1 = 2 ^ f * t)
    (h3 : ∀ q, q.Prime → q ≤ p → q ^ ((n - 1) / 2) % n = 1 ∨ q ^ ((n - 1) / 2) % n = n - 1)
    (hbase : e = 1 ∨ ∃ b, b.Prime ∧ b ≤ p ∧ b ^ ((n - 1) / 2) % n = n - 1) :
    e ≤ f ∧ ∀ q, q.Prime → q ≤ p → q ≠ x ∧
      (legendreSym x q = -1 ↔ (q ^ ((n - 1) / 2) % n = n - 1 ∧ f = e)) := by
  have hn1 : 1 ≤ n := by omega
  have hx2' : x / 2 = 2 ^ (f - 1) * t := half_of hf hx.out.one_lt.le hxt
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hpos : 2 ^ (e - 1) * m ≠ 0 := by positivity
  have h1ne : (1 : ZMod x) ≠ -1 := one_ne_neg_one hx2
  have hεq : ∀ q, q.Prime → q ≤ p →
      ((q : ZMod x) ^ (2 ^ (e - 1) * m) = 1 ∨ (q : ZMod x) ^ (2 ^ (e - 1) * m) = -1) ∧
      ((q : ZMod x) ^ (2 ^ (e - 1) * m) = -1 ↔ q ^ ((n - 1) / 2) % n = n - 1) := by
    intro q hq hqp
    have hc : ((q ^ ((n - 1) / 2) % n : ℕ) : ZMod x) = (q : ZMod x) ^ (2 ^ (e - 1) * m) := by
      rw [cast_mod_of_dvd hxn, Nat.cast_pow, hexp]
    rcases h3 q hq hqp with h | h
    · rw [h, Nat.cast_one] at hc
      refine ⟨Or.inl hc.symm, fun h' => ?_, fun h' => ?_⟩
      · rw [← hc] at h'; exact absurd h' h1ne
      · exfalso; rw [h] at h'; omega
    · rw [h, cast_n_sub_one hxn hn1] at hc
      exact ⟨Or.inr hc.symm, fun _ => h, fun _ => hc.symm⟩
  have hq0 : ∀ q, q.Prime → q ≤ p → (q : ZMod x) ≠ 0 := by
    intro q hq hqp h0
    rcases (hεq q hq hqp).1 with h | h <;> rw [h0, zero_pow hpos] at h
    · exact zero_ne_one h
    · exact one_ne_zero (neg_eq_zero.1 h.symm)
  have hef : e ≤ f := by
    rcases hbase with h | ⟨b, hb, hbp, hbn⟩
    · omega
    · exact claim1 hx2 he hm ht hxt (((hεq b hb hbp).2).2 hbn)
  refine ⟨hef, fun q hq hqp => ⟨?_, ?_⟩⟩
  · rintro rfl; exact hq0 q hq hqp (ZMod.natCast_self q)
  · have hleg : legendreSym x q = -1 ↔ (q : ZMod x) ^ (2 ^ (f - 1) * t) = -1 := by
      have heq := legendreSym.eq_pow x (q : ℤ)
      rw [Int.cast_natCast, hx2'] at heq
      have hq0' : ((q : ℤ) : ZMod x) ≠ 0 := by rw [Int.cast_natCast]; exact hq0 q hq hqp
      rcases legendreSym.eq_one_or_neg_one x hq0' with h | h
      · rw [h, Int.cast_one] at heq
        rw [h, ← heq]
        exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' h1ne⟩
      · rw [h, Int.cast_neg, Int.cast_one] at heq
        rw [h, ← heq]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
    rw [hleg, claim2 hx2 (hq0 q hq hqp) he hm ht hf hxt hef (hεq q hq hqp).1, (hεq q hq hqp).2]

/-! ### The two cases of the proof -/

lemma pow_split4 {f : ℕ} (hf : 2 ≤ f) (t : ℕ) : 2 ^ f * t = 4 * (2 ^ (f - 2) * t) := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
  simp only [Nat.add_sub_cancel, pow_add]; ring

lemma prime_not_square {x : ℕ} (hx : x.Prime) : ¬ IsSquare x := by
  rintro ⟨k, rfl⟩
  rcases Nat.prime_mul_iff.1 hx with ⟨hk, h1⟩ | ⟨hk, h1⟩ <;> (subst h1; exact Nat.not_prime_one hk)

lemma two_primes_not_square {r d : ℕ} (hr : r.Prime) (hd : d.Prime) (hrd : r ≠ d) :
    ¬ IsSquare (r * d) := by
  rintro ⟨k, hk⟩
  have hrk : r ∣ k := by
    rcases (Nat.Prime.dvd_mul hr).1 (hk ▸ dvd_mul_right r d : r ∣ k * k) with h | h <;> exact h
  obtain ⟨j, rfl⟩ := hrk
  have : d = j * (r * j) := by
    have h := hk
    rw [show r * j * (r * j) = r * (j * (r * j)) by ring] at h
    exact Nat.eq_of_mul_eq_mul_left hr.pos h
  have hrd' : r ∣ d := ⟨j * j, by rw [this]; ring⟩
  rcases (Nat.Prime.eq_one_or_self_of_dvd hd r hrd') with h | h
  · exact hr.one_lt.ne' h
  · exact hrd h

lemma cast_ne_zero_of_prime {x q : ℕ} (hx : x.Prime) (hq : q.Prime) (hqx : q ≠ x) :
    ((q : ℤ) : ZMod x) ≠ 0 := by
  rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  rcases Nat.Prime.eq_one_or_self_of_dvd hq x h with h1 | h1
  · exact hx.one_lt.ne' h1
  · exact hqx h1.symm

lemma lt_of_cofactor {n s L x c : ℕ} (hn : n = x * c) (hc : s < c) (hnL : n < L * s) : x < L := by
  by_contra h
  have h1 : L * s ≤ x * c := Nat.mul_le_mul (Nat.le_of_not_lt h) hc.le
  omega

lemma s_lt_cofactor {n s c : ℕ} (hs : ∀ r, r.Prime → r ∣ n → s < r) (hcn : c ∣ n) (hc1 : c ≠ 1)
    (hc0 : c ≠ 0) : s < c :=
  lt_of_lt_of_le (hs _ (Nat.minFac_prime hc1) (dvd_trans (Nat.minFac_dvd c) hcn))
    (Nat.minFac_le (Nat.pos_of_ne_zero hc0))

/-- Case A: a prime factor `x` with `v₂(x - 1) > v₂(n - 1)` is a quadratic residue of every odd
prime `q ≤ p` and `≡ 1 (mod 8)`, yet `x < L`: impossible. -/
theorem caseA {n s p L e x f t c : ℕ} {P : ℕ → Prop} [hx : Fact x.Prime] (hxn : n = x * c)
    (hc2 : 2 ≤ c) (hx2 : x ≠ 2) (hs : ∀ r, r.Prime → r ∣ n → s < r) (hnL : n < L * s)
    (hL : ∀ N, N < L → N % 8 = 1 →
      (∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ N ∧ IsSquare (N : ZMod q)) → IsSquare N)
    (h2p : 2 ≤ p) (hxt : x - 1 = 2 ^ f * t) (hfe : e < f) (he : 1 ≤ e)
    (hchar : ∀ q, q.Prime → q ≤ p → q ≠ x ∧ (legendreSym x q = -1 ↔ (P q ∧ f = e))) : False := by
  have hleg1 : ∀ q, q.Prime → q ≤ p → legendreSym x q = 1 := by
    intro q hq hqp
    rcases legendreSym.eq_one_or_neg_one x (cast_ne_zero_of_prime hx.out hq (hchar q hq hqp).1)
      with h | h
    · exact h
    · exact absurd ((hchar q hq hqp).2.1 h).2 (by omega)
  have hx1 : 1 ≤ x := hx.out.one_lt.le
  have hx4 : x % 4 = 1 := by
    rw [pow_split4 (by omega) t] at hxt
    omega
  have hx8 : x % 8 = 1 := by
    have h2 := hleg1 2 Nat.prime_two h2p
    rw [legendreSym.eq_one_iff x (cast_ne_zero_of_prime hx.out Nat.prime_two (Ne.symm hx2))] at h2
    have : IsSquare (2 : ZMod x) := by simpa using h2
    rcases (ZMod.exists_sq_eq_two_iff hx2).1 this with h | h <;> omega
  have hq : ∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ x ∧ IsSquare (x : ZMod q) := by
    intro q hq hq3 hqp
    have hqx := (hchar q hq hqp).1
    refine ⟨fun h => ?_, ?_⟩
    · rcases Nat.Prime.eq_one_or_self_of_dvd hx.out q h with h1 | h1
      · omega
      · exact hqx h1
    · have := Fact.mk hq
      have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := x) (q := q) hx4
        (by omega)
      rw [hleg1 q hq hqp] at hrec
      have hne : ((x : ℤ) : ZMod q) ≠ 0 := cast_ne_zero_of_prime hq hx.out (Ne.symm hqx)
      have := (legendreSym.eq_one_iff q hne).1 hrec
      simpa using this
  have hsc : s < c := s_lt_cofactor hs ⟨x, by rw [hxn]; ring⟩ (by omega) (by omega)
  exact prime_not_square hx.out (hL x (lt_of_cofactor hxn hsc hnL) hx8 hq)

/-- Case B: two different prime factors `r, d` with `v₂(r - 1) = v₂(d - 1) = v₂(n - 1)` have the
same quadratic character, so `r d` is a non-square pseudosquare candidate below `L`. -/
theorem caseB {n s p L e m r d t1 t2 c : ℕ} {P : ℕ → Prop} [hr : Fact r.Prime]
    [hd : Fact d.Prime] (hrd : r ≠ d) (hr2 : r ≠ 2) (hd2 : d ≠ 2) (hn : n = r * d * c)
    (hc0 : c ≠ 0) (he : 1 ≤ e) (hm : Odd m) (hnm : n - 1 = 2 ^ e * m)
    (hrt : r - 1 = 2 ^ e * t1) (hdt : d - 1 = 2 ^ e * t2) (ht1 : Odd t1) (ht2 : Odd t2)
    (hs : ∀ r, r.Prime → r ∣ n → s < r) (hnL : n < L * s)
    (hL : ∀ N, N < L → N % 8 = 1 →
      (∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ N ∧ IsSquare (N : ZMod q)) → IsSquare N)
    (h2p : 2 ≤ p)
    (hcr : ∀ q, q.Prime → q ≤ p → q ≠ r ∧ (legendreSym r q = -1 ↔ P q))
    (hcd : ∀ q, q.Prime → q ≤ p → q ≠ d ∧ (legendreSym d q = -1 ↔ P q)) : False := by
  have hr1 : 1 ≤ r := hr.out.one_lt.le
  have hd1 : 1 ≤ d := hd.out.one_lt.le
  have hsame : ∀ q, q.Prime → q ≤ p → legendreSym r q = legendreSym d q := by
    intro q hq hqp
    rcases legendreSym.eq_one_or_neg_one r (cast_ne_zero_of_prime hr.out hq (hcr q hq hqp).1)
      with h1 | h1 <;>
    rcases legendreSym.eq_one_or_neg_one d (cast_ne_zero_of_prime hd.out hq (hcd q hq hqp).1)
      with h2 | h2
    · rw [h1, h2]
    · exact absurd ((hcr q hq hqp).2.2 ((hcd q hq hqp).2.1 h2)) (by rw [h1]; norm_num)
    · exact absurd ((hcd q hq hqp).2.2 ((hcr q hq hqp).2.1 h1)) (by rw [h2]; norm_num)
    · rw [h1, h2]
  -- the cofactor is not 1: otherwise v₂(n - 1) > e
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hR : r = 2 ^ e * t1 + 1 := by omega
    have hD : d = 2 ^ e * t2 + 1 := by omega
    have key : 2 ^ e * m = 2 ^ e * (2 ^ e * t1 * t2 + t1 + t2) := by
      rw [← hnm, hn, hR, hD]
      have : (2 ^ e * t1 + 1) * (2 ^ e * t2 + 1) * 1 =
          2 ^ e * (2 ^ e * t1 * t2 + t1 + t2) + 1 := by ring
      rw [this]; omega
    have hm' := Nat.eq_of_mul_eq_mul_left (by positivity) key
    have hev : Even (2 ^ e * t1 * t2 + t1 + t2) := by
      have h2e : Even (2 ^ e) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      rw [add_assoc]
      exact Even.add ((h2e.mul_right t1).mul_right t2) (Odd.add_odd ht1 ht2)
    rw [← hm'] at hev
    exact (Nat.not_even_iff_odd.2 hm) hev
  have hsc : s < c := s_lt_cofactor hs ⟨r * d, by rw [hn]; ring⟩ hc1 hc0
  have hNL : r * d < L := lt_of_cofactor hn hsc hnL
  have hodd1 : t1 % 2 = 1 := Nat.odd_iff.1 ht1
  have hodd2 : t2 % 2 = 1 := Nat.odd_iff.1 ht2
  have hr4 : r % 4 = d % 4 := by
    rcases Nat.lt_or_ge e 2 with h | h
    · have : e = 1 := by omega
      subst this; simp only [pow_one] at hrt hdt; omega
    · rw [pow_split4 h t1] at hrt
      rw [pow_split4 h t2] at hdt
      omega
  have h2r : (2 : ZMod r) = ((2 : ℤ) : ZMod r) := by norm_num
  have hsq2 : IsSquare (2 : ZMod r) ↔ IsSquare (2 : ZMod d) := by
    have e1 := legendreSym.eq_one_iff r (cast_ne_zero_of_prime hr.out Nat.prime_two (Ne.symm hr2))
    have e2 := legendreSym.eq_one_iff d (cast_ne_zero_of_prime hd.out Nat.prime_two (Ne.symm hd2))
    have hs2 := hsame 2 Nat.prime_two h2p
    push_cast at e1 e2 hs2
    rw [← e1, ← e2, hs2]
  have hr8 : r % 8 = d % 8 := by
    have a := ZMod.exists_sq_eq_two_iff (p := r) hr2
    have b := ZMod.exists_sq_eq_two_iff (p := d) hd2
    have hro : r % 2 = 1 := (hr.out.eq_one_or_self_of_dvd 2 |> fun _ => by
      rcases Nat.Prime.eq_two_or_odd hr.out with h | h; exact absurd h hr2; exact h)
    have hdo : d % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hd.out with h | h; exact absurd h hd2; exact h
    by_cases h : IsSquare (2 : ZMod r)
    · have h' := hsq2.1 h; have x1 := a.1 h; have x2 := b.1 h'; omega
    · have h' : ¬ IsSquare (2 : ZMod d) := fun h'' => h (hsq2.2 h'')
      have x1 : ¬ (r % 8 = 1 ∨ r % 8 = 7) := fun h'' => h (a.2 h'')
      have x2 : ¬ (d % 8 = 1 ∨ d % 8 = 7) := fun h'' => h' (b.2 h'')
      omega
  have hN8 : r * d % 8 = 1 := by
    have hro : r % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hr.out with h | h; exact absurd h hr2; exact h
    rw [Nat.mul_mod, ← hr8]
    have : r % 8 = 1 ∨ r % 8 = 3 ∨ r % 8 = 5 ∨ r % 8 = 7 := by omega
    rcases this with h | h | h | h <;> rw [h]
  have hq : ∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ r * d ∧ IsSquare ((r * d : ℕ) : ZMod q) := by
    intro q hq hq3 hqp
    have hqr := (hcr q hq hqp).1
    have hqd := (hcd q hq hqp).1
    have hndvd : ¬ q ∣ r * d := by
      intro h
      rcases (Nat.Prime.dvd_mul hq).1 h with h' | h'
      · rcases Nat.Prime.eq_one_or_self_of_dvd hr.out q h' with h1 | h1 <;> omega
      · rcases Nat.Prime.eq_one_or_self_of_dvd hd.out q h' with h1 | h1 <;> omega
    refine ⟨hndvd, ?_⟩
    have := Fact.mk hq
    have hq2 : q ≠ 2 := by omega
    have rr := legendreSym.quadratic_reciprocity (p := r) (q := q) hr2 hq2 (Ne.symm hqr)
    have rd := legendreSym.quadratic_reciprocity (p := d) (q := q) hd2 hq2 (Ne.symm hqd)
    have hℓ := hsame q hq hqp
    have hsq : legendreSym r q * legendreSym r q = 1 := by
      rcases legendreSym.eq_one_or_neg_one r (cast_ne_zero_of_prime hr.out hq hqr) with h | h <;>
        rw [h] <;> norm_num
    have hev : Even ((r / 2 + d / 2) * (q / 2)) := by
      apply Even.mul_right
      rw [Nat.even_iff]; omega
    have hprod : legendreSym q (r : ℤ) * legendreSym q (d : ℤ) = 1 := by
      have : legendreSym q (r : ℤ) * legendreSym q (d : ℤ) =
          (legendreSym q (r : ℤ) * legendreSym r q) * (legendreSym q (d : ℤ) * legendreSym d q) := by
        rw [← hℓ]
        calc legendreSym q (r : ℤ) * legendreSym q (d : ℤ)
            = legendreSym q (r : ℤ) * legendreSym q (d : ℤ) * (legendreSym r q * legendreSym r q) := by
              rw [hsq, mul_one]
          _ = _ := by ring
      rw [this, rr, rd, ← pow_add, ← add_mul]
      exact Even.neg_one_pow hev
    have hne : (((r * d : ℕ) : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]; exact hndvd
    have h1 : legendreSym q ((r * d : ℕ) : ℤ) = 1 := by
      rw [Nat.cast_mul, legendreSym.mul]; exact hprod
    have := (legendreSym.eq_one_iff q hne).1 h1
    simpa using this
  exact two_primes_not_square hr.out hd.out hrd (hL (r * d) hNL hN8 hq)

/-! ### The theorem -/

/-- **Lukes–Patterson–Williams with Sorenson's sieve bound** (Sorenson 2006, Lemma 3.1).
Let `n > 1` be odd, every prime factor of `n` above `s`, `n < L s`, where `L` bounds the
pseudosquares for `p` from below (no non-square `N < L`, `N ≡ 1 mod 8`, is a quadratic residue
coprime to every odd prime `q ≤ p`). If
(3) `q^((n-1)/2) ≡ ±1 (mod n)` for every prime `q ≤ p`,
(4) `2^((n-1)/2) ≡ -1` when `n ≡ 5 (mod 8)`, and some `q ≤ p` gives `-1` when `n ≡ 1 (mod 8)`,
then `n` is a prime power. -/
theorem lpw_sorenson {n s p L : ℕ} (hn1 : 1 < n) (hodd : Odd n)
    (hs : ∀ r, r.Prime → r ∣ n → s < r) (hnL : n < L * s)
    (hL : ∀ N, N < L → N % 8 = 1 →
      (∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ N ∧ IsSquare (N : ZMod q)) → IsSquare N)
    (h2p : 2 ≤ p)
    (h3 : ∀ q, q.Prime → q ≤ p → q ^ ((n - 1) / 2) % n = 1 ∨ q ^ ((n - 1) / 2) % n = n - 1)
    (h5 : n % 8 = 5 → 2 ^ ((n - 1) / 2) % n = n - 1)
    (h1 : n % 8 = 1 → ∃ q, q.Prime ∧ q ≤ p ∧ q ^ ((n - 1) / 2) % n = n - 1) :
    ∃ r k, r.Prime ∧ n = r ^ k := by
  have hn3 : 3 ≤ n := by
    rcases hodd with ⟨k, hk⟩; omega
  have hno : n % 2 = 1 := Nat.odd_iff.1 hodd
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n - 1 ≠ 0 by omega)
  have hmo : m % 2 = 1 := Nat.odd_iff.1 hm
  have he : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    subst this; simp at hnm; omega
  have hexp : (n - 1) / 2 = 2 ^ (e - 1) * m := by
    rw [hnm, two_pow_split he]; omega
  have hbase : e = 1 ∨ ∃ b, b.Prime ∧ b ≤ p ∧ b ^ ((n - 1) / 2) % n = n - 1 := by
    have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
    rcases h8 with h | h | h | h
    · obtain ⟨q, hq, hqp, hqn⟩ := h1 h; exact Or.inr ⟨q, hq, hqp, hqn⟩
    · left; by_contra he2
      rw [pow_split4 (by omega) m] at hnm; omega
    · exact Or.inr ⟨2, Nat.prime_two, h2p, h5 h⟩
    · left; by_contra he2
      rw [pow_split4 (by omega) m] at hnm; omega
  -- data of an odd prime factor
  have hdata : ∀ x, x.Prime → x ∣ n → x ≠ 2 ∧ ∃ f t, Odd t ∧ 1 ≤ f ∧ x - 1 = 2 ^ f * t := by
    intro x hx hxn
    have hx2 : x ≠ 2 := by
      rintro rfl; obtain ⟨k, hk⟩ := hxn; omega
    obtain ⟨f, t, ht, hxt⟩ := Nat.exists_eq_two_pow_mul_odd (show x - 1 ≠ 0 by
      have := hx.two_le; omega)
    refine ⟨hx2, f, t, ht, ?_, hxt⟩
    by_contra hf
    have : f = 0 := by omega
    subst this
    have hto := Nat.odd_iff.1 ht
    rcases Nat.Prime.eq_two_or_odd hx with h | h
    · exact hx2 h
    · simp at hxt; omega
  by_contra H
  set r := n.minFac with hrdef
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  obtain ⟨d, hd, hdn, hdr⟩ : ∃ d, d.Prime ∧ d ∣ n ∧ d ≠ r := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact H ⟨r, _, hr, Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
      (fun {x} hx hxn => hall x hx hxn)⟩
  obtain ⟨hr2, f1, t1, ht1, hf1, hrt⟩ := hdata r hr hrn
  obtain ⟨hd2, f2, t2, ht2, hf2, hdt⟩ := hdata d hd hdn
  have := Fact.mk hr
  have := Fact.mk hd
  obtain ⟨hef1, hch1⟩ := factor_char (x := r) hn3 hrn hr2 he hm hexp ht1 hf1 hrt h3 hbase
  obtain ⟨hef2, hch2⟩ := factor_char (x := d) hn3 hdn hd2 he hm hexp ht2 hf2 hdt h3 hbase
  by_cases hB : f1 = e ∧ f2 = e
  · obtain ⟨rfl, hf2e⟩ := hB
    subst hf2e
    have hcop : Nat.Coprime r d := (Nat.coprime_primes hr hd).2 (Ne.symm hdr)
    obtain ⟨c, hc⟩ := hcop.mul_dvd_of_dvd_of_dvd hrn hdn
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc; omega
    exact caseB (P := fun q => q ^ ((n - 1) / 2) % n = n - 1) (Ne.symm hdr) hr2 hd2 hc hc0
      he hm hnm hrt hdt ht1 ht2 hs hnL hL h2p
      (fun q hq hqp => ⟨(hch1 q hq hqp).1, by rw [(hch1 q hq hqp).2]; simp⟩)
      (fun q hq hqp => ⟨(hch2 q hq hqp).1, by rw [(hch2 q hq hqp).2]; simp⟩)
  · -- some factor has v₂ above e
    have hcof : ∀ x y, x.Prime → y.Prime → x ∣ n → y ∣ n → x ≠ y → ∃ c, n = x * c ∧ 2 ≤ c := by
      intro x y hx hy hxn hyn hxy
      obtain ⟨c, hc⟩ := hxn
      refine ⟨c, hc, ?_⟩
      by_contra hc2
      have : c = 1 ∨ c = 0 := by omega
      rcases this with rfl | rfl
      · rw [mul_one] at hc; rw [hc] at hyn
        rcases Nat.Prime.eq_one_or_self_of_dvd hx y hyn with h | h
        · exact hy.one_lt.ne' h
        · exact hxy h.symm
      · simp at hc; omega
    by_cases h1e : f1 = e
    · have h2e : e < f2 := by
        have : f2 ≠ e := fun h => hB ⟨h1e, h⟩
        omega
      obtain ⟨c, hc, hc2⟩ := hcof d r hd hr hdn hrn hdr
      exact caseA (P := fun q => q ^ ((n - 1) / 2) % n = n - 1) hc hc2 hd2 hs hnL hL h2p hdt h2e
        he hch2
    · have h1e' : e < f1 := by omega
      obtain ⟨c, hc, hc2⟩ := hcof r d hr hd hrn hdn (Ne.symm hdr)
      exact caseA (P := fun q => q ^ ((n - 1) / 2) % n = n - 1) hc hc2 hr2 hs hnL hL h2p hrt h1e'
        he hch1

/-- **Deterministic primality for pt1's survivors.** With the sieve bound `s` above `n^(1/4)`
(`n < (s + 1)^4`, as pt1's `B = isqrt(isqrt(top))` gives), a survivor that passes the
pseudosquares conditions and is neither a square nor a cube is prime. -/
theorem prime_of_pss {n s p L : ℕ} (hn1 : 1 < n) (hodd : Odd n)
    (hs : ∀ r, r.Prime → r ∣ n → s < r) (hs4 : n < (s + 1) ^ 4) (hnL : n < L * s)
    (hL : ∀ N, N < L → N % 8 = 1 →
      (∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ N ∧ IsSquare (N : ZMod q)) → IsSquare N)
    (h2p : 2 ≤ p)
    (h3 : ∀ q, q.Prime → q ≤ p → q ^ ((n - 1) / 2) % n = 1 ∨ q ^ ((n - 1) / 2) % n = n - 1)
    (h5 : n % 8 = 5 → 2 ^ ((n - 1) / 2) % n = n - 1)
    (h1 : n % 8 = 1 → ∃ q, q.Prime ∧ q ≤ p ∧ q ^ ((n - 1) / 2) % n = n - 1)
    (hsq : ∀ k, k * k ≠ n) (hcube : ∀ k, k * k * k ≠ n) : n.Prime := by
  obtain ⟨r, k, hr, rfl⟩ := lpw_sorenson hn1 hodd hs hnL hL h2p h3 h5 h1
  have hrs : s + 1 ≤ r := hs r hr (dvd_pow_self r (by rintro rfl; simp at hn1))
  have hk4 : k < 4 := by
    by_contra h
    have : (s + 1) ^ 4 ≤ r ^ k :=
      le_trans (Nat.pow_le_pow_left hrs 4) (Nat.pow_le_pow_right hr.pos (by omega))
    omega
  interval_cases k
  · simp at hn1
  · simpa using hr
  · exact absurd (by ring) (hsq r)
  · exact absurd (by ring) (hcube r)

/-- **Completeness: the test never rejects a prime.** For a prime `n > p`: every base gives
`±1` (Euler), `2` gives `-1` when `n ≡ 5 (mod 8)`, and when `n ≡ 1 (mod 8)` and every base
`q ≤ p` gives `+1`, then `n ≥ L` (so `pss_prove` returns "composite" in that branch only for
`n < L`, i.e. never for a prime). -/
theorem pss_complete {n p L : ℕ} (hn : n.Prime) (hn2 : n ≠ 2) (hpn : p < n)
    (hL : ∀ N, N < L → N % 8 = 1 →
      (∀ q, q.Prime → 3 ≤ q → q ≤ p → ¬ q ∣ N ∧ IsSquare (N : ZMod q)) → IsSquare N) :
    (∀ q, q.Prime → q ≤ p → q ^ ((n - 1) / 2) % n = 1 ∨ q ^ ((n - 1) / 2) % n = n - 1) ∧
    (n % 8 = 5 → 2 ^ ((n - 1) / 2) % n = n - 1) ∧
    (n % 8 = 1 → (∀ q, q.Prime → q ≤ p → q ^ ((n - 1) / 2) % n = 1) → L ≤ n) := by
  have := Fact.mk hn
  have hn1 : 1 ≤ n := hn.one_lt.le
  have hhalf : (n - 1) / 2 = n / 2 := by
    rcases Nat.Prime.eq_two_or_odd hn with h | h
    · exact absurd h hn2
    · omega
  -- in ZMod n, q^((n-1)/2) is ±1, and the remainder mod n is 1 or n - 1
  have hval : ∀ q, q.Prime → q ≤ p →
      ((q : ZMod n) ^ (n / 2) = 1 ∨ (q : ZMod n) ^ (n / 2) = -1) := by
    intro q hq hqp
    apply ZMod.pow_div_two_eq_neg_one_or_one
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd hq.pos h; omega
  have hmod : ∀ x : ℕ, ((x : ZMod n) = 1 → x % n = 1) ∧ ((x : ZMod n) = -1 → x % n = n - 1) := by
    intro x
    constructor
    · intro h
      have : ((x % n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by rw [ZMod.natCast_mod]; simpa using h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.mod_eq_of_lt hn.one_lt] at this
      exact this
    · intro h
      have h2 : ((x : ℕ) : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
        rw [h, Nat.cast_sub hn1, ZMod.natCast_self]; simp
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : n - 1 < n)] at h2
      exact h2
  refine ⟨fun q hq hqp => ?_, fun h5 => ?_, fun h1 hall => ?_⟩
  · rw [hhalf]
    rcases hval q hq hqp with h | h
    · left; exact (hmod _).1 (by rw [Nat.cast_pow]; exact h)
    · right; exact (hmod _).2 (by rw [Nat.cast_pow]; exact h)
  · rw [hhalf]
    have hns : ¬ IsSquare (2 : ZMod n) := by
      rw [ZMod.exists_sq_eq_two_iff hn2]; omega
    have h20 : (2 : ZMod n) ≠ 0 := by
      intro h; apply hns; rw [h]; exact ⟨0, by ring⟩
    rcases ZMod.pow_div_two_eq_neg_one_or_one n h20 with h | h
    · exact absurd ((ZMod.euler_criterion n h20).2 h) hns
    · exact (hmod _).2 (by push_cast; exact h)
  · by_contra hlt
    apply prime_not_square hn
    apply hL n (by omega) h1
    intro q hq hq3 hqp
    have := Fact.mk hq
    have hqn : q ≠ n := by omega
    refine ⟨fun h => ?_, ?_⟩
    · rcases Nat.Prime.eq_one_or_self_of_dvd hn q h with h' | h' <;> omega
    · have hq1 := hall q hq hqp
      have hq0 : ((q : ℤ) : ZMod n) ≠ 0 := cast_ne_zero_of_prime hn hq hqn
      have hpow : (q : ZMod n) ^ (n / 2) = 1 := by
        rcases hval q hq hqp with h | h
        · exact h
        · exfalso
          have := (hmod _).2 (by rw [Nat.cast_pow]; exact h)
          rw [← hhalf] at this; omega
      have hsq : IsSquare (q : ZMod n) := (ZMod.euler_criterion n (by simpa using hq0)).2 hpow
      have hl : legendreSym n q = 1 := (legendreSym.eq_one_iff n hq0).2 (by simpa using hsq)
      have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := n) (q := q) (by omega)
        (by omega)
      rw [hl] at hrec
      have := (legendreSym.eq_one_iff q (cast_ne_zero_of_prime hq hn (Ne.symm hqn))).1 hrec
      simpa using this


/-! ## The C routine `pss_prove` and its table -/

def pssTable : List (ℕ × ℕ) := [
  (2, 17),
  (3, 73),
  (5, 241),
  (7, 1009),
  (11, 2641),
  (13, 8089),
  (17, 18001),
  (19, 53881),
  (23, 87481),
  (29, 117049),
  (31, 515761),
  (37, 1083289),
  (41, 3206641),
  (43, 3818929),
  (47, 9257329),
  (53, 22000801),
  (59, 48473881),
  (61, 48473881),
  (67, 175244281),
  (71, 427733329),
  (73, 427733329),
  (79, 898716289),
  (83, 2805544681),
  (89, 2805544681),
  (97, 2805544681),
  (101, 10310263441),
  (103, 23616331489),
  (107, 85157610409),
  (109, 85157610409),
  (113, 196265095009),
  (127, 196265095009),
  (131, 2871842842801),
  (137, 2871842842801),
  (139, 2871842842801),
  (149, 26250887023729),
  (151, 26250887023729),
  (157, 112434732901969),
  (163, 112434732901969),
  (167, 112434732901969),
  (173, 178936222537081),
  (179, 178936222537081),
  (181, 696161110209049),
  (191, 696161110209049),
  (193, 2854909648103881),
  (197, 6450045516630769),
  (199, 6450045516630769),
  (211, 11641399247947921),
  (223, 11641399247947921),
  (227, 190621428905186449),
  (229, 196640148121928601),
  (233, 712624335095093521),
  (239, 1773855791877850321),
  (241, 2327687064124474441),
  (251, 6384991873059836689),
  (257, 8019204661305419761),
  (263, 10198100582046287689),
  (269, 10198100582046287689),
  (271, 10198100582046287689),
  (277, 69848288320900186969),
  (281, 208936365799044975961),
  (283, 533552663339828203681),
  (293, 936664079266714697089),
  (307, 936664079266714697089),
  (311, 2142202860370269916129),
  (313, 2142202860370269916129),
  (317, 2142202860370269916129),
  (331, 13649154491558298803281),
  (337, 34594858801670127778801),
  (347, 99492945930479213334049),
  (349, 99492945930479213334049),
  (353, 295363187400900310880401),
  (359, 295363187400900310880401),
  (367, 3655334429477057460046489),
  (373, 4235025223080597503519329)]

def tp (k : ℕ) : ℕ := (pssTable.getD k (0, 0)).1
def tL (k : ℕ) : ℕ := (pssTable.getD k (0, 0)).2

theorem table_len : pssTable.length = 74 := by decide
theorem tp_zero : tp 0 = 2 := by decide
theorem tp_lt : ∀ k < 74, tp k < 374 := by decide
theorem tp_succ : ∀ k < 73, tp k < tp (k + 1) := by decide
theorem tL_succ : ∀ k < 73, tL k ≤ tL (k + 1) := by decide
set_option maxRecDepth 100000 in
theorem tp_all_primes : ∀ q < 374, q.Prime → ∃ j < 74, tp j = q := by decide
set_option maxRecDepth 100000 in
theorem tp_prime : ∀ k < 74, (tp k).Prime := by decide


set_option maxRecDepth 100000 in
/-- Sanity check of the transcribed table: every `L_p` except three is `≡ 1 (mod 8)` and a
quadratic residue of every odd prime `q ≤ p` (Euler's criterion). -/
theorem table_pseudosquares : ∀ k < 74, k = 49 ∨ k = 70 ∨ k = 71 ∨ (tL k % 8 = 1 ∧
    ∀ j < k + 1, 1 ≤ j → (tL k % tp j) ^ ((tp j - 1) / 2) % tp j = 1) := by
  decide

/-- The three exceptions are typos in the C table (and in the table of Sorenson's 2010 paper):
`L_229` has a `1` for a `2` (the C value is divisible by 3), `L_353 = L_359` a `1` for a `4`
(Sorenson 2006 has the `4`). Each C value is below the corrected value, and each corrected
value passes the check, so the C table errs on the safe side: `TableCorrect` for the C values
follows from it for the published values. -/
theorem table_typos : tp 49 = 229 ∧ tp 70 = 353 ∧ tp 71 = 359 ∧
    tL 49 = 196640148121928601 ∧ tL 70 = 295363187400900310880401 ∧
    tL 71 = 295363187400900310880401 ∧
    196640148121928601 % 3 = 0 ∧
    tL 49 < 196640248121928601 ∧ tL 70 < 295363487400900310880401 ∧
    tL 71 < 295363487400900310880401 := by
  decide

set_option maxRecDepth 100000 in
/-- The corrected values pass the check. -/
theorem table_corrected :
    196640248121928601 % 8 = 1 ∧
    (∀ j < 50, 1 ≤ j → (196640248121928601 % tp j) ^ ((tp j - 1) / 2) % tp j = 1) ∧
    295363487400900310880401 % 8 = 1 ∧
    (∀ j < 72, 1 ≤ j → (295363487400900310880401 % tp j) ^ ((tp j - 1) / 2) % tp j = 1) := by
  decide

lemma tp_strict {i j : ℕ} (hij : i < j) (hj : j < 74) : tp i < tp j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact lt_trans (ih h (by omega)) (tp_succ j (by omega))
    · subst h; exact tp_succ i (by omega)

lemma tL_le {i j : ℕ} (hij : i ≤ j) (hj : j < 74) : tL i ≤ tL j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with h | h
    · exact le_trans (ih (by omega) (by omega)) (tL_succ j (by omega))
    · rw [h]

/-- Every prime up to `tp k` is one of the bases `tp 0, …, tp k`. -/
lemma bases_cover {k q : ℕ} (hk : k < 74) (hq : q.Prime) (hqk : q ≤ tp k) :
    ∃ j ≤ k, tp j = q := by
  obtain ⟨j, hj, hjq⟩ := tp_all_primes q (lt_of_le_of_lt hqk (tp_lt k hk)) hq
  refine ⟨j, ?_, hjq⟩
  by_contra h
  have := tp_strict (Nat.lt_of_not_le h) hj
  omega

/-- The published pseudosquares table is correct: no non-square `N < L_p`, `N ≡ 1 (mod 8)`, is a
quadratic residue coprime to every odd prime `q ≤ p`. (Assumed, not recomputed.) -/
def TableCorrect : Prop :=
  ∀ k < 74, ∀ N, N < tL k → N % 8 = 1 →
    (∀ q, q.Prime → 3 ≤ q → q ≤ tp k → ¬ q ∣ N ∧ IsSquare (N : ZMod q)) → IsSquare N

/-- The tail of `pss_prove`: bases past the first `n_bases`, one at a time. -/
def tailProve (n e : ℕ) (k : ℕ) : Int :=
  if k < 74 then
    if tp k ^ e % n = n - 1 then 1
    else if tp k ^ e % n ≠ 1 then 0
    else if n < tL k then 0
    else tailProve n e (k + 1)
  else -1
termination_by 74 - k

/-- `pss_prove(n, n_bases)` (1 prime, 0 composite, -1 undecided). Montgomery arithmetic is
modelled as `x^e mod n`; the order of the checks within the first bases does not change the
result. -/
def pssProve (n nb : ℕ) : Int :=
  if ¬ (∀ k < nb, tp k ^ ((n - 1) / 2) % n = 1 ∨ tp k ^ ((n - 1) / 2) % n = n - 1) then 0
  else if n % 8 = 5 ∧ 2 ^ ((n - 1) / 2) % n ≠ n - 1 then 0
  else if n % 8 ≠ 1 ∨ (∃ k < nb, tp k ^ ((n - 1) / 2) % n = n - 1) then 1
  else if n < tL (nb - 1) then 0
  else tailProve n ((n - 1) / 2) nb

lemma tail_sound {n e : ℕ} : ∀ m k, 74 - k = m →
    (∀ j < k, tp j ^ e % n = 1 ∨ tp j ^ e % n = n - 1) → tailProve n e k = 1 →
    ∃ k', k ≤ k' ∧ k' < 74 ∧ (∀ j ≤ k', tp j ^ e % n = 1 ∨ tp j ^ e % n = n - 1) ∧
      tp k' ^ e % n = n - 1 := by
  intro m
  induction m with
  | zero =>
    intro k hk _ h
    have h0 : ¬ k < 74 := by omega
    rw [tailProve] at h
    simp only [h0, ↓reduceIte] at h
    exact absurd h (by norm_num)
  | succ m ih =>
    intro k hk hall h
    have h0 : k < 74 := by omega
    rw [tailProve] at h
    simp only [h0, ↓reduceIte] at h
    by_cases h1 : tp k ^ e % n = n - 1
    · exact ⟨k, le_refl _, h0, fun j hj => (Nat.lt_or_eq_of_le hj).elim (hall j)
        (fun e => by subst e; exact Or.inr h1), h1⟩
    simp only [h1, ↓reduceIte] at h
    by_cases h2 : tp k ^ e % n = 1
    · simp only [h2, ne_eq, not_true_eq_false, ↓reduceIte] at h
      by_cases h3 : n < tL k
      · simp only [h3, ↓reduceIte] at h; exact absurd h (by norm_num)
      simp only [h3, ↓reduceIte] at h
      obtain ⟨k', hk', h74, hall', hm⟩ := ih (k + 1) (by omega)
        (fun j hj => (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj)).elim (hall j)
          (fun e => by subst e; exact Or.inl h2)) h
      exact ⟨k', by omega, h74, hall', hm⟩
    · simp only [h2, ne_eq, not_false_eq_true, ↓reduceIte] at h
      exact absurd h (by norm_num)

lemma tail_complete {n e : ℕ} (hpm : ∀ j < 74, tp j ^ e % n = 1 ∨ tp j ^ e % n = n - 1)
    (hgeL : ∀ j < 74, (∀ i ≤ j, tp i ^ e % n = 1) → tL j ≤ n) :
    ∀ m k, 74 - k = m → (∀ j < k, tp j ^ e % n = 1) → tailProve n e k ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro k hk _
    have h0 : ¬ k < 74 := by omega
    rw [tailProve]
    simp only [h0, ↓reduceIte]
    norm_num
  | succ m ih =>
    intro k hk hall
    have h0 : k < 74 := by omega
    rw [tailProve]
    simp only [h0, ↓reduceIte]
    by_cases h1 : tp k ^ e % n = n - 1
    · simp only [h1, ↓reduceIte]; norm_num
    simp only [h1, ↓reduceIte]
    have h2 : tp k ^ e % n = 1 := (hpm k h0).resolve_right h1
    have hL : tL k ≤ n := hgeL k h0 (fun i hi => (Nat.lt_or_eq_of_le hi).elim (hall i)
      (fun e => by subst e; exact h2))
    have h3 : ¬ n < tL k := by omega
    simp only [h2, ne_eq, not_true_eq_false, ↓reduceIte, h3]
    exact ih (k + 1) (by omega) (fun j hj => (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj)).elim
      (hall j) (fun e => by subst e; exact h2))

/-- **`pss_prove` is sound**: a survivor of pt1's sieve (every prime factor above `s`,
`n < (s+1)^4`, `n < L_p s` for the first `n_bases` bases) that `pss_prove` accepts and that is
neither a square nor a cube is prime. -/
theorem pssProve_sound {n s nb : ℕ} (htab : TableCorrect) (hnb1 : 1 ≤ nb) (hnb : nb ≤ 74)
    (hn1 : 1 < n) (hodd : Odd n) (hs : ∀ r, r.Prime → r ∣ n → s < r) (hs4 : n < (s + 1) ^ 4)
    (hnL : n < tL (nb - 1) * s) (hsq : ∀ k, k * k ≠ n) (hcube : ∀ k, k * k * k ≠ n)
    (h : pssProve n nb = 1) : n.Prime := by
  have h2 : ∀ k < 74, 2 ≤ tp k := fun k hk => (tp_prime k hk).two_le
  unfold pssProve at h
  split_ifs at h with H1 H2 H3 H4
  · exact absurd h (by norm_num)
  · -- accepted after the first n_bases bases
    refine prime_of_pss (p := tp (nb - 1)) (L := tL (nb - 1)) hn1 hodd hs hs4 hnL
      (htab (nb - 1) (by omega)) (h2 _ (by omega)) ?_ ?_ ?_ hsq hcube
    · intro q hq hqp
      obtain ⟨j, hj, rfl⟩ := bases_cover (by omega) hq hqp
      exact H1 j (by omega)
    · intro h5; by_contra hc; exact H2 ⟨h5, hc⟩
    · intro h1
      rcases H3 with h3 | ⟨k, hk, hkm⟩
      · exact absurd h1 h3
      · refine ⟨tp k, tp_prime k (by omega), ?_, hkm⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hk) with h' | h'
        · exact (tp_strict h' (by omega)).le
        · rw [h']
  · exact absurd h (by norm_num)
  · -- accepted in the tail at some k' ≥ n_bases
    simp only [not_or, not_not] at H3
    obtain ⟨k', hk', h74, hall, hm⟩ := tail_sound (74 - nb) nb rfl H1 h
    refine prime_of_pss (p := tp k') (L := tL k') hn1 hodd hs hs4
      (lt_of_lt_of_le hnL (Nat.mul_le_mul_right s (tL_le (by omega) h74)))
      (htab k' h74) (h2 k' h74) ?_ ?_ ?_ hsq hcube
    · intro q hq hqp
      obtain ⟨j, hj, rfl⟩ := bases_cover h74 hq hqp
      exact hall j hj
    · intro h5; omega
    · intro _; exact ⟨tp k', tp_prime k' h74, le_refl _, hm⟩
  · exact absurd h (by norm_num)

/-- **`pss_prove` never rejects a prime** above 373 (the C precondition). -/
theorem pssProve_complete {n nb : ℕ} (htab : TableCorrect) (hnb1 : 1 ≤ nb) (hnb : nb ≤ 74)
    (hn : n.Prime) (h373 : 373 < n) : pssProve n nb ≠ 0 := by
  have hn2 : n ≠ 2 := by omega
  have hcomp : ∀ k, k < 74 →
      (∀ q, q.Prime → q ≤ tp k → q ^ ((n - 1) / 2) % n = 1 ∨ q ^ ((n - 1) / 2) % n = n - 1) ∧
      (n % 8 = 5 → 2 ^ ((n - 1) / 2) % n = n - 1) ∧
      (n % 8 = 1 → (∀ q, q.Prime → q ≤ tp k → q ^ ((n - 1) / 2) % n = 1) → tL k ≤ n) :=
    fun k hk => pss_complete hn hn2 (by have := tp_lt k hk; omega) (htab k hk)
  have hpm : ∀ j < 74, tp j ^ ((n - 1) / 2) % n = 1 ∨ tp j ^ ((n - 1) / 2) % n = n - 1 :=
    fun j hj => (hcomp j hj).1 (tp j) (tp_prime j hj) (le_refl _)
  have hgeL : n % 8 = 1 → ∀ j < 74, (∀ i ≤ j, tp i ^ ((n - 1) / 2) % n = 1) → tL j ≤ n := by
    intro h81 j hj hall
    apply (hcomp j hj).2.2 h81
    intro q hq hqj
    obtain ⟨i, hi, rfl⟩ := bases_cover hj hq hqj
    exact hall i hi
  unfold pssProve
  split_ifs with H1 H2 H3 H4
  · exact absurd ((hcomp 0 (by norm_num)).2.1 H2.1) H2.2
  · norm_num
  · simp only [not_or, not_not, not_exists, not_and] at H3
    obtain ⟨h81, hno⟩ := H3
    have hplus : ∀ k < nb, tp k ^ ((n - 1) / 2) % n = 1 := fun k hk =>
      (hpm k (by omega)).resolve_right (hno k hk)
    have := hgeL h81 (nb - 1) (by omega) (fun i hi => hplus i (by omega))
    omega
  · simp only [not_or, not_not, not_exists, not_and] at H3
    obtain ⟨h81, hno⟩ := H3
    exact tail_complete hpm (hgeL h81) (74 - nb) nb rfl (fun k hk =>
      (hpm k (by omega)).resolve_right (hno k hk))
  · exact absurd (fun k hk => hpm k (by omega)) H1

end PseudoSquares
