import Mathlib

set_option linter.unnecessarySimpa false
set_option linter.style.emptyLine false

noncomputable abbrev putnam_2024_a1_solution : Set ℕ := {1}

/--
Auxiliary predicate: `sol n a b c` means `a,b,c` are positive naturals
solving `2*a^n + 3*b^n = 4*c^n`.
-/
def sol (n a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 2 * a^n + 3 * b^n = 4 * c^n

lemma sol_pos_a {n a b c : ℕ} (h : sol n a b c) : 0 < a := h.1
lemma sol_pos_b {n a b c : ℕ} (h : sol n a b c) : 0 < b := h.2.1
lemma sol_pos_c {n a b c : ℕ} (h : sol n a b c) : 0 < c := h.2.2.1
lemma sol_eqn {n a b c : ℕ} (h : sol n a b c) :
    2 * a^n + 3 * b^n = 4 * c^n := h.2.2.2

/-- A concrete solution for `n = 1`: `(a,b,c) = (1,2,2)`. -/
lemma sol_n1_example : sol 1 1 2 2 := by
  unfold sol
  refine ⟨by decide, by decide, by decide, ?_⟩
  norm_num

/-- For `n ≥ 3`, any solution `(a,b,c)` gives a strictly smaller solution. -/
lemma descent_step_ge3 {n a b c : ℕ} (hn : 3 ≤ n) (h : sol n a b c) :
    ∃ a' b' c', sol n a' b' c' ∧ a' + b' + c' < a + b + c := by
  classical
  -- We unpack the bundled assumptions from `sol`.
  have ha_pos := sol_pos_a h
  have hb_pos := sol_pos_b h
  have hc_pos := sol_pos_c h
  have heqn := sol_eqn h

  -- Overall plan (infinite descent step for n≥3):
  -- (1) show b is even (mod 2 argument),
  -- (2) show a is even (mod 4 argument),
  -- (3) show c is even (mod 8 argument),
  -- then write a = 2 * a1, b = 2 * b1, c = 2 * c1 and
  -- divide out 2^n to get a smaller solution.

  -- 1) b even
  have hb_even : Even b := by
    -- Work mod 2: RHS is even, and 2*a^n is even, so 3*b^n must be even.
    have h4dvd : 2 ∣ 4 * c^n := by
      exact dvd_mul_of_dvd_left (by decide : 2 ∣ 4) (c^n)
    have h4mod : (4 * c^n) % 2 = 0 := Nat.mod_eq_zero_of_dvd h4dvd
    have hsum_mod : (2 * a^n + 3 * b^n) % 2 = 0 := by
      -- Replace RHS by LHS using the equation.
      simpa [heqn] using h4mod

    -- Split the mod of a sum.
    have hsum_mod' : ((2 * a^n) % 2 + (3 * b^n) % 2) % 2 = 0 := by
      simpa [Nat.add_mod] using hsum_mod

    -- 2 divides 2*a^n, so (2*a^n)%2 = 0.
    have h2dvd : 2 ∣ 2 * a^n := by
      exact dvd_mul_of_dvd_left (dvd_rfl : 2 ∣ 2) (a^n)
    have h2mod : (2 * a^n) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd

    -- Therefore (3*b^n)%2 = 0, hence 2 ∣ 3*b^n.
    have h3bn_mod : (3 * b^n) % 2 = 0 := by
      have : ((0 : ℕ) + (3 * b^n) % 2) % 2 = 0 := by
        simpa [h2mod] using hsum_mod'
      simpa using this
    have h2_dvd_3bn : 2 ∣ 3 * b^n := Nat.dvd_of_mod_eq_zero h3bn_mod

    -- Cancel the factor 3 using gcd(2,3)=1, getting 2 ∣ b^n.
    -- Euclid’s lemma in a coprime form
    have hcop : Nat.Coprime 2 3 := by decide
    have h2_dvd_bpow : 2 ∣ b^n := hcop.dvd_of_dvd_mul_left h2_dvd_3bn

    -- Prime 2 dividing b^n implies 2 divides b.
    have h2_dvd_b : 2 ∣ b := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2_dvd_bpow

    -- Turn 2 ∣ b into Even b.
    rcases h2_dvd_b with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [ht, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  -- Introduce b1 with b = 2*b1 (and show b1>0).
  rcases hb_even with ⟨b1, hb1⟩
  have hb1_2 : b = 2 * b1 := by
    simpa [two_mul] using hb1
  have hb1_ne0 : b1 ≠ 0 := by
    intro hb10
    have hb0 : b = 0 := by simpa [hb1_2, hb10]
    have : (0 : ℕ) < 0 := by simpa [hb0] using hb_pos
    exact (Nat.lt_irrefl 0) this
  have hb1_pos : 0 < b1 := Nat.pos_of_ne_zero hb1_ne0

  -- Rewrite equation with b = 2*b1.
  have h1 : 2 * a^n + 3 * (2 * b1)^n = 4 * c^n := by
    simpa [hb1_2] using heqn

  -- 2) a even
  have ha_even : Even a := by
    -- Key point: n≥3 ⇒ n≥2 ⇒ 4 ∣ 2^n, so 4 ∣ (2*b1)^n and hence 4 ∣ 3*(2*b1)^n.
    have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
    have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
    have h4_dvd_2pow : 4 ∣ (2 : ℕ) ^ n := by
      have : (2 : ℕ) ^ 2 ∣ (2 : ℕ) ^ n := pow_dvd_pow 2 hn2
      simpa [hpow] using this
    have h4_dvd_2b1pow : 4 ∣ (2 * b1) ^ n := by
      have : 4 ∣ (2 : ℕ) ^ n * b1 ^ n := dvd_mul_of_dvd_left h4_dvd_2pow (b1 ^ n)
      simpa [mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    have h4_dvd_3term : 4 ∣ 3 * (2 * b1) ^ n :=
      dvd_mul_of_dvd_right h4_dvd_2b1pow 3

    -- RHS is divisible by 4, so LHS is divisible by 4.
    have h4rhs : 4 ∣ 4 * c ^ n := ⟨c ^ n, rfl⟩
    have h4sum : 4 ∣ 2 * a ^ n + 3 * (2 * b1) ^ n := by
      simpa [h1] using h4rhs

    -- Reorder and cancel the known divisible term to get 4 ∣ 2*a^n.
    have h4sum' : 4 ∣ 3 * (2 * b1) ^ n + 2 * a ^ n := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h4sum
    have h4_2an : 4 ∣ 2 * a ^ n :=
      (Nat.dvd_add_iff_right h4_dvd_3term).2 h4sum'

    -- From 4 ∣ 2*a^n, we get 2 ∣ a^n, hence 2 ∣ a, hence Even a.
    rcases h4_2an with ⟨t, ht⟩
    have ht' : 2 * a ^ n = 2 * (2 * t) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht
    have han_eq : a ^ n = 2 * t := by
      exact Nat.mul_left_cancel (by decide : 0 < (2 : ℕ)) ht'
    have h2_dvd_an : 2 ∣ a ^ n := ⟨t, han_eq⟩
    have h2_dvd_a : 2 ∣ a := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2_dvd_an
    rcases h2_dvd_a with ⟨k, hk⟩
    exact ⟨k, by simpa [two_mul] using hk⟩

  -- Introduce a1 with a = 2*a1 (and show a1>0).
  rcases ha_even with ⟨a1, ha1⟩
  have ha1_2 : a = 2 * a1 := by
    simpa [two_mul] using ha1
  have ha1_ne0 : a1 ≠ 0 := by
    intro ha10
    have ha0 : a = 0 := by simpa [ha1_2, ha10]
    have : (0 : ℕ) < 0 := by simpa [ha0] using ha_pos
    exact (Nat.lt_irrefl 0) this
  have ha1_pos : 0 < a1 := Nat.pos_of_ne_zero ha1_ne0

  -- Rewrite equation with a=2*a1 and b=2*b1.
  have h2 : 2 * (2 * a1)^n + 3 * (2 * b1)^n = 4 * c^n := by
    simpa [ha1_2, hb1_2] using sol_eqn h

  -- 3) c even
  have hc_even : Even c := by
    -- Key point: n≥3 ⇒ 8 ∣ 2^n, so both terms on the LHS are divisible by 8,
    -- hence RHS = 4*c^n is divisible by 8, forcing 2 ∣ c^n and hence c even.
    have hpow : (2 : ℕ) ^ 3 = 8 := by norm_num
    have h8_dvd_2pow : 8 ∣ (2 : ℕ) ^ n := by
      have : (2 : ℕ) ^ 3 ∣ (2 : ℕ) ^ n := pow_dvd_pow 2 hn
      simpa [hpow] using this
    have h8_dvd_term1 : 8 ∣ 2 * (2 * a1) ^ n := by
      have htmp : 8 ∣ (2 : ℕ) ^ n * (2 * a1 ^ n) :=
        dvd_mul_of_dvd_left h8_dvd_2pow (2 * a1 ^ n)
      have : 8 ∣ 2 * ((2 : ℕ) ^ n * a1 ^ n) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using htmp
      simpa [mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    have h8_dvd_term2 : 8 ∣ 3 * (2 * b1) ^ n := by
      have htmp : 8 ∣ (2 : ℕ) ^ n * b1 ^ n :=
        dvd_mul_of_dvd_left h8_dvd_2pow (b1 ^ n)
      have : 8 ∣ 3 * ((2 : ℕ) ^ n * b1 ^ n) :=
        dvd_mul_of_dvd_right htmp 3
      simpa [mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    have h8_dvd_lhs : 8 ∣ 2 * (2 * a1) ^ n + 3 * (2 * b1) ^ n :=
      dvd_add h8_dvd_term1 h8_dvd_term2
    have h8_dvd_rhs : 8 ∣ 4 * c ^ n := by
      simpa [h2] using h8_dvd_lhs
    have h2_dvd_cpow : 2 ∣ c ^ n := by
      have hmul : (4 : ℕ) * 2 ∣ (4 : ℕ) * (c ^ n) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h8_dvd_rhs
      exact (mul_dvd_mul_iff_left (show (4 : ℕ) ≠ 0 by decide)).1 hmul
    have h2_dvd_c : 2 ∣ c := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2_dvd_cpow
    rcases h2_dvd_c with ⟨k, hk⟩
    exact ⟨k, by simpa [two_mul] using hk⟩

  -- Introduce c1 with c = 2*c1 (and show c1>0).
  rcases hc_even with ⟨c1, hc1⟩
  have hc1_2 : c = 2 * c1 := by
    simpa [two_mul] using hc1
  have hc1_ne0 : c1 ≠ 0 := by
    intro hc10
    have hc0 : c = 0 := by simpa [hc1_2, hc10]
    have : (0 : ℕ) < 0 := by simpa [hc0] using hc_pos
    exact (Nat.lt_irrefl 0) this
  have hc1_pos : 0 < c1 := Nat.pos_of_ne_zero hc1_ne0

  -- 4) reduced equation for (a1,b1,c1) by expanding (2*x)^n and cancelling 2^n.
  have h_eqn' : 2 * a1^n + 3 * b1^n = 4 * c1^n := by
    have heqn_sub :
        2 * (2 * a1)^n + 3 * (2 * b1)^n = 4 * (2 * c1)^n := by
      simpa [ha1_2, hb1_2, hc1_2] using heqn
    have heqn_pow :
        2 * (2^n * a1^n) + 3 * (2^n * b1^n) = 4 * (2^n * c1^n) := by
      simpa [mul_pow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using heqn_sub
    have hA : 2 * (2^n * a1^n) = 2^n * (2 * a1^n) := by
      ac_rfl
    have hB : 3 * (2^n * b1^n) = 2^n * (3 * b1^n) := by
      ac_rfl
    have hC : 4 * (2^n * c1^n) = 2^n * (4 * c1^n) := by
      ac_rfl
    have heqn_pow' :
        2^n * (2 * a1^n) + 2^n * (3 * b1^n) = 2^n * (4 * c1^n) := by
      simpa [hA, hB, hC] using heqn_pow
    have heqn_fact :
        2^n * (2 * a1^n + 3 * b1^n) = 2^n * (4 * c1^n) := by
      simpa [Nat.mul_add] using heqn_pow'
    have hpos : 0 < 2^n := pow_pos (by decide : 0 < (2 : ℕ)) n
    -- Cancel the common (positive) factor 2^n.
    exact Nat.mul_left_cancel hpos heqn_fact

  -- 5) Package the smaller solution and prove the sum decreased.
  refine ⟨a1, b1, c1, ?_, ?_⟩
  · exact ⟨ha1_pos, hb1_pos, hc1_pos, h_eqn'⟩
  · have hsum : a + b + c = 2 * (a1 + b1 + c1) := by
      simp [ha1_2, hb1_2, hc1_2, Nat.mul_add]
    have hpos' : 0 < a1 + b1 + c1 := by
      have hab : 0 < a1 + b1 := add_pos ha1_pos hb1_pos
      simpa [Nat.add_assoc] using add_pos hab hc1_pos
    have hlt : a1 + b1 + c1 < a + b + c := by
      have : a1 + b1 + c1 < (a1 + b1 + c1) + (a1 + b1 + c1) :=
        Nat.lt_add_of_pos_right hpos'
      have : a1 + b1 + c1 < 2 * (a1 + b1 + c1) := by
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      simpa [hsum] using this
    exact hlt

/-- For `n ≥ 3`, there are no solutions at all. -/
lemma no_solution_ge3 {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∃ a b c, sol n a b c := by
  classical
  -- We prove this by contradiction + minimal counterexample.
  -- Assume there exists at least one solution (a,b,c).
  intro h

  -- Define the property P(s): “there exists a solution whose sum a+b+c equals s”.
  let P : ℕ → Prop := fun s => ∃ a b c, sol n a b c ∧ a + b + c = s

  -- Show P is inhabited: from the assumed solution, take s = a+b+c.
  have hP : ∃ s, P s := by
    rcases h with ⟨a, b, c, hs⟩
    exact ⟨a + b + c, a, b, c, hs, rfl⟩

  -- Let s0 be the *least* natural number such that P(s0) holds.
  -- (Nat.find picks the smallest witness of an existential over ℕ.)
  let s0 := Nat.find hP

  -- By definition/spec of Nat.find, P(s0) holds.
  have hP0 : P s0 := Nat.find_spec hP

  -- Unpack P(s0): we get a specific solution (a0,b0,c0) whose sum is exactly s0.
  rcases hP0 with ⟨a0, b0, c0, hsol0, hsum0⟩

  -- Apply the “descent step”: from a solution when n≥3, we can construct a smaller one.
  -- This gives a new solution (a1,b1,c1) with strictly smaller sum.
  rcases descent_step_ge3 hn hsol0 with ⟨a1, b1, c1, hsol1, hlt⟩

  -- Turn that new solution into a witness that P holds at the new sum.
  have hP1 : P (a1 + b1 + c1) := ⟨a1, b1, c1, hsol1, rfl⟩

  -- Minimality property of Nat.find:
  -- if P(m) holds, then s0 ≤ m.
  have hmin := Nat.find_min' hP hP1

  -- Rewrite hlt using hsum0 : a0+b0+c0 = s0, to get the strict inequality “new sum < s0”.
  have : a1 + b1 + c1 < s0 := by
    simpa [hsum0] using hlt

  -- Now we have (a1+b1+c1) < s0 and also s0 ≤ (a1+b1+c1), contradiction.
  exact Nat.lt_irrefl _ (lt_of_lt_of_le this hmin)


/-- For `n = 2`, there are no solutions (mod 3 + descent). -/
lemma no_solution_n2 : ¬ ∃ a b c, sol 2 a b c := by
  classical
  intro h
  -- Standard infinite descent setup (Minimal Counterexample)
  let P : ℕ → Prop := fun s => ∃ a b c, sol 2 a b c ∧ a + b + c = s
  have hP : ∃ s, P s := by
    rcases h with ⟨a, b, c, hs⟩
    exact ⟨a + b + c, a, b, c, hs, rfl⟩
  let s0 := Nat.find hP
  have hP0 : P s0 := Nat.find_spec hP
  rcases hP0 with ⟨a0, b0, c0, hsol0, hsum0⟩

  -- Unpack the solution
  have ha0_pos := sol_pos_a hsol0
  have hb0_pos := sol_pos_b hsol0
  have hc0_pos := sol_pos_c hsol0
  have heqn0 : 2 * a0^2 + 3 * b0^2 = 4 * c0^2 := sol_eqn hsol0

  -- -----------------------------------------------------------
  -- TODO: Implement Mod 3 arithmetic here.
  -- Current strategy:
  -- 1. 2a^2 + 3b^2 = 4c^2 implies 2a^2 ≡ c^2 (mod 3)
  -- 2. Squares mod 3 are 0 or 1.
  -- 3. If a ≢ 0, a^2 ≡ 1 => 2 ≡ c^2 (mod 3), impossible.
  -- 4. Therefore 3|a and 3|c.
  -- -----------------------------------------------------------

  have ha0_div3 : 3 ∣ a0 := by
    -- Need to import ZMod or use Nat.mod_eq?
    -- Struggling to simplify the modulo arithmetic here.
    sorry

  have hc0_div3 : 3 ∣ c0 := by
    -- Similar logic to above, need to formalize "squares mod 3"
    sorry

  -- Extract the factors (a0 = 3a1, c0 = 3c1)
  rcases ha0_div3 with ⟨a1, ha1⟩
  rcases hc0_div3 with ⟨c1, hc1⟩

  -- Step 2: Show b must be divisible by 3
  -- Substitution: 2*(3a1)^2 + 3*b0^2 = 4*(3c1)^2
  -- Reduces to: 6*a1^2 + b0^2 = 12*c1^2
  -- Mod 3 implies b0^2 ≡ 0 (mod 3)
  have hb0_div3 : 3 ∣ b0 := by
    rw [ha1, hc1] at heqn0
    -- Need a tactic to simplify powers and divide by 3
    sorry

  rcases hb0_div3 with ⟨b1, hb1⟩

  -- Check positivity of new variables (boilerplate)
  have ha1_pos : 0 < a1 := by
    -- a0 > 0 and a0 = 3a1 implies a1 > 0
    sorry
  have hb1_pos : 0 < b1 := by sorry
  have hc1_pos : 0 < c1 := by sorry

  -- Step 3: Construct the smaller solution equation
  -- 2(3a1)^2 + 3(3b1)^2 = 4(3c1)^2
  -- 18a1^2 + 27b1^2 = 36c1^2
  -- Divide entire equation by 9
  have h_eqn' : 2 * a1^2 + 3 * b1^2 = 4 * c1^2 := by
    rw [ha1, hb1, hc1] at heqn0
    -- Algebra verification needed here
    sorry

  -- Package the new solution
  have hsol1 : sol 2 a1 b1 c1 := ⟨ha1_pos, hb1_pos, hc1_pos, h_eqn'⟩

  -- Step 4: Show the sum is strictly smaller
  have hsum : a0 + b0 + c0 = 3 * (a1 + b1 + c1) := by
    rw [ha1, hb1, hc1]
    ring

  have hlt : a1 + b1 + c1 < s0 := by
    rw [←hsum0, hsum]
    -- n < 3n is true for positive n
    sorry

  -- Final contradiction with the minimal counterexample
  have hP1 : P (a1 + b1 + c1) := ⟨a1, b1, c1, hsol1, rfl⟩
  have hmin := Nat.find_min' hP hP1
  exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt hmin)

/-- If there is a solution for `n > 0`, then `n = 1`. -/
lemma n_eq_one_of_sol {n : ℕ}
    (hnpos : 0 < n)
    (h : ∃ a b c, sol n a b c) :
    n = 1 := by
  cases n with
  | zero => cases hnpos
  | succ n1 =>
    cases n1 with
    | zero => rfl
    | succ n2 =>
      cases n2 with
      | zero =>
        have : ¬ ∃ a b c, sol 2 a b c := no_solution_n2
        exact (this (by simpa using h)).elim
      | succ n3 =>
        have hn : 3 ≤ Nat.succ (Nat.succ (Nat.succ n3)) := by
          have : 3 ≤ 3 + n3 := Nat.le_add_right 3 n3
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
        have : ¬ ∃ a b c, sol (Nat.succ (Nat.succ (Nat.succ n3))) a b c :=
          no_solution_ge3 hn
        exact (this (by simpa using h)).elim

/--
Determine all positive integers `n` for which there exist positive integers `a`, `b` and `c`
satisfying `2*a^n + 3*b^n = 4*c^n`.
-/
theorem putnam_2024_a1 :
    {n : ℕ | 0 < n ∧ ∃ (a b c : ℕ), sol n a b c}
      = putnam_2024_a1_solution := by
  classical
  unfold putnam_2024_a1_solution
  ext n
  constructor
  · intro h
    rcases h with ⟨hnpos, a, b, c, hsol⟩
    have hn1 : n = 1 := n_eq_one_of_sol hnpos ⟨a, b, c, hsol⟩
    simp [Set.mem_singleton_iff, hn1]
  · intro hn
    have hn1 : n = 1 := by
      simpa [Set.mem_singleton_iff] using hn
    subst hn1
    refine ⟨Nat.succ_pos _, ?_⟩
    exact ⟨1, 2, 2, sol_n1_example⟩
