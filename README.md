# Formalization of Putnam 2024 A1

**Course Type:** Seminar, Saarland University  
**Instructors:** Alexander Ikonomou and Leon Pernak

## Project Context
This repository contains my final project for the mathematics formalization seminar. The goal of the project was to write a computer-verified proof for the **William Lowell Putnam Mathematical Competition 2024, Problem A1**, using the Lean 4 theorem prover. 

**Provided by the University:**
The course provided the theoretical foundation for using Lean 4 and guidelines for formalizing mathematics.

**Implemented by Me:**
While the mathematical solution to this problem is publicly available online, my contribution was purely the **formalization** of this proof. I translated the existing informal mathematical logic into strict, computer-verified Lean 4 code, ensuring the Diophantine equation $2a^n + 3b^n = 4c^n$ has no positive integer solutions for $n \ge 2$. I completed the full implementation without any remaining gaps (`sorry` blocks) and documented the formalization effort.

## Tech Stack
* Lean 4 (Theorem Prover)
* Mathlib (Lean mathematical library)

## My Contributions

### Formalization of the Existing Proof (Lean 4)
* **Solution Modeling:** Created a core definition (`sol`) that stores the constraints of the problem (positive integers satisfying the target equation).
* **Minimal Solution Strategy:** Formalized the Method of Infinite Descent using `Nat.find` to target the set of all possible solutions and extract the one with the smallest sum ($a + b + c$).
* **Translating the $n \ge 3$ Case:** Programmed the computer to verify parity rules. Used the `Even` tactic to handle parity constraints and applied `pow_dvd_pow` to prove divisibility by 8 for large powers of 2, allowing the construction of a strictly smaller solution.
* **Translating the $n = 2$ Case:** Modeled the divisibility by 3 step using modular arithmetic via `ZMod 3`. Used the `decide` tactic to exhaustively check remainders (0, 1, and 2) to prove that $a$, $b$, and $c$ must be multiples of 3.
* **Algebraic Verification:** Overcame technical difficulties regarding natural number division in Lean by explicitly proving that the divisions by 2 and 3 were "exact" (without remainders). Closed all algebraic goals using the `ring` and `norm_num` tactics.

*Key deliverables: Lean 4 source code, theoretical documentation (1-2 pages), and formalization documentation (2 pages).*
