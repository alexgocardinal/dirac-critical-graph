import Mathlib.Tactic

/-!
# A proof-producing certificate for the order-60 Dirac graph

The graph data and all finite Boolean constraints are explicit below.  The
three main negative results use `bv_decide`, whose SAT proof is replayed by
Lean's verified reflection pipeline.  The precise axioms used by the selected
toolchain are printed at the end of this file.  `native_decide` is used only
for positive concrete witness replay; it is never used to establish an
UNSAT/non-colourability claim.

Color codes are `00`, `10`, and `01`; `11` is invalid.  Thus two Boolean
variables encode one of three colours without using an untrusted parser.
-/

namespace Dirac60

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def validCode (a b : Bool) : Bool := !(a && b)

def sameCode (a b x y : Bool) : Bool := (a == x) && (b == y)

def is0 (a b : Bool) : Bool := (!a) && (!b)
def is1 (a b : Bool) : Bool := a && (!b)
def is2 (a b : Bool) : Bool := (!a) && b

def allB : List Bool → Bool
  | [] => true
  | x :: xs => x && allB xs

def atMostOneAux : Bool → List Bool → Bool
  | _, [] => true
  | seen, x :: xs => (!(seen && x)) && atMostOneAux (seen || x) xs

def atMostOne (xs : List Bool) : Bool := atMostOneAux false xs

def exactlyTwo6 (a b c d e f : Bool) : Bool :=
  ((a && b) && (!c && !d && !e && !f)) ||
  ((a && c) && (!b && !d && !e && !f)) ||
  ((a && d) && (!b && !c && !e && !f)) ||
  ((a && e) && (!b && !c && !d && !f)) ||
  ((a && f) && (!b && !c && !d && !e)) ||
  ((b && c) && (!a && !d && !e && !f)) ||
  ((b && d) && (!a && !c && !e && !f)) ||
  ((b && e) && (!a && !c && !d && !f)) ||
  ((b && f) && (!a && !c && !d && !e)) ||
  ((c && d) && (!a && !b && !e && !f)) ||
  ((c && e) && (!a && !b && !d && !f)) ||
  ((c && f) && (!a && !b && !d && !e)) ||
  ((d && e) && (!a && !b && !c && !f)) ||
  ((d && f) && (!a && !b && !c && !e)) ||
  ((e && f) && (!a && !b && !c && !d))

/- Every proper three-colouring of `G - 0` gives each colour exactly twice
on `N(0) = {5,26,30,33,37,55}`.  No normalization is assumed. -/
theorem puncture_balance_universal
  (c0a c0b c1a c1b c2a c2b c3a c3b c4a c4b c5a c5b : Bool)
  (c6a c6b c7a c7b c8a c8b c9a c9b c10a c10b c11a c11b : Bool)
  (c12a c12b c13a c13b c14a c14b c15a c15b c16a c16b c17a c17b : Bool)
  (c18a c18b c19a c19b c20a c20b c21a c21b c22a c22b c23a c23b : Bool)
  (c24a c24b c25a c25b c26a c26b c27a c27b c28a c28b c29a c29b : Bool)
  (c30a c30b c31a c31b c32a c32b c33a c33b c34a c34b c35a c35b : Bool)
  (c36a c36b c37a c37b c38a c38b c39a c39b c40a c40b c41a c41b : Bool)
  (c42a c42b c43a c43b c44a c44b c45a c45b c46a c46b c47a c47b : Bool)
  (c48a c48b c49a c49b c50a c50b c51a c51b c52a c52b c53a c53b : Bool)
  (c54a c54b c55a c55b c56a c56b c57a c57b c58a c58b c59a c59b : Bool) :
  let premise :=
    (allB
      [validCode c1a c1b, validCode c2a c2b, validCode c3a c3b, validCode c4a c4b,
       validCode c5a c5b, validCode c6a c6b, validCode c7a c7b, validCode c8a c8b,
       validCode c9a c9b, validCode c10a c10b, validCode c11a c11b, validCode c12a c12b,
       validCode c13a c13b, validCode c14a c14b, validCode c15a c15b, validCode c16a c16b,
       validCode c17a c17b, validCode c18a c18b, validCode c19a c19b, validCode c20a c20b,
       validCode c21a c21b, validCode c22a c22b, validCode c23a c23b, validCode c24a c24b,
       validCode c25a c25b, validCode c26a c26b, validCode c27a c27b, validCode c28a c28b,
       validCode c29a c29b, validCode c30a c30b, validCode c31a c31b, validCode c32a c32b,
       validCode c33a c33b, validCode c34a c34b, validCode c35a c35b, validCode c36a c36b,
       validCode c37a c37b, validCode c38a c38b, validCode c39a c39b, validCode c40a c40b,
       validCode c41a c41b, validCode c42a c42b, validCode c43a c43b, validCode c44a c44b,
       validCode c45a c45b, validCode c46a c46b, validCode c47a c47b, validCode c48a c48b,
       validCode c49a c49b, validCode c50a c50b, validCode c51a c51b, validCode c52a c52b,
       validCode c53a c53b, validCode c54a c54b, validCode c55a c55b, validCode c56a c56b,
       validCode c57a c57b, validCode c58a c58b, validCode c59a c59b]) &&
    (allB
      [!(sameCode c1a c1b c6a c6b), !(sameCode c1a c1b c27a c27b), !(sameCode c1a c1b c31a c31b), !(sameCode c1a c1b c34a c34b),
       !(sameCode c1a c1b c38a c38b), !(sameCode c1a c1b c56a c56b), !(sameCode c2a c2b c7a c7b), !(sameCode c2a c2b c28a c28b),
       !(sameCode c2a c2b c30a c30b), !(sameCode c2a c2b c32a c32b), !(sameCode c2a c2b c39a c39b), !(sameCode c2a c2b c57a c57b),
       !(sameCode c3a c3b c8a c8b), !(sameCode c3a c3b c29a c29b), !(sameCode c3a c3b c31a c31b), !(sameCode c3a c3b c33a c33b),
       !(sameCode c3a c3b c35a c35b), !(sameCode c3a c3b c58a c58b), !(sameCode c4a c4b c9a c9b), !(sameCode c4a c4b c25a c25b),
       !(sameCode c4a c4b c32a c32b), !(sameCode c4a c4b c34a c34b), !(sameCode c4a c4b c36a c36b), !(sameCode c4a c4b c59a c59b),
       !(sameCode c5a c5b c10a c10b), !(sameCode c5a c5b c32a c32b), !(sameCode c5a c5b c35a c35b), !(sameCode c5a c5b c36a c36b),
       !(sameCode c5a c5b c44a c44b), !(sameCode c6a c6b c11a c11b), !(sameCode c6a c6b c33a c33b), !(sameCode c6a c6b c36a c36b),
       !(sameCode c6a c6b c37a c37b), !(sameCode c6a c6b c40a c40b), !(sameCode c7a c7b c12a c12b), !(sameCode c7a c7b c34a c34b),
       !(sameCode c7a c7b c37a c37b), !(sameCode c7a c7b c38a c38b), !(sameCode c7a c7b c41a c41b), !(sameCode c8a c8b c13a c13b),
       !(sameCode c8a c8b c30a c30b), !(sameCode c8a c8b c38a c38b), !(sameCode c8a c8b c39a c39b), !(sameCode c8a c8b c42a c42b),
       !(sameCode c9a c9b c14a c14b), !(sameCode c9a c9b c31a c31b), !(sameCode c9a c9b c35a c35b), !(sameCode c9a c9b c39a c39b),
       !(sameCode c9a c9b c43a c43b), !(sameCode c10a c10b c15a c15b), !(sameCode c10a c10b c39a c39b), !(sameCode c10a c10b c40a c40b),
       !(sameCode c10a c10b c42a c42b), !(sameCode c10a c10b c48a c48b), !(sameCode c11a c11b c16a c16b), !(sameCode c11a c11b c35a c35b),
       !(sameCode c11a c11b c41a c41b), !(sameCode c11a c11b c43a c43b), !(sameCode c11a c11b c49a c49b), !(sameCode c12a c12b c17a c17b),
       !(sameCode c12a c12b c36a c36b), !(sameCode c12a c12b c42a c42b), !(sameCode c12a c12b c44a c44b), !(sameCode c12a c12b c45a c45b),
       !(sameCode c13a c13b c18a c18b), !(sameCode c13a c13b c37a c37b), !(sameCode c13a c13b c40a c40b), !(sameCode c13a c13b c43a c43b),
       !(sameCode c13a c13b c46a c46b), !(sameCode c14a c14b c19a c19b), !(sameCode c14a c14b c38a c38b), !(sameCode c14a c14b c41a c41b),
       !(sameCode c14a c14b c44a c44b), !(sameCode c14a c14b c47a c47b), !(sameCode c15a c15b c20a c20b), !(sameCode c15a c15b c43a c43b),
       !(sameCode c15a c15b c45a c45b), !(sameCode c15a c15b c49a c49b), !(sameCode c15a c15b c51a c51b), !(sameCode c16a c16b c21a c21b),
       !(sameCode c16a c16b c44a c44b), !(sameCode c16a c16b c45a c45b), !(sameCode c16a c16b c46a c46b), !(sameCode c16a c16b c52a c52b),
       !(sameCode c17a c17b c22a c22b), !(sameCode c17a c17b c40a c40b), !(sameCode c17a c17b c46a c46b), !(sameCode c17a c17b c47a c47b),
       !(sameCode c17a c17b c53a c53b), !(sameCode c18a c18b c23a c23b), !(sameCode c18a c18b c41a c41b), !(sameCode c18a c18b c47a c47b),
       !(sameCode c18a c18b c48a c48b), !(sameCode c18a c18b c54a c54b), !(sameCode c19a c19b c24a c24b), !(sameCode c19a c19b c42a c42b),
       !(sameCode c19a c19b c48a c48b), !(sameCode c19a c19b c49a c49b), !(sameCode c19a c19b c50a c50b), !(sameCode c20a c20b c25a c25b),
       !(sameCode c20a c20b c46a c46b), !(sameCode c20a c20b c50a c50b), !(sameCode c20a c20b c53a c53b), !(sameCode c20a c20b c57a c57b),
       !(sameCode c21a c21b c26a c26b), !(sameCode c21a c21b c47a c47b), !(sameCode c21a c21b c51a c51b), !(sameCode c21a c21b c54a c54b),
       !(sameCode c21a c21b c58a c58b), !(sameCode c22a c22b c27a c27b), !(sameCode c22a c22b c48a c48b), !(sameCode c22a c22b c50a c50b),
       !(sameCode c22a c22b c52a c52b), !(sameCode c22a c22b c59a c59b), !(sameCode c23a c23b c28a c28b), !(sameCode c23a c23b c49a c49b),
       !(sameCode c23a c23b c51a c51b), !(sameCode c23a c23b c53a c53b), !(sameCode c23a c23b c55a c55b), !(sameCode c24a c24b c29a c29b),
       !(sameCode c24a c24b c45a c45b), !(sameCode c24a c24b c52a c52b), !(sameCode c24a c24b c54a c54b), !(sameCode c24a c24b c56a c56b),
       !(sameCode c25a c25b c30a c30b), !(sameCode c25a c25b c52a c52b), !(sameCode c25a c25b c55a c55b), !(sameCode c25a c25b c56a c56b),
       !(sameCode c26a c26b c31a c31b), !(sameCode c26a c26b c53a c53b), !(sameCode c26a c26b c56a c56b), !(sameCode c26a c26b c57a c57b),
       !(sameCode c27a c27b c32a c32b), !(sameCode c27a c27b c54a c54b), !(sameCode c27a c27b c57a c57b), !(sameCode c27a c27b c58a c58b),
       !(sameCode c28a c28b c33a c33b), !(sameCode c28a c28b c50a c50b), !(sameCode c28a c28b c58a c58b), !(sameCode c28a c28b c59a c59b),
       !(sameCode c29a c29b c34a c34b), !(sameCode c29a c29b c51a c51b), !(sameCode c29a c29b c55a c55b), !(sameCode c29a c29b c59a c59b),
       !(sameCode c30a c30b c35a c35b), !(sameCode c30a c30b c59a c59b), !(sameCode c31a c31b c36a c36b), !(sameCode c31a c31b c55a c55b),
       !(sameCode c32a c32b c37a c37b), !(sameCode c32a c32b c56a c56b), !(sameCode c33a c33b c38a c38b), !(sameCode c33a c33b c57a c57b),
       !(sameCode c34a c34b c39a c39b), !(sameCode c34a c34b c58a c58b), !(sameCode c35a c35b c40a c40b), !(sameCode c36a c36b c41a c41b),
       !(sameCode c37a c37b c42a c42b), !(sameCode c38a c38b c43a c43b), !(sameCode c39a c39b c44a c44b), !(sameCode c40a c40b c45a c45b),
       !(sameCode c41a c41b c46a c46b), !(sameCode c42a c42b c47a c47b), !(sameCode c43a c43b c48a c48b), !(sameCode c44a c44b c49a c49b),
       !(sameCode c45a c45b c50a c50b), !(sameCode c46a c46b c51a c51b), !(sameCode c47a c47b c52a c52b), !(sameCode c48a c48b c53a c53b),
       !(sameCode c49a c49b c54a c54b), !(sameCode c50a c50b c55a c55b), !(sameCode c51a c51b c56a c56b), !(sameCode c52a c52b c57a c57b),
       !(sameCode c53a c53b c58a c58b), !(sameCode c54a c54b c59a c59b)])
  let balanced :=
    exactlyTwo6 (is0 c5a c5b) (is0 c26a c26b) (is0 c30a c30b) (is0 c33a c33b) (is0 c37a c37b) (is0 c55a c55b) &&
    exactlyTwo6 (is1 c5a c5b) (is1 c26a c26b) (is1 c30a c30b) (is1 c33a c33b) (is1 c37a c37b) (is1 c55a c55b) &&
    exactlyTwo6 (is2 c5a c5b) (is2 c26a c26b) (is2 c30a c30b) (is2 c33a c33b) (is2 c37a c37b) (is2 c55a c55b)
  ((!premise) || balanced) = true := by
  simp [validCode, sameCode, is0, is1, is2, allB, exactlyTwo6]
  bv_decide

/- With `c(1)=0` and `c(6)=1`, the punctured colourings are exactly the
16 assignments described by the four independent stars in the paper. -/
theorem normalized_puncture_classifier
  (c0a c0b c1a c1b c2a c2b c3a c3b c4a c4b c5a c5b : Bool)
  (c6a c6b c7a c7b c8a c8b c9a c9b c10a c10b c11a c11b : Bool)
  (c12a c12b c13a c13b c14a c14b c15a c15b c16a c16b c17a c17b : Bool)
  (c18a c18b c19a c19b c20a c20b c21a c21b c22a c22b c23a c23b : Bool)
  (c24a c24b c25a c25b c26a c26b c27a c27b c28a c28b c29a c29b : Bool)
  (c30a c30b c31a c31b c32a c32b c33a c33b c34a c34b c35a c35b : Bool)
  (c36a c36b c37a c37b c38a c38b c39a c39b c40a c40b c41a c41b : Bool)
  (c42a c42b c43a c43b c44a c44b c45a c45b c46a c46b c47a c47b : Bool)
  (c48a c48b c49a c49b c50a c50b c51a c51b c52a c52b c53a c53b : Bool)
  (c54a c54b c55a c55b c56a c56b c57a c57b c58a c58b c59a c59b : Bool) :
  let normalizedProper :=
    (allB
      [validCode c1a c1b, validCode c2a c2b, validCode c3a c3b, validCode c4a c4b,
       validCode c5a c5b, validCode c6a c6b, validCode c7a c7b, validCode c8a c8b,
       validCode c9a c9b, validCode c10a c10b, validCode c11a c11b, validCode c12a c12b,
       validCode c13a c13b, validCode c14a c14b, validCode c15a c15b, validCode c16a c16b,
       validCode c17a c17b, validCode c18a c18b, validCode c19a c19b, validCode c20a c20b,
       validCode c21a c21b, validCode c22a c22b, validCode c23a c23b, validCode c24a c24b,
       validCode c25a c25b, validCode c26a c26b, validCode c27a c27b, validCode c28a c28b,
       validCode c29a c29b, validCode c30a c30b, validCode c31a c31b, validCode c32a c32b,
       validCode c33a c33b, validCode c34a c34b, validCode c35a c35b, validCode c36a c36b,
       validCode c37a c37b, validCode c38a c38b, validCode c39a c39b, validCode c40a c40b,
       validCode c41a c41b, validCode c42a c42b, validCode c43a c43b, validCode c44a c44b,
       validCode c45a c45b, validCode c46a c46b, validCode c47a c47b, validCode c48a c48b,
       validCode c49a c49b, validCode c50a c50b, validCode c51a c51b, validCode c52a c52b,
       validCode c53a c53b, validCode c54a c54b, validCode c55a c55b, validCode c56a c56b,
       validCode c57a c57b, validCode c58a c58b, validCode c59a c59b]) &&
    (allB
      [!(sameCode c1a c1b c6a c6b), !(sameCode c1a c1b c27a c27b), !(sameCode c1a c1b c31a c31b), !(sameCode c1a c1b c34a c34b),
       !(sameCode c1a c1b c38a c38b), !(sameCode c1a c1b c56a c56b), !(sameCode c2a c2b c7a c7b), !(sameCode c2a c2b c28a c28b),
       !(sameCode c2a c2b c30a c30b), !(sameCode c2a c2b c32a c32b), !(sameCode c2a c2b c39a c39b), !(sameCode c2a c2b c57a c57b),
       !(sameCode c3a c3b c8a c8b), !(sameCode c3a c3b c29a c29b), !(sameCode c3a c3b c31a c31b), !(sameCode c3a c3b c33a c33b),
       !(sameCode c3a c3b c35a c35b), !(sameCode c3a c3b c58a c58b), !(sameCode c4a c4b c9a c9b), !(sameCode c4a c4b c25a c25b),
       !(sameCode c4a c4b c32a c32b), !(sameCode c4a c4b c34a c34b), !(sameCode c4a c4b c36a c36b), !(sameCode c4a c4b c59a c59b),
       !(sameCode c5a c5b c10a c10b), !(sameCode c5a c5b c32a c32b), !(sameCode c5a c5b c35a c35b), !(sameCode c5a c5b c36a c36b),
       !(sameCode c5a c5b c44a c44b), !(sameCode c6a c6b c11a c11b), !(sameCode c6a c6b c33a c33b), !(sameCode c6a c6b c36a c36b),
       !(sameCode c6a c6b c37a c37b), !(sameCode c6a c6b c40a c40b), !(sameCode c7a c7b c12a c12b), !(sameCode c7a c7b c34a c34b),
       !(sameCode c7a c7b c37a c37b), !(sameCode c7a c7b c38a c38b), !(sameCode c7a c7b c41a c41b), !(sameCode c8a c8b c13a c13b),
       !(sameCode c8a c8b c30a c30b), !(sameCode c8a c8b c38a c38b), !(sameCode c8a c8b c39a c39b), !(sameCode c8a c8b c42a c42b),
       !(sameCode c9a c9b c14a c14b), !(sameCode c9a c9b c31a c31b), !(sameCode c9a c9b c35a c35b), !(sameCode c9a c9b c39a c39b),
       !(sameCode c9a c9b c43a c43b), !(sameCode c10a c10b c15a c15b), !(sameCode c10a c10b c39a c39b), !(sameCode c10a c10b c40a c40b),
       !(sameCode c10a c10b c42a c42b), !(sameCode c10a c10b c48a c48b), !(sameCode c11a c11b c16a c16b), !(sameCode c11a c11b c35a c35b),
       !(sameCode c11a c11b c41a c41b), !(sameCode c11a c11b c43a c43b), !(sameCode c11a c11b c49a c49b), !(sameCode c12a c12b c17a c17b),
       !(sameCode c12a c12b c36a c36b), !(sameCode c12a c12b c42a c42b), !(sameCode c12a c12b c44a c44b), !(sameCode c12a c12b c45a c45b),
       !(sameCode c13a c13b c18a c18b), !(sameCode c13a c13b c37a c37b), !(sameCode c13a c13b c40a c40b), !(sameCode c13a c13b c43a c43b),
       !(sameCode c13a c13b c46a c46b), !(sameCode c14a c14b c19a c19b), !(sameCode c14a c14b c38a c38b), !(sameCode c14a c14b c41a c41b),
       !(sameCode c14a c14b c44a c44b), !(sameCode c14a c14b c47a c47b), !(sameCode c15a c15b c20a c20b), !(sameCode c15a c15b c43a c43b),
       !(sameCode c15a c15b c45a c45b), !(sameCode c15a c15b c49a c49b), !(sameCode c15a c15b c51a c51b), !(sameCode c16a c16b c21a c21b),
       !(sameCode c16a c16b c44a c44b), !(sameCode c16a c16b c45a c45b), !(sameCode c16a c16b c46a c46b), !(sameCode c16a c16b c52a c52b),
       !(sameCode c17a c17b c22a c22b), !(sameCode c17a c17b c40a c40b), !(sameCode c17a c17b c46a c46b), !(sameCode c17a c17b c47a c47b),
       !(sameCode c17a c17b c53a c53b), !(sameCode c18a c18b c23a c23b), !(sameCode c18a c18b c41a c41b), !(sameCode c18a c18b c47a c47b),
       !(sameCode c18a c18b c48a c48b), !(sameCode c18a c18b c54a c54b), !(sameCode c19a c19b c24a c24b), !(sameCode c19a c19b c42a c42b),
       !(sameCode c19a c19b c48a c48b), !(sameCode c19a c19b c49a c49b), !(sameCode c19a c19b c50a c50b), !(sameCode c20a c20b c25a c25b),
       !(sameCode c20a c20b c46a c46b), !(sameCode c20a c20b c50a c50b), !(sameCode c20a c20b c53a c53b), !(sameCode c20a c20b c57a c57b),
       !(sameCode c21a c21b c26a c26b), !(sameCode c21a c21b c47a c47b), !(sameCode c21a c21b c51a c51b), !(sameCode c21a c21b c54a c54b),
       !(sameCode c21a c21b c58a c58b), !(sameCode c22a c22b c27a c27b), !(sameCode c22a c22b c48a c48b), !(sameCode c22a c22b c50a c50b),
       !(sameCode c22a c22b c52a c52b), !(sameCode c22a c22b c59a c59b), !(sameCode c23a c23b c28a c28b), !(sameCode c23a c23b c49a c49b),
       !(sameCode c23a c23b c51a c51b), !(sameCode c23a c23b c53a c53b), !(sameCode c23a c23b c55a c55b), !(sameCode c24a c24b c29a c29b),
       !(sameCode c24a c24b c45a c45b), !(sameCode c24a c24b c52a c52b), !(sameCode c24a c24b c54a c54b), !(sameCode c24a c24b c56a c56b),
       !(sameCode c25a c25b c30a c30b), !(sameCode c25a c25b c52a c52b), !(sameCode c25a c25b c55a c55b), !(sameCode c25a c25b c56a c56b),
       !(sameCode c26a c26b c31a c31b), !(sameCode c26a c26b c53a c53b), !(sameCode c26a c26b c56a c56b), !(sameCode c26a c26b c57a c57b),
       !(sameCode c27a c27b c32a c32b), !(sameCode c27a c27b c54a c54b), !(sameCode c27a c27b c57a c57b), !(sameCode c27a c27b c58a c58b),
       !(sameCode c28a c28b c33a c33b), !(sameCode c28a c28b c50a c50b), !(sameCode c28a c28b c58a c58b), !(sameCode c28a c28b c59a c59b),
       !(sameCode c29a c29b c34a c34b), !(sameCode c29a c29b c51a c51b), !(sameCode c29a c29b c55a c55b), !(sameCode c29a c29b c59a c59b),
       !(sameCode c30a c30b c35a c35b), !(sameCode c30a c30b c59a c59b), !(sameCode c31a c31b c36a c36b), !(sameCode c31a c31b c55a c55b),
       !(sameCode c32a c32b c37a c37b), !(sameCode c32a c32b c56a c56b), !(sameCode c33a c33b c38a c38b), !(sameCode c33a c33b c57a c57b),
       !(sameCode c34a c34b c39a c39b), !(sameCode c34a c34b c58a c58b), !(sameCode c35a c35b c40a c40b), !(sameCode c36a c36b c41a c41b),
       !(sameCode c37a c37b c42a c42b), !(sameCode c38a c38b c43a c43b), !(sameCode c39a c39b c44a c44b), !(sameCode c40a c40b c45a c45b),
       !(sameCode c41a c41b c46a c46b), !(sameCode c42a c42b c47a c47b), !(sameCode c43a c43b c48a c48b), !(sameCode c44a c44b c49a c49b),
       !(sameCode c45a c45b c50a c50b), !(sameCode c46a c46b c51a c51b), !(sameCode c47a c47b c52a c52b), !(sameCode c48a c48b c53a c53b),
       !(sameCode c49a c49b c54a c54b), !(sameCode c50a c50b c55a c55b), !(sameCode c51a c51b c56a c56b), !(sameCode c52a c52b c57a c57b),
       !(sameCode c53a c53b c58a c58b), !(sameCode c54a c54b c59a c59b)]) &&
    (allB
      [is0 c1a c1b, is1 c6a c6b])
  let template :=
    allB
      [is0 c1a c1b, ((is1 c2a c2b) || (is2 c2a c2b)), ((is0 c3a c3b) || (is1 c3a c3b)), is2 c4a c4b,
       is1 c5a c5b, is1 c6a c6b, is0 c7a c7b, is2 c8a c8b,
       is1 c9a c9b, is2 c10a c10b, is0 c11a c11b, is1 c12a c12b,
       is1 c13a c13b, is0 c14a c14b, is0 c15a c15b, is1 c16a c16b,
       is2 c17a c17b, is0 c18a c18b, is2 c19a c19b, is2 c20a c20b,
       is0 c21a c21b, is0 c22a c22b, is2 c23a c23b, ((is0 c24a c24b) || (is1 c24a c24b)),
       is1 c25a c25b, is1 c26a c26b, is1 c27a c27b, is0 c28a c28b,
       is2 c29a c29b, is0 c30a c30b, is2 c31a c31b, is0 c32a c32b,
       is2 c33a c33b, is1 c34a c34b, is2 c35a c35b, is0 c36a c36b,
       is2 c37a c37b, is1 c38a c38b, is0 c39a c39b, is0 c40a c40b,
       ((is1 c41a c41b) || (is2 c41a c41b)), is0 c42a c42b, is2 c43a c43b, is2 c44a c44b,
       is2 c45a c45b, is0 c46a c46b, is1 c47a c47b, is1 c48a c48b,
       is1 c49a c49b, is1 c50a c50b, is1 c51a c51b, is2 c52a c52b,
       is0 c53a c53b, is2 c54a c54b, is0 c55a c55b, is2 c56a c56b,
       is0 c57a c57b, is2 c58a c58b, is1 c59a c59b]
  (normalizedProper == template) = true := by
  simp [validCode, sameCode, is0, is1, is2, allB]
  bv_decide

/- Equivalently, no valid three-colour assignment has zero or one bad edge.
This is the compact Boolean form of `q₃(G) ≥ 2`, and directly implies that
deleting any single edge leaves the graph non-three-colourable. -/
theorem q3_ge_two_encoded
  (c0a c0b c1a c1b c2a c2b c3a c3b c4a c4b c5a c5b : Bool)
  (c6a c6b c7a c7b c8a c8b c9a c9b c10a c10b c11a c11b : Bool)
  (c12a c12b c13a c13b c14a c14b c15a c15b c16a c16b c17a c17b : Bool)
  (c18a c18b c19a c19b c20a c20b c21a c21b c22a c22b c23a c23b : Bool)
  (c24a c24b c25a c25b c26a c26b c27a c27b c28a c28b c29a c29b : Bool)
  (c30a c30b c31a c31b c32a c32b c33a c33b c34a c34b c35a c35b : Bool)
  (c36a c36b c37a c37b c38a c38b c39a c39b c40a c40b c41a c41b : Bool)
  (c42a c42b c43a c43b c44a c44b c45a c45b c46a c46b c47a c47b : Bool)
  (c48a c48b c49a c49b c50a c50b c51a c51b c52a c52b c53a c53b : Bool)
  (c54a c54b c55a c55b c56a c56b c57a c57b c58a c58b c59a c59b : Bool) :
  ((allB
      [validCode c0a c0b, validCode c1a c1b, validCode c2a c2b, validCode c3a c3b,
       validCode c4a c4b, validCode c5a c5b, validCode c6a c6b, validCode c7a c7b,
       validCode c8a c8b, validCode c9a c9b, validCode c10a c10b, validCode c11a c11b,
       validCode c12a c12b, validCode c13a c13b, validCode c14a c14b, validCode c15a c15b,
       validCode c16a c16b, validCode c17a c17b, validCode c18a c18b, validCode c19a c19b,
       validCode c20a c20b, validCode c21a c21b, validCode c22a c22b, validCode c23a c23b,
       validCode c24a c24b, validCode c25a c25b, validCode c26a c26b, validCode c27a c27b,
       validCode c28a c28b, validCode c29a c29b, validCode c30a c30b, validCode c31a c31b,
       validCode c32a c32b, validCode c33a c33b, validCode c34a c34b, validCode c35a c35b,
       validCode c36a c36b, validCode c37a c37b, validCode c38a c38b, validCode c39a c39b,
       validCode c40a c40b, validCode c41a c41b, validCode c42a c42b, validCode c43a c43b,
       validCode c44a c44b, validCode c45a c45b, validCode c46a c46b, validCode c47a c47b,
       validCode c48a c48b, validCode c49a c49b, validCode c50a c50b, validCode c51a c51b,
       validCode c52a c52b, validCode c53a c53b, validCode c54a c54b, validCode c55a c55b,
       validCode c56a c56b, validCode c57a c57b, validCode c58a c58b, validCode c59a c59b]) &&
    atMostOne
      [sameCode c0a c0b c5a c5b, sameCode c0a c0b c26a c26b, sameCode c0a c0b c30a c30b, sameCode c0a c0b c33a c33b,
       sameCode c0a c0b c37a c37b, sameCode c0a c0b c55a c55b, sameCode c1a c1b c6a c6b, sameCode c1a c1b c27a c27b,
       sameCode c1a c1b c31a c31b, sameCode c1a c1b c34a c34b, sameCode c1a c1b c38a c38b, sameCode c1a c1b c56a c56b,
       sameCode c2a c2b c7a c7b, sameCode c2a c2b c28a c28b, sameCode c2a c2b c30a c30b, sameCode c2a c2b c32a c32b,
       sameCode c2a c2b c39a c39b, sameCode c2a c2b c57a c57b, sameCode c3a c3b c8a c8b, sameCode c3a c3b c29a c29b,
       sameCode c3a c3b c31a c31b, sameCode c3a c3b c33a c33b, sameCode c3a c3b c35a c35b, sameCode c3a c3b c58a c58b,
       sameCode c4a c4b c9a c9b, sameCode c4a c4b c25a c25b, sameCode c4a c4b c32a c32b, sameCode c4a c4b c34a c34b,
       sameCode c4a c4b c36a c36b, sameCode c4a c4b c59a c59b, sameCode c5a c5b c10a c10b, sameCode c5a c5b c32a c32b,
       sameCode c5a c5b c35a c35b, sameCode c5a c5b c36a c36b, sameCode c5a c5b c44a c44b, sameCode c6a c6b c11a c11b,
       sameCode c6a c6b c33a c33b, sameCode c6a c6b c36a c36b, sameCode c6a c6b c37a c37b, sameCode c6a c6b c40a c40b,
       sameCode c7a c7b c12a c12b, sameCode c7a c7b c34a c34b, sameCode c7a c7b c37a c37b, sameCode c7a c7b c38a c38b,
       sameCode c7a c7b c41a c41b, sameCode c8a c8b c13a c13b, sameCode c8a c8b c30a c30b, sameCode c8a c8b c38a c38b,
       sameCode c8a c8b c39a c39b, sameCode c8a c8b c42a c42b, sameCode c9a c9b c14a c14b, sameCode c9a c9b c31a c31b,
       sameCode c9a c9b c35a c35b, sameCode c9a c9b c39a c39b, sameCode c9a c9b c43a c43b, sameCode c10a c10b c15a c15b,
       sameCode c10a c10b c39a c39b, sameCode c10a c10b c40a c40b, sameCode c10a c10b c42a c42b, sameCode c10a c10b c48a c48b,
       sameCode c11a c11b c16a c16b, sameCode c11a c11b c35a c35b, sameCode c11a c11b c41a c41b, sameCode c11a c11b c43a c43b,
       sameCode c11a c11b c49a c49b, sameCode c12a c12b c17a c17b, sameCode c12a c12b c36a c36b, sameCode c12a c12b c42a c42b,
       sameCode c12a c12b c44a c44b, sameCode c12a c12b c45a c45b, sameCode c13a c13b c18a c18b, sameCode c13a c13b c37a c37b,
       sameCode c13a c13b c40a c40b, sameCode c13a c13b c43a c43b, sameCode c13a c13b c46a c46b, sameCode c14a c14b c19a c19b,
       sameCode c14a c14b c38a c38b, sameCode c14a c14b c41a c41b, sameCode c14a c14b c44a c44b, sameCode c14a c14b c47a c47b,
       sameCode c15a c15b c20a c20b, sameCode c15a c15b c43a c43b, sameCode c15a c15b c45a c45b, sameCode c15a c15b c49a c49b,
       sameCode c15a c15b c51a c51b, sameCode c16a c16b c21a c21b, sameCode c16a c16b c44a c44b, sameCode c16a c16b c45a c45b,
       sameCode c16a c16b c46a c46b, sameCode c16a c16b c52a c52b, sameCode c17a c17b c22a c22b, sameCode c17a c17b c40a c40b,
       sameCode c17a c17b c46a c46b, sameCode c17a c17b c47a c47b, sameCode c17a c17b c53a c53b, sameCode c18a c18b c23a c23b,
       sameCode c18a c18b c41a c41b, sameCode c18a c18b c47a c47b, sameCode c18a c18b c48a c48b, sameCode c18a c18b c54a c54b,
       sameCode c19a c19b c24a c24b, sameCode c19a c19b c42a c42b, sameCode c19a c19b c48a c48b, sameCode c19a c19b c49a c49b,
       sameCode c19a c19b c50a c50b, sameCode c20a c20b c25a c25b, sameCode c20a c20b c46a c46b, sameCode c20a c20b c50a c50b,
       sameCode c20a c20b c53a c53b, sameCode c20a c20b c57a c57b, sameCode c21a c21b c26a c26b, sameCode c21a c21b c47a c47b,
       sameCode c21a c21b c51a c51b, sameCode c21a c21b c54a c54b, sameCode c21a c21b c58a c58b, sameCode c22a c22b c27a c27b,
       sameCode c22a c22b c48a c48b, sameCode c22a c22b c50a c50b, sameCode c22a c22b c52a c52b, sameCode c22a c22b c59a c59b,
       sameCode c23a c23b c28a c28b, sameCode c23a c23b c49a c49b, sameCode c23a c23b c51a c51b, sameCode c23a c23b c53a c53b,
       sameCode c23a c23b c55a c55b, sameCode c24a c24b c29a c29b, sameCode c24a c24b c45a c45b, sameCode c24a c24b c52a c52b,
       sameCode c24a c24b c54a c54b, sameCode c24a c24b c56a c56b, sameCode c25a c25b c30a c30b, sameCode c25a c25b c52a c52b,
       sameCode c25a c25b c55a c55b, sameCode c25a c25b c56a c56b, sameCode c26a c26b c31a c31b, sameCode c26a c26b c53a c53b,
       sameCode c26a c26b c56a c56b, sameCode c26a c26b c57a c57b, sameCode c27a c27b c32a c32b, sameCode c27a c27b c54a c54b,
       sameCode c27a c27b c57a c57b, sameCode c27a c27b c58a c58b, sameCode c28a c28b c33a c33b, sameCode c28a c28b c50a c50b,
       sameCode c28a c28b c58a c58b, sameCode c28a c28b c59a c59b, sameCode c29a c29b c34a c34b, sameCode c29a c29b c51a c51b,
       sameCode c29a c29b c55a c55b, sameCode c29a c29b c59a c59b, sameCode c30a c30b c35a c35b, sameCode c30a c30b c59a c59b,
       sameCode c31a c31b c36a c36b, sameCode c31a c31b c55a c55b, sameCode c32a c32b c37a c37b, sameCode c32a c32b c56a c56b,
       sameCode c33a c33b c38a c38b, sameCode c33a c33b c57a c57b, sameCode c34a c34b c39a c39b, sameCode c34a c34b c58a c58b,
       sameCode c35a c35b c40a c40b, sameCode c36a c36b c41a c41b, sameCode c37a c37b c42a c42b, sameCode c38a c38b c43a c43b,
       sameCode c39a c39b c44a c44b, sameCode c40a c40b c45a c45b, sameCode c41a c41b c46a c46b, sameCode c42a c42b c47a c47b,
       sameCode c43a c43b c48a c48b, sameCode c44a c44b c49a c49b, sameCode c45a c45b c50a c50b, sameCode c46a c46b c51a c51b,
       sameCode c47a c47b c52a c52b, sameCode c48a c48b c53a c53b, sameCode c49a c49b c54a c54b, sameCode c50a c50b c55a c55b,
       sameCode c51a c51b c56a c56b, sameCode c52a c52b c57a c57b, sameCode c53a c53b c58a c58b, sameCode c54a c54b c59a c59b]) = false := by
  simp (config := { maxSteps := 1000000 }) only
    [validCode, sameCode, allB, atMostOne, atMostOneAux]
  bv_decide

abbrev V := Fin 60

def edges : List (Nat × Nat) :=
  [(0, 5), (0, 26), (0, 30), (0, 33),
   (0, 37), (0, 55), (1, 6), (1, 27),
   (1, 31), (1, 34), (1, 38), (1, 56),
   (2, 7), (2, 28), (2, 30), (2, 32),
   (2, 39), (2, 57), (3, 8), (3, 29),
   (3, 31), (3, 33), (3, 35), (3, 58),
   (4, 9), (4, 25), (4, 32), (4, 34),
   (4, 36), (4, 59), (5, 10), (5, 32),
   (5, 35), (5, 36), (5, 44), (6, 11),
   (6, 33), (6, 36), (6, 37), (6, 40),
   (7, 12), (7, 34), (7, 37), (7, 38),
   (7, 41), (8, 13), (8, 30), (8, 38),
   (8, 39), (8, 42), (9, 14), (9, 31),
   (9, 35), (9, 39), (9, 43), (10, 15),
   (10, 39), (10, 40), (10, 42), (10, 48),
   (11, 16), (11, 35), (11, 41), (11, 43),
   (11, 49), (12, 17), (12, 36), (12, 42),
   (12, 44), (12, 45), (13, 18), (13, 37),
   (13, 40), (13, 43), (13, 46), (14, 19),
   (14, 38), (14, 41), (14, 44), (14, 47),
   (15, 20), (15, 43), (15, 45), (15, 49),
   (15, 51), (16, 21), (16, 44), (16, 45),
   (16, 46), (16, 52), (17, 22), (17, 40),
   (17, 46), (17, 47), (17, 53), (18, 23),
   (18, 41), (18, 47), (18, 48), (18, 54),
   (19, 24), (19, 42), (19, 48), (19, 49),
   (19, 50), (20, 25), (20, 46), (20, 50),
   (20, 53), (20, 57), (21, 26), (21, 47),
   (21, 51), (21, 54), (21, 58), (22, 27),
   (22, 48), (22, 50), (22, 52), (22, 59),
   (23, 28), (23, 49), (23, 51), (23, 53),
   (23, 55), (24, 29), (24, 45), (24, 52),
   (24, 54), (24, 56), (25, 30), (25, 52),
   (25, 55), (25, 56), (26, 31), (26, 53),
   (26, 56), (26, 57), (27, 32), (27, 54),
   (27, 57), (27, 58), (28, 33), (28, 50),
   (28, 58), (28, 59), (29, 34), (29, 51),
   (29, 55), (29, 59), (30, 35), (30, 59),
   (31, 36), (31, 55), (32, 37), (32, 56),
   (33, 38), (33, 57), (34, 39), (34, 58),
   (35, 40), (36, 41), (37, 42), (38, 43),
   (39, 44), (40, 45), (41, 46), (42, 47),
   (43, 48), (44, 49), (45, 50), (46, 51),
   (47, 52), (48, 53), (49, 54), (50, 55),
   (51, 56), (52, 57), (53, 58), (54, 59)]

def graphEdges : List (V × V) :=
  [(0, 5), (0, 26), (0, 30), (0, 33),
   (0, 37), (0, 55), (1, 6), (1, 27),
   (1, 31), (1, 34), (1, 38), (1, 56),
   (2, 7), (2, 28), (2, 30), (2, 32),
   (2, 39), (2, 57), (3, 8), (3, 29),
   (3, 31), (3, 33), (3, 35), (3, 58),
   (4, 9), (4, 25), (4, 32), (4, 34),
   (4, 36), (4, 59), (5, 10), (5, 32),
   (5, 35), (5, 36), (5, 44), (6, 11),
   (6, 33), (6, 36), (6, 37), (6, 40),
   (7, 12), (7, 34), (7, 37), (7, 38),
   (7, 41), (8, 13), (8, 30), (8, 38),
   (8, 39), (8, 42), (9, 14), (9, 31),
   (9, 35), (9, 39), (9, 43), (10, 15),
   (10, 39), (10, 40), (10, 42), (10, 48),
   (11, 16), (11, 35), (11, 41), (11, 43),
   (11, 49), (12, 17), (12, 36), (12, 42),
   (12, 44), (12, 45), (13, 18), (13, 37),
   (13, 40), (13, 43), (13, 46), (14, 19),
   (14, 38), (14, 41), (14, 44), (14, 47),
   (15, 20), (15, 43), (15, 45), (15, 49),
   (15, 51), (16, 21), (16, 44), (16, 45),
   (16, 46), (16, 52), (17, 22), (17, 40),
   (17, 46), (17, 47), (17, 53), (18, 23),
   (18, 41), (18, 47), (18, 48), (18, 54),
   (19, 24), (19, 42), (19, 48), (19, 49),
   (19, 50), (20, 25), (20, 46), (20, 50),
   (20, 53), (20, 57), (21, 26), (21, 47),
   (21, 51), (21, 54), (21, 58), (22, 27),
   (22, 48), (22, 50), (22, 52), (22, 59),
   (23, 28), (23, 49), (23, 51), (23, 53),
   (23, 55), (24, 29), (24, 45), (24, 52),
   (24, 54), (24, 56), (25, 30), (25, 52),
   (25, 55), (25, 56), (26, 31), (26, 53),
   (26, 56), (26, 57), (27, 32), (27, 54),
   (27, 57), (27, 58), (28, 33), (28, 50),
   (28, 58), (28, 59), (29, 34), (29, 51),
   (29, 55), (29, 59), (30, 35), (30, 59),
   (31, 36), (31, 55), (32, 37), (32, 56),
   (33, 38), (33, 57), (34, 39), (34, 58),
   (35, 40), (36, 41), (37, 42), (38, 43),
   (39, 44), (40, 45), (41, 46), (42, 47),
   (43, 48), (44, 49), (45, 50), (46, 51),
   (47, 52), (48, 53), (49, 54), (50, 55),
   (51, 56), (52, 57), (53, 58), (54, 59)]

def graphEdgesAsNats : List (Nat × Nat) :=
  graphEdges.map fun e => (e.1.val, e.2.val)

theorem edge_tables_agree : graphEdgesAsNats = edges := by
  native_decide

def vertexWitnesses : Array (Array Nat) := #[
  #[0, 0, 1, 0, 2, 1, 1, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2, 2, 0, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 2, 0, 2, 0, 2, 1],
  #[0, 0, 2, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 2, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2, 1, 2, 0, 2, 0],
  #[0, 1, 0, 0, 1, 1, 2, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 1, 1, 0, 1, 0, 0, 0, 1, 2, 2, 2, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 0, 2, 2, 1, 0, 2, 0, 1, 2, 2, 1, 1, 2, 0, 1, 0],
  #[0, 0, 2, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 0, 1, 2, 0, 1, 2, 2, 0, 1, 2, 1, 1, 2, 2, 1, 0, 0, 0, 0, 2, 1, 2, 1, 2, 0, 0, 1, 2, 0, 1, 2],
  #[0, 1, 0, 2, 0, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2, 1, 2, 0, 2, 0, 0, 0, 2, 0, 2, 1, 1, 0, 2, 1, 2, 0, 2, 1, 0, 0, 2, 1, 0, 2, 1, 0, 2, 2, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 0],
  #[0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 0, 1, 2, 0, 0, 2, 0, 0, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2, 0, 2, 2, 2, 0, 2, 1, 1],
  #[0, 0, 1, 1, 2, 1, 0, 0, 0, 1, 0, 2, 1, 2, 2, 2, 1, 2, 0, 0, 1, 0, 0, 2, 1, 0, 1, 1, 0, 0, 2, 2, 0, 2, 1, 0, 0, 1, 1, 2, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1],
  #[0, 2, 2, 1, 1, 1, 0, 0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 1, 1, 2, 2, 0, 0, 2, 1, 1, 2, 1, 0, 0, 2, 0, 0, 2, 2, 1, 1, 2, 1, 1, 0, 2, 1, 2, 2, 1, 0, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0],
  #[0, 2, 1, 1, 0, 1, 0, 0, 0, 1, 2, 2, 1, 2, 0, 1, 1, 2, 0, 2, 2, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 0, 2, 2, 1, 0, 2, 1, 1, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0, 1, 2, 2, 0, 2, 2, 0, 0, 2, 1],
  #[0, 0, 1, 2, 2, 1, 2, 0, 0, 0, 0, 1, 1, 2, 1, 1, 2, 2, 1, 0, 2, 1, 0, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0, 1, 1, 0, 0, 1, 2, 2, 1, 2, 2, 0, 0, 0, 0, 0, 2, 2, 1, 2, 1, 1, 0, 2, 1, 0, 0, 1],
  #[0, 2, 1, 2, 0, 1, 0, 2, 1, 2, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 2, 1, 0, 0, 1, 1, 2, 1, 2, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 0, 1, 0, 2, 1, 2, 2, 1, 0, 2, 1, 1, 2, 2, 1, 0, 2, 0, 0, 0, 1],
  #[0, 0, 1, 2, 1, 1, 2, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2, 2, 1, 2, 0, 0, 0, 2, 1, 2, 1, 2, 1, 0, 1, 2, 0, 0, 1, 2, 0, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 0, 2, 1, 1, 2, 2, 1, 0, 0, 0],
  #[0, 2, 2, 0, 1, 1, 0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 2, 2, 2, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1, 1, 1, 0, 1, 0, 2, 2, 2, 0, 1, 1, 0, 1, 2, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 2, 1, 0, 2, 2],
  #[0, 1, 2, 2, 1, 1, 0, 1, 0, 2, 0, 1, 0, 0, 1, 1, 0, 2, 2, 2, 2, 2, 0, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 1, 1, 0, 1, 0, 2, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 2, 0, 1, 2],
  #[0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 1, 1, 2, 1, 1, 2, 0, 0, 2, 0, 1, 2, 1, 0, 2, 2, 0, 0, 2, 1, 1, 1, 1, 0, 2, 0, 2, 2, 1, 0, 2, 0, 0, 0, 2, 0, 2, 1, 1, 1, 2, 0],
  #[0, 1, 1, 2, 1, 1, 0, 0, 1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 2, 1, 1, 2, 1, 1, 0, 0, 1, 2, 2, 1, 2, 0, 0, 1, 2, 0, 2, 1, 2, 0, 1, 1, 0, 1, 2, 2, 2, 1, 0, 0, 0, 0, 2, 2, 1, 2, 2, 0, 0, 0],
  #[0, 2, 0, 0, 1, 1, 0, 2, 2, 0, 2, 1, 1, 0, 2, 0, 0, 0, 2, 1, 2, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 1, 2, 2, 0, 2, 2, 1, 0, 1, 1, 0, 0, 2, 0, 2, 1, 1, 0, 2, 0, 2, 2, 1, 1, 2, 1, 1, 2, 0],
  #[0, 1, 2, 1, 1, 1, 0, 1, 2, 2, 2, 2, 0, 0, 1, 0, 0, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 2, 2, 0, 2, 2, 0, 0, 1, 0, 1, 1, 2, 2, 2, 0, 0, 1, 0, 1, 2, 2, 0, 1, 2, 0, 0, 2],
  #[0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 2, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 2, 1, 0, 2, 1, 1, 2, 1, 0, 2, 0, 0, 0, 1, 1, 2, 2, 2, 2, 0, 1, 1, 1, 0, 1, 2, 2],
  #[0, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 0, 2, 0, 0, 1, 0, 0, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 2, 1, 2, 2, 0, 1, 2, 1, 0, 1, 2],
  #[0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 2, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0, 1, 0, 1, 2, 2, 0, 1, 2, 1, 0, 2, 2, 0, 0, 2, 1, 0, 1, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 0],
  #[0, 2, 0, 2, 0, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2, 1, 2, 0, 2, 0, 0, 0, 2, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 2, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 0, 2, 0, 2, 0, 1],
  #[0, 0, 2, 0, 2, 1, 1, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0, 2, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 2, 0, 2, 1, 2, 0, 2, 0],
  #[0, 2, 2, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 0, 0, 0, 2, 1, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 1, 1, 0, 2, 1, 0, 2, 2, 1, 0, 2, 0],
  #[0, 1, 0, 0, 1, 1, 2, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 1, 1, 0, 1, 0, 0, 2, 1, 0, 2, 2, 1, 2, 2, 1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 0, 2, 2, 1, 0, 2, 0, 1, 0, 2, 1, 1, 0, 2, 1, 0],
  #[0, 2, 1, 1, 0, 1, 0, 0, 0, 1, 0, 2, 1, 2, 2, 2, 1, 2, 0, 0, 1, 0, 0, 2, 1, 0, 1, 1, 0, 0, 2, 0, 2, 2, 1, 0, 2, 1, 1, 2, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 1, 0, 0, 2, 1],
  #[0, 0, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0, 1, 2, 0, 2, 2, 2, 0, 2, 1, 1, 0, 1, 1, 2, 0, 1, 0, 0, 1, 1, 2, 2, 1, 2, 0, 1, 1, 0, 0, 2],
  #[0, 1, 1, 2, 0, 1, 0, 0, 1, 1, 2, 2, 1, 2, 0, 1, 1, 2, 0, 2, 2, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0, 1, 2, 2, 0, 2, 2, 0, 0, 1, 1],
  #[0, 0, 1, 1, 2, 1, 1, 0, 0, 1, 0, 2, 2, 1, 2, 2, 1, 1, 2, 0, 1, 2, 0, 0, 1, 0, 1, 1, 0, 0, 2, 2, 0, 2, 1, 0, 0, 2, 1, 2, 2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 0, 1, 2, 0, 0, 1],
  #[0, 2, 2, 1, 1, 1, 0, 1, 2, 2, 0, 2, 0, 0, 1, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 2, 0, 1, 2, 0, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 1, 0, 0, 1, 1, 0, 2, 2],
  #[0, 2, 1, 0, 1, 1, 0, 2, 1, 0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 2, 2, 1, 0, 2, 1, 0, 2, 2, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 2, 1, 0, 2, 2],
  #[0, 1, 2, 0, 1, 1, 0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 2, 2, 2, 2, 2, 0, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 1, 0, 1, 2, 2, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 2, 0, 1, 2],
  #[0, 1, 0, 2, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 2, 0, 1, 2, 2, 1, 2, 2, 1, 0, 0, 1, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 0, 0, 0, 1, 0, 1, 2, 2, 2, 1, 0],
  #[0, 2, 0, 2, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 1, 1, 0, 0, 2, 0, 2, 1, 1, 0, 2, 0, 0, 0, 2, 1, 1, 1, 1, 1, 2, 0, 2, 2, 0, 1, 2, 0, 0, 2, 2, 0, 1, 2, 1, 1, 1, 0],
  #[0, 2, 1, 2, 1, 1, 0, 2, 1, 2, 2, 2, 1, 0, 1, 0, 0, 0, 1, 2, 2, 1, 2, 0, 0, 0, 2, 1, 2, 1, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1, 0, 0, 1, 2, 2, 1, 2, 0, 1, 0, 2, 1, 1, 2, 2, 1, 0, 0, 0],
  #[0, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 2, 1, 1, 0, 1, 1, 2, 0, 2, 2, 0, 0, 1, 0, 0, 2, 2, 0, 1, 1, 1, 0, 2, 2, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 2, 0, 1, 1, 0, 1, 2, 2, 0, 1, 2, 1, 0, 1, 2],
  #[0, 2, 2, 1, 2, 1, 0, 0, 2, 1, 2, 1, 1, 0, 0, 1, 0, 0, 1, 1, 2, 1, 2, 2, 0, 0, 2, 1, 1, 2, 1, 0, 0, 2, 1, 0, 0, 1, 1, 0, 1, 2, 0, 2, 2, 2, 1, 2, 0, 0, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0],
  #[0, 2, 0, 0, 1, 1, 1, 2, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 1, 2, 2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 1, 1, 2, 1, 1, 2, 0],
  #[0, 1, 2, 1, 1, 1, 0, 0, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 2, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 2, 2, 0, 2, 1, 0, 0, 1, 1, 0, 1, 2, 2, 2, 1, 0, 1, 0, 1, 2, 2, 0, 1, 2, 0, 0, 2],
  #[0, 2, 0, 1, 0, 1, 0, 2, 2, 1, 2, 1, 1, 0, 2, 1, 2, 0, 2, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 2, 1, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 2, 2],
  #[0, 2, 2, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 2, 2, 0, 2, 0, 0, 0, 2, 1, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 2, 0, 1, 0, 2, 1, 1, 2, 2, 1, 0, 2, 0],
  #[0, 1, 0, 0, 1, 1, 2, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 2, 1, 2, 2, 1, 0, 2, 0, 1, 0, 1, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 2, 1, 0, 2, 1, 0],
  #[0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 1, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 2, 0, 1, 2, 1, 0, 2, 2, 0, 0, 2, 1, 0, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 2, 0],
  #[0, 2, 0, 2, 0, 1, 0, 2, 1, 1, 0, 2, 1, 0, 2, 2, 1, 0, 2, 0, 0, 2, 2, 0, 1, 1, 1, 1, 2, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 0, 0, 0, 2, 1, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1],
  #[0, 0, 2, 0, 2, 1, 1, 0, 2, 1, 2, 0, 2, 1, 0, 0, 2, 1, 0, 2, 1, 0, 2, 2, 0, 0, 1, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2, 1, 2, 0, 2, 0],
  #[0, 0, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 1, 1, 2, 0, 1, 2, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2, 0, 2, 2, 2, 0, 2, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 2, 1, 2, 2, 0, 1, 2, 0, 0, 2],
  #[0, 1, 1, 2, 0, 1, 0, 0, 1, 1, 2, 2, 1, 2, 0, 1, 1, 0, 0, 2, 0, 0, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0, 1, 2, 0, 2, 2, 2, 0, 2, 1, 1],
  #[0, 0, 1, 1, 2, 1, 1, 0, 0, 1, 0, 2, 2, 1, 2, 2, 1, 1, 0, 0, 1, 0, 0, 2, 1, 0, 1, 1, 0, 0, 2, 2, 0, 2, 1, 0, 0, 2, 1, 2, 2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1],
  #[0, 2, 2, 1, 1, 1, 0, 1, 2, 2, 0, 2, 0, 0, 1, 2, 0, 1, 1, 2, 1, 1, 2, 2, 0, 0, 2, 1, 1, 2, 1, 0, 0, 2, 0, 0, 2, 2, 0, 1, 2, 0, 1, 1, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0],
  #[0, 2, 1, 1, 0, 1, 0, 0, 0, 1, 0, 2, 1, 2, 2, 1, 1, 2, 0, 0, 2, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 0, 2, 2, 1, 0, 2, 1, 1, 2, 1, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 2, 2, 0, 2, 2, 0, 0, 2, 1],
  #[0, 1, 2, 2, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 0, 0, 1, 2, 0, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 0, 0, 0, 1, 0, 1, 2, 2, 0, 1, 2],
  #[0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 2, 0, 1, 2, 1, 0, 2, 2, 0, 0, 2, 1, 1, 1, 1, 1, 2, 0, 2, 2, 0, 1, 2, 0, 0, 0, 2, 0, 1, 1, 1, 1, 2, 0],
  #[0, 2, 1, 2, 0, 1, 0, 2, 1, 2, 2, 2, 1, 0, 1, 0, 0, 0, 1, 2, 2, 1, 2, 0, 1, 1, 2, 1, 2, 0, 2, 0, 2, 1, 1, 0, 2, 1, 0, 0, 1, 0, 0, 1, 2, 2, 1, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 0, 1],
  #[0, 0, 1, 2, 1, 1, 2, 0, 1, 2, 2, 1, 1, 2, 0, 1, 0, 0, 0, 2, 2, 1, 2, 1, 0, 0, 2, 1, 2, 1, 2, 1, 0, 1, 2, 0, 0, 1, 2, 0, 1, 2, 0, 0, 2, 2, 1, 2, 1, 0, 0, 0, 1, 0, 2, 2, 1, 0, 0, 0],
  #[0, 2, 2, 0, 1, 1, 0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 2, 2, 2, 2, 1, 0, 1, 0, 0, 2, 1, 0, 1, 1, 1, 0, 1, 0, 2, 2, 2, 0, 1, 1, 0, 1, 2, 2, 2, 1, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0, 2, 2],
  #[0, 2, 0, 0, 1, 1, 0, 2, 2, 0, 2, 1, 1, 0, 2, 1, 2, 0, 2, 1, 0, 0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 1, 2, 2, 0, 2, 2, 1, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0, 2, 2, 2, 0, 1, 1, 0, 0, 1, 2, 0],
  #[0, 1, 2, 1, 1, 1, 0, 1, 2, 2, 2, 2, 0, 0, 1, 0, 0, 2, 1, 2, 2, 1, 1, 0, 1, 0, 2, 2, 1, 0, 1, 0, 0, 2, 2, 0, 2, 2, 0, 0, 1, 0, 1, 1, 2, 2, 1, 0, 0, 1, 0, 2, 2, 1, 0, 1, 0, 0, 0, 2],
  #[0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 2, 2, 1, 2, 2, 1, 0, 0, 1, 0, 0, 2, 2, 2, 1, 1, 0, 1, 0, 2, 2, 1, 0, 2, 1, 1, 2, 1, 0, 2, 0, 0, 0, 1, 0, 2, 2, 2, 2, 1, 1, 0, 1, 0, 0, 0, 2],
  #[0, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 0, 0, 0, 2, 2, 1, 1, 1, 1, 0, 2, 2, 2, 0, 2, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 1, 1, 2, 1, 0, 0, 0],
  #[0, 1, 1, 2, 1, 1, 0, 0, 1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 2, 2, 1, 2, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 0, 1, 2, 0, 2, 1, 2, 0, 1, 1, 0, 1, 2, 2, 2, 1, 0, 1, 0, 1, 2, 2, 0, 1, 2, 0, 0, 0]
]

def edgeOKAway (deleted : Nat) (row : Array Nat) (e : Nat × Nat) : Bool :=
  let (u, v) := e
  (u == deleted) || (v == deleted) ||
    ((decide (row.getD u 3 < 3)) && (decide (row.getD v 3 < 3)) &&
      !(row.getD u 3 == row.getD v 3))

def witnessRowOK (deleted : Nat) : Bool :=
  match vertexWitnesses[deleted]? with
  | none => false
  | some row =>
      (row.size == 60) &&
      allB (edges.map (edgeOKAway deleted row))

def allVertexWitnessesOK : Bool :=
  allB ((List.range 60).map witnessRowOK)

/- Positive certificate only: sixty explicitly stored colourings, one for
each deleted vertex. -/
theorem all_vertex_deletion_witnesses : allVertexWitnessesOK = true := by
  native_decide

def defectColouring : Array Nat :=
  #[1, 0, 1, 0, 2, 1, 1, 0, 2, 1, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2,
    2, 0, 0, 2, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0,
    0, 1, 0, 2, 2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 2, 0, 2, 0, 2, 1]

def defectCount : Nat :=
  (edges.filter fun e =>
    defectColouring.getD e.1 3 == defectColouring.getD e.2 3).length

def defectWitnessWellFormed : Bool :=
  (defectColouring.size == 60) &&
    allB (defectColouring.toList.map fun x => decide (x < 3))

/- Positive certificate for the matching upper bound `q₃(G) ≤ 2`. -/
theorem q3_le_two_witness :
    defectWitnessWellFormed = true ∧ defectCount = 2 := by
  native_decide

/-! ## Proposition-level semantic bridge -/

inductive Colour3 where
  | red | green | blue
  deriving DecidableEq, Repr

def bitA : Colour3 → Bool
  | .red => false
  | .green => true
  | .blue => false

def bitB : Colour3 → Bool
  | .red => false
  | .green => false
  | .blue => true

@[simp] theorem valid_encoding (x : Colour3) :
    validCode (bitA x) (bitB x) = true := by
  cases x <;> decide

@[simp] theorem same_encoding (x y : Colour3) :
    sameCode (bitA x) (bitB x) (bitA y) (bitB y) = decide (x = y) := by
  cases x <;> cases y <;> decide

@[simp] theorem is0_encoding (x : Colour3) :
    is0 (bitA x) (bitB x) = decide (x = .red) := by
  cases x <;> decide

@[simp] theorem is1_encoding (x : Colour3) :
    is1 (bitA x) (bitB x) = decide (x = .green) := by
  cases x <;> decide

@[simp] theorem is2_encoding (x : Colour3) :
    is2 (bitA x) (bitB x) = decide (x = .blue) := by
  cases x <;> decide

def conflicts (c : V → Colour3) : List Bool :=
  graphEdges.map fun e => decide (c e.1 = c e.2)

def proper3 (c : V → Colour3) : Bool :=
  allB ((conflicts c).map fun x => !x)

def ThreeColourable : Prop := ∃ c : V → Colour3, proper3 c = true

/- This theorem is the semantic form of `q3_ge_two_encoded`: the quantified
object is now an ordinary map from the 60 graph vertices to an inductive
three-element colour type. -/
theorem no_at_most_one_bad_edge (c : V → Colour3) :
    atMostOne (conflicts c) = false := by
  have h := q3_ge_two_encoded
    (bitA (c 0)) (bitB (c 0)) (bitA (c 1)) (bitB (c 1)) (bitA (c 2)) (bitB (c 2)) (bitA (c 3)) (bitB (c 3))
    (bitA (c 4)) (bitB (c 4)) (bitA (c 5)) (bitB (c 5)) (bitA (c 6)) (bitB (c 6)) (bitA (c 7)) (bitB (c 7))
    (bitA (c 8)) (bitB (c 8)) (bitA (c 9)) (bitB (c 9)) (bitA (c 10)) (bitB (c 10)) (bitA (c 11)) (bitB (c 11))
    (bitA (c 12)) (bitB (c 12)) (bitA (c 13)) (bitB (c 13)) (bitA (c 14)) (bitB (c 14)) (bitA (c 15)) (bitB (c 15))
    (bitA (c 16)) (bitB (c 16)) (bitA (c 17)) (bitB (c 17)) (bitA (c 18)) (bitB (c 18)) (bitA (c 19)) (bitB (c 19))
    (bitA (c 20)) (bitB (c 20)) (bitA (c 21)) (bitB (c 21)) (bitA (c 22)) (bitB (c 22)) (bitA (c 23)) (bitB (c 23))
    (bitA (c 24)) (bitB (c 24)) (bitA (c 25)) (bitB (c 25)) (bitA (c 26)) (bitB (c 26)) (bitA (c 27)) (bitB (c 27))
    (bitA (c 28)) (bitB (c 28)) (bitA (c 29)) (bitB (c 29)) (bitA (c 30)) (bitB (c 30)) (bitA (c 31)) (bitB (c 31))
    (bitA (c 32)) (bitB (c 32)) (bitA (c 33)) (bitB (c 33)) (bitA (c 34)) (bitB (c 34)) (bitA (c 35)) (bitB (c 35))
    (bitA (c 36)) (bitB (c 36)) (bitA (c 37)) (bitB (c 37)) (bitA (c 38)) (bitB (c 38)) (bitA (c 39)) (bitB (c 39))
    (bitA (c 40)) (bitB (c 40)) (bitA (c 41)) (bitB (c 41)) (bitA (c 42)) (bitB (c 42)) (bitA (c 43)) (bitB (c 43))
    (bitA (c 44)) (bitB (c 44)) (bitA (c 45)) (bitB (c 45)) (bitA (c 46)) (bitB (c 46)) (bitA (c 47)) (bitB (c 47))
    (bitA (c 48)) (bitB (c 48)) (bitA (c 49)) (bitB (c 49)) (bitA (c 50)) (bitB (c 50)) (bitA (c 51)) (bitB (c 51))
    (bitA (c 52)) (bitB (c 52)) (bitA (c 53)) (bitB (c 53)) (bitA (c 54)) (bitB (c 54)) (bitA (c 55)) (bitB (c 55))
    (bitA (c 56)) (bitB (c 56)) (bitA (c 57)) (bitB (c 57)) (bitA (c 58)) (bitB (c 58)) (bitA (c 59)) (bitB (c 59))
  simp only [valid_encoding, allB] at h
  simpa [conflicts, graphEdges] using h

theorem atMostOne_of_noConflicts :
    ∀ xs : List Bool,
      allB (xs.map fun x => !x) = true → atMostOne xs = true
  | [], _ => by decide
  | false :: xs, h => by
      have ih := atMostOne_of_noConflicts xs
      simpa [allB, atMostOne, atMostOneAux] using ih (by simpa [allB] using h)
  | true :: xs, h => by
      simp [allB] at h

theorem not_three_colourable : ¬ ThreeColourable := by
  rintro ⟨c, hc⟩
  have ha : atMostOne (conflicts c) = true :=
    atMostOne_of_noConflicts (conflicts c) hc
  have hn := no_at_most_one_bad_edge c
  rw [ha] at hn
  cases hn

/- A colouring of `G-e` is exactly a colouring of `G` with at most one bad
edge, because the only allowed conflict is the deleted edge. -/
def ThreeColourableAfterDeletingAtMostOneEdge : Prop :=
  ∃ c : V → Colour3, atMostOne (conflicts c) = true

theorem no_single_edge_deletion_is_three_colourable :
    ¬ ThreeColourableAfterDeletingAtMostOneEdge := by
  rintro ⟨c, hc⟩
  have hn := no_at_most_one_bad_edge c
  rw [hc] at hn
  cases hn

def properAway (deleted : V) (c : V → Colour3) : Bool :=
  allB (graphEdges.map fun e =>
    decide (e.1 = deleted) || decide (e.2 = deleted) ||
      !(decide (c e.1 = c e.2)))

def colour3OfNat : Nat → Colour3
  | 0 => .red
  | 1 => .green
  | _ => .blue

def witnessColour (deleted u : V) : Colour3 :=
  colour3OfNat ((vertexWitnesses.getD deleted.val #[]).getD u.val 0)

/- Concrete semantic witness for every vertex deletion. -/
theorem every_vertex_deletion_has_displayed_colouring :
    ∀ deleted : V, properAway deleted (witnessColour deleted) = true := by
  native_decide

theorem every_vertex_deletion_is_three_colourable :
    ∀ deleted : V, ∃ c : V → Colour3, properAway deleted c = true := by
  intro deleted
  exact ⟨witnessColour deleted,
    every_vertex_deletion_has_displayed_colouring deleted⟩

def properAwayZero (c : V → Colour3) : Bool := properAway 0 c

def balancedAtZero (c : V → Colour3) : Bool :=
  exactlyTwo6
      (decide (c 5 = .red)) (decide (c 26 = .red))
      (decide (c 30 = .red)) (decide (c 33 = .red))
      (decide (c 37 = .red)) (decide (c 55 = .red)) &&
  exactlyTwo6
      (decide (c 5 = .green)) (decide (c 26 = .green))
      (decide (c 30 = .green)) (decide (c 33 = .green))
      (decide (c 37 = .green)) (decide (c 55 = .green)) &&
  exactlyTwo6
      (decide (c 5 = .blue)) (decide (c 26 = .blue))
      (decide (c 30 = .blue)) (decide (c 33 = .blue))
      (decide (c 37 = .blue)) (decide (c 55 = .blue))

/- The encoded theorem `puncture_balance_universal` above is the compact
certificate for puncture balance.  Its proposition-level graph formulation is
proved in the independent `lean_search_tree` development.  Keeping that bridge
out of this compact file avoids asking `simp` to reassociate two generated
180-entry Boolean lists. -/

inductive Colour4 where
  | red | green | blue | extra
  deriving DecidableEq, Repr

def embed3 : Colour3 → Colour4
  | .red => .red
  | .green => .green
  | .blue => .blue

def displayedFourColouring (u : V) : Colour4 :=
  if u = 0 then .extra else embed3 (witnessColour 0 u)

def proper4 (c : V → Colour4) : Bool :=
  allB (graphEdges.map fun e => !(decide (c e.1 = c e.2)))

theorem displayed_four_colouring_is_proper :
    proper4 displayedFourColouring = true := by
  native_decide

structure CertifiedDiracResult : Prop where
  notThreeColourable : ¬ ThreeColourable
  fourColouring : ∃ c : V → Colour4, proper4 c = true
  vertexDeletions : ∀ deleted : V,
    ∃ c : V → Colour3, properAway deleted c = true
  noOneEdgeRepair : ¬ ThreeColourableAfterDeletingAtMostOneEdge

theorem certified_dirac_result : CertifiedDiracResult where
  notThreeColourable := not_three_colourable
  fourColouring := ⟨displayedFourColouring,
    displayed_four_colouring_is_proper⟩
  vertexDeletions := every_vertex_deletion_is_three_colourable
  noOneEdgeRepair := no_single_edge_deletion_is_three_colourable

/- These commands make the exact trust footprint visible in every build log.
In particular, they distinguish the `bv_decide` theorems from the positive
`native_decide` witness replays. -/
#print axioms puncture_balance_universal
#print axioms normalized_puncture_classifier
#print axioms q3_ge_two_encoded
#print axioms no_at_most_one_bad_edge
#print axioms certified_dirac_result

end Dirac60
