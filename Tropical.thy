theory Tropical
  imports Main
begin

section \<open>Tropical Semiring over \<nat> \<union> {-\<infinity>}\<close>

text \<open>
  Formalises the max-plus tropical semiring with carrier \<open>\<nat> \<union> {-\<infinity>}\<close>.
  Tropical addition is @{text max} (identity: -\<infinity>);
  tropical multiplication is ordinary addition (identity: Fin 0).

  We instantiate Isabelle's @{class comm_semiring_1} hierarchy, then prove
  idempotency of addition separately \<dash> it sits outside the standard ring
  hierarchy (it makes the structure a \<^emph>\<open>dioid\<close>).

  Note on carrier choice: replacing @{text "Fin nat"} with
  @{text "Fin int"} or @{text "Fin real"} gives the more usual algebraic-
  geometry semiring over \<open>\<int> \<union> {-\<infinity>}\<close> or \<open>\<real> \<union> {-\<infinity>}\<close>.  The proof
  obligations below are structurally identical.
\<close>

(* ------------------------------------------------------------------ *)
subsection \<open>1  Carrier Type\<close>
(* ------------------------------------------------------------------ *)

datatype tropical
  = Fin nat    \<comment> \<open>a natural number embedded in the semiring\<close>
  | NegInf     \<comment> \<open>\<minus>\<infinity>, the additive zero and absorbing element\<close>

(* ------------------------------------------------------------------ *)
subsection \<open>2  Primitive Operations\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  We define @{text trop_add} and @{text trop_mul} as plain functions and
  connect them to Isabelle's @{command instantiation} infrastructure in
  Section 4.  This separation keeps the algebraic lemmas readable and free
  of typeclass notation.
\<close>

fun trop_add :: "tropical \<Rightarrow> tropical \<Rightarrow> tropical" where
  "trop_add NegInf    b        = b"
| "trop_add a        NegInf   = a"
| "trop_add (Fin a) (Fin b)   = Fin (max a b)"

fun trop_mul :: "tropical \<Rightarrow> tropical \<Rightarrow> tropical" where
  "trop_mul NegInf   _        = NegInf"
| "trop_mul _       NegInf    = NegInf"
| "trop_mul (Fin a) (Fin b)   = Fin (a + b)"

(* ------------------------------------------------------------------ *)
subsection \<open>3  Algebraic Lemmas\<close>
(* ------------------------------------------------------------------ *)

(* ---- addition ---- *)

lemma trop_add_NegInf_left [simp]:
  "trop_add NegInf a = a"
  by (cases a) simp_all

lemma trop_add_NegInf_right [simp]:
  "trop_add a NegInf = a"
  by (cases a) simp_all

lemma trop_add_comm:
  "trop_add a b = trop_add b a"
  by (cases a; cases b) (simp_all add: max.commute)

lemma trop_add_assoc:
  "trop_add (trop_add a b) c = trop_add a (trop_add b c)"
  by (cases a; cases b; cases c) (simp_all add: max.assoc)

lemma trop_add_idem [simp]:
  "trop_add a a = a"
  by (cases a) simp_all

(* ---- multiplication ---- *)

lemma trop_mul_NegInf_left [simp]:
  "trop_mul NegInf a = NegInf"
  by (cases a) simp_all

lemma trop_mul_NegInf_right [simp]:
  "trop_mul a NegInf = NegInf"
  by (cases a) simp_all

lemma trop_mul_one_left [simp]:
  "trop_mul (Fin 0) a = a"
  by (cases a) simp_all

lemma trop_mul_one_right [simp]:
  "trop_mul a (Fin 0) = a"
  by (cases a) simp_all

lemma trop_mul_comm:
  "trop_mul a b = trop_mul b a"
  by (cases a; cases b) (simp_all add: add.commute)

lemma trop_mul_assoc:
  "trop_mul (trop_mul a b) c = trop_mul a (trop_mul b c)"
  by (cases a; cases b; cases c) (simp_all add: add.assoc)

(* ---- key arithmetic fact on nat ---- *)

text \<open>
  Addition distributes over @{term max} on @{typ nat}.
  Isabelle's default simp set already contains the necessary arithmetic
  and ordering lemmas to close both goals directly.  The [simp] attribute
  means the distributivity proofs below need no extra hints.
\<close>

lemma nat_add_distrib_max_left [simp]:
  "(k :: nat) + max m n = max (k + m) (k + n)"
  by simp

lemma nat_add_distrib_max_right [simp]:
  "max m n + (k :: nat) = max (m + k) (n + k)"
  by simp

(* ---- distributivity ---- *)

lemma trop_distrib_left:
  "trop_mul a (trop_add b c) = trop_add (trop_mul a b) (trop_mul a c)"
  by (cases a; cases b; cases c) simp_all

lemma trop_distrib_right:
  "trop_mul (trop_add a b) c = trop_add (trop_mul a c) (trop_mul b c)"
  by (cases a; cases b; cases c) simp_all

(* ------------------------------------------------------------------ *)
subsection \<open>4  Typeclass Instantiation\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  We wire @{typ tropical} into Isabelle's algebraic hierarchy in six steps,
  each adding one layer and discharging only the new proof obligations.
  Earlier layers are discharged automatically by Isabelle's instance
  resolution.

  Layer summary:
    4a  @{class comm_monoid_add}   \<dash> trop_add, NegInf as 0
    4b  @{class comm_monoid_mult}  \<dash> trop_mul, Fin 0 as 1
    4c  @{class semiring}          \<dash> distributivity
    4d  @{class semiring_0}        \<dash> 0 * a = 0
    4e  @{class zero_neq_one}      \<dash> NegInf \<noteq> Fin 0
    4f  @{class semiring_1}        \<dash> trivial from 4a\<dash>4e
    4g  @{class comm_semiring_1}   \<dash> trivial from 4b, 4f
\<close>

(* 4a -- additive commutative monoid --------------------------------- *)

instantiation tropical :: comm_monoid_add
begin

definition zero_tropical :: tropical where
  "(0 :: tropical) \<equiv> NegInf"

definition plus_tropical :: "tropical \<Rightarrow> tropical \<Rightarrow> tropical" where
  "(a :: tropical) + b \<equiv> trop_add a b"

instance
proof
  fix a b c :: tropical
  show "a + b + c = a + (b + c)"
    unfolding plus_tropical_def
    by (simp add: trop_add_assoc)
  show "a + b = b + a"
    unfolding plus_tropical_def
    by (simp add: trop_add_comm)
  show "(0 :: tropical) + a = a"
    unfolding plus_tropical_def zero_tropical_def
    by simp
qed

end

(* 4b -- multiplicative commutative monoid -------------------------- *)

instantiation tropical :: comm_monoid_mult
begin

definition one_tropical :: tropical where
  "(1 :: tropical) \<equiv> Fin 0"

definition times_tropical :: "tropical \<Rightarrow> tropical \<Rightarrow> tropical" where
  "(a :: tropical) * b \<equiv> trop_mul a b"

instance
proof
  fix a b c :: tropical
  show "a * b * c = a * (b * c)"
    unfolding times_tropical_def
    by (simp add: trop_mul_assoc)
  show "a * b = b * a"
    unfolding times_tropical_def
    by (simp add: trop_mul_comm)
  show "(1 :: tropical) * a = a"
    unfolding times_tropical_def one_tropical_def
    by simp
qed

end

(* 4c -- semiring: distributivity ------------------------------------ *)

instance tropical :: semiring
proof
  fix a b c :: tropical
  show "(a + b) * c = a * c + b * c"
    by (simp add: plus_tropical_def times_tropical_def trop_distrib_right)
  show "a * (b + c) = a * b + a * c"
    by (simp add: plus_tropical_def times_tropical_def trop_distrib_left)
qed

(* 4d -- semiring_0: zero annihilation ------------------------------- *)

instance tropical :: semiring_0
proof
  fix a :: tropical
  show "(0 :: tropical) * a = 0"
    by (simp add: times_tropical_def zero_tropical_def)
  show "a * (0 :: tropical) = 0"
    by (simp add: times_tropical_def zero_tropical_def)
qed

(* 4e -- zero_neq_one ------------------------------------------------ *)

instance tropical :: zero_neq_one
proof
  show "(0 :: tropical) \<noteq> 1"
    by (simp add: zero_tropical_def one_tropical_def)
qed

(* 4f -- semiring_1: trivially from 4b-4e --------------------------- *)

instance tropical :: semiring_1 ..

(* 4f' -- comm_semiring: distributivity required explicitly in Isabelle 2025 *)

instance tropical :: comm_semiring
proof
  fix a b c :: tropical
  show "(a + b) * c = a * c + b * c"
    by (simp add: plus_tropical_def times_tropical_def trop_distrib_right)
qed

(* 4g -- comm_semiring_1: trivially from 4b, 4f, 4f' --------------------- *)

instance tropical :: comm_semiring_1 ..

(* ------------------------------------------------------------------ *)
subsection \<open>5  Characteristic Properties\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The tropical semiring is a \<^emph>\<open>dioid\<close>: an idempotent semiring.
  Idempotency of addition (\<open>a \<oplus> a = a\<close>) is its defining structural
  property; it places the tropical semiring outside the usual ring
  hierarchy and enables the connection to shortest-path algorithms and
  tropical geometry.

  It is not an axiom of @{class comm_semiring_1} and is proved here
  for downstream use.
\<close>

theorem tropical_add_idem:
  "(a :: tropical) + a = a"
  unfolding plus_tropical_def
  by simp

text \<open>
  Derived ordering: define \<open>a \<le> b \<longleftrightarrow> a + b = b\<close> (equivalently, \<open>max a b = b\<close>).
  This coincides with the natural order on @{typ nat} with NegInf at the
  bottom.  Formalising the induced @{class order} instance is
  straightforward from @{text tropical_add_idem}, @{text trop_add_comm},
  and @{text trop_add_assoc}, and is left as an exercise.
\<close>

end
