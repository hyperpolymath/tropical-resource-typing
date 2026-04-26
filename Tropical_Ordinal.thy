(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_Ordinal
  imports Main
begin

text \<open>
  Rung 1 of the tropical-types \<longrightarrow> Buchholz-ordinals ladder.

  Goal: the tropical-semiring construction lifts from \<open>nat\<close> coefficients to
  \<^bold>\<open>any\<close> commutative ordered monoid whose \<open>+\<close> is monotone in each argument.
  Hessenberg sum on ordinals is the motivating instance, but the typeclass
  formulation lets us reuse all algebraic theorems uniformly.

  This is a deliberately minimal first cut. The proof obligations marked
  with \<open>oops\<close> are the ones we want ECHIDNA to evaluate: each is either
  closeable by direct automation or surfaces a missing piece of the design.
\<close>

(* ================================================================== *)
section \<open>1  Tropical Coefficient Class\<close>
(* ================================================================== *)

text \<open>
  The minimum the coefficient algebra must provide: a commutative monoid
  under \<open>+\<close> (with identity \<open>0\<close>), a linear order, and monotonicity of \<open>+\<close>
  in each argument. Distributivity of \<open>+\<close> over \<open>max\<close> follows from
  monotonicity in a linear order.
\<close>

class tropical_coeff = comm_monoid_add + linorder +
  assumes plus_mono_left:  "a \<le> b \<Longrightarrow> a + c \<le> b + c"
      and plus_mono_right: "a \<le> b \<Longrightarrow> c + a \<le> c + b"

text \<open>Sanity instance: \<open>nat\<close>.\<close>

instantiation nat :: tropical_coeff
begin
instance by standard auto
end

(* ================================================================== *)
section \<open>2  Generic Tropical Lift\<close>
(* ================================================================== *)

datatype 'a trop_o
  = FinO 'a
  | NegInfO

fun tropO_add :: "'a::tropical_coeff trop_o \<Rightarrow> 'a trop_o \<Rightarrow> 'a trop_o" where
  "tropO_add NegInfO    b          = b"
| "tropO_add a         NegInfO     = a"
| "tropO_add (FinO m) (FinO n)     = FinO (max m n)"

fun tropO_mul :: "'a::tropical_coeff trop_o \<Rightarrow> 'a trop_o \<Rightarrow> 'a trop_o" where
  "tropO_mul NegInfO   _           = NegInfO"
| "tropO_mul _        NegInfO      = NegInfO"
| "tropO_mul (FinO m) (FinO n)     = FinO (m + n)"

(* ================================================================== *)
section \<open>3  Algebraic Obligations\<close>
(* ================================================================== *)

(* ---- addition ---- *)

lemma tropO_add_NegInfO_left [simp]:
  "tropO_add NegInfO a = a"
  by (cases a) simp_all

lemma tropO_add_NegInfO_right [simp]:
  "tropO_add a NegInfO = a"
  by (cases a) simp_all

lemma tropO_add_comm:
  "tropO_add a b = tropO_add b a"
  by (cases a; cases b) (simp_all add: max.commute)

lemma tropO_add_assoc:
  "tropO_add (tropO_add a b) c = tropO_add a (tropO_add b c)"
  by (cases a; cases b; cases c) (simp_all add: max.assoc)

lemma tropO_add_idem [simp]:
  "tropO_add a a = a"
  by (cases a) simp_all

(* ---- multiplication ---- *)

lemma tropO_mul_NegInfO_left [simp]:
  "tropO_mul NegInfO a = NegInfO"
  by (cases a) simp_all

lemma tropO_mul_NegInfO_right [simp]:
  "tropO_mul a NegInfO = NegInfO"
  by (cases a) simp_all

lemma tropO_mul_one_left [simp]:
  "tropO_mul (FinO 0) a = a"
  by (cases a) simp_all

lemma tropO_mul_one_right [simp]:
  "tropO_mul a (FinO 0) = a"
  by (cases a) simp_all

lemma tropO_mul_comm:
  "tropO_mul a b = tropO_mul b a"
  by (cases a; cases b) (simp_all add: add.commute)

lemma tropO_mul_assoc:
  "tropO_mul (tropO_mul a b) c = tropO_mul a (tropO_mul b c)"
  by (cases a; cases b; cases c) (simp_all add: add.assoc)

(* ---- distributivity (the load-bearing one for Rung 1) ---- *)

text \<open>
  Distributivity of \<open>+\<close> over \<open>max\<close> in a linearly-ordered monoid with
  monotone addition. This is where the Hessenberg-vs-ordinary-ordinal
  distinction will bite later: ordinary ordinal sum fails commutativity,
  not monotonicity.
\<close>

lemma plus_max_distrib_left:
  fixes a b c :: "'a::tropical_coeff"
  shows "a + max b c = max (a + b) (a + c)"
proof (cases "b \<le> c")
  case True
  hence "a + b \<le> a + c" by (rule plus_mono_right)
  with True show ?thesis by (simp add: max.absorb2)
next
  case False
  hence "c \<le> b" by simp
  hence "a + c \<le> a + b" by (rule plus_mono_right)
  with False show ?thesis by (simp add: max.absorb1)
qed

lemma plus_max_distrib_right:
  fixes a b c :: "'a::tropical_coeff"
  shows "max a b + c = max (a + c) (b + c)"
proof (cases "a \<le> b")
  case True
  hence "a + c \<le> b + c" by (rule plus_mono_left)
  with True show ?thesis by (simp add: max.absorb2)
next
  case False
  hence "b \<le> a" by simp
  hence "b + c \<le> a + c" by (rule plus_mono_left)
  with False show ?thesis by (simp add: max.absorb1)
qed

lemma tropO_distrib_left:
  "tropO_mul a (tropO_add b c) = tropO_add (tropO_mul a b) (tropO_mul a c)"
  by (cases a; cases b; cases c) (simp_all add: plus_max_distrib_left)

lemma tropO_distrib_right:
  "tropO_mul (tropO_add a b) c = tropO_add (tropO_mul a c) (tropO_mul b c)"
  by (cases a; cases b; cases c) (simp_all add: plus_max_distrib_right)

text \<open>
  The bridge to \<open>Tropical_v2\<close>'s concrete \<open>tropical\<close> type is split into
  \<open>Tropical_Ordinal_Bridge.thy\<close>, which requires multi-file Isabelle
  staging (currently a gap in ECHIDNA's prove pipeline).
\<close>

end
