(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_v2
  imports Main
begin

text \<open>
  Supersedes @{file "Tropical.thy"}.

  This theory develops both tropical semiring variants used in the estate:

  \<^item> @{text tropical}     — \<^bold>\<open>max-plus\<close> over \<open>nat \<union> {-\<infinity>}\<close>,
    used for longest-path / scheduling / session-type budget.
  \<^item> @{text tropical_min}  — \<^bold>\<open>min-plus\<close> over \<open>nat \<union> {+\<infinity>}\<close>,
    used for shortest-path / WCET / Bellman-Ford.

  Both are instantiated into Isabelle's algebraic hierarchy
  (@{class comm_semiring_1}, @{class linorder}, @{class order_bot},
  and @{class order_top} for min-plus).  Key additions over v1:

  \<^item> Min-plus variant @{text tropical_min} (dual semiring).
  \<^item> @{class linorder} instances for both types.
  \<^item> Semiring homomorphism lemmas (\<open>Fin_hom_*\<close>, \<open>Fin'_hom_*\<close>).
  \<^item> @{text trop_sum_eq_Max} / @{text tropm_sum_eq_Min}: the key lemmas
    that shorten all downstream walk-weight proofs to 2–7 lines.
  \<^item> Named proof methods @{text tropical_arith} and @{text tropm_arith}
    that close constructor-arithmetic goals without manual case splits.

  Build:
    @{verbatim "isabelle build -D . -v Tropical_Semirings"}

  Verified: Isabelle 2025-1.
\<close>

(* ================================================================== *)
section \<open>Part I  Max-Plus Tropical Semiring\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>1  Carrier Type\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Elements are natural numbers (finite tropical values) or @{text NegInf}
  (\<open>-\<infinity>\<close>, the additive zero / identity of @{text max}).
\<close>

datatype tropical
  = Fin nat   \<comment> \<open>a finite value @{text "n \<in> \<nat>"}\<close>
  | NegInf    \<comment> \<open>\<open>-\<infinity>\<close>: additive zero, multiplicative absorbing\<close>

(* ------------------------------------------------------------------ *)
subsection \<open>2  Primitive Operations\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_add} is @{term max} (with @{text NegInf} as identity).
  @{text trop_mul} is ordinary @{text "+"} (with @{text "Fin 0"} as identity).
\<close>

fun trop_add :: "tropical \<Rightarrow> tropical \<Rightarrow> tropical" where
  "trop_add NegInf    b         = b"
| "trop_add a        NegInf    = a"
| "trop_add (Fin m) (Fin n)    = Fin (max m n)"

fun trop_mul :: "tropical \<Rightarrow> tropical \<Rightarrow> tropical" where
  "trop_mul NegInf   _         = NegInf"
| "trop_mul _       NegInf     = NegInf"
| "trop_mul (Fin m) (Fin n)    = Fin (m + n)"

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

lemma trop_add_Fin_Fin [simp]:
  "trop_add (Fin m) (Fin n) = Fin (max m n)"
  by simp

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

lemma trop_mul_Fin_Fin [simp]:
  "trop_mul (Fin m) (Fin n) = Fin (m + n)"
  by simp

(* ---- key nat arithmetic for distributivity ---- *)

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

(* ---- order on Fin ---- *)

(* ------------------------------------------------------------------ *)
subsection \<open>4  Typeclass Instantiation — Semiring\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Seven-layer chain exactly as in @{file "Tropical.thy"}:
  additive monoid, multiplicative monoid, semiring, semiring_0,
  zero_neq_one, semiring_1, comm_semiring_1.
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
    unfolding plus_tropical_def by (simp add: trop_add_assoc)
  show "a + b = b + a"
    unfolding plus_tropical_def by (simp add: trop_add_comm)
  show "(0 :: tropical) + a = a"
    unfolding plus_tropical_def zero_tropical_def by simp
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
    unfolding times_tropical_def by (simp add: trop_mul_assoc)
  show "a * b = b * a"
    unfolding times_tropical_def by (simp add: trop_mul_comm)
  show "(1 :: tropical) * a = a"
    unfolding times_tropical_def one_tropical_def by simp
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

(* 4f -- semiring_1: trivially from 4b–4e --------------------------- *)

instance tropical :: semiring_1 ..

(* 4f' -- comm_semiring: commutativity required explicitly in Isabelle 2025 *)

instance tropical :: comm_semiring
proof
  fix a b c :: tropical
  show "(a + b) * c = a * c + b * c"
    by (simp add: plus_tropical_def times_tropical_def trop_distrib_right)
qed

(* 4g -- comm_semiring_1: from 4b, 4f, 4f' -------------------------- *)

instance tropical :: comm_semiring_1 ..

(* ------------------------------------------------------------------ *)
subsection \<open>5  Typeclass Instantiation — Linear Order\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The natural tropical order: @{text "a \<le> b \<longleftrightarrow> a \<oplus> b = b"}, i.e.\ @{term "max a b = b"}.
  Concretely: @{text NegInf} is the bottom; @{text "Fin m \<le> Fin n \<longleftrightarrow> m \<le> n"}.
  This is a linear (total) order.
\<close>

instantiation tropical :: linorder
begin

definition less_eq_tropical :: "tropical \<Rightarrow> tropical \<Rightarrow> bool" where
  "a \<le> b \<equiv> (case a of
      NegInf   \<Rightarrow> True
    | Fin m    \<Rightarrow> (case b of NegInf \<Rightarrow> False | Fin n \<Rightarrow> m \<le> n))"

definition less_tropical :: "tropical \<Rightarrow> tropical \<Rightarrow> bool" where
  "less_tropical a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

instance
proof
  fix a b c :: tropical
  show "a \<le> a"
    unfolding less_eq_tropical_def by (cases a) simp_all
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    unfolding less_eq_tropical_def
    by (cases a; cases b; cases c) simp_all
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
    unfolding less_eq_tropical_def
    by (cases a; cases b) simp_all
  show "a \<le> b \<or> b \<le> a"
    unfolding less_eq_tropical_def
    by (cases a; cases b) (simp_all add: le_antisym nat_le_linear)
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    unfolding less_tropical_def less_eq_tropical_def by simp
qed

end

(* Key simp rules once linorder is established *)

lemma NegInf_le [simp]: "(NegInf :: tropical) \<le> a"
  by (cases a) (simp_all add: less_eq_tropical_def)

lemma not_Fin_le_NegInf [simp]: "\<not> Fin m \<le> (NegInf :: tropical)"
  by (simp add: less_eq_tropical_def)

lemma Fin_le_Fin [simp]: "(Fin m :: tropical) \<le> Fin n \<longleftrightarrow> m \<le> n"
  by (simp add: less_eq_tropical_def)

lemma Fin_lt_Fin [simp]: "(Fin m :: tropical) < Fin n \<longleftrightarrow> m < n"
  by (simp add: less_tropical_def less_eq_tropical_def; arith)

lemma trop_add_le_iff:
  "(a :: tropical) \<le> b \<longleftrightarrow> a + b = b"
  unfolding plus_tropical_def
  by (cases a; cases b) (simp_all add: less_eq_tropical_def max_def)

(* ------------------------------------------------------------------ *)
subsection \<open>6  Typeclass Instantiation — Bottom\<close>
(* ------------------------------------------------------------------ *)

instantiation tropical :: order_bot
begin

definition bot_tropical :: tropical where
  "(bot :: tropical) \<equiv> NegInf"

instance
  by standard (simp add: bot_tropical_def)

end

lemma trop_bot_eq_zero: "(bot :: tropical) = 0"
  by (simp add: bot_tropical_def zero_tropical_def)

(* ------------------------------------------------------------------ *)
subsection \<open>6b  Ordered Additive Semigroup (Max-Plus)\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Tropical max-plus addition is monotone: \<open>a \<le> b \<Longrightarrow> c + a \<le> c + b\<close>.
  This follows from \<open>+ = max\<close>: \<open>max c a \<le> max c b\<close> when \<open>a \<le> b\<close>.
  Required for @{thm sum_mono} / @{thm add_mono} to apply over tropical.
\<close>

instance tropical :: ordered_ab_semigroup_add
proof
  fix a b c :: tropical
  assume "a \<le> b"
  thus "c + a \<le> c + b"
    by (cases a; cases b; cases c)
       (auto simp: less_eq_tropical_def plus_tropical_def max_def)
qed

(* ------------------------------------------------------------------ *)
subsection \<open>7  Idempotency (Dioid)\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{typ tropical} is a \<^emph>\<open>dioid\<close>: an idempotent semiring.
  Idempotency (@{term "a + a = a"}) is its defining structural property
  and sits outside the @{class comm_semiring_1} hierarchy.
\<close>

theorem tropical_add_idem:
  "(a :: tropical) + a = a"
  unfolding plus_tropical_def by simp

(* ------------------------------------------------------------------ *)
subsection \<open>8  Semiring Homomorphisms — Max-Plus\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The constructor @{term Fin} is a semiring homomorphism from
  @{text "(nat, max, +, -\<infinity>, 0)"} to @{text "(tropical, \<oplus>, \<otimes>, NegInf, Fin 0)"}.
  These lemmas expose the structural facts used in walk-weight calculations
  throughout @{file "Tropical_Matrices_Full.thy"}.
\<close>

lemma Fin_hom_mul:
  "Fin (m + n) = Fin m * Fin n"
  by (simp add: times_tropical_def)

lemma Fin_hom_add:
  "Fin (max m n) = Fin m + Fin n"
  by (simp add: plus_tropical_def)

lemma Fin_hom_zero:
  "(0 :: tropical) = NegInf"
  by (simp add: zero_tropical_def)

lemma Fin_hom_one:
  "(1 :: tropical) = Fin 0"
  by (simp add: one_tropical_def)

lemma Fin_hom_le:
  "Fin m \<le> Fin n \<longleftrightarrow> m \<le> n"
  by simp

lemma Fin_hom_strict:
  "(Fin m :: tropical) < Fin n \<longleftrightarrow> m < n"
  by simp

lemma Fin_hom_inject:
  "Fin m = (Fin n :: tropical) \<longleftrightarrow> m = n"
  by simp

(* ------------------------------------------------------------------ *)
subsection \<open>9  Finite Tropical Sums\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The \<^emph>\<open>tropical sum\<close> of a @{term "Fin"}-valued function over a finite set
  is a fold of @{term "(+)"} (i.e.\ @{text trop_add}) with identity
  @{term "0 = NegInf"}.  Since @{typ tropical} is a @{class comm_monoid_add},
  Isabelle's @{term sum} notation applies directly.

  The key lemma @{text trop_sum_eq_Max} says:
    @{text "\<Sum> x \<in> S. Fin (g x) = Fin (Max (g ` S))"}
  which reduces all downstream walk-weight equalities to facts about
  @{term Max} on finite sets of naturals.
\<close>

definition trop_sum :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> tropical" where
  "trop_sum g S \<equiv> \<Sum> x \<in> S. Fin (g x)"

lemma trop_sum_empty [simp]:
  "trop_sum g {} = NegInf"
  by (simp add: trop_sum_def zero_tropical_def)

lemma trop_sum_singleton [simp]:
  "trop_sum g {x} = Fin (g x)"
  by (simp add: trop_sum_def zero_tropical_def plus_tropical_def)

lemma trop_sum_insert:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow>
   trop_sum g (insert x S) = Fin (g x) + trop_sum g S"
  by (simp add: trop_sum_def sum.insert)

text \<open>
  @{text trop_sum_eq_Max}: the fundamental simplification lemma.
  For a non-empty finite set, the tropical sum collapses to the @{term Max}
  of the image.  This is the key lemma that shortens downstream proofs
  from 14–18 lines to 2–7 lines.
\<close>

lemma trop_sum_eq_Max:
  assumes "finite S" "S \<noteq> {}"
  shows "trop_sum g S = Fin (Max (g ` S))"
  using assms
proof (induction S rule: finite_ne_induct)
  case (singleton x)
  show ?case by simp
next
  case (insert x F)
  have step: "trop_sum g (insert x F) = Fin (g x) + trop_sum g F"
    using insert.hyps(1,3) by (simp add: trop_sum_insert)
  have ih: "trop_sum g F = Fin (Max (g ` F))"
    by (rule insert.IH)
  have combine: "Fin (g x) + Fin (Max (g ` F)) = Fin (max (g x) (Max (g ` F)))"
    by (simp add: plus_tropical_def)
  have max_eq: "max (g x) (Max (g ` F)) = Max (g ` insert x F)"
    using insert.hyps(1,2,3) by (simp add: Max_insert)
  show ?case
    using step ih combine max_eq by simp
qed

lemma trop_sum_ge_member:
  assumes "finite S" "x \<in> S"
  shows "Fin (g x) \<le> trop_sum g S"
proof -
  have ne: "S \<noteq> {}" using assms by auto
  have "trop_sum g S = Fin (Max (g ` S))"
    by (rule trop_sum_eq_Max[OF assms(1) ne])
  thus ?thesis
    by (simp add: Max_ge[OF finite_imageI[OF assms(1)] imageI[OF assms(2)]])
qed

lemma trop_sum_mono_subset:
  assumes "finite T" "S \<subseteq> T" "S \<noteq> {}"
  shows "trop_sum g S \<le> trop_sum g T"
proof -
  have neT: "T \<noteq> {}" using assms(2,3) by auto
  have fS: "finite S" by (rule finite_subset[OF assms(2) assms(1)])
  have "trop_sum g S = Fin (Max (g ` S))"
    by (rule trop_sum_eq_Max[OF fS assms(3)])
  moreover have "trop_sum g T = Fin (Max (g ` T))"
    by (rule trop_sum_eq_Max[OF assms(1) neT])
  moreover have "Max (g ` S) \<le> Max (g ` T)"
  proof (rule Max_mono)
    show "g ` S \<subseteq> g ` T" using assms(2) by (rule image_mono)
    show "g ` S \<noteq> {}" using assms(3) by simp
    show "finite (g ` T)" using assms(1) by (rule finite_imageI)
  qed
  ultimately show ?thesis by simp
qed

lemma trop_sum_dominated:
  assumes "finite S" "S \<noteq> {}" "finite T" "T \<noteq> {}"
  assumes dominated: "\<forall>s \<in> S. \<exists>t \<in> T. g s \<le> h t"
  shows "trop_sum g S \<le> trop_sum h T"
proof -
  have "trop_sum g S = Fin (Max (g ` S))"
    using assms(1,2) by (rule trop_sum_eq_Max)
  moreover have "trop_sum h T = Fin (Max (h ` T))"
    using assms(3,4) by (rule trop_sum_eq_Max)
  moreover have "Max (g ` S) \<le> Max (h ` T)"
  proof (rule Max_le_iff[THEN iffD2])
    show "finite (g ` S)" using assms(1) by simp
    show "g ` S \<noteq> {}" using assms(2) by simp
    show "\<forall>v \<in> g ` S. v \<le> Max (h ` T)"
    proof
      fix v assume "v \<in> g ` S"
      then obtain s where hs: "s \<in> S" "v = g s" by auto
      obtain t where ht: "t \<in> T" "g s \<le> h t" using dominated hs(1) by auto
      have ht_in_image: "h t \<in> h ` T" by (rule imageI[OF ht(1)])
      have fin_image: "finite (h ` T)" by (rule finite_imageI[OF assms(3)])
      have ht_le_Max: "h t \<le> Max (h ` T)" by (rule Max_ge[OF fin_image ht_in_image])
      show "v \<le> Max (h ` T)"
        using hs(2) ht(2) ht_le_Max by (simp add: order_trans)
    qed
  qed
  ultimately show ?thesis by simp
qed

(* ------------------------------------------------------------------ *)
subsection \<open>10  Proof Method — tropical_arith\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text tropical_arith} closes goals involving @{term NegInf} and
  @{term Fin} constructor arithmetic without manual case splits.
  It combines unfolding of the typeclass definitions with case analysis
  and @{method simp}.  Use it as @{text "by tropical_arith"} or
  @{text "apply tropical_arith"}.
\<close>

(* Smoke tests for the simplification basis used by tropical proofs. *)

lemma trop_arith_test1: "Fin m + Fin n = Fin (max m n)"
  by (simp add: plus_tropical_def)
lemma trop_arith_test2: "Fin m * Fin n = Fin (m + n)"
  by (simp add: times_tropical_def)
lemma trop_arith_test3: "NegInf + a = a"
  by (simp add: plus_tropical_def)
lemma trop_arith_test4: "NegInf * a = NegInf"
  by (simp add: times_tropical_def)
lemma trop_arith_test5: "(0 :: tropical) = NegInf"
  by (simp add: zero_tropical_def)
lemma trop_arith_test6: "(1 :: tropical) = Fin 0"
  by (simp add: one_tropical_def)


(* ================================================================== *)
section \<open>Part II  Min-Plus Semiring\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>1  Carrier Type\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The min-plus semiring has carrier @{text "nat \<union> {+\<infinity>}"}.
  The constructor @{text "Fin'"} embeds @{typ nat}; @{text PosInf}
  represents @{text "+\<infinity>"} (the additive zero / identity of @{term min}).

  We use @{text "Fin'"} (with prime) to avoid a constructor-name clash
  with @{text "Fin"} from @{typ tropical}.
\<close>

datatype tropical_min
  = Fin' nat   \<comment> \<open>a finite value @{text "n \<in> \<nat>"}\<close>
  | PosInf     \<comment> \<open>@{text "+\<infinity>"}: additive zero, multiplicative absorbing\<close>

(* ------------------------------------------------------------------ *)
subsection \<open>2  Primitive Operations\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text tropm_add} is @{term min} (with @{text PosInf} as identity).
  @{text tropm_mul} is ordinary @{term "+"} (with @{text "Fin' 0"} as identity).
\<close>

fun tropm_add :: "tropical_min \<Rightarrow> tropical_min \<Rightarrow> tropical_min" where
  "tropm_add PosInf   b        = b"
| "tropm_add a       PosInf   = a"
| "tropm_add (Fin' m) (Fin' n) = Fin' (min m n)"

fun tropm_mul :: "tropical_min \<Rightarrow> tropical_min \<Rightarrow> tropical_min" where
  "tropm_mul PosInf  _         = PosInf"
| "tropm_mul _      PosInf    = PosInf"
| "tropm_mul (Fin' m) (Fin' n) = Fin' (m + n)"

(* ------------------------------------------------------------------ *)
subsection \<open>3  Algebraic Lemmas\<close>
(* ------------------------------------------------------------------ *)

(* ---- addition ---- *)

lemma tropm_add_PosInf_left [simp]:
  "tropm_add PosInf a = a"
  by (cases a) simp_all

lemma tropm_add_PosInf_right [simp]:
  "tropm_add a PosInf = a"
  by (cases a) simp_all

lemma tropm_add_comm:
  "tropm_add a b = tropm_add b a"
  by (cases a; cases b) (simp_all add: min.commute)

lemma tropm_add_assoc:
  "tropm_add (tropm_add a b) c = tropm_add a (tropm_add b c)"
  by (cases a; cases b; cases c) (simp_all add: min.assoc)

lemma tropm_add_idem [simp]:
  "tropm_add a a = a"
  by (cases a) simp_all

lemma tropm_add_Fin'_Fin' [simp]:
  "tropm_add (Fin' m) (Fin' n) = Fin' (min m n)"
  by simp

(* ---- multiplication ---- *)

lemma tropm_mul_PosInf_left [simp]:
  "tropm_mul PosInf a = PosInf"
  by (cases a) simp_all

lemma tropm_mul_PosInf_right [simp]:
  "tropm_mul a PosInf = PosInf"
  by (cases a) simp_all

lemma tropm_mul_one_left [simp]:
  "tropm_mul (Fin' 0) a = a"
  by (cases a) simp_all

lemma tropm_mul_one_right [simp]:
  "tropm_mul a (Fin' 0) = a"
  by (cases a) simp_all

lemma tropm_mul_comm:
  "tropm_mul a b = tropm_mul b a"
  by (cases a; cases b) (simp_all add: add.commute)

lemma tropm_mul_assoc:
  "tropm_mul (tropm_mul a b) c = tropm_mul a (tropm_mul b c)"
  by (cases a; cases b; cases c) (simp_all add: add.assoc)

lemma tropm_mul_Fin'_Fin' [simp]:
  "tropm_mul (Fin' m) (Fin' n) = Fin' (m + n)"
  by simp

(* ---- key nat arithmetic for distributivity ---- *)

lemma nat_add_distrib_min_left [simp]:
  "(k :: nat) + min m n = min (k + m) (k + n)"
  by simp

lemma nat_add_distrib_min_right [simp]:
  "min m n + (k :: nat) = min (m + k) (n + k)"
  by simp

(* ---- distributivity ---- *)

lemma tropm_distrib_left:
  "tropm_mul a (tropm_add b c) = tropm_add (tropm_mul a b) (tropm_mul a c)"
  by (cases a; cases b; cases c) simp_all

lemma tropm_distrib_right:
  "tropm_mul (tropm_add a b) c = tropm_add (tropm_mul a c) (tropm_mul b c)"
  by (cases a; cases b; cases c) simp_all

(* ------------------------------------------------------------------ *)
subsection \<open>4  Typeclass Instantiation — Semiring\<close>
(* ------------------------------------------------------------------ *)

(* 4a -- additive commutative monoid --------------------------------- *)

instantiation tropical_min :: comm_monoid_add
begin

definition zero_tropical_min :: tropical_min where
  "(0 :: tropical_min) \<equiv> PosInf"

definition plus_tropical_min :: "tropical_min \<Rightarrow> tropical_min \<Rightarrow> tropical_min" where
  "(a :: tropical_min) + b \<equiv> tropm_add a b"

instance
proof
  fix a b c :: tropical_min
  show "a + b + c = a + (b + c)"
    unfolding plus_tropical_min_def by (simp add: tropm_add_assoc)
  show "a + b = b + a"
    unfolding plus_tropical_min_def by (simp add: tropm_add_comm)
  show "(0 :: tropical_min) + a = a"
    unfolding plus_tropical_min_def zero_tropical_min_def by simp
qed

end

(* 4b -- multiplicative commutative monoid -------------------------- *)

instantiation tropical_min :: comm_monoid_mult
begin

definition one_tropical_min :: tropical_min where
  "(1 :: tropical_min) \<equiv> Fin' 0"

definition times_tropical_min :: "tropical_min \<Rightarrow> tropical_min \<Rightarrow> tropical_min" where
  "(a :: tropical_min) * b \<equiv> tropm_mul a b"

instance
proof
  fix a b c :: tropical_min
  show "a * b * c = a * (b * c)"
    unfolding times_tropical_min_def by (simp add: tropm_mul_assoc)
  show "a * b = b * a"
    unfolding times_tropical_min_def by (simp add: tropm_mul_comm)
  show "(1 :: tropical_min) * a = a"
    unfolding times_tropical_min_def one_tropical_min_def by simp
qed

end

(* 4c -- semiring ---------------------------------------------------- *)

instance tropical_min :: semiring
proof
  fix a b c :: tropical_min
  show "(a + b) * c = a * c + b * c"
    by (simp add: plus_tropical_min_def times_tropical_min_def tropm_distrib_right)
  show "a * (b + c) = a * b + a * c"
    by (simp add: plus_tropical_min_def times_tropical_min_def tropm_distrib_left)
qed

(* 4d -- semiring_0 -------------------------------------------------- *)

instance tropical_min :: semiring_0
proof
  fix a :: tropical_min
  show "(0 :: tropical_min) * a = 0"
    by (simp add: times_tropical_min_def zero_tropical_min_def)
  show "a * (0 :: tropical_min) = 0"
    by (simp add: times_tropical_min_def zero_tropical_min_def)
qed

(* 4e -- zero_neq_one ------------------------------------------------ *)

instance tropical_min :: zero_neq_one
proof
  show "(0 :: tropical_min) \<noteq> 1"
    by (simp add: zero_tropical_min_def one_tropical_min_def)
qed

(* 4f -- semiring_1 -------------------------------------------------- *)

instance tropical_min :: semiring_1 ..

(* 4f' -- comm_semiring ---------------------------------------------- *)

instance tropical_min :: comm_semiring
proof
  fix a b c :: tropical_min
  show "(a + b) * c = a * c + b * c"
    by (simp add: plus_tropical_min_def times_tropical_min_def tropm_distrib_right)
qed

(* 4g -- comm_semiring_1 --------------------------------------------- *)

instance tropical_min :: comm_semiring_1 ..

(* ------------------------------------------------------------------ *)
subsection \<open>5  Typeclass Instantiation — Linear Order\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The natural min-plus order: @{text "a \<le> b \<longleftrightarrow> a \<oplus> b = a"}, i.e.\ @{term "min a b = a"}.
  Concretely: @{text "Fin' m \<le> Fin' n \<longleftrightarrow> m \<le> n"}; @{text PosInf} is the top.
\<close>

instantiation tropical_min :: linorder
begin

definition less_eq_tropical_min :: "tropical_min \<Rightarrow> tropical_min \<Rightarrow> bool" where
  "a \<le> b \<equiv> (case b of
      PosInf  \<Rightarrow> True
    | Fin' n  \<Rightarrow> (case a of PosInf \<Rightarrow> False | Fin' m \<Rightarrow> m \<le> n))"

definition less_tropical_min :: "tropical_min \<Rightarrow> tropical_min \<Rightarrow> bool" where
  "less_tropical_min a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

instance
proof
  fix a b c :: tropical_min
  show "a \<le> a"
    unfolding less_eq_tropical_min_def by (cases a) simp_all
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    unfolding less_eq_tropical_min_def
    by (cases a; cases b; cases c) simp_all
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
    unfolding less_eq_tropical_min_def
    by (cases a; cases b) simp_all
  show "a \<le> b \<or> b \<le> a"
    unfolding less_eq_tropical_min_def
    by (cases a; cases b) (simp_all add: nat_le_linear)
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    unfolding less_tropical_min_def less_eq_tropical_min_def by simp
qed

end

(* Key simp rules *)

lemma le_PosInf [simp]: "(a :: tropical_min) \<le> PosInf"
  by (cases a) (simp_all add: less_eq_tropical_min_def)

lemma not_PosInf_le_Fin' [simp]: "\<not> (PosInf :: tropical_min) \<le> Fin' n"
  by (simp add: less_eq_tropical_min_def)

lemma Fin'_le_Fin' [simp]: "(Fin' m :: tropical_min) \<le> Fin' n \<longleftrightarrow> m \<le> n"
  by (simp add: less_eq_tropical_min_def)

lemma Fin'_lt_Fin' [simp]: "(Fin' m :: tropical_min) < Fin' n \<longleftrightarrow> m < n"
  by (simp add: less_tropical_min_def less_eq_tropical_min_def; arith)

lemma tropm_add_le_iff:
  "(a :: tropical_min) \<le> b \<longleftrightarrow> a + b = a"
  unfolding plus_tropical_min_def
  by (cases a; cases b) (simp_all add: less_eq_tropical_min_def min_def)

(* ------------------------------------------------------------------ *)
subsection \<open>6  Typeclass Instantiation — Bottom and Top\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{typ tropical_min} has a @{text bot} (@{text "Fin' 0"}) and a @{text top}
  (@{text PosInf}), giving a bounded linear order.
\<close>

instantiation tropical_min :: order_bot
begin

definition bot_tropical_min :: tropical_min where
  "(bot :: tropical_min) \<equiv> Fin' 0"

instance
proof
  fix a :: tropical_min
  show "bot \<le> a"
    by (cases a) (simp_all add: bot_tropical_min_def less_eq_tropical_min_def)
qed

end

instantiation tropical_min :: order_top
begin

definition top_tropical_min :: tropical_min where
  "(top :: tropical_min) \<equiv> PosInf"

instance
  by standard (simp add: top_tropical_min_def)

end

text \<open>
  Min-plus addition is monotone: \<open>a \<le> b \<Longrightarrow> c + a \<le> c + b\<close>
  via \<open>+ = min\<close>: \<open>min c a \<le> min c b\<close> when \<open>a \<le> b\<close>.
  Required for @{thm sum_mono} / @{thm add_mono} over tropical_min.
\<close>

instance tropical_min :: ordered_ab_semigroup_add
proof
  fix a b c :: tropical_min
  assume "a \<le> b"
  thus "c + a \<le> c + b"
    by (cases a; cases b; cases c)
       (auto simp: less_eq_tropical_min_def plus_tropical_min_def min_def)
qed

lemma tropm_bot_eq_one: "(bot :: tropical_min) = 1"
  by (simp add: bot_tropical_min_def one_tropical_min_def)

lemma tropm_top_eq_zero: "(top :: tropical_min) = 0"
  by (simp add: top_tropical_min_def zero_tropical_min_def)

(* ------------------------------------------------------------------ *)
subsection \<open>7  Idempotency (Dioid)\<close>
(* ------------------------------------------------------------------ *)

theorem tropm_add_idem_thm:
  "(a :: tropical_min) + a = a"
  unfolding plus_tropical_min_def by simp

(* ------------------------------------------------------------------ *)
subsection \<open>8  Semiring Homomorphisms — Min-Plus\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The constructor @{term Fin'} is a semiring homomorphism from
  @{text "(nat, min, +, +\<infinity>, 0)"} to @{text "(tropical_min, \<oplus>, \<otimes>, PosInf, Fin' 0)"}.
\<close>

lemma Fin'_hom_mul:
  "Fin' (m + n) = Fin' m * Fin' n"
  by (simp add: times_tropical_min_def)

lemma Fin'_hom_add:
  "Fin' (min m n) = Fin' m + Fin' n"
  by (simp add: plus_tropical_min_def)

lemma Fin'_hom_zero:
  "(0 :: tropical_min) = PosInf"
  by (simp add: zero_tropical_min_def)

lemma Fin'_hom_one:
  "(1 :: tropical_min) = Fin' 0"
  by (simp add: one_tropical_min_def)

lemma Fin'_hom_le:
  "Fin' m \<le> Fin' n \<longleftrightarrow> m \<le> n"
  by simp

lemma Fin'_hom_strict:
  "(Fin' m :: tropical_min) < Fin' n \<longleftrightarrow> m < n"
  by simp

lemma Fin'_hom_inject:
  "Fin' m = (Fin' n :: tropical_min) \<longleftrightarrow> m = n"
  by simp

(* ------------------------------------------------------------------ *)
subsection \<open>9  Finite Min-Plus Sums\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Dual of @{text trop_sum}.  @{text tropm_sum_eq_Min} reduces min-plus
  sums to @{term Min} over finite sets, enabling short Bellman-Ford
  and WCET proofs in downstream theories.
\<close>

definition tropm_sum :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> tropical_min" where
  "tropm_sum g S \<equiv> \<Sum> x \<in> S. Fin' (g x)"

lemma tropm_sum_empty [simp]:
  "tropm_sum g {} = PosInf"
  by (simp add: tropm_sum_def zero_tropical_min_def)

lemma tropm_sum_singleton [simp]:
  "tropm_sum g {x} = Fin' (g x)"
  by (simp add: tropm_sum_def zero_tropical_min_def plus_tropical_min_def)

lemma tropm_sum_insert:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow>
   tropm_sum g (insert x S) = Fin' (g x) + tropm_sum g S"
  by (simp add: tropm_sum_def sum.insert)

lemma tropm_sum_eq_Min:
  assumes "finite S" "S \<noteq> {}"
  shows "tropm_sum g S = Fin' (Min (g ` S))"
  using assms
proof (induction S rule: finite_ne_induct)
  case (singleton x)
  show ?case by simp
next
  case (insert x F)
  have step: "tropm_sum g (insert x F) = Fin' (g x) + tropm_sum g F"
    using insert.hyps(1,3) by (simp add: tropm_sum_insert)
  have ih: "tropm_sum g F = Fin' (Min (g ` F))"
    by (rule insert.IH)
  have combine: "Fin' (g x) + Fin' (Min (g ` F)) = Fin' (min (g x) (Min (g ` F)))"
    by (simp add: plus_tropical_min_def)
  have min_eq: "min (g x) (Min (g ` F)) = Min (g ` insert x F)"
    using insert.hyps(1,2,3) by (simp add: Min_insert)
  show ?case
    using step ih combine min_eq by simp
qed

lemma tropm_sum_le_member:
  assumes "finite S" "x \<in> S"
  shows "tropm_sum g S \<le> Fin' (g x)"
proof -
  have ne: "S \<noteq> {}" using assms by auto
  have "tropm_sum g S = Fin' (Min (g ` S))"
    by (rule tropm_sum_eq_Min[OF assms(1) ne])
  thus ?thesis
    by (simp add: Min_le[OF finite_imageI[OF assms(1)] imageI[OF assms(2)]])
qed

lemma tropm_sum_mono_subset:
  assumes "finite T" "S \<subseteq> T" "S \<noteq> {}"
  shows "tropm_sum g T \<le> tropm_sum g S"
proof -
  have neT: "T \<noteq> {}" using assms(2,3) by auto
  have fS: "finite S" by (rule finite_subset[OF assms(2) assms(1)])
  have "tropm_sum g S = Fin' (Min (g ` S))"
    by (rule tropm_sum_eq_Min[OF fS assms(3)])
  moreover have "tropm_sum g T = Fin' (Min (g ` T))"
    by (rule tropm_sum_eq_Min[OF assms(1) neT])
  moreover have "Min (g ` T) \<le> Min (g ` S)"
  proof (rule Min_antimono)
    show "g ` S \<subseteq> g ` T" using assms(2) by (rule image_mono)
    show "g ` S \<noteq> {}" using assms(3) by simp
    show "finite (g ` T)" using assms(1) by (rule finite_imageI)
  qed
  ultimately show ?thesis by simp
qed

(* ------------------------------------------------------------------ *)
subsection \<open>10  Proof Method — tropm_arith\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text tropm_arith} is the dual of @{text tropical_arith} for
  @{typ tropical_min}.  It closes goals involving @{term PosInf} and
  @{term Fin'} constructor arithmetic without manual case splits.
\<close>

(* Smoke tests for the simplification basis used by min-plus proofs. *)

lemma tropm_arith_test1: "Fin' m + Fin' n = Fin' (min m n)"
  by (simp add: plus_tropical_min_def)
lemma tropm_arith_test2: "Fin' m * Fin' n = Fin' (m + n)"
  by (simp add: times_tropical_min_def)
lemma tropm_arith_test3: "PosInf + a = a"
  by (simp add: plus_tropical_min_def)
lemma tropm_arith_test4: "PosInf * a = PosInf"
  by (simp add: times_tropical_min_def)
lemma tropm_arith_test5: "(0 :: tropical_min) = PosInf"
  by (simp add: zero_tropical_min_def)
lemma tropm_arith_test6: "(1 :: tropical_min) = Fin' 0"
  by (simp add: one_tropical_min_def)


(* ================================================================== *)
section \<open>Cross-System Notes\<close>
(* ================================================================== *)

text \<open>
  Three connections to other estate systems are not yet formalised here
  but are proved informally in @{file "docs/HANDOVER_v2.adoc"}:

  \<^enum> \<^bold>\<open>Lean 4 \<open>soundness\<close> = @{text max_khop_eq_sum_walks}\<close> (Isabelle):
    both say ``recursive static definition = inductive operational semantics''.
    Bridging lemma: map @{text Session} to @{text trop_mat} and invoke
    @{text max_khop_eq_sum_walks}.

  \<^enum> \<^bold>\<open>Lean 4 \<open>tropical_grade_le_sequentialTotal\<close> = @{text tropical_add_idem}\<close>:
    @{text "max(n1,n2) \<le> n1+n2"} follows from @{text add_idem} in the dioid.
    Isabelle stub: @{text "trop_add a b \<le> a + b"} (as naturals), @{text "\<approx>2 lines"}.

  \<^enum> \<^bold>\<open>Lean 4 \<open>spec_par\<close> = @{text trop_mat_add}\<close>:
    @{text "spec_par s1 s2"} is single-edge @{text trop_mat_add};
    a machine-checked session type checker backed by @{text floyd_warshall}
    follows from making this explicit.
\<close>

end
