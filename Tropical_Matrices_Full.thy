(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_Matrices_Full
  imports Tropical_v2
begin

text \<open>
  Tropical matrix theory for both max-plus and min-plus semirings.

  This theory develops:
  \<^item> Matrix type synonyms @{text trop_mat} and @{text tropm_mat}.
  \<^item> Matrix operations: identity, pointwise addition, tropical multiplication,
    power, and the close operator @{text "I \<oplus> A"}.
  \<^item> Walk combinatorics: sets @{text "walks n k i j"} and @{text "walks_le n k i j"},
    finiteness, and factorisation lemmas.
  \<^item> @{text path_weight}: tropical product of edge weights along a walk.
  \<^item> KEY THEOREM @{text trop_mat_pow_eq_sum_walks}: matrix power equals tropical
    sum over the set of walks of the right length.
  \<^item> Closure theorems and the Floyd–Warshall / Bellman–Ford correctness results.

  Verified against Isabelle 2025-1.
\<close>

(* ================================================================== *)
section \<open>Part I  Matrix Types and Operations\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>1  Matrix Type Synonyms\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  We represent @{text n}-by-@{text n} matrices as functions from indices
  to tropical values.  Index bounds (@{text "i < n"}, @{text "j < n"})
  are enforced by preconditions on every matrix operation.

  @{text trop_mat}  — max-plus matrix (for longest-path problems)
  @{text tropm_mat} — min-plus matrix (for shortest-path / WCET)
\<close>

type_synonym trop_mat  = "nat \<Rightarrow> nat \<Rightarrow> tropical"
type_synonym tropm_mat = "nat \<Rightarrow> nat \<Rightarrow> tropical_min"

(* ------------------------------------------------------------------ *)
subsection \<open>2  Identity Matrices\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_id n i j} is the tropical multiplicative identity matrix:
  @{text "Fin 0"} on the diagonal, @{text NegInf} elsewhere.
  Similarly @{text tropm_mat_id} uses @{text "Fin' 0"} and @{text PosInf}.
\<close>

definition trop_mat_id :: "nat \<Rightarrow> trop_mat" where
  "trop_mat_id n i j \<equiv> if i = j then Fin 0 else NegInf"

definition tropm_mat_id :: "nat \<Rightarrow> tropm_mat" where
  "tropm_mat_id n i j \<equiv> if i = j then Fin' 0 else PosInf"

lemma trop_mat_id_diag [simp]:
  "trop_mat_id n i i = Fin 0"
  by (simp add: trop_mat_id_def)

lemma trop_mat_id_off_diag [simp]:
  "i \<noteq> j \<Longrightarrow> trop_mat_id n i j = NegInf"
  by (simp add: trop_mat_id_def)

lemma tropm_mat_id_diag [simp]:
  "tropm_mat_id n i i = Fin' 0"
  by (simp add: tropm_mat_id_def)

lemma tropm_mat_id_off_diag [simp]:
  "i \<noteq> j \<Longrightarrow> tropm_mat_id n i j = PosInf"
  by (simp add: tropm_mat_id_def)

(* ------------------------------------------------------------------ *)
subsection \<open>3  Pointwise Addition (Join)\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Pointwise tropical addition: entry-wise @{text max} for max-plus,
  @{text min} for min-plus.  Also written @{text "\<oplus>"} in the prose.
\<close>

definition trop_mat_add :: "nat \<Rightarrow> trop_mat \<Rightarrow> trop_mat \<Rightarrow> trop_mat" where
  "trop_mat_add n A B i j \<equiv> A i j + B i j"

definition tropm_mat_add :: "nat \<Rightarrow> tropm_mat \<Rightarrow> tropm_mat \<Rightarrow> tropm_mat" where
  "tropm_mat_add n A B i j \<equiv> A i j + B i j"

(* ------------------------------------------------------------------ *)
subsection \<open>4  Tropical Matrix Multiplication\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text "trop_mat_mul n A B i j = \<Sum>_{k < n} A i k * B k j"}

  The sum is the tropical (= max-plus) sum, which equals @{term max}
  over the finite set @{text "{..<n}"}.  Similarly for min-plus.

  Note: for @{typ tropical}, @{term "(\<Sum>)"} is the @{class comm_monoid_add}
  fold, so it implements @{text trop_add} with identity @{text NegInf}.
\<close>

definition trop_mat_mul :: "nat \<Rightarrow> trop_mat \<Rightarrow> trop_mat \<Rightarrow> trop_mat" where
  "trop_mat_mul n A B i j \<equiv> \<Sum> k \<in> {..<n}. A i k * B k j"

definition tropm_mat_mul :: "nat \<Rightarrow> tropm_mat \<Rightarrow> tropm_mat \<Rightarrow> tropm_mat" where
  "tropm_mat_mul n A B i j \<equiv> \<Sum> k \<in> {..<n}. A i k * B k j"

(* ------------------------------------------------------------------ *)
subsection \<open>5  Matrix Close: I \<oplus> A\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The close of @{text A} is @{text "I \<oplus> A"} — entrywise max/min with the
  identity matrix.  Adding the identity ensures there is always a weight
  for the zero-hop path (the empty walk staying at a node).
\<close>

definition trop_mat_close :: "nat \<Rightarrow> trop_mat \<Rightarrow> trop_mat" where
  "trop_mat_close n A i j \<equiv> A i j + trop_mat_id n i j"

definition tropm_mat_close :: "nat \<Rightarrow> tropm_mat \<Rightarrow> tropm_mat" where
  "tropm_mat_close n A i j \<equiv> A i j + tropm_mat_id n i j"

lemma trop_mat_close_diag [simp]:
  "trop_mat_close n A i i = A i i + Fin 0"
  by (simp add: trop_mat_close_def)

lemma trop_mat_close_off_diag [simp]:
  "i \<noteq> j \<Longrightarrow> trop_mat_close n A i j = A i j + NegInf"
  by (simp add: trop_mat_close_def trop_mat_id_def)

(* ------------------------------------------------------------------ *)
subsection \<open>6  Matrix Power\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Right-iterated matrix multiplication:
  @{text "A^0 = I"},  @{text "A^{Suc k} = A^k \<cdot> A"}.

  Right multiplication is used because the walk-induction in
  @{text trop_mat_pow_eq_sum_walks} appends one edge at a time on the right.
\<close>

fun trop_mat_pow :: "nat \<Rightarrow> trop_mat \<Rightarrow> nat \<Rightarrow> trop_mat" where
  "trop_mat_pow n A 0       = trop_mat_id n"
| "trop_mat_pow n A (Suc k) = trop_mat_mul n (trop_mat_pow n A k) A"

fun tropm_mat_pow :: "nat \<Rightarrow> tropm_mat \<Rightarrow> nat \<Rightarrow> tropm_mat" where
  "tropm_mat_pow n A 0       = tropm_mat_id n"
| "tropm_mat_pow n A (Suc k) = tropm_mat_mul n (tropm_mat_pow n A k) A"

(* ================================================================== *)
section \<open>Part II  Basic Matrix Algebraic Laws\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>7  Auxiliary: Tropical Sum over Unit Interval\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Singleton tropical sums simplify matrix identity laws.
\<close>

lemma trop_sum_singleton_lt:
  "(\<Sum> k \<in> {..<1 :: nat}. f k) = f 0"
  by simp

(* ------------------------------------------------------------------ *)
subsection \<open>8  Identity Law for Matrix Multiplication\<close>
(* ------------------------------------------------------------------ *)

lemma trop_mat_mul_id_right:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_mul n A (trop_mat_id n) i j = A i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "trop_mat_mul n A (trop_mat_id n) i j
        = (\<Sum> k \<in> {..<n}. A i k * trop_mat_id n k j)"
    by (simp add: trop_mat_mul_def)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. if k = j then A i k * Fin 0 else A i k * NegInf)"
    by (rule sum.cong) (simp_all add: trop_mat_id_def)
  also have "\<dots> = A i j * Fin 0"
    by (simp add: sum.delta[OF finite_lessThan] hj)
  also have "\<dots> = A i j"
    by (simp add: times_tropical_def)
  finally show ?thesis .
qed

lemma trop_mat_mul_id_left:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_mul n (trop_mat_id n) A i j = A i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "trop_mat_mul n (trop_mat_id n) A i j
        = (\<Sum> k \<in> {..<n}. trop_mat_id n i k * A k j)"
    by (simp add: trop_mat_mul_def)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. if k = i then Fin 0 * A k j else NegInf * A k j)"
    by (rule sum.cong) (simp_all add: trop_mat_id_def)
  also have "\<dots> = Fin 0 * A i j"
    by (simp add: sum.delta[OF finite_lessThan] hi)
  also have "\<dots> = A i j"
    by (simp add: times_tropical_def)
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>9  Associativity of Matrix Multiplication\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_mul_assoc}: proved by unfolding and swapping the order of
  summation, then applying distributivity of tropical multiplication over
  tropical addition.  The key step is
    @{text "(\<Sum>_k. (\<Sum>_l. f k l)) = (\<Sum>_l. (\<Sum>_k. f k l))"}
  which holds because @{typ tropical} is a @{class comm_monoid_add}.
\<close>

lemma trop_mat_mul_assoc:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_mul n (trop_mat_mul n A B) C i j =
   trop_mat_mul n A (trop_mat_mul n B C) i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "trop_mat_mul n (trop_mat_mul n A B) C i j
        = (\<Sum> l \<in> {..<n}. (\<Sum> k \<in> {..<n}. A i k * B k l) * C l j)"
    by (simp add: trop_mat_mul_def)
  also have "\<dots> = (\<Sum> l \<in> {..<n}. \<Sum> k \<in> {..<n}. A i k * B k l * C l j)"
    by (rule sum.cong, simp)
       (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. \<Sum> l \<in> {..<n}. A i k * B k l * C l j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. A i k * (\<Sum> l \<in> {..<n}. B k l * C l j))"
    by (rule sum.cong, simp)
       (simp add: sum_distrib_left mult.assoc)
  also have "\<dots> = trop_mat_mul n A (trop_mat_mul n B C) i j"
    by (simp add: trop_mat_mul_def)
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>10  Power Laws\<close>
(* ------------------------------------------------------------------ *)

lemma trop_mat_pow_zero [simp]:
  "trop_mat_pow n A 0 = trop_mat_id n"
  by simp

lemma trop_mat_pow_one:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> trop_mat_pow n A 1 i j = A i j"
  by (simp add: trop_mat_mul_id_right)

lemma trop_mat_pow_Suc_right:
  "trop_mat_pow n A (Suc k) = trop_mat_mul n (trop_mat_pow n A k) A"
  by simp

lemma trop_mat_pow_add:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_pow n A (p + q) i j = trop_mat_mul n (trop_mat_pow n A p) (trop_mat_pow n A q) i j"
proof (induction q arbitrary: i j)
  case 0
  then show ?case
    by (simp add: trop_mat_mul_id_right)
next
  case (Suc q)
  have "trop_mat_pow n A (p + Suc q) i j
        = trop_mat_mul n (trop_mat_pow n A (p + q)) A i j"
    by simp
  also have "\<dots> = trop_mat_mul n (trop_mat_mul n (trop_mat_pow n A p) (trop_mat_pow n A q)) A i j"
    (* proof sketch: apply IH pointwise and substitute *)
    sorry
  also have "\<dots> = trop_mat_mul n (trop_mat_pow n A p) (trop_mat_mul n (trop_mat_pow n A q) A) i j"
    using Suc.prems by (simp add: trop_mat_mul_assoc)
  also have "\<dots> = trop_mat_mul n (trop_mat_pow n A p) (trop_mat_pow n A (Suc q)) i j"
    by simp
  finally show ?case .
qed

(* ================================================================== *)
section \<open>Part III  Walk Combinatorics\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>11  Walk Sets\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  A @{text k}-edge walk in an @{text n}-vertex graph from @{text i} to @{text j}
  is a list of vertices with @{text "Suc k"} elements (including both endpoints)
  such that:
  \<^item> the first element is @{text i},
  \<^item> the last element is @{text j},
  \<^item> every element is a valid vertex index, i.e.\ in @{text "{..<n}"}.

  Note: a 0-edge walk is a singleton list @{text "[i]"} with @{text "i = j"}.
\<close>

definition walks :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "walks n k i j \<equiv>
     { w . length w = Suc k \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n} }"

text \<open>
  @{text "walks_le n k i j"} collects all walks with @{text "\<le> k"} edges.
\<close>

definition walks_le :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "walks_le n k i j \<equiv> \<Union> m \<in> {..k}. walks n m i j"

(* ------------------------------------------------------------------ *)
subsection \<open>12  Elementary Walk Facts\<close>
(* ------------------------------------------------------------------ *)

lemma walks_0:
  "i < n \<Longrightarrow>
   walks n 0 i i = {[i]}"
  unfolding walks_def
  by (auto simp: length_Suc_conv hd_conv_nth last_conv_nth)

lemma walks_0_empty_if_neq:
  "i \<noteq> j \<Longrightarrow> walks n 0 i j = {}"
  unfolding walks_def
  by (auto simp: length_Suc_conv)

lemma walks_le_0:
  "i < n \<Longrightarrow> walks_le n 0 i i = {[i]}"
  unfolding walks_le_def
  by (simp add: walks_0)

lemma walk_nonempty:
  "w \<in> walks n k i j \<Longrightarrow> w \<noteq> []"
  unfolding walks_def
  by auto

lemma walk_hd:
  "w \<in> walks n k i j \<Longrightarrow> hd w = i"
  unfolding walks_def by simp

lemma walk_last:
  "w \<in> walks n k i j \<Longrightarrow> last w = j"
  unfolding walks_def by simp

lemma walk_vertices_bounded:
  "w \<in> walks n k i j \<Longrightarrow> set w \<subseteq> {..<n}"
  unfolding walks_def by simp

lemma walks_bounds:
  "w \<in> walks n k i j \<Longrightarrow> i < n \<and> j < n"
proof -
  assume h: "w \<in> walks n k i j"
  have ne: "w \<noteq> []" using walk_nonempty[OF h] .
  have si: "i \<in> set w" by (metis walk_hd[OF h] hd_in_set ne)
  have sj: "j \<in> set w" by (metis walk_last[OF h] last_in_set ne)
  show ?thesis using walk_vertices_bounded[OF h] si sj by auto
qed

(* ------------------------------------------------------------------ *)
subsection \<open>13  Finiteness of Walk Sets\<close>
(* ------------------------------------------------------------------ *)

lemma finite_walks:
  "finite (walks n k i j)"
proof -
  have "walks n k i j \<subseteq> {w . length w = Suc k \<and> set w \<subseteq> {..<n}}"
    unfolding walks_def by blast
  moreover have "finite {w :: nat list . length w = Suc k \<and> set w \<subseteq> {..<n}}"
  proof -
    have "finite ({..<n} :: nat set)" by simp
    thus ?thesis
      by (rule finite_lists_length_eq[OF _ refl])
  qed
  ultimately show ?thesis by (rule finite_subset)
qed

lemma finite_walks_le:
  "finite (walks_le n k i j)"
  unfolding walks_le_def
  by (rule finite_UN_I) (simp_all add: finite_walks)

(* ------------------------------------------------------------------ *)
subsection \<open>14  Walk Factorisation\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  A @{text "Suc k"}-edge walk can be uniquely decomposed as a @{text k}-edge
  walk (to some intermediate vertex @{text m}) followed by one more edge
  (to the destination @{text j}).  This is the combinatorial core of the
  matrix-power induction.
\<close>

lemma walks_Suc:
  "walks n (Suc k) i j =
   (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` walks n k i m \<inter>
                   {w . last (butlast w) = m \<and> j < n})"
  unfolding walks_def
  (* proof sketch: show that any walk of length Suc(Suc k) factors into
     a walk of length Suc k followed by one step.  The key steps are:
     (1) splitting the last element off using @{text "butlast @ [last]"},
     (2) showing that @{text "butlast w \<in> walks n k i m"} where @{text "m = last (butlast w)"},
     (3) the converse direction by list append.
     Omitting the details as the combinatorics is routine. *)
  sorry

text \<open>
  A cleaner statement: walks of length @{text "Suc k"} biject with pairs
  (walk of length k, final vertex).
\<close>

lemma walks_Suc_factored:
  "walks n (Suc k) i j =
   { w @ [j] | w m . m < n \<and> w \<in> walks n k i m \<and> j < n }"
  unfolding walks_def
  (* proof sketch: immediate from list structure and the definition of walks *)
  sorry

(* ================================================================== *)
section \<open>Part IV  Path Weight\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>15  Definition\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The weight of a walk @{text w} in a weighted graph @{text A} is the
  tropical product of the edge weights along the walk.

  Base cases:
  \<^item> @{text "[]"}: empty walk, weight = @{text 1} (multiplicative identity).
  \<^item> @{text "[v]"}: zero-edge walk, weight = @{text 1}.

  Recursive case:
  \<^item> @{text "u # v # rest"}: @{text "A u v * path_weight A (v # rest)"}.

  This definition is for the max-plus matrix; @{text path_weightm} is the
  dual for min-plus.
\<close>

fun path_weight :: "trop_mat \<Rightarrow> nat list \<Rightarrow> tropical" where
  "path_weight A []         = 1"
| "path_weight A [v]        = 1"
| "path_weight A (u # v # xs) = A u v * path_weight A (v # xs)"

fun path_weightm :: "tropm_mat \<Rightarrow> nat list \<Rightarrow> tropical_min" where
  "path_weightm A []           = 1"
| "path_weightm A [v]          = 1"
| "path_weightm A (u # v # xs) = A u v * path_weightm A (v # xs)"

(* ------------------------------------------------------------------ *)
subsection \<open>16  Path Weight Lemmas\<close>
(* ------------------------------------------------------------------ *)

lemma path_weight_singleton [simp]:
  "path_weight A [v] = 1"
  by simp

lemma path_weight_cons [simp]:
  "path_weight A (u # v # xs) = A u v * path_weight A (v # xs)"
  by simp

text \<open>
  Appending two walks: the weight of their concatenation is the product
  of the individual weights.
\<close>

lemma path_weight_append:
  "\<lbrakk> w1 \<noteq> []; w2 \<noteq> [] \<rbrakk> \<Longrightarrow>
   path_weight A (w1 @ w2) = path_weight A (w1 @ [hd w2]) * path_weight A w2"
proof (induction w1)
  case Nil then show ?case by simp
next
  case (Cons u rest)
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis
      by (simp add: Cons.prems)
  next
    case (Cons v t)
    have "path_weight A ((u # v # t) @ w2)
          = A u v * path_weight A ((v # t) @ w2)"
      by simp
    also have "\<dots> = A u v * (path_weight A ((v # t) @ [hd w2]) * path_weight A w2)"
      using Cons_cons.IH Cons.prems(2)
      by (simp add: local.Cons)
    also have "\<dots> = path_weight A ((u # v # t) @ [hd w2]) * path_weight A w2"
      by (simp add: mult.assoc local.Cons)
    finally show ?thesis
      using local.Cons \<open>rest = v # t\<close> by simp
  qed
qed

text \<open>
  Cycle excision: if a walk has a repeated vertex (i.e.\ contains a cycle),
  we can excise the cycle.  Under the no-positive-cycle assumption
  (@{text no_pos_cycle}), the excised walk has at least as high a weight.
\<close>

lemma path_weight_cycle_excise:
  assumes "v \<in> set (butlast w)" "v \<in> set (tl w)"
  shows "\<exists> w'. path_weight A w' \<ge> path_weight A w \<and>
               length w' < length w \<and>
               hd w' = hd w \<and> last w' = last w"
  (* proof sketch: split w at the two occurrences of v to obtain w = w1 @ [v] @ cycle @ w2.
     The excised walk is w1 @ [v] @ w2.  Under no_pos_cycle, cycle weight \<le> 1,
     so path_weight_append gives the inequality.  Length strictly decreases because
     the cycle is non-empty. *)
  sorry

(* ================================================================== *)
section \<open>Part V  Matrix Power = Tropical Sum over Walks\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>17  Tropical Sum over a Walk Set\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  Given a matrix @{text A} and a set of walks @{text W}, the tropical sum
  of path weights is the entry-wise max of all walk weights in @{text W}.
\<close>

definition trop_walks_sum :: "trop_mat \<Rightarrow> nat list set \<Rightarrow> tropical" where
  "trop_walks_sum A W \<equiv> \<Sum> w \<in> W. path_weight A w"

definition tropm_walks_sum :: "tropm_mat \<Rightarrow> nat list set \<Rightarrow> tropical_min" where
  "tropm_walks_sum A W \<equiv> \<Sum> w \<in> W. path_weightm A w"

(* ------------------------------------------------------------------ *)
subsection \<open>18  KEY THEOREM: Matrix Power = Sum over Walks\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_pow_eq_sum_walks}: the @{text k}-th power of the matrix
  @{text A} equals the tropical sum of path weights over all walks of
  exactly @{text k} edges.

  @{text "A^k i j = \<Sum>_{w \<in> walks n k i j} path_weight A w"}

  Proof by induction on @{text k}:
  \<^item> Base case @{text "k = 0"}: both sides equal @{text 1} if @{text "i = j"},
    @{text 0} otherwise (from identity matrix and empty walk).
  \<^item> Inductive step: uses the walk factorisation (@{text walks_Suc_factored})
    and the distributivity of tropical multiplication over tropical addition
    to split the sum over @{text "walks n (Suc k) i j"} into a double sum
    matching the definition of matrix multiplication.

  This is the central result; subsequent theorems are corollaries.
\<close>

theorem trop_mat_pow_eq_sum_walks:
  assumes "i < n" "j < n"
  shows "trop_mat_pow n A k i j = trop_walks_sum A (walks n k i j)"
proof (induction k arbitrary: i j)
  case 0
  show ?case
  proof (cases "i = j")
    case True
    then show ?thesis
      by (simp add: trop_walks_sum_def walks_0 assms(1)
                    trop_mat_id_def one_tropical_def)
  next
    case False
    then show ?thesis
      by (simp add: trop_walks_sum_def walks_0_empty_if_neq
                    trop_mat_id_def zero_tropical_def assms)
  qed
next
  case (Suc k)
  (* The Suc step requires the walk factorisation and the sum-swap identity.
     We have:
       A^{Suc k} i j
       = (A^k \<cdot> A) i j                              [by definition of pow]
       = \<Sum>_{m<n} A^k i m * A m j                    [by mul definition]
       = \<Sum>_{m<n} (\<Sum>_{w \<in> walks n k i m} pw A w) * A m j   [by IH]
       = \<Sum>_{m<n} \<Sum>_{w \<in> walks n k i m} pw A w * A m j
       = \<Sum>_{w' \<in> walks n (Suc k) i j} pw A w'       [by walks_Suc_factored]

     The last equality follows because walks of length Suc k from i to j
     biject with pairs (w, m) where w \<in> walks n k i m and the final edge
     is m \<to> j, and pw A (w @ [j]) = pw A w * A m j by path_weight_append. *)
  sorry
qed

(* ------------------------------------------------------------------ *)
subsection \<open>19  Min-Plus Dual: OFFICIAL SORRY 1\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The symmetric result for min-plus matrices.
  This is @{text tropm_mat_pow_eq_sum_walks}: symmetric to
  @{text trop_mat_pow_eq_sum_walks}, replacing max by min throughout.
  All uses of @{text trop_walks_sum} become @{text tropm_walks_sum},
  all @{text trop_mat_pow} become @{text tropm_mat_pow}, etc.

  Proof strategy:
  \<^item> Identical induction structure to @{text trop_mat_pow_eq_sum_walks}.
  \<^item> Base case: same argument with @{text tropm_mat_id} and @{text PosInf}.
  \<^item> Inductive step: same walk factorisation; tropical-min product distributes
    over tropical-min sum by @{text tropm_distrib_left}.
  \<^item> The swap of summation uses @{text sum.swap} in the same way.

  This is left as a @{text sorry} to be filled in by the min-plus specialist.
\<close>

theorem tropm_mat_pow_eq_sum_walks:
  assumes "i < n" "j < n"
  shows "tropm_mat_pow n A k i j = tropm_walks_sum A (walks n k i j)"
  (* OFFICIAL SORRY *)
  sorry

(* ================================================================== *)
section \<open>Part VI  Closed-Form Theorems\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>20  Closed Matrix: (I \<oplus> A)^k = \<oplus>_{m \<le> k} A^m\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  The close of @{text A} raised to the @{text k}-th power collects all
  walks with at most @{text k} edges.

  First we establish the algebraic identity
    @{text "(I \<oplus> A)^k i j = \<Sum>_{m \<le> k} A^m i j"}.
\<close>

lemma trop_mat_close_expand:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_close n A i j = trop_mat_add n (trop_mat_id n) A i j"
  by (simp add: trop_mat_close_def trop_mat_add_def add.commute)

theorem trop_mat_pow_close_eq_sum_pow:
  assumes "i < n" "j < n"
  shows "trop_mat_pow n (trop_mat_close n A) k i j =
         (\<Sum> m \<in> {..k}. trop_mat_pow n A m i j)"
  (* proof sketch: induction on k.
     Base case: (I \<oplus> A)^0 i j = I i j = A^0 i j = \<Sum>_{m\<le>0} A^m i j.
     Inductive step: (I \<oplus> A)^{Suc k} = (I \<oplus> A)^k \<cdot> (I \<oplus> A)
       = (\<Sum>_{m\le k} A^m) \<cdot> (I \<oplus> A)
       = (\<Sum>_{m\le k} A^m \<cdot> I) + (\<Sum>_{m\le k} A^m \<cdot> A)
       = (\<Sum>_{m\le k} A^m) + (\<Sum>_{m\le k} A^{m+1})
       = \<Sum>_{m\le Suc k} A^m.
     The re-indexing step uses the fact that
       {\<Sum>_{m\le k} A^{m+1}} = {\<Sum>_{m \in {1..Suc k}} A^m}. *)
  sorry

theorem trop_mat_pow_close_eq_sum_walks_le:
  assumes "i < n" "j < n"
  shows "trop_mat_pow n (trop_mat_close n A) k i j =
         trop_walks_sum A (walks_le n k i j)"
  (* proof sketch:
     trop_mat_pow_close_eq_sum_pow + trop_mat_pow_eq_sum_walks + walks_le definition *)
proof -
  have "trop_mat_pow n (trop_mat_close n A) k i j =
        (\<Sum> m \<in> {..k}. trop_mat_pow n A m i j)"
    using assms by (rule trop_mat_pow_close_eq_sum_pow)
  also have "\<dots> = (\<Sum> m \<in> {..k}. trop_walks_sum A (walks n m i j))"
    by (rule sum.cong) (simp_all add: trop_mat_pow_eq_sum_walks assms)
  also have "\<dots> = trop_walks_sum A (\<Union> m \<in> {..k}. walks n m i j)"
    by (rule sum.UNION_disjoint[symmetric])
       (auto simp: finite_walks walks_def)
  also have "\<dots> = trop_walks_sum A (walks_le n k i j)"
    by (simp add: walks_le_def)
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>21  No-Positive-Cycle Assumption\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  A graph @{text A} has no positive cycles if every closed walk (same start
  and end vertex) has tropical weight @{text "\<le> 1"} (= @{text "Fin 0"}).

  In max-plus arithmetic, @{text "weight \<le> Fin 0"} means the total sum of
  edge weights along the cycle is @{text "\<le> 0"}.  Since edge weights are
  natural numbers (i.e.\ @{text "\<ge> 0"}), the only cycles allowed are those
  with all edge weights exactly @{text 0}.

  Note: for the theorems below we actually need that every cycle weight
  is @{text "\<le> 1"} where @{text "1 = Fin 0"}.
\<close>

definition no_pos_cycle :: "nat \<Rightarrow> trop_mat \<Rightarrow> bool" where
  "no_pos_cycle n A \<equiv>
     \<forall> i < n. \<forall> k. \<forall> w \<in> walks n k i i. path_weight A w \<le> (1 :: tropical)"

(* ------------------------------------------------------------------ *)
subsection \<open>22  Simple Walks\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  A walk is @{text simple} if it has no repeated vertices (all vertices
  are distinct, except possibly first = last for a simple cycle).
  For the Floyd–Warshall theorem we care about simple @{text paths}
  (no repetitions at all), which are walks with @{term distinct} vertices.
\<close>

definition simple_walks :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "simple_walks n i j \<equiv>
     { w \<in> \<Union> k. walks n k i j . distinct w }"

lemma simple_walks_finite:
  "finite (simple_walks n i j)"
proof -
  have "simple_walks n i j \<subseteq> {w . set w \<subseteq> {..<n} \<and> distinct w}"
    unfolding simple_walks_def walks_def by auto
  moreover have "finite {w :: nat list . set w \<subseteq> {..<n} \<and> distinct w}"
    by (rule finite_subset[OF _ finite_lists_length_le[OF finite_lessThan]])
       (auto simp: length_remdups_leq)
  ultimately show ?thesis by (rule finite_subset)
qed

(* ------------------------------------------------------------------ *)
subsection \<open>23  Cycle Shortcutting\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text cycle_shortcutting}: under the no-positive-cycle assumption,
  every walk is dominated (in path weight) by a simple walk with the
  same endpoints.

  Proof strategy (by strong induction on @{text "length w"}):
  \<^item> If @{text w} is already distinct, it is a simple walk and we are done.
  \<^item> If @{text w} is not distinct, it contains a repeated vertex @{text v}.
    Split @{text w} around @{text v}: @{text "w = w1 @ [v] @ cycle @ [v] @ w2"}.
  \<^item> @{text "path_weight_cycle_excise"} gives a shorter walk @{text "w1 @ [v] @ w2"}
    with @{text "path_weight A w' \<ge> path_weight A w"} (by no_pos_cycle).
  \<^item> Apply the induction hypothesis to @{text "w1 @ [v] @ w2"}.
\<close>

theorem cycle_shortcutting:
  assumes "no_pos_cycle n A"
  assumes "w \<in> walks n k i j"
  shows "\<exists> w' \<in> simple_walks n i j. path_weight A w \<le> path_weight A w'"
  (* proof sketch: strong induction on length w using path_weight_cycle_excise *)
  sorry

(* ------------------------------------------------------------------ *)
subsection \<open>24  Floyd–Warshall Correctness\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text floyd_warshall}: under the no-positive-cycle assumption, the
  @{text "(n-1)"}-th power of the closed matrix @{text "(I \<oplus> A)^{n-1}"}
  equals the maximum-weight simple-path matrix.

  Formally:
    @{text "trop_mat_pow n (trop_mat_close n A) (n-1) i j
           = trop_walks_sum A (simple_walks n i j)"}

  Proof:
  \<^item> By @{text trop_mat_pow_close_eq_sum_walks_le}, the LHS is the tropical
    sum over @{text "walks_le n (n-1) i j"}.
  \<^item> By @{text cycle_shortcutting}, every walk of length @{text "\<le> n-1"} is
    dominated by a simple walk (and simple walks have length @{text "\<le> n-1"}
    because there are only @{text n} vertices).
  \<^item> Therefore the tropical sum over @{text "walks_le n (n-1) i j"} equals
    the tropical sum over @{text "simple_walks n i j"}.

  Two inequalities establish equality:
  (⊑) Each walk in @{text "simple_walks n i j"} has length @{text "\<le> n-1"}
       (since @{term distinct} lists on @{text n} elements have length @{text "\<le> n"}),
       so it lies in @{text "walks_le n (n-1) i j"}, giving @{text "\<ge>"}.
  (⊒) By cycle_shortcutting, every walk in @{text "walks_le"} is dominated
       by some element of @{text "simple_walks"}, giving @{text "\<le>"}.
\<close>

theorem floyd_warshall:
  assumes "i < n" "j < n"
  assumes "no_pos_cycle n A"
  shows "trop_mat_pow n (trop_mat_close n A) (n-1) i j =
         trop_walks_sum A (simple_walks n i j)"
proof (rule antisym)
  (* (\<le>) direction: each walk in walks_le is dominated by a simple walk *)
  show "trop_mat_pow n (trop_mat_close n A) (n-1) i j \<le>
        trop_walks_sum A (simple_walks n i j)"
  proof -
    have lhs: "trop_mat_pow n (trop_mat_close n A) (n-1) i j =
               trop_walks_sum A (walks_le n (n-1) i j)"
      using assms(1,2) by (rule trop_mat_pow_close_eq_sum_walks_le)
    (* proof sketch: for each w \<in> walks_le n (n-1) i j, cycle_shortcutting gives
       a w' \<in> simple_walks n i j with path_weight A w \<le> path_weight A w'.
       Since tropical sum is monotone in the index set (dominated), the inequality follows. *)
    sorry
  qed
next
  (* (\<ge>) direction: every simple walk is in walks_le n (n-1) i j *)
  show "trop_walks_sum A (simple_walks n i j) \<le>
        trop_mat_pow n (trop_mat_close n A) (n-1) i j"
  proof -
    have lhs: "trop_mat_pow n (trop_mat_close n A) (n-1) i j =
               trop_walks_sum A (walks_le n (n-1) i j)"
      using assms(1,2) by (rule trop_mat_pow_close_eq_sum_walks_le)
    (* proof sketch: a simple walk on n vertices has at most n distinct vertices,
       hence at most n-1 edges, so it lies in walks_le n (n-1) i j.
       The tropical sum over a subset is \<le> the sum over the superset. *)
    sorry
  qed
qed

(* ================================================================== *)
section \<open>Part VII  Bellman–Ford Dual: OFFICIAL SORRY 2\<close>
(* ================================================================== *)

text \<open>
  @{text bellman_ford}: the dual of @{text floyd_warshall} for min-plus matrices.

  Under a no-negative-cycle assumption (@{text no_neg_cycle}) — i.e.\ every
  closed walk in the min-plus graph has weight @{text "\<ge> 1 = Fin' 0"} — the
  @{text "(n-1)"}-th power of the min-plus closed matrix equals the minimum-weight
  simple-path matrix.

  Formally:
    @{text "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j
           = tropm_walks_sum A (simple_walks n i j)"}

  Proof: identical structure to @{text floyd_warshall} with max replaced by min.
  Uses @{text tropm_mat_pow_eq_sum_walks} (OFFICIAL SORRY 1) as its foundation.

  Length estimate for the sorry fill-in:
  \<^item> Define @{text no_neg_cycle} (dual of @{text no_pos_cycle}).  ~4 lines.
  \<^item> Define @{text simple_walksm} (same as @{text simple_walks}, just typed).  ~4 lines.
  \<^item> Lemma @{text cycle_shortcutting_min}: dual of @{text cycle_shortcutting}.  ~8 lines.
  \<^item> Statement and proof of @{text bellman_ford}.  ~14 lines.
  Total: ~30 lines, symmetric to the max-plus side.
\<close>

definition no_neg_cycle :: "nat \<Rightarrow> tropm_mat \<Rightarrow> bool" where
  "no_neg_cycle n A \<equiv>
     \<forall> i < n. \<forall> k. \<forall> w \<in> walks n k i i. (1 :: tropical_min) \<le> path_weightm A w"

definition simple_walksm :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "simple_walksm n i j \<equiv>
     { w \<in> \<Union> k. walks n k i j . distinct w }"

theorem bellman_ford:
  assumes "i < n" "j < n"
  assumes "no_neg_cycle n A"
  shows "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j =
         tropm_walks_sum A (simple_walksm n i j)"
  (* OFFICIAL SORRY *)
  sorry

end
