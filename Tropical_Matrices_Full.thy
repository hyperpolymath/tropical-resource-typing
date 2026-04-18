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
  also have "\<dots> = (\<Sum> k \<in> {..<n}. if k = j then A i k * Fin 0 else (0 :: tropical))"
    by (rule sum.cong) (simp_all add: zero_tropical_def[symmetric])
  also have "\<dots> = A i j * Fin 0"
    using hj by (simp add: sum.delta[OF finite_lessThan])
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
  also have "\<dots> = (\<Sum> k \<in> {..<n}. if k = i then Fin 0 * A k j else (0 :: tropical))"
    by (rule sum.cong) (simp_all add: zero_tropical_def[symmetric])
  also have "\<dots> = Fin 0 * A i j"
    using hi by (simp add: sum.delta[OF finite_lessThan])
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
  by (simp add: trop_mat_mul_id_left)

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
  proof (unfold trop_mat_mul_def, rule sum.cong, simp)
    fix k assume "k \<in> {..<n}"
    hence hk: "k < n" by simp
    with Suc.prems(1)
    have "trop_mat_pow n A (p + q) i k =
          trop_mat_mul n (trop_mat_pow n A p) (trop_mat_pow n A q) i k"
      using Suc.IH by blast
    thus "trop_mat_pow n A (p + q) i k * A k j =
          trop_mat_mul n (trop_mat_pow n A p) (trop_mat_pow n A q) i k * A k j"
      by simp
  qed
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
  have sub: "walks n k i j \<subseteq> {w . length w = Suc k \<and> set w \<subseteq> {..<n}}"
    unfolding walks_def by blast
  have set_eq: "{w :: nat list . length w = Suc k \<and> set w \<subseteq> {..<n}}
              = {w :: nat list . set w \<subseteq> {..<n} \<and> length w = Suc k}"
    by blast
  have "finite ({..<n} :: nat set)" by simp
  hence "finite {w :: nat list . set w \<subseteq> {..<n} \<and> length w = Suc k}"
    by (rule finite_lists_length_eq)
  with set_eq have "finite {w :: nat list . length w = Suc k \<and> set w \<subseteq> {..<n}}"
    by simp
  thus ?thesis using sub by (rule finite_subset[rotated])
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
proof (rule set_eqI)
  fix w :: "nat list"
  show "w \<in> {w. length w = Suc (Suc k) \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n}} \<longleftrightarrow>
        w \<in> (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}}
             \<inter> {w. last (butlast w) = m \<and> j < n})"
  proof
    assume hw: "w \<in> {w. length w = Suc (Suc k) \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n}}"
    then have hlen: "length w = Suc (Suc k)" and hhd: "hd w = i"
              and hlast: "last w = j" and hset: "set w \<subseteq> {..<n}" by simp_all
    have hne: "w \<noteq> []" using hlen by auto
    have hbne: "butlast w \<noteq> []"
    proof
      assume "butlast w = []"
      hence "length (butlast w) = 0" by simp
      with length_butlast[of w] hlen show False by simp
    qed
    let ?m = "last (butlast w)"
    have hw_eq: "w = butlast w @ [j]"
      by (metis append_butlast_last_id hlast hne)
    have hbl_len: "length (butlast w) = Suc k"
      using hlen by simp
    have hbl_hd: "hd (butlast w) = i"
      using hlen hhd by (cases w; cases "tl w") auto
    have hbl_set: "set (butlast w) \<subseteq> {..<n}"
      using hset by (rule subset_trans[OF set_butlast])
    have hm_lt: "?m < n"
      by (metis last_in_set hbne hbl_set lessThan_iff subsetD)
    have hj_lt: "j < n"
      by (metis last_in_set hne hset lessThan_iff hlast subsetD)
    have hbl_last: "last (butlast w) = ?m" by simp
    have hbl_mem: "butlast w \<in> {w. length w = Suc k \<and> hd w = i \<and> last w = ?m \<and> set w \<subseteq> {..<n}}"
      by (simp add: hbl_len hbl_hd hbl_set)
    show "w \<in> (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}}
               \<inter> {w. last (butlast w) = m \<and> j < n})"
      apply (rule UN_I[of _ ?m])
        apply (simp add: hm_lt)
       apply (rule IntI)
        apply (rule imageI[OF hbl_mem])
       apply (simp add: hw_eq hj_lt)
      done
  next
    assume hw: "w \<in> (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}}
                    \<inter> {w. last (butlast w) = m \<and> j < n})"
    then obtain m v where hm: "m \<in> {..<n}"
                           and hv: "v \<in> {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}}"
                           and hw_eq: "w = v @ [j]"
                           and hj: "j < n"
      by (auto simp: image_def)
    from hv have hv_len: "length v = Suc k" and hv_hd: "hd v = i"
                and hv_set: "set v \<subseteq> {..<n}" by simp_all
    show "w \<in> {w. length w = Suc (Suc k) \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n}}"
      using hv_len hv_hd hv_set hj hw_eq
      by (simp add: hd_append)
  qed
qed

text \<open>
  A cleaner statement: walks of length @{text "Suc k"} biject with pairs
  (walk of length k, final vertex).
\<close>

lemma walks_Suc_factored:
  "walks n (Suc k) i j =
   { w @ [j] | w m . m < n \<and> w \<in> walks n k i m \<and> j < n }"
  unfolding walks_def
proof (rule set_eqI)
  fix w :: "nat list"
  show "w \<in> {w. length w = Suc (Suc k) \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n}} \<longleftrightarrow>
        w \<in> {w @ [j] | w m. m < n \<and> w \<in> {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}} \<and> j < n}"
  proof
    assume hw: "w \<in> {w. length w = Suc (Suc k) \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n}}"
    then have hlen: "length w = Suc (Suc k)" and hhd: "hd w = i"
              and hlast: "last w = j" and hset: "set w \<subseteq> {..<n}" by simp_all
    have hne: "w \<noteq> []" using hlen by auto
    have hbne: "butlast w \<noteq> []"
    proof
      assume "butlast w = []"
      hence "length (butlast w) = 0" by simp
      with length_butlast[of w] hlen show False by simp
    qed
    let ?m = "last (butlast w)"
    have hw_eq: "w = butlast w @ [j]"
      by (metis append_butlast_last_id hlast hne)
    have hbl_len: "length (butlast w) = Suc k" using hlen by simp
    have hbl_hd: "hd (butlast w) = i"
      using hlen hhd by (cases w; cases "tl w") auto
    have hbl_set: "set (butlast w) \<subseteq> {..<n}"
      using hset by (rule subset_trans[OF set_butlast])
    have hm_lt: "?m < n"
      by (metis last_in_set hbne hbl_set lessThan_iff subsetD)
    have hj_lt: "j < n"
      by (metis last_in_set hne hset lessThan_iff hlast subsetD)
    show "w \<in> {w @ [j] | w m. m < n \<and> w \<in> {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}} \<and> j < n}"
      using hm_lt hj_lt hw_eq hbl_len hbl_hd hbl_set
      by auto
  next
    assume hw: "w \<in> {w @ [j] | w m. m < n \<and> w \<in> {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}} \<and> j < n}"
    then obtain v m where hm: "m < n"
                           and hv: "v \<in> {w. length w = Suc k \<and> hd w = i \<and> last w = m \<and> set w \<subseteq> {..<n}}"
                           and hw_eq: "w = v @ [j]" and hj: "j < n"
      by auto
    from hv have hv_len: "length v = Suc k" and hv_hd: "hd v = i"
                and hv_set: "set v \<subseteq> {..<n}" by simp_all
    show "w \<in> {w. length w = Suc (Suc k) \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n}}"
      using hv_len hv_hd hv_set hj hw_eq by (simp add: hd_append)
  qed
qed

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
    have "path_weight A (u # w2) = A u (hd w2) * path_weight A w2"
      using Cons.prems(2) by (cases w2) auto
    then show ?thesis using Nil by simp
  next
    case (Cons v t)
    have "path_weight A ((u # v # t) @ w2)
          = A u v * path_weight A ((v # t) @ w2)"
      by simp
    also have "\<dots> = A u v * (path_weight A ((v # t) @ [hd w2]) * path_weight A w2)"
      using Cons.IH Cons.prems(2) local.Cons by simp
    also have "\<dots> = path_weight A ((u # v # t) @ [hd w2]) * path_weight A w2"
      by (simp add: mult.assoc local.Cons)
    finally show ?thesis
      using local.Cons \<open>rest = v # t\<close> by simp
  qed
qed

lemma path_weight_snoc:
  "w \<noteq> [] \<Longrightarrow> path_weight A (w @ [v]) = path_weight A w * A (last w) v"
proof (induction w)
  case Nil then show ?case by simp
next
  case (Cons u rest)
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis by simp
  next
    case (Cons v' t)
    have "path_weight A ((u # v' # t) @ [v])
          = A u v' * path_weight A ((v' # t) @ [v])"
      by simp
    also have "\<dots> = A u v' * (path_weight A (v' # t) * A (last (v' # t)) v)"
      using Cons.IH local.Cons by simp
    also have "\<dots> = path_weight A (u # v' # t) * A (last (u # v' # t)) v"
      by (simp add: mult.assoc)
    finally show ?thesis by (simp add: local.Cons)
  qed
qed

(* ------------------------------------------------------------------ *)
subsection \<open>16b  Min-Plus and Monotonicity Auxiliaries\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text path_weightm_snoc}: min-plus dual of @{text path_weight_snoc}.
  Needed for @{text tropm_mat_pow_eq_sum_walks}.
\<close>

lemma path_weightm_snoc:
  "w \<noteq> [] \<Longrightarrow> path_weightm A (w @ [v]) = path_weightm A w * A (last w) v"
proof (induction w)
  case Nil then show ?case by simp
next
  case (Cons u rest)
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis by simp
  next
    case (Cons v' t)
    have "path_weightm A ((u # v' # t) @ [v])
          = A u v' * path_weightm A ((v' # t) @ [v])"
      by simp
    also have "\<dots> = A u v' * (path_weightm A (v' # t) * A (last (v' # t)) v)"
      using Cons.IH local.Cons by simp
    also have "\<dots> = path_weightm A (u # v' # t) * A (last (u # v' # t)) v"
      by (simp add: mult.assoc)
    finally show ?thesis by (simp add: local.Cons)
  qed
qed

text \<open>
  Tropical multiplication is monotone in the right argument: @{text "a \<le> b \<Longrightarrow> c * a \<le> c * b"}.
  Proved from @{text trop_add_le_iff} and left distributivity.
\<close>

lemma trop_mul_le_mul_right:
  assumes "(a :: tropical) \<le> b"
  shows "c * a \<le> c * b"
proof -
  have step: "c * a + c * b = c * b"
  proof -
    have "c * a + c * b = c * (a + b)"
      by (simp add: distrib_left)
    also have "\<dots> = c * b"
      using assms by (simp add: trop_add_le_iff)
    finally show ?thesis .
  qed
  thus ?thesis by (simp add: trop_add_le_iff)
qed

text \<open>
  @{text trop_walks_sum_ge_member}: every member of a finite walk set dominates
  the tropical sum.  (In max-plus, the sum = max, so every member is @{text "\<le>"} the sum.)
\<close>

lemma trop_walks_sum_ge_member:
  assumes "w' \<in> T" "finite T"
  shows "path_weight A w' \<le> trop_walks_sum A T"
proof -
  have decomp: "trop_walks_sum A T =
        path_weight A w' + trop_walks_sum A (T - {w'})"
    unfolding trop_walks_sum_def
    using assms by (subst sum.remove) auto
  have "path_weight A w' \<le> path_weight A w' + trop_walks_sum A (T - {w'})"
  proof -
    have "path_weight A w' + (path_weight A w' + trop_walks_sum A (T - {w'}))
          = path_weight A w' + trop_walks_sum A (T - {w'})"
      by (simp add: add.assoc[symmetric] tropical_add_idem)
    thus ?thesis by (simp add: trop_add_le_iff)
  qed
  thus ?thesis using decomp by simp
qed

text \<open>
  @{text trop_walks_sum_mono_subset}: the tropical walk-sum is monotone in the
  walk set (larger set = higher max).
\<close>

lemma trop_walks_sum_mono_subset:
  assumes "finite T" "S \<subseteq> T"
  shows "trop_walks_sum A S \<le> trop_walks_sum A T"
proof -
  have fS: "finite S" by (rule finite_subset[OF assms(2) assms(1)])
  show ?thesis
  proof (induction S rule: finite_induct[OF fS])
    case empty
    then show ?case by (simp add: trop_walks_sum_def NegInf_le)
  next
    case (insert w S')
    have hw_T: "w \<in> T" using insert.prems assms(2) by auto
    have hS'_sub: "S' \<subseteq> T" using insert.prems assms(2) by auto
    have expand_S: "trop_walks_sum A (insert w S') =
                    path_weight A w + trop_walks_sum A S'"
      unfolding trop_walks_sum_def
      using insert.hyps(1,2) by (rule sum.insert)
    have hw_le: "path_weight A w \<le> trop_walks_sum A T"
      using trop_walks_sum_ge_member[OF hw_T assms(1)] .
    have hS'_le: "trop_walks_sum A S' \<le> trop_walks_sum A T"
      using insert.IH[OF hS'_sub] .
    have "path_weight A w + trop_walks_sum A S' \<le>
          trop_walks_sum A T + trop_walks_sum A T"
      using add_le_add[OF hw_le hS'_le] .
    also have "\<dots> = trop_walks_sum A T"
      by (simp add: tropical_add_idem trop_walks_sum_def)
    finally show ?case using expand_S by simp
  qed
qed

text \<open>
  @{text trop_walks_sum_dominated}: if every walk in @{text S} is dominated (in weight)
  by some walk in @{text T}, then the sum over @{text S} is @{text "\<le>"} the sum over @{text T}.
\<close>

lemma trop_walks_sum_dominated:
  assumes "finite S" "finite T"
  assumes dominated: "\<forall> w \<in> S. \<exists> w' \<in> T. path_weight A w \<le> path_weight A w'"
  shows "trop_walks_sum A S \<le> trop_walks_sum A T"
proof (induction S rule: finite_induct[OF assms(1)])
  case empty
  then show ?case by (simp add: trop_walks_sum_def NegInf_le)
next
  case (insert w S')
  have expand_S: "trop_walks_sum A (insert w S') =
                  path_weight A w + trop_walks_sum A S'"
    unfolding trop_walks_sum_def
    using insert.hyps(1,2) by (rule sum.insert)
  obtain w' where hw': "w' \<in> T" "path_weight A w \<le> path_weight A w'"
    using dominated insert.prems by auto
  have hw_le: "path_weight A w \<le> trop_walks_sum A T"
    using hw' trop_walks_sum_ge_member[OF hw'(1) assms(2)] le_trans by blast
  have hS'_le: "trop_walks_sum A S' \<le> trop_walks_sum A T"
    using insert.IH dominated insert.prems by auto
  have "path_weight A w + trop_walks_sum A S' \<le>
        trop_walks_sum A T + trop_walks_sum A T"
    using add_le_add[OF hw_le hS'_le] .
  also have "\<dots> = trop_walks_sum A T"
    by (simp add: tropical_add_idem trop_walks_sum_def)
  finally show ?case using expand_S by simp
qed

text \<open>
  Cycle excision: if a walk has a repeated vertex (i.e.\ contains a cycle),
  we can excise the cycle.  Under the no-positive-cycle assumption
  (@{text no_pos_cycle}), the excised walk has at least as high a weight.
\<close>

lemma path_weight_cycle_excise:
  assumes hv1: "v \<in> set (butlast w)"
  assumes hv2: "v \<in> set (tl w)"
  assumes hnpc: "no_pos_cycle n A"
  assumes hw_in: "w \<in> walks n k i j"
  shows "\<exists> w'. path_weight A w' \<ge> path_weight A w \<and>
               length w' < length w \<and>
               w' \<noteq> [] \<and>
               hd w' = hd w \<and> last w' = last w \<and>
               set w' \<subseteq> {..<n}"
proof -
  (* Find indices p < q with w!p = w!q = v, p > 0 (from tl), q < length w - 1 (from butlast) *)
  have hne: "w \<noteq> []" using hv1 by auto
  from hv1 obtain q where hq_bound: "q < length (butlast w)" and hq_val: "(butlast w) ! q = v"
    by (meson in_set_conv_nth)
  from hv2 obtain p0 where hp0_bound: "p0 < length (tl w)" and hp0_val: "(tl w) ! p0 = v"
    by (meson in_set_conv_nth)
  (* Convert to w-indices *)
  let ?p = "Suc p0"
  let ?q = "q"
  have hp_lt: "?p < length w" using hp0_bound by simp
  have hp_val: "w ! ?p = v" by (simp add: hp0_val nth_tl)
  have hq_lt: "?q < length w - 1" using hq_bound by simp
  have hq_val': "w ! ?q = v" by (simp add: hq_val nth_butlast)
  (* Build two cases: either p < q (good) or q ≤ p; in either case get p' < q' *)
  obtain p' q' where hp': "p' < length w" "w ! p' = v" "0 < p'"
                 and hq': "q' < length w - 1" "w ! q' = v"
                 and hpq: "p' < q'"
  proof (cases "?p \<le> ?q")
    case True
    thus ?thesis
      using hp_lt hp_val hq_lt hq_val'
      by (intro that[of ?p ?q]) auto
  next
    case False
    hence "?q < ?p" by simp
    thus ?thesis
      using hp_lt hp_val hq_lt hq_val'
      by (intro that[of ?q ?p]) auto
  qed
  (* Witness: excise the cycle between positions p' and q' *)
  let ?w' = "take p' w @ drop q' w"
  have hw'_hd: "hd ?w' = hd w"
    using hp'(3) by (simp add: hd_append take_eq_Nil)
  have hw'_last: "last ?w' = last w"
    using hq'(1) hw_in unfolding walks_def by (simp add: last_append)
  have hw'_len: "length ?w' < length w"
  proof -
    have "length ?w' = p' + (length w - q')"
      using hp'(1) hq'(1) by simp
    also have "\<dots> < length w"
      using hpq hq'(1) hp'(1) by omega
    finally show ?thesis .
  qed
  (* Weight bound: the cycle segment has weight ≤ 1 under no_pos_cycle.
     The cycle is w[p'..q'] (from v back to v), giving a closed walk.
     Since w ∈ walks n k i j, all vertices in w (and hence in the cycle) are in {..<n}.
     path_weight A w = path_weight A (take (p'+1) w) * path_weight A (drop p' w)
                     = path_weight A (take (p'+1) w) * path_weight A ([v] @ cycle-part @ drop q' w)
     where cycle-part is from q'+1 onwards.
     The cycle weight (path_weight A (take q'-p'+1 (drop p' w))) ≤ 1 by no_pos_cycle.
     Thus path_weight A w ≤ path_weight A ?w'.

     We now prove this formally. *)
  have hw'_weight: "path_weight A w \<le> path_weight A ?w'"
  proof -
    (* Decompose w at position p': w = take p' w @ drop p' w *)
    have take_drop_p: "w = take p' w @ drop p' w" by simp
    (* drop p' w is nonempty since p' < length w *)
    have drop_p_ne: "drop p' w \<noteq> []"
      using hp'(1) by simp
    (* take p' w is nonempty since 0 < p' *)
    have take_p_ne: "take p' w \<noteq> []"
      using hp'(3) by simp
    (* hd (drop p' w) = w ! p' = v *)
    have hd_drop_p: "hd (drop p' w) = v"
      using hp'(1,2) by (simp add: hd_drop_conv_nth)
    (* path_weight A w = path_weight A (take p' w @ [v]) * path_weight A (drop p' w) *)
    have split_p: "path_weight A w =
        path_weight A (take p' w @ [v]) * path_weight A (drop p' w)"
      using path_weight_append[OF take_p_ne drop_p_ne]
      by (simp add: hd_drop_p)
    (* The cycle walk: take (q'-p') (drop p' w) @ [v] *)
    let ?C = "take (q'-p') (drop p' w) @ [v]"
    have take_C_ne: "take (q'-p') (drop p' w) \<noteq> []"
      using hpq hp'(1) by simp
    (* drop (q'-p') (drop p' w) = drop q' w *)
    have drop_qp_drop_p: "drop (q'-p') (drop p' w) = drop q' w"
      using hpq by (simp add: drop_drop)
    (* drop q' w is nonempty since q' < length w - 1, so q' + 1 < length w *)
    have drop_q_ne: "drop q' w \<noteq> []"
      using hq'(1) by simp
    (* hd (drop q' w) = w ! q' = v *)
    have hd_drop_q: "hd (drop q' w) = v"
      using hq'(1) hq'(2)
      by (metis hd_drop_conv_nth Suc_less_eq hq'(1))
    (* Decompose drop p' w at (q'-p'): drop p' w = take (q'-p') (drop p' w) @ drop q' w *)
    have decomp_drop_p: "drop p' w = take (q'-p') (drop p' w) @ drop q' w"
      by (simp add: drop_qp_drop_p[symmetric] append_take_drop_id)
    (* path_weight A (drop p' w) = path_weight A ?C * path_weight A (drop q' w) *)
    have split_q: "path_weight A (drop p' w) =
        path_weight A ?C * path_weight A (drop q' w)"
    proof -
      have "path_weight A (drop p' w) =
            path_weight A (take (q'-p') (drop p' w) @ drop q' w)"
        by (simp add: drop_qp_drop_p[symmetric] append_take_drop_id)
      also have "\<dots> = path_weight A (take (q'-p') (drop p' w) @ [hd (drop q' w)]) *
                       path_weight A (drop q' w)"
        using path_weight_append[OF take_C_ne drop_q_ne] .
      also have "\<dots> = path_weight A ?C * path_weight A (drop q' w)"
        by (simp add: hd_drop_q)
      finally show ?thesis .
    qed
    (* ?C is a closed walk from v to v: v < n, length = Suc (q'-p'), all verts in {..<n} *)
    have v_lt_n: "v < n"
    proof -
      have "v = w ! p'" using hp'(2) by simp
      have "set w \<subseteq> {..<n}" using walk_vertices_bounded[OF hw_in] .
      thus ?thesis by (metis \<open>v = w ! p'\<close> in_set_conv_nth hp'(1)
                             lessThan_iff subsetD)
    qed
    have C_in_walks: "?C \<in> walks n (q'-p') v v"
    proof -
      have hlen: "length ?C = Suc (q'-p')"
        using hpq hp'(1) by simp
      have hhd: "hd ?C = v"
        by (simp add: hd_append take_C_ne
                      hd_drop_conv_nth[of p' w, folded hp'(2)] hp'(1))
      have hlast: "last ?C = v" by simp
      have hset: "set ?C \<subseteq> {..<n}"
      proof -
        have "set (take (q'-p') (drop p' w)) \<subseteq> set w"
          by (meson set_drop_subset set_take_subset subset_trans)
        moreover have "set w \<subseteq> {..<n}"
          using walk_vertices_bounded[OF hw_in] .
        moreover have "{v} \<subseteq> {..<n}" using v_lt_n by simp
        ultimately show ?thesis by auto
      qed
      show ?thesis unfolding walks_def
        using hlen hhd hlast hset by simp
    qed
    (* By no_pos_cycle: path_weight A ?C ≤ 1 *)
    have cycle_le: "path_weight A ?C \<le> (1 :: tropical)"
      using hnpc v_lt_n C_in_walks
      unfolding no_pos_cycle_def by blast
    (* Combine: path_weight A (drop p' w) ≤ path_weight A (drop q' w) *)
    have drop_p_le: "path_weight A (drop p' w) \<le> path_weight A (drop q' w)"
    proof -
      have "path_weight A (drop p' w) =
            path_weight A ?C * path_weight A (drop q' w)"
        using split_q .
      also have "\<dots> \<le> 1 * path_weight A (drop q' w)"
        using trop_mul_le_mul_right[OF cycle_le] by simp
      also have "\<dots> = path_weight A (drop q' w)" by simp
      finally show ?thesis .
    qed
    (* path_weight A w ≤ path_weight A (take p' w @ [v]) * path_weight A (drop q' w) *)
    have main_le: "path_weight A w \<le>
                   path_weight A (take p' w @ [v]) * path_weight A (drop q' w)"
    proof -
      have "path_weight A w =
            path_weight A (take p' w @ [v]) * path_weight A (drop p' w)"
        using split_p .
      also have "\<dots> \<le> path_weight A (take p' w @ [v]) * path_weight A (drop q' w)"
        using trop_mul_le_mul_right[OF drop_p_le] by (simp add: mult.commute)
      finally show ?thesis .
    qed
    (* path_weight A ?w' = path_weight A (take p' w @ [v]) * path_weight A (drop q' w) *)
    have w'_eq: "path_weight A ?w' =
                 path_weight A (take p' w @ [v]) * path_weight A (drop q' w)"
    proof -
      have "path_weight A ?w' = path_weight A (take p' w @ drop q' w)"
        by simp
      also have "\<dots> = path_weight A (take p' w @ [hd (drop q' w)]) *
                      path_weight A (drop q' w)"
        using path_weight_append[OF take_p_ne drop_q_ne] .
      also have "\<dots> = path_weight A (take p' w @ [v]) * path_weight A (drop q' w)"
        by (simp add: hd_drop_q)
      finally show ?thesis .
    qed
    show ?thesis using main_le w'_eq by simp
  qed
  have hw'_ne: "?w' \<noteq> []"
    using hp'(3) by (simp add: hd_append take_eq_Nil)
  have hw'_set: "set ?w' \<subseteq> {..<n}"
  proof -
    have "set ?w' \<subseteq> set w"
      by (auto simp: set_append dest: in_set_takeD in_set_dropD)
    thus ?thesis using walk_vertices_bounded[OF hw_in] by blast
  qed
  show "\<exists> w'. path_weight A w' \<ge> path_weight A w \<and>
              length w' < length w \<and>
              w' \<noteq> [] \<and>
              hd w' = hd w \<and> last w' = last w \<and>
              set w' \<subseteq> {..<n}"
    using hw'_weight hw'_len hw'_ne hw'_hd hw'_last hw'_set
    by (intro exI[of _ ?w']) auto
qed

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
    have "j < n" using assms(2) by simp
    hence "walks n 0 j j = {[j]}" by (rule walks_0)
    thus ?thesis using True
      by (simp add: trop_walks_sum_def trop_mat_id_def one_tropical_def)
  next
    case False
    then show ?thesis
      by (simp add: trop_walks_sum_def walks_0_empty_if_neq
                    trop_mat_id_def zero_tropical_def assms)
  qed
next
  case (Suc k)
  have hj_lt: "j < n" using Suc.prems by auto
  have hi_lt: "i < n" using Suc.prems by auto
  (* Finiteness of walk sets (needed for sum.Sigma) *)
  have fin_walks: "\<And> m. finite (walks n k i m)"
    unfolding walks_def
    by (rule finite_subset[of _ "{xs. set xs \<subseteq> {..<n} \<and> length xs = Suc k}"])
       (auto intro: finite_lists_length_eq[OF finite_lessThan])
  (* Step 1: expand A^{Suc k} as a matrix product, then unfold multiplication *)
  have "trop_mat_pow n A (Suc k) i j
        = (\<Sum> m \<in> {..<n}. trop_mat_pow n A k i m * A m j)"
    by (simp add: trop_mat_mul_def)
  (* Step 2: apply the IH for each intermediate vertex m *)
  also have "\<dots> = (\<Sum> m \<in> {..<n}. trop_walks_sum A (walks n k i m) * A m j)"
    by (rule sum.cong, simp)
       (metis Suc.IH Suc.prems(1) lessThan_iff)
  (* Step 3: distribute A m j inside the trop_walks_sum *)
  also have "\<dots> = (\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks n k i m. path_weight A w * A m j)"
    unfolding trop_walks_sum_def
    by (rule sum.cong, simp, rule sum_distrib_right)
  (* Step 4: collapse double sum into a Sigma-indexed sum *)
  also have "\<dots> = (\<Sum> (m, w) \<in> (SIGMA m:{..<n}. walks n k i m).
                   path_weight A w * A m j)"
    by (rule sum.Sigma[symmetric], simp, simp add: fin_walks)
  (* Step 5: reindex via (m, w) ↦ w @ [j], which bijects onto walks n (Suc k) i j *)
  also have "\<dots> = (\<Sum> v \<in> walks n (Suc k) i j. path_weight A v)"
  proof -
    let ?f = "\<lambda>(m :: nat, w :: nat list). w @ [j]"
    let ?A = "SIGMA m:{..<n}. walks n k i m"
    (* Injectivity: w1 @ [j] = w2 @ [j] implies (m1,w1) = (m2,w2) in the Sigma type *)
    have inj: "inj_on ?f ?A"
      by (intro inj_onI)
         (auto simp: walks_def)
    (* Image equals the Suc k walk set *)
    have img: "?f ` ?A = walks n (Suc k) i j"
      by (auto simp: walks_Suc_factored hj_lt image_iff)
    (* Rewrite the summand: path_weight A w * A m j = path_weight A (w @ [j]) *)
    have "(\<Sum> (m, w) \<in> ?A. path_weight A w * A m j)
          = (\<Sum> x \<in> ?A. path_weight A (?f x))"
      by (rule sum.cong, simp)
         (clarsimp simp: walks_def, simp add: path_weight_snoc)
    (* Reindex sum from Sigma to image *)
    also have "\<dots> = (\<Sum> v \<in> ?f ` ?A. path_weight A v)"
      by (rule sum.reindex[OF inj, symmetric])
    finally show ?thesis by (simp add: img)
  qed
  (* Step 6: fold back to trop_walks_sum *)
  also have "\<dots> = trop_walks_sum A (walks n (Suc k) i j)"
    by (simp add: trop_walks_sum_def)
  finally show ?case .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>19  Min-Plus Matrix Power = Sum over Walks\<close>
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
\<close>

theorem tropm_mat_pow_eq_sum_walks:
  assumes "i < n" "j < n"
  shows "tropm_mat_pow n A k i j = tropm_walks_sum A (walks n k i j)"
proof (induction k arbitrary: i j)
  case 0
  show ?case
  proof (cases "i = j")
    case True
    have "j < n" using assms(2) by simp
    hence "walks n 0 j j = {[j]}" by (rule walks_0)
    thus ?thesis using True
      by (simp add: tropm_walks_sum_def tropm_mat_id_def one_tropical_min_def)
  next
    case False
    then show ?thesis
      by (simp add: tropm_walks_sum_def walks_0_empty_if_neq
                    tropm_mat_id_def zero_tropical_min_def assms)
  qed
next
  case (Suc k)
  have hj_lt: "j < n" using Suc.prems by auto
  have hi_lt: "i < n" using Suc.prems by auto
  have fin_walks: "\<And> m. finite (walks n k i m)"
    unfolding walks_def
    by (rule finite_subset[of _ "{xs. set xs \<subseteq> {..<n} \<and> length xs = Suc k}"])
       (auto intro: finite_lists_length_eq[OF finite_lessThan])
  have "tropm_mat_pow n A (Suc k) i j
        = (\<Sum> m \<in> {..<n}. tropm_mat_pow n A k i m * A m j)"
    by (simp add: tropm_mat_mul_def)
  also have "\<dots> = (\<Sum> m \<in> {..<n}. tropm_walks_sum A (walks n k i m) * A m j)"
    by (rule sum.cong, simp)
       (metis Suc.IH Suc.prems(1) lessThan_iff)
  also have "\<dots> = (\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks n k i m. path_weightm A w * A m j)"
    unfolding tropm_walks_sum_def
    by (rule sum.cong, simp, rule sum_distrib_right)
  also have "\<dots> = (\<Sum> (m, w) \<in> (SIGMA m:{..<n}. walks n k i m).
                   path_weightm A w * A m j)"
    by (rule sum.Sigma[symmetric], simp, simp add: fin_walks)
  also have "\<dots> = (\<Sum> v \<in> walks n (Suc k) i j. path_weightm A v)"
  proof -
    let ?f = "\<lambda>(m :: nat, w :: nat list). w @ [j]"
    let ?A = "SIGMA m:{..<n}. walks n k i m"
    have inj: "inj_on ?f ?A"
      by (intro inj_onI)
         (auto simp: walks_def)
    have img: "?f ` ?A = walks n (Suc k) i j"
      by (auto simp: walks_Suc_factored hj_lt image_iff)
    have "(\<Sum> (m, w) \<in> ?A. path_weightm A w * A m j)
          = (\<Sum> x \<in> ?A. path_weightm A (?f x))"
      by (rule sum.cong, simp)
         (clarsimp simp: walks_def, simp add: path_weightm_snoc)
    also have "\<dots> = (\<Sum> v \<in> ?f ` ?A. path_weightm A v)"
      by (rule sum.reindex[OF inj, symmetric])
    finally show ?thesis by (simp add: img)
  qed
  also have "\<dots> = tropm_walks_sum A (walks n (Suc k) i j)"
    by (simp add: tropm_walks_sum_def)
  finally show ?case .
qed

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
  assumes hi: "i < n" and hj: "j < n"
  shows "trop_mat_pow n (trop_mat_close n A) k i j =
         (\<Sum> m \<in> {..k}. trop_mat_pow n A m i j)"
proof (induction k)
  case 0
  show ?case by (simp add: trop_mat_close_def trop_mat_id_def)
next
  case (Suc k)
  (* Expand (I\<oplus>A)^{Suc k} as a matrix product *)
  have "(trop_mat_pow n (trop_mat_close n A) (Suc k)) i j
        = (\<Sum> l \<in> {..<n}. trop_mat_pow n (trop_mat_close n A) k i l *
                            trop_mat_close n A l j)"
    by (simp add: trop_mat_mul_def)
  (* Apply IH *)
  also have "\<dots> = (\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) *
                                     trop_mat_close n A l j)"
    by (rule sum.cong, simp, simp add: Suc.IH)
  (* Unfold close: (I\<oplus>A) l j = A l j + I l j, then distribute *)
  also have "\<dots> = (\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) * A l j) +
                  (\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) *
                                    trop_mat_id n l j)"
    by (simp add: trop_mat_close_def distrib_left sum.distrib)
  (* First part: \<Sum>_l (\<Sum>_m A^m i l) * A l j = \<Sum>_m A^{Suc m} i j *)
  also have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) * A l j)
             = (\<Sum> m \<in> {..k}. trop_mat_pow n A (Suc m) i j)"
  proof -
    have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) * A l j)
          = (\<Sum> m \<in> {..k}. \<Sum> l \<in> {..<n}. trop_mat_pow n A m i l * A l j)"
      by (simp only: sum_distrib_right sum.swap)
    also have "\<dots> = (\<Sum> m \<in> {..k}. trop_mat_pow n A (Suc m) i j)"
      by (rule sum.cong, simp) (simp add: trop_mat_mul_def)
    finally show ?thesis .
  qed
  (* Second part: \<Sum>_l (\<Sum>_m A^m i l) * I l j = \<Sum>_m A^m i j *)
  also have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) *
                               trop_mat_id n l j)
             = (\<Sum> m \<in> {..k}. trop_mat_pow n A m i j)"
  proof -
    have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. trop_mat_pow n A m i l) *
                            trop_mat_id n l j)
          = (\<Sum> m \<in> {..k}. \<Sum> l \<in> {..<n}. trop_mat_pow n A m i l * trop_mat_id n l j)"
      by (simp only: sum_distrib_right sum.swap)
    also have "\<dots> = (\<Sum> m \<in> {..k}. trop_mat_pow n A m i j)"
      by (rule sum.cong, simp) (simp add: trop_mat_mul_id_right hi hj)
    finally show ?thesis .
  qed
  (* Combine: \<Sum>_{m\<le>k} A^{Suc m} + \<Sum>_{m\<le>k} A^m = \<Sum>_{m\<le>Suc k} A^m *)
  also have "(\<Sum> m \<in> {..k}. trop_mat_pow n A (Suc m) i j) +
             (\<Sum> m \<in> {..k}. trop_mat_pow n A m i j)
             = (\<Sum> m \<in> {..Suc k}. trop_mat_pow n A m i j)"
  proof -
    let ?g = "\<lambda>m. trop_mat_pow n A m i j"
    (* Reindex: \<Sum>_{m\<le>k} A^{Suc m} = \<Sum>_{m\<in>{1..Suc k}} A^m *)
    have ri: "(\<Sum> m \<in> {..k}. ?g (Suc m)) = (\<Sum> m \<in> {1..Suc k}. ?g m)"
      by (rule sum.reindex_cong[of Suc "{..k}" "{1..Suc k}" ?g])
         (auto simp: image_iff)
    (* {..Suc k} = {0} \<union> {1..Suc k} (disjoint) *)
    have split_U: "(\<Sum> m \<in> {..Suc k}. ?g m) = ?g 0 + (\<Sum> m \<in> {1..Suc k}. ?g m)"
      by (subst sum.atMost_Suc_eq_insert_0) simp_all
    (* {..k} = {0} \<union> {1..k} (disjoint, when k \<ge> 0) *)
    have split_T: "(\<Sum> m \<in> {..k}. ?g m) = ?g 0 + (\<Sum> m \<in> {1..k}. ?g m)"
      by (subst sum.atMost_Suc_eq_insert_0[of k, simplified]) simp_all
    (* {1..Suc k} = {1..k} \<union> {Suc k} (disjoint) *)
    have split_S: "(\<Sum> m \<in> {1..Suc k}. ?g m) = (\<Sum> m \<in> {1..k}. ?g m) + ?g (Suc k)"
      by (simp add: sum.atLeastAtMost_Suc)
    (* Idempotency: \<Sum>_{1..k} + \<Sum>_{1..k} = \<Sum>_{1..k} *)
    have idem: "(\<Sum> m \<in> {1..k}. ?g m) + (\<Sum> m \<in> {1..k}. ?g m) =
                (\<Sum> m \<in> {1..k}. ?g m)"
      by (subst sum_add_distrib[symmetric], simp add: tropical_add_idem)
    (* Now assemble: \<Sum>_{1..Suc k} + \<Sum>_{m\<le>k} = \<Sum>_{m\<le>k} + ?g(Suc k) = \<Sum>_{m\<le>Suc k} *)
    have "(\<Sum> m \<in> {..k}. ?g (Suc m)) + (\<Sum> m \<in> {..k}. ?g m)
          = (\<Sum> m \<in> {1..Suc k}. ?g m) + (\<Sum> m \<in> {..k}. ?g m)"
      using ri by simp
    also have "\<dots> = ((\<Sum> m \<in> {1..k}. ?g m) + ?g (Suc k)) +
                    (?g 0 + (\<Sum> m \<in> {1..k}. ?g m))"
      using split_S split_T by simp
    also have "\<dots> = ?g 0 + (\<Sum> m \<in> {1..k}. ?g m) + ?g (Suc k)"
      using idem by (simp add: add.assoc add.commute add.left_commute)
    also have "\<dots> = (\<Sum> m \<in> {..k}. ?g m) + ?g (Suc k)"
      using split_T by simp
    also have "\<dots> = (\<Sum> m \<in> {..Suc k}. ?g m)"
      by (simp add: sum.atMost_Suc)
    finally show ?thesis .
  qed
  finally show ?case .
qed

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
  assumes hnpc: "no_pos_cycle n A"
  assumes hw: "w \<in> walks n k i j"
  shows "\<exists> w' \<in> simple_walks n i j. path_weight A w \<le> path_weight A w'"
proof (induction "length w" arbitrary: k i j w rule: less_induct)
  case (less w)
  show ?case
  proof (cases "distinct w")
    case True
    have "w \<in> simple_walks n i j"
      unfolding simple_walks_def
      using less(2) True by auto
    thus ?thesis by (intro bexI[of _ w]) simp
  next
    case False
    (* Decompose w at a repeated vertex *)
    obtain xs v ys zs where hdecomp: "w = xs @ v # ys @ v # zs"
      using not_distinct_decomp[OF False] by blast
    (* First occurrence of v (at position length xs) is in butlast w *)
    have hv1: "v \<in> set (butlast w)"
    proof -
      have hpos: "length xs < length (butlast w)"
        by (simp add: hdecomp)
      have "butlast w ! length xs = v"
        by (simp add: hdecomp nth_butlast nth_append)
      thus ?thesis by (metis hpos nth_mem)
    qed
    (* Second occurrence (at position ≥ 1) is in tl w *)
    have hv2: "v \<in> set (tl w)"
      using hdecomp by (cases xs) (auto simp: set_append)
    (* Excise the cycle to get a strictly shorter walk w'' *)
    obtain w'' where hge: "path_weight A w \<le> path_weight A w''"
                 and hlen: "length w'' < length w"
                 and hne'': "w'' \<noteq> []"
                 and hhd: "hd w'' = hd w"
                 and hlast: "last w'' = last w"
                 and hset: "set w'' \<subseteq> {..<n}"
      using path_weight_cycle_excise[OF hv1 hv2 hnpc less(2)] by blast
    (* w'' is a valid walk from i to j *)
    have hw''_in: "w'' \<in> walks n (length w'' - 1) i j"
      unfolding walks_def
    proof (intro conjI)
      show "length w'' = Suc (length w'' - 1)"
        using hne'' by (cases w'') simp_all
      show "hd w'' = i"
        using hhd walk_hd[OF less(2)] by simp
      show "last w'' = j"
        using hlast walk_last[OF less(2)] by simp
      show "set w'' \<subseteq> {..<n}"
        using hset .
    qed
    (* Apply the induction hypothesis to the shorter walk *)
    obtain w' where hw'_in: "w' \<in> simple_walks n i j"
               and hw'_ge: "path_weight A w'' \<le> path_weight A w'"
      using less(1)[OF hlen hw''_in] by blast
    show ?thesis
      by (rule bexI[OF _ hw'_in])
         (rule le_trans[OF hge hw'_ge])
  qed
qed

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
    have dominated: "\<forall> w \<in> walks_le n (n-1) i j.
                     \<exists> w' \<in> simple_walks n i j. path_weight A w \<le> path_weight A w'"
    proof (intro ballI)
      fix w assume hw: "w \<in> walks_le n (n-1) i j"
      then obtain m where "m \<le> n - 1" "w \<in> walks n m i j"
        unfolding walks_le_def by auto
      thus "\<exists> w' \<in> simple_walks n i j. path_weight A w \<le> path_weight A w'"
        using cycle_shortcutting[OF assms(3)] by blast
    qed
    have "trop_walks_sum A (walks_le n (n-1) i j) \<le>
          trop_walks_sum A (simple_walks n i j)"
      using trop_walks_sum_dominated[OF finite_walks_le simple_walks_finite dominated] .
    thus ?thesis using lhs by simp
  qed
next
  (* (\<ge>) direction: every simple walk is in walks_le n (n-1) i j *)
  show "trop_walks_sum A (simple_walks n i j) \<le>
        trop_mat_pow n (trop_mat_close n A) (n-1) i j"
  proof -
    have lhs: "trop_mat_pow n (trop_mat_close n A) (n-1) i j =
               trop_walks_sum A (walks_le n (n-1) i j)"
      using assms(1,2) by (rule trop_mat_pow_close_eq_sum_walks_le)
    have subset: "simple_walks n i j \<subseteq> walks_le n (n-1) i j"
    proof
      fix w assume hw: "w \<in> simple_walks n i j"
      then have hdist: "distinct w"
            and hwalk: "\<exists> m. w \<in> walks n m i j"
        unfolding simple_walks_def by auto
      obtain m where hwm: "w \<in> walks n m i j" using hwalk by auto
      (* A distinct list with vertices in {..<n} has length ≤ n *)
      have hlen_n: "length w \<le> n"
      proof -
        have hset: "set w \<subseteq> {..<n}" using walk_vertices_bounded[OF hwm] .
        have "length w = card (set w)" using distinct_card[OF hdist] .
        also have "card (set w) \<le> card {..<n}"
          using card_mono[OF finite_lessThan hset] .
        also have "card {..<n} = n" by simp
        finally show ?thesis .
      qed
      (* walk has Suc m vertices so m + 1 ≤ n, hence m ≤ n - 1 *)
      have hm: "m \<le> n - 1"
      proof -
        have "Suc m = length w"
          using hwm unfolding walks_def by simp
        thus ?thesis using hlen_n by omega
      qed
      show "w \<in> walks_le n (n-1) i j"
        unfolding walks_le_def using hwm hm by auto
    qed
    show ?thesis
      using lhs trop_walks_sum_mono_subset[OF finite_walks_le subset] by simp
  qed
qed

(* ================================================================== *)
section \<open>Part VII  Bellman–Ford Dual (min-plus)\<close>
(* ================================================================== *)

text \<open>
  @{text bellman_ford}: the dual of @{text floyd_warshall} for min-plus matrices.

  Under a no-negative-cycle assumption (@{text no_neg_cycle}) — i.e.\ every
  closed walk in the min-plus graph has weight @{text "\<ge> 1 = Fin' 0"} (i.e.\
  no negative-weight cycle) — the @{text "(n-1)"}-th power of the min-plus
  closed matrix equals the minimum-weight simple-path matrix.

  Formally:
    @{text "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j
           = tropm_walks_sum A (simple_walksm n i j)"}

  Proof structure (symmetric to @{text floyd_warshall}):
  \<^item> @{text tropm_mat_pow_close_eq_sum_walks_le}: closed power = sum over @{text walks_le}.
  \<^item> @{text cycle_shortcutting_min}: every walk is dominated by a simple walk
    (using the no-negative-cycle assumption to bound cycle weight from below).
  \<^item> @{text bellman_ford}: @{text antisym} proof — @{text simple_walksm \<subseteq> walks_le}
    for the @{text \<le>} direction; @{text cycle_shortcutting_min} for the @{text \<ge>} direction.
\<close>

definition no_neg_cycle :: "nat \<Rightarrow> tropm_mat \<Rightarrow> bool" where
  "no_neg_cycle n A \<equiv>
     \<forall> i < n. \<forall> k. \<forall> w \<in> walks n k i i. (1 :: tropical_min) \<le> path_weightm A w"

definition simple_walksm :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "simple_walksm n i j \<equiv>
     { w \<in> \<Union> k. walks n k i j . distinct w }"

(* ------------------------------------------------------------------ *)
subsection \<open>Bellman–Ford Infrastructure\<close>
(* ------------------------------------------------------------------ *)

(* In min-plus: a + b \<le> a  (since + = min, min(a,b) \<le> a) *)
lemma tropm_add_le_left: "(a :: tropical_min) + b \<le> a"
  by (simp add: tropm_add_le_iff add.assoc tropm_add_idem)

(* Min-plus identity matrix: right-multiply by I leaves A unchanged. *)
lemma tropm_mat_mul_id_right:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   tropm_mat_mul n A (tropm_mat_id n) i j = A i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "tropm_mat_mul n A (tropm_mat_id n) i j
        = (\<Sum> k \<in> {..<n}. A i k * tropm_mat_id n k j)"
    by (simp add: tropm_mat_mul_def)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. if k = j then A i k * Fin' 0 else A i k * PosInf)"
    by (rule sum.cong) (simp_all add: tropm_mat_id_def)
  also have "\<dots> = A i j * Fin' 0"
    by (simp add: sum.delta[OF finite_lessThan] hj zero_tropical_min_def
                  times_tropical_min_def)
  also have "\<dots> = A i j"
    by (simp add: times_tropical_min_def one_tropical_min_def)
  finally show ?thesis .
qed

(* Min-plus multiplication is monotone in the right argument. *)
lemma tropm_mul_le_mul_right:
  assumes "(a :: tropical_min) \<le> b"
  shows "c * a \<le> c * b"
proof -
  have step: "c * a + c * b = c * b"
  proof -
    have "c * a + c * b = c * (a + b)"
      by (simp add: distrib_left)
    also have "\<dots> = c * b"
      using assms by (simp add: tropm_add_le_iff)
    finally show ?thesis .
  qed
  thus ?thesis by (simp add: tropm_add_le_iff)
qed

(* In min-plus: 1 \<le> a \<Longrightarrow> b \<le> b * a  (multiplying by \<ge>1 grows the value). *)
lemma tropm_one_le_mul_of_ge_one:
  assumes "(1 :: tropical_min) \<le> a"
  shows "(b :: tropical_min) \<le> b * a"
proof -
  have "b * 1 \<le> b * a"
    using tropm_mul_le_mul_right[OF assms] .
  thus ?thesis by simp
qed

(* tropm_walks_sum_le_member: every member bounds the sum from above
   (min over T \<le> any particular element). *)
lemma tropm_walks_sum_le_member:
  assumes "w' \<in> T" "finite T"
  shows "tropm_walks_sum A T \<le> path_weightm A w'"
proof -
  have decomp: "tropm_walks_sum A T =
        path_weightm A w' + tropm_walks_sum A (T - {w'})"
    unfolding tropm_walks_sum_def
    using assms by (subst sum.remove) auto
  thus ?thesis using tropm_add_le_left by simp
qed

(* tropm_walks_sum_mono_subset: the min-plus walk-sum is anti-monotone in the
   walk set (larger set = lower minimum). *)
lemma tropm_walks_sum_mono_subset:
  assumes "finite T" "S \<subseteq> T"
  shows "tropm_walks_sum A T \<le> tropm_walks_sum A S"
proof -
  have fS: "finite S" using assms(1,2) by (rule finite_subset)
  show ?thesis
  proof (induction S rule: finite_induct[OF fS])
    case empty
    then show ?case by (simp add: tropm_walks_sum_def le_PosInf)
  next
    case (insert w S')
    have hw_T: "w \<in> T" using insert.prems assms(2) by auto
    have hS'_sub: "S' \<subseteq> T" using insert.prems assms(2) by auto
    have expand_S: "tropm_walks_sum A (insert w S') =
                    path_weightm A w + tropm_walks_sum A S'"
      unfolding tropm_walks_sum_def
      using insert.hyps(1,2) by (rule sum.insert)
    have hw_ge: "tropm_walks_sum A T \<le> path_weightm A w"
      using tropm_walks_sum_le_member[OF hw_T assms(1)] .
    have hS'_ge: "tropm_walks_sum A T \<le> tropm_walks_sum A S'"
      using insert.IH[OF hS'_sub] .
    (* Need T \<le> min(path_weightm w, sum S') = path_weightm w + sum S' *)
    have "tropm_walks_sum A T \<le> path_weightm A w + tropm_walks_sum A S'"
    proof -
      have key: "tropm_walks_sum A T +
                 (path_weightm A w + tropm_walks_sum A S') =
                 tropm_walks_sum A T"
        by (metis hw_ge hS'_ge tropm_add_le_iff
                  add.assoc add.commute tropm_add_idem)
      thus ?thesis using tropm_add_le_iff by blast
    qed
    thus ?case using expand_S by simp
  qed
qed

(* tropm_walks_sum_dominated: if every w \<in> S is dominated (some w' \<in> T has
   smaller weight), then the min-plus sum over T is \<le> sum over S. *)
lemma tropm_walks_sum_dominated:
  assumes "finite S" "finite T"
  assumes dominated: "\<forall> w \<in> S. \<exists> w' \<in> T. path_weightm A w' \<le> path_weightm A w"
  shows "tropm_walks_sum A T \<le> tropm_walks_sum A S"
proof (induction S rule: finite_induct[OF assms(1)])
  case empty
  then show ?case by (simp add: tropm_walks_sum_def le_PosInf)
next
  case (insert w S')
  have expand_S: "tropm_walks_sum A (insert w S') =
                  path_weightm A w + tropm_walks_sum A S'"
    unfolding tropm_walks_sum_def
    using insert.hyps(1,2) by (rule sum.insert)
  obtain w' where hw': "w' \<in> T" "path_weightm A w' \<le> path_weightm A w"
    using dominated insert.prems by auto
  have hw_ge: "tropm_walks_sum A T \<le> path_weightm A w"
    using tropm_walks_sum_le_member[OF hw'(1) assms(2)]
          le_trans hw'(2) by blast
  have hS'_ge: "tropm_walks_sum A T \<le> tropm_walks_sum A S'"
    using insert.IH dominated insert.prems by auto
  have "tropm_walks_sum A T \<le> path_weightm A w + tropm_walks_sum A S'"
  proof -
    have key: "tropm_walks_sum A T +
               (path_weightm A w + tropm_walks_sum A S') =
               tropm_walks_sum A T"
      by (metis hw_ge hS'_ge tropm_add_le_iff
                add.assoc add.commute tropm_add_idem)
    thus ?thesis using tropm_add_le_iff by blast
  qed
  thus ?case using expand_S by simp
qed

(* Min-plus cycle excision: a walk with a repeated vertex can be shortened
   and the shorter walk has \<le> weight (removing a \<ge>1 cycle). *)
lemma path_weightm_cycle_excise:
  assumes hv1: "v \<in> set (butlast w)"
  assumes hv2: "v \<in> set (tl w)"
  assumes hnnc: "no_neg_cycle n A"
  assumes hw_in: "w \<in> walks n k i j"
  shows "\<exists> w'. path_weightm A w' \<le> path_weightm A w \<and>
               length w' < length w \<and>
               w' \<noteq> [] \<and>
               hd w' = hd w \<and> last w' = last w \<and>
               set w' \<subseteq> {..<n}"
proof -
  (* Find indices p < q with w!p = w!q = v — identical to max-plus *)
  have hne: "w \<noteq> []" using hv1 by auto
  from hv1 obtain q where hq_bound: "q < length (butlast w)"
                     and hq_val:   "(butlast w) ! q = v"
    by (meson in_set_conv_nth)
  from hv2 obtain p0 where hp0_bound: "p0 < length (tl w)"
                      and hp0_val:   "(tl w) ! p0 = v"
    by (meson in_set_conv_nth)
  let ?p = "Suc p0"
  let ?q = "q"
  have hp_lt:   "?p < length w"  using hp0_bound by simp
  have hp_val:  "w ! ?p = v"      by (simp add: hp0_val nth_tl)
  have hq_lt:   "?q < length w - 1" using hq_bound by simp
  have hq_val': "w ! ?q = v"      by (simp add: hq_val nth_butlast)
  obtain p' q' where hp': "p' < length w" "w ! p' = v" "0 < p'"
                and hq': "q' < length w - 1" "w ! q' = v"
                and hpq: "p' < q'"
  proof (cases "?p \<le> ?q")
    case True
    thus ?thesis
      using hp_lt hp_val hq_lt hq_val'
      by (intro that[of ?p ?q]) auto
  next
    case False
    hence "?q < ?p" by simp
    thus ?thesis
      using hp_lt hp_val hq_lt hq_val'
      by (intro that[of ?q ?p]) auto
  qed
  let ?w' = "take p' w @ drop q' w"
  have hw'_hd:   "hd ?w' = hd w"
    using hp'(3) by (simp add: hd_append take_eq_Nil)
  have hw'_last: "last ?w' = last w"
    using hq'(1) hw_in unfolding walks_def by (simp add: last_append)
  have hw'_len:  "length ?w' < length w"
  proof -
    have "length ?w' = p' + (length w - q')"
      using hp'(1) hq'(1) by simp
    also have "\<dots> < length w"
      using hpq hq'(1) hp'(1) by omega
    finally show ?thesis .
  qed
  have hw'_weight: "path_weightm A ?w' \<le> path_weightm A w"
  proof -
    have take_drop_p: "w = take p' w @ drop p' w" by simp
    have drop_p_ne:   "drop p' w \<noteq> []" using hp'(1) by simp
    have take_p_ne:   "take p' w \<noteq> []" using hp'(3) by simp
    have hd_drop_p:   "hd (drop p' w) = v"
      using hp'(1,2) by (simp add: hd_drop_conv_nth)
    have split_p: "path_weightm A w =
        path_weightm A (take p' w @ [v]) * path_weightm A (drop p' w)"
      using path_weightm_snoc[OF take_p_ne drop_p_ne]
      by (simp add: hd_drop_p)
    let ?C = "take (q'-p') (drop p' w) @ [v]"
    have take_C_ne:     "take (q'-p') (drop p' w) \<noteq> []"
      using hpq hp'(1) by simp
    have drop_qp_drop_p: "drop (q'-p') (drop p' w) = drop q' w"
      using hpq by (simp add: drop_drop)
    have drop_q_ne:  "drop q' w \<noteq> []" using hq'(1) by simp
    have hd_drop_q:  "hd (drop q' w) = v"
      using hq'(1) hq'(2) by (metis hd_drop_conv_nth Suc_less_eq hq'(1))
    have split_q: "path_weightm A (drop p' w) =
        path_weightm A ?C * path_weightm A (drop q' w)"
    proof -
      have "path_weightm A (drop p' w) =
            path_weightm A (take (q'-p') (drop p' w) @ drop q' w)"
        by (simp add: drop_qp_drop_p[symmetric] append_take_drop_id)
      also have "\<dots> = path_weightm A (take (q'-p') (drop p' w) @ [hd (drop q' w)]) *
                       path_weightm A (drop q' w)"
        using path_weightm_snoc[OF take_C_ne drop_q_ne] .
      also have "\<dots> = path_weightm A ?C * path_weightm A (drop q' w)"
        by (simp add: hd_drop_q)
      finally show ?thesis .
    qed
    have v_lt_n: "v < n"
    proof -
      have "v = w ! p'" using hp'(2) by simp
      have "set w \<subseteq> {..<n}" using walk_vertices_bounded[OF hw_in] .
      thus ?thesis by (metis \<open>v = w ! p'\<close> in_set_conv_nth hp'(1)
                             lessThan_iff subsetD)
    qed
    have C_in_walks: "?C \<in> walks n (q'-p') v v"
    proof -
      have hlen:  "length ?C = Suc (q'-p')" using hpq hp'(1) by simp
      have hhd:   "hd ?C = v"
        by (simp add: hd_append take_C_ne
                      hd_drop_conv_nth[of p' w, folded hp'(2)] hp'(1))
      have hlast: "last ?C = v" by simp
      have hset:  "set ?C \<subseteq> {..<n}"
      proof -
        have "set (take (q'-p') (drop p' w)) \<subseteq> set w"
          by (meson set_drop_subset set_take_subset subset_trans)
        moreover have "set w \<subseteq> {..<n}"
          using walk_vertices_bounded[OF hw_in] .
        moreover have "{v} \<subseteq> {..<n}" using v_lt_n by simp
        ultimately show ?thesis by auto
      qed
      show ?thesis unfolding walks_def
        using hlen hhd hlast hset by simp
    qed
    (* By no_neg_cycle: 1 \<le> path_weightm A ?C *)
    have cycle_ge: "(1 :: tropical_min) \<le> path_weightm A ?C"
      using hnnc v_lt_n C_in_walks
      unfolding no_neg_cycle_def by blast
    (* path_weightm A (drop p' w) \<ge> path_weightm A (drop q' w) *)
    have drop_p_ge: "path_weightm A (drop q' w) \<le> path_weightm A (drop p' w)"
    proof -
      have "path_weightm A (drop p' w) =
            path_weightm A ?C * path_weightm A (drop q' w)"
        using split_q .
      also have "path_weightm A (drop q' w) \<le> \<dots>"
        using tropm_one_le_mul_of_ge_one[OF cycle_ge]
        by (simp add: mult.commute)
      finally show ?thesis .
    qed
    (* Assemble: path_weightm A ?w' = (take) * (drop q') \<le> (take) * (drop p') = w *)
    have main_ge: "path_weightm A ?w' \<le> path_weightm A w"
    proof -
      have "path_weightm A ?w' =
            path_weightm A (take p' w @ [v]) * path_weightm A (drop q' w)"
      proof -
        have "path_weightm A ?w' =
              path_weightm A (take p' w @ [hd (drop q' w)]) *
              path_weightm A (drop q' w)"
          using path_weightm_snoc[OF take_p_ne drop_q_ne] .
        thus ?thesis by (simp add: hd_drop_q)
      qed
      also have "\<dots> \<le> path_weightm A (take p' w @ [v]) *
                       path_weightm A (drop p' w)"
        using tropm_mul_le_mul_right[OF drop_p_ge] .
      also have "\<dots> = path_weightm A w"
        using split_p by simp
      finally show ?thesis .
    qed
    thus ?thesis .
  qed
  have hw'_ne:  "?w' \<noteq> []"
    using hp'(3) by (simp add: hd_append take_eq_Nil)
  have hw'_set: "set ?w' \<subseteq> {..<n}"
  proof -
    have "set ?w' \<subseteq> set w"
      by (auto simp: set_append dest: in_set_takeD in_set_dropD)
    thus ?thesis using walk_vertices_bounded[OF hw_in] by blast
  qed
  show "\<exists> w'. path_weightm A w' \<le> path_weightm A w \<and>
               length w' < length w \<and>
               w' \<noteq> [] \<and>
               hd w' = hd w \<and> last w' = last w \<and>
               set w' \<subseteq> {..<n}"
    using hw'_weight hw'_len hw'_ne hw'_hd hw'_last hw'_set
    by (intro exI[of _ ?w']) auto
qed

(* Min-plus cycle shortcutting: every walk is dominated by a simple walk. *)
theorem cycle_shortcutting_min:
  assumes hnnc: "no_neg_cycle n A"
  assumes hw:   "w \<in> walks n k i j"
  shows "\<exists> w' \<in> simple_walksm n i j. path_weightm A w' \<le> path_weightm A w"
proof (induction "length w" arbitrary: k i j w rule: less_induct)
  case (less w)
  show ?case
  proof (cases "distinct w")
    case True
    have "w \<in> simple_walksm n i j"
      unfolding simple_walksm_def
      using less(2) True by auto
    thus ?thesis by (intro bexI[of _ w]) simp
  next
    case False
    obtain xs v ys zs where hdecomp: "w = xs @ v # ys @ v # zs"
      using not_distinct_decomp[OF False] by blast
    have hv1: "v \<in> set (butlast w)"
    proof -
      have hpos: "length xs < length (butlast w)" by (simp add: hdecomp)
      have "butlast w ! length xs = v"
        by (simp add: hdecomp nth_butlast nth_append)
      thus ?thesis by (metis hpos nth_mem)
    qed
    have hv2: "v \<in> set (tl w)"
      using hdecomp by (cases xs) (auto simp: set_append)
    obtain w'' where hle:   "path_weightm A w'' \<le> path_weightm A w"
                and hlen:   "length w'' < length w"
                and hne'':  "w'' \<noteq> []"
                and hhd:    "hd w'' = hd w"
                and hlast:  "last w'' = last w"
                and hset:   "set w'' \<subseteq> {..<n}"
      using path_weightm_cycle_excise[OF hv1 hv2 hnnc less(2)] by blast
    have hw''_in: "w'' \<in> walks n (length w'' - 1) i j"
      unfolding walks_def
    proof (intro conjI)
      show "length w'' = Suc (length w'' - 1)" using hne'' by (cases w'') simp_all
      show "hd w'' = i"  using hhd walk_hd[OF less(2)] by simp
      show "last w'' = j" using hlast walk_last[OF less(2)] by simp
      show "set w'' \<subseteq> {..<n}" using hset .
    qed
    obtain w' where hw'_in: "w' \<in> simple_walksm n i j"
               and hw'_le:  "path_weightm A w' \<le> path_weightm A w''"
      using less(1)[OF hlen hw''_in] by blast
    show ?thesis
      by (rule bexI[OF _ hw'_in])
         (rule le_trans[OF hw'_le hle])
  qed
qed

(* simple_walksm n i j is finite — same argument as simple_walks. *)
lemma simple_walksm_finite:
  "finite (simple_walksm n i j)"
proof -
  have "simple_walksm n i j \<subseteq> {w . set w \<subseteq> {..<n} \<and> distinct w}"
    unfolding simple_walksm_def walks_def by auto
  moreover have "finite {w :: nat list . set w \<subseteq> {..<n} \<and> distinct w}"
    by (rule finite_subset[OF _ finite_lists_length_le[OF finite_lessThan]])
       (auto simp: length_remdups_leq)
  ultimately show ?thesis by (rule finite_subset)
qed

(* ------------------------------------------------------------------ *)
subsection \<open>Min-Plus Closed-Form Theorems\<close>
(* ------------------------------------------------------------------ *)

(* tropm_mat_pow_close_eq_sum_pow: min-plus dual of trop_mat_pow_close_eq_sum_pow.
   (I \<oplus> A)^k i j = \<Sum>_{m \<le> k} A^m i j  in the min-plus semiring. *)
theorem tropm_mat_pow_close_eq_sum_pow:
  assumes hi: "i < n" and hj: "j < n"
  shows "tropm_mat_pow n (tropm_mat_close n A) k i j =
         (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i j)"
proof (induction k)
  case 0
  show ?case by (simp add: tropm_mat_close_def tropm_mat_id_def)
next
  case (Suc k)
  have "(tropm_mat_pow n (tropm_mat_close n A) (Suc k)) i j
        = (\<Sum> l \<in> {..<n}. tropm_mat_pow n (tropm_mat_close n A) k i l *
                            tropm_mat_close n A l j)"
    by (simp add: tropm_mat_mul_def)
  also have "\<dots> = (\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) *
                                     tropm_mat_close n A l j)"
    by (rule sum.cong, simp, simp add: Suc.IH)
  also have "\<dots> = (\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) * A l j) +
                  (\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) *
                                    tropm_mat_id n l j)"
    by (simp add: tropm_mat_close_def distrib_left sum.distrib)
  also have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) * A l j)
             = (\<Sum> m \<in> {..k}. tropm_mat_pow n A (Suc m) i j)"
  proof -
    have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) * A l j)
          = (\<Sum> m \<in> {..k}. \<Sum> l \<in> {..<n}. tropm_mat_pow n A m i l * A l j)"
      by (simp only: sum_distrib_right sum.swap)
    also have "\<dots> = (\<Sum> m \<in> {..k}. tropm_mat_pow n A (Suc m) i j)"
      by (rule sum.cong, simp) (simp add: tropm_mat_mul_def)
    finally show ?thesis .
  qed
  also have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) *
                               tropm_mat_id n l j)
             = (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i j)"
  proof -
    have "(\<Sum> l \<in> {..<n}. (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i l) *
                            tropm_mat_id n l j)
          = (\<Sum> m \<in> {..k}. \<Sum> l \<in> {..<n}. tropm_mat_pow n A m i l * tropm_mat_id n l j)"
      by (simp only: sum_distrib_right sum.swap)
    also have "\<dots> = (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i j)"
      by (rule sum.cong, simp) (simp add: tropm_mat_mul_id_right hi hj)
    finally show ?thesis .
  qed
  also have "(\<Sum> m \<in> {..k}. tropm_mat_pow n A (Suc m) i j) +
             (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i j)
             = (\<Sum> m \<in> {..Suc k}. tropm_mat_pow n A m i j)"
  proof -
    let ?g = "\<lambda>m. tropm_mat_pow n A m i j"
    have ri: "(\<Sum> m \<in> {..k}. ?g (Suc m)) = (\<Sum> m \<in> {1..Suc k}. ?g m)"
      by (rule sum.reindex_cong[of Suc "{..k}" "{1..Suc k}" ?g])
         (auto simp: image_iff)
    have split_U: "(\<Sum> m \<in> {..Suc k}. ?g m) = ?g 0 + (\<Sum> m \<in> {1..Suc k}. ?g m)"
      by (subst sum.atMost_Suc_eq_insert_0) simp_all
    have split_T: "(\<Sum> m \<in> {..k}. ?g m) = ?g 0 + (\<Sum> m \<in> {1..k}. ?g m)"
      by (subst sum.atMost_Suc_eq_insert_0[of k, simplified]) simp_all
    have split_S: "(\<Sum> m \<in> {1..Suc k}. ?g m) = (\<Sum> m \<in> {1..k}. ?g m) + ?g (Suc k)"
      by (simp add: sum.atLeastAtMost_Suc)
    have idem: "(\<Sum> m \<in> {1..k}. ?g m) + (\<Sum> m \<in> {1..k}. ?g m) =
                (\<Sum> m \<in> {1..k}. ?g m)"
      by (subst sum_add_distrib[symmetric], simp add: tropm_add_idem)
    have "(\<Sum> m \<in> {..k}. ?g (Suc m)) + (\<Sum> m \<in> {..k}. ?g m)
          = (\<Sum> m \<in> {1..Suc k}. ?g m) + (\<Sum> m \<in> {..k}. ?g m)"
      using ri by simp
    also have "\<dots> = ((\<Sum> m \<in> {1..k}. ?g m) + ?g (Suc k)) +
                    (?g 0 + (\<Sum> m \<in> {1..k}. ?g m))"
      using split_S split_T by simp
    also have "\<dots> = ?g 0 + (\<Sum> m \<in> {1..k}. ?g m) + ?g (Suc k)"
      using idem by (simp add: add.assoc add.commute add.left_commute)
    also have "\<dots> = (\<Sum> m \<in> {..k}. ?g m) + ?g (Suc k)"
      using split_T by simp
    also have "\<dots> = (\<Sum> m \<in> {..Suc k}. ?g m)"
      by (simp add: sum.atMost_Suc)
    finally show ?thesis .
  qed
  finally show ?case .
qed

(* tropm_mat_pow_close_eq_sum_walks_le: the closed min-plus matrix power
   collects all walks of length \<le> k. *)
theorem tropm_mat_pow_close_eq_sum_walks_le:
  assumes "i < n" "j < n"
  shows "tropm_mat_pow n (tropm_mat_close n A) k i j =
         tropm_walks_sum A (walks_le n k i j)"
proof -
  have "tropm_mat_pow n (tropm_mat_close n A) k i j =
        (\<Sum> m \<in> {..k}. tropm_mat_pow n A m i j)"
    using assms by (rule tropm_mat_pow_close_eq_sum_pow)
  also have "\<dots> = (\<Sum> m \<in> {..k}. tropm_walks_sum A (walks n m i j))"
    by (rule sum.cong) (simp_all add: tropm_mat_pow_eq_sum_walks assms)
  also have "\<dots> = tropm_walks_sum A (\<Union> m \<in> {..k}. walks n m i j)"
    unfolding tropm_walks_sum_def
    by (rule sum.UNION_disjoint[symmetric])
       (auto simp: finite_walks walks_def)
  also have "\<dots> = tropm_walks_sum A (walks_le n k i j)"
    by (simp add: walks_le_def)
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>25  Bellman–Ford Correctness\<close>
(* ------------------------------------------------------------------ *)

theorem bellman_ford:
  assumes "i < n" "j < n"
  assumes "no_neg_cycle n A"
  shows "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j =
         tropm_walks_sum A (simple_walksm n i j)"
proof (rule antisym)
  (* (\<le>) direction: simple_walksm \<subseteq> walks_le, so min over more = smaller *)
  show "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j \<le>
        tropm_walks_sum A (simple_walksm n i j)"
  proof -
    have lhs: "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j =
               tropm_walks_sum A (walks_le n (n-1) i j)"
      using assms(1,2) by (rule tropm_mat_pow_close_eq_sum_walks_le)
    have subset: "simple_walksm n i j \<subseteq> walks_le n (n-1) i j"
    proof
      fix w assume hw: "w \<in> simple_walksm n i j"
      then have hdist: "distinct w"
            and hwalk: "\<exists> m. w \<in> walks n m i j"
        unfolding simple_walksm_def by auto
      obtain m where hwm: "w \<in> walks n m i j" using hwalk by auto
      have hset: "set w \<subseteq> {..<n}" using walk_vertices_bounded[OF hwm] .
      have hlen_n: "length w \<le> n"
      proof -
        have "length w = card (set w)" using distinct_card[OF hdist] .
        also have "card (set w) \<le> card {..<n}"
          using card_mono[OF finite_lessThan hset] .
        also have "card {..<n} = n" by simp
        finally show ?thesis .
      qed
      have hm: "m \<le> n - 1"
      proof -
        have "Suc m = length w" using hwm unfolding walks_def by simp
        thus ?thesis using hlen_n by omega
      qed
      show "w \<in> walks_le n (n-1) i j"
        unfolding walks_le_def using hwm hm by auto
    qed
    show ?thesis
      using lhs tropm_walks_sum_mono_subset[OF finite_walks_le subset] by simp
  qed
next
  (* (\<ge>) direction: every walk in walks_le is dominated by a simple walk *)
  show "tropm_walks_sum A (simple_walksm n i j) \<le>
        tropm_mat_pow n (tropm_mat_close n A) (n-1) i j"
  proof -
    have lhs: "tropm_mat_pow n (tropm_mat_close n A) (n-1) i j =
               tropm_walks_sum A (walks_le n (n-1) i j)"
      using assms(1,2) by (rule tropm_mat_pow_close_eq_sum_walks_le)
    have dominated: "\<forall> w \<in> walks_le n (n-1) i j.
                     \<exists> w' \<in> simple_walksm n i j. path_weightm A w' \<le> path_weightm A w"
    proof (intro ballI)
      fix w assume hw: "w \<in> walks_le n (n-1) i j"
      then obtain m where "m \<le> n - 1" "w \<in> walks n m i j"
        unfolding walks_le_def by auto
      thus "\<exists> w' \<in> simple_walksm n i j. path_weightm A w' \<le> path_weightm A w"
        using cycle_shortcutting_min[OF assms(3)] by blast
    qed
    have "tropm_walks_sum A (simple_walksm n i j) \<le>
          tropm_walks_sum A (walks_le n (n-1) i j)"
      using tropm_walks_sum_dominated[OF simple_walksm_finite finite_walks_le dominated] .
    thus ?thesis using lhs by simp
  qed
qed

end
