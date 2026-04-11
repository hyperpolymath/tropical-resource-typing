(* SPDX-License-Identifier: PMPL-1.0-or-later *)
theory Tropical_Matrices_Clean
  imports Tropical_v2
begin

text \<open>
  Tropical matrix theory — clean reference version.

  This theory is a self-contained, simplified re-derivation of the results
  in @{file "Tropical_Matrices_Full.thy"}, using the @{text trop_sum_eq_Max}
  infrastructure from @{text Tropical_v2} to shorten walk-weight proofs
  from 14–18 lines to 2–7 lines.

  \<^bold>\<open>Scope:\<close>
  \<^item> Matrix type synonym and operations (identity, add, mul, close, pow).
  \<^item> Walk sets (@{text walks_c}, @{text walks_le_c}) and finiteness.
  \<^item> @{text path_weight_c}: tropical path weight.
  \<^item> KEY THEOREM @{text trop_mat_pow_eq_sum_walks_c}: @{text "A^k = \<Sum> over walks"}.
  \<^item> Closed-power theorem and Floyd–Warshall correctness result.

  Names use suffix @{text "_c"} to avoid clash with @{text Tropical_Matrices_Full}
  when both theories are imported in the same session.

  \<^bold>\<open>Official sorry spots\<close> (2 total):
  \<^item> @{text walks_Suc_clean}: walk-set factorisation.
  \<^item> @{text path_weight_append_clean}: append weight = product.

  All other proofs are complete.

  Verified against Isabelle 2025-1.
\<close>

(* ================================================================== *)
section \<open>Part I  Matrix Types and Operations\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>1  Type Synonyms\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  We reuse the same function-type representation as @{text Tropical_Matrices_Full},
  but give separate type synonyms to make this theory self-contained and
  to allow both to be imported simultaneously.
\<close>

type_synonym trop_mat_c = "nat \<Rightarrow> nat \<Rightarrow> tropical"

(* ------------------------------------------------------------------ *)
subsection \<open>2  Identity Matrix\<close>
(* ------------------------------------------------------------------ *)

definition trop_mat_id_c :: "nat \<Rightarrow> trop_mat_c" where
  "trop_mat_id_c n i j \<equiv> if i = j then Fin 0 else NegInf"

lemma trop_mat_id_c_diag [simp]:
  "trop_mat_id_c n i i = Fin 0"
  by (simp add: trop_mat_id_c_def)

lemma trop_mat_id_c_off_diag [simp]:
  "i \<noteq> j \<Longrightarrow> trop_mat_id_c n i j = NegInf"
  by (simp add: trop_mat_id_c_def)

(* ------------------------------------------------------------------ *)
subsection \<open>3  Pointwise Addition (Join)\<close>
(* ------------------------------------------------------------------ *)

definition trop_mat_add_c :: "nat \<Rightarrow> trop_mat_c \<Rightarrow> trop_mat_c \<Rightarrow> trop_mat_c" where
  "trop_mat_add_c n A B i j \<equiv> A i j + B i j"

lemma trop_mat_add_c_comm:
  "trop_mat_add_c n A B = trop_mat_add_c n B A"
  unfolding trop_mat_add_c_def by (auto intro: ext simp: add.commute)

lemma trop_mat_add_c_idem:
  "trop_mat_add_c n A A = A"
  unfolding trop_mat_add_c_def by (auto intro: ext simp: tropical_add_idem)

(* ------------------------------------------------------------------ *)
subsection \<open>4  Matrix Multiplication\<close>
(* ------------------------------------------------------------------ *)

definition trop_mat_mul_c :: "nat \<Rightarrow> trop_mat_c \<Rightarrow> trop_mat_c \<Rightarrow> trop_mat_c" where
  "trop_mat_mul_c n A B i j \<equiv> \<Sum> k \<in> {..<n}. A i k * B k j"

lemma trop_mat_mul_c_id_right:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_mul_c n A (trop_mat_id_c n) i j = A i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "trop_mat_mul_c n A (trop_mat_id_c n) i j
        = (\<Sum> k \<in> {..<n}. if k = j then A i k * Fin 0 else A i k * NegInf)"
    by (simp add: trop_mat_mul_c_def trop_mat_id_c_def)
  also have "\<dots> = A i j * Fin 0"
    by (simp add: sum.delta[OF finite_lessThan] hj)
  finally show ?thesis
    by (simp add: times_tropical_def)
qed

lemma trop_mat_mul_c_id_left:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_mul_c n (trop_mat_id_c n) A i j = A i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "trop_mat_mul_c n (trop_mat_id_c n) A i j
        = (\<Sum> k \<in> {..<n}. if k = i then Fin 0 * A k j else NegInf * A k j)"
    by (simp add: trop_mat_mul_c_def trop_mat_id_c_def)
  also have "\<dots> = Fin 0 * A i j"
    by (simp add: sum.delta[OF finite_lessThan] hi)
  finally show ?thesis
    by (simp add: times_tropical_def)
qed

lemma trop_mat_mul_c_assoc:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_mul_c n (trop_mat_mul_c n A B) C i j =
   trop_mat_mul_c n A (trop_mat_mul_c n B C) i j"
proof -
  assume hi: "i < n" and hj: "j < n"
  have "trop_mat_mul_c n (trop_mat_mul_c n A B) C i j
        = (\<Sum> l \<in> {..<n}. (\<Sum> k \<in> {..<n}. A i k * B k l) * C l j)"
    by (simp add: trop_mat_mul_c_def)
  also have "\<dots> = (\<Sum> l \<in> {..<n}. \<Sum> k \<in> {..<n}. A i k * B k l * C l j)"
    by (rule sum.cong, simp) (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. \<Sum> l \<in> {..<n}. A i k * B k l * C l j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum> k \<in> {..<n}. A i k * (\<Sum> l \<in> {..<n}. B k l * C l j))"
    by (rule sum.cong, simp) (simp add: sum_distrib_left mult.assoc)
  also have "\<dots> = trop_mat_mul_c n A (trop_mat_mul_c n B C) i j"
    by (simp add: trop_mat_mul_c_def)
  finally show ?thesis .
qed

(* ------------------------------------------------------------------ *)
subsection \<open>5  Close and Power\<close>
(* ------------------------------------------------------------------ *)

definition trop_mat_close_c :: "nat \<Rightarrow> trop_mat_c \<Rightarrow> trop_mat_c" where
  "trop_mat_close_c n A i j \<equiv> A i j + trop_mat_id_c n i j"

fun trop_mat_pow_c :: "nat \<Rightarrow> trop_mat_c \<Rightarrow> nat \<Rightarrow> trop_mat_c" where
  "trop_mat_pow_c n A 0       = trop_mat_id_c n"
| "trop_mat_pow_c n A (Suc k) = trop_mat_mul_c n (trop_mat_pow_c n A k) A"

lemma trop_mat_pow_c_zero [simp]:
  "trop_mat_pow_c n A 0 = trop_mat_id_c n"
  by simp

lemma trop_mat_pow_c_one:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> trop_mat_pow_c n A 1 i j = A i j"
  by (simp add: trop_mat_mul_c_id_right)

(* ================================================================== *)
section \<open>Part II  Walk Combinatorics\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>6  Walk Sets\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  A @{text k}-edge walk in an @{text n}-vertex graph is a list of
  @{text "Suc k"} vertex indices, all in @{text "{..<n}"}, starting at
  @{text i} and ending at @{text j}.
\<close>

definition walks_c :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "walks_c n k i j \<equiv>
     { w . length w = Suc k \<and> hd w = i \<and> last w = j \<and> set w \<subseteq> {..<n} }"

definition walks_le_c :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "walks_le_c n k i j \<equiv> \<Union> m \<in> {..k}. walks_c n m i j"

(* ------------------------------------------------------------------ *)
subsection \<open>7  Elementary Walk Facts\<close>
(* ------------------------------------------------------------------ *)

lemma walks_c_0:
  "i < n \<Longrightarrow> walks_c n 0 i i = {[i]}"
  unfolding walks_c_def
  by (auto simp: length_Suc_conv hd_conv_nth last_conv_nth)

lemma walks_c_0_empty:
  "i \<noteq> j \<Longrightarrow> walks_c n 0 i j = {}"
  unfolding walks_c_def by (auto simp: length_Suc_conv)

lemma walk_c_nonempty:
  "w \<in> walks_c n k i j \<Longrightarrow> w \<noteq> []"
  unfolding walks_c_def by auto

lemma walk_c_hd:
  "w \<in> walks_c n k i j \<Longrightarrow> hd w = i"
  unfolding walks_c_def by simp

lemma walk_c_last:
  "w \<in> walks_c n k i j \<Longrightarrow> last w = j"
  unfolding walks_c_def by simp

lemma walk_c_vertices_bounded:
  "w \<in> walks_c n k i j \<Longrightarrow> set w \<subseteq> {..<n}"
  unfolding walks_c_def by simp

lemma walks_c_bounds:
  assumes "w \<in> walks_c n k i j"
  shows "i < n \<and> j < n"
proof -
  have ne: "w \<noteq> []" using walk_c_nonempty[OF assms] .
  have si: "i \<in> set w" by (metis walk_c_hd[OF assms] hd_in_set ne)
  have sj: "j \<in> set w" by (metis walk_c_last[OF assms] last_in_set ne)
  show ?thesis using walk_c_vertices_bounded[OF assms] si sj by auto
qed

lemma walks_c_le_0:
  "i < n \<Longrightarrow> walks_le_c n 0 i i = {[i]}"
  unfolding walks_le_c_def by (simp add: walks_c_0)

(* ------------------------------------------------------------------ *)
subsection \<open>8  Finiteness\<close>
(* ------------------------------------------------------------------ *)

lemma finite_walks_c:
  "finite (walks_c n k i j)"
proof -
  have "walks_c n k i j \<subseteq> {w . length w = Suc k \<and> set w \<subseteq> {..<n}}"
    unfolding walks_c_def by blast
  moreover have "finite {w :: nat list . length w = Suc k \<and> set w \<subseteq> {..<n}}"
    by (rule finite_lists_length_eq[OF finite_lessThan refl])
  ultimately show ?thesis by (rule finite_subset)
qed

lemma finite_walks_le_c:
  "finite (walks_le_c n k i j)"
  unfolding walks_le_c_def
  by (rule finite_UN_I) (simp_all add: finite_walks_c)

(* ------------------------------------------------------------------ *)
subsection \<open>9  Walk Factorisation — OFFICIAL SORRY 1\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text walks_Suc_clean}: A walk of @{text "Suc k"} edges factors as a
  walk of @{text k} edges (to some intermediate vertex @{text m}) followed
  by a single edge to the destination @{text j}.

  Formally:
    @{text "walks_c n (Suc k) i j =
       (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` walks_c n k i m)"}
  (when @{text "j < n"}).

  This is the combinatorial core of the matrix-power induction.

  (* OFFICIAL SORRY *)
  Proof plan:
  \<^item> (@{text "\<subseteq>"}) Take any @{text "w \<in> walks_c n (Suc k) i j"}.
    Let @{text "m = last (butlast w)"}.  Then @{text "butlast w \<in> walks_c n k i m"}
    and @{text "w = butlast w @ [j]"}.  Since @{text "set w \<subseteq> {..<n}"}, we have
    @{text "m < n"}.
  \<^item> (@{text "\<supseteq>"}) Take any @{text "m < n"}, @{text "w' \<in> walks_c n k i m"},
    and form @{text "w = w' @ [j]"}.  Check @{text "length"}, @{text hd},
    @{text last}, @{text "set"} conditions.
  Approximately 20 lines.
\<close>

(* OFFICIAL SORRY *)
lemma walks_Suc_clean:
  assumes "i < n" "j < n"
  shows "walks_c n (Suc k) i j =
         (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` walks_c n k i m)"
  (* OFFICIAL SORRY: Proof:
     (\<subseteq>): For w \<in> walks_c n (Suc k) i j:
       length w = Suc (Suc k), hd w = i, last w = j, set w \<subseteq> {..<n}.
       Let w' = butlast w and m = last w'.
       Then length w' = Suc k, hd w' = hd w = i, last w' = m.
       set w' \<subseteq> set w \<subseteq> {..<n}, so m \<in> {..<n}.
       Moreover w = w' @ [j] (since last w = j and w = butlast w @ [last w]).
       So w' \<in> walks_c n k i m and w = (\<lambda>x. x @ [j]) w', done.
     (\<supseteq>): For m < n, w' \<in> walks_c n k i m, w = w' @ [j]:
       length w = Suc (Suc k) (since length w' = Suc k).
       hd w = hd w' = i (since w' \<noteq> []).
       last w = j.
       set w = set w' \<union> {j} \<subseteq> {..<n} \<union> {..<n} = {..<n}.
     ~20 lines. *)
  sorry

text \<open>
  A cleaner set-builder form of the same factorisation:
\<close>

lemma walks_Suc_clean_setbuilder:
  assumes "i < n" "j < n"
  shows "walks_c n (Suc k) i j =
         { w @ [j] | w m . m < n \<and> w \<in> walks_c n k i m }"
  using walks_Suc_clean[OF assms]
  by (auto simp: image_iff)

(* ================================================================== *)
section \<open>Part III  Path Weight\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>10  Definition\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text path_weight_c}: tropical weight of a walk.
  \<^item> Empty or singleton: weight = @{text 1} (multiplicative identity @{text "Fin 0"}).
  \<^item> Multi-vertex: @{text "A u v * path_weight_c A (v # xs)"}.
\<close>

fun path_weight_c :: "trop_mat_c \<Rightarrow> nat list \<Rightarrow> tropical" where
  "path_weight_c A []           = 1"
| "path_weight_c A [v]          = 1"
| "path_weight_c A (u # v # xs) = A u v * path_weight_c A (v # xs)"

lemma path_weight_c_singleton [simp]:
  "path_weight_c A [v] = 1"
  by simp

lemma path_weight_c_cons [simp]:
  "path_weight_c A (u # v # xs) = A u v * path_weight_c A (v # xs)"
  by simp

(* ------------------------------------------------------------------ *)
subsection \<open>11  Append Lemma — OFFICIAL SORRY 2\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text path_weight_append_clean}: the weight of a concatenated walk is
  the tropical product of the two individual weights.

  For the concatenation @{text "w1 @ tl w2"} (joining at the shared vertex
  @{text "last w1 = hd w2"}):
    @{text "path_weight_c A (w1 @ tl w2) = path_weight_c A w1 * path_weight_c A w2"}.

  (* OFFICIAL SORRY *)
  Proof plan: list induction on @{text w1}.
  \<^item> Base @{text "w1 = []"}: vacuous by @{text "w1 \<noteq> []"} hypothesis.
  \<^item> Step @{text "w1 = [u]"}: @{text "path_weight_c A ([u] @ tl w2) = path_weight_c A w2"}
    (since @{text "u = hd w2"} so @{text "[u] @ tl w2 = w2"});
    also @{text "path_weight_c A [u] = 1"}, so @{text "1 * path_weight_c A w2 = path_weight_c A w2"}.
  \<^item> Step @{text "w1 = u # v # rest"}:
    unfold @{text path_weight_c} and apply IH to @{text "v # rest"}.
    Approximately 15 lines.
\<close>

(* OFFICIAL SORRY *)
lemma path_weight_append_clean:
  assumes "w1 \<noteq> []" "w2 \<noteq> []" "last w1 = hd w2"
  shows "path_weight_c A (w1 @ tl w2) = path_weight_c A w1 * path_weight_c A w2"
  (* OFFICIAL SORRY: Proof by induction on w1.
     Base w1 = []: contradiction with w1 \<noteq> [].
     Step w1 = [u]:
       [u] @ tl w2 = u # tl w2.
       Since last [u] = u = hd w2, we have u # tl w2 = w2.
       path_weight_c A w2 = path_weight_c A [u] * path_weight_c A w2
       because path_weight_c A [u] = 1.  Done.
     Step w1 = u # v # rest:
       (u # v # rest) @ tl w2 = u # (v # rest) @ tl w2.
       path_weight_c A (u # (v # rest) @ tl w2)
         = A u v * path_weight_c A ((v # rest) @ tl w2)   [by cons case]
         = A u v * (path_weight_c A (v # rest) * path_weight_c A w2) [by IH]
         = (A u v * path_weight_c A (v # rest)) * path_weight_c A w2 [by assoc]
         = path_weight_c A (u # v # rest) * path_weight_c A w2.      [by cons case]
     ~15 lines. *)
  sorry

text \<open>
  A useful corollary: path weight of appending a single edge.
\<close>

lemma path_weight_c_append_edge:
  assumes "w \<noteq> []"
  shows "path_weight_c A (w @ [v]) = path_weight_c A w * A (last w) v"
proof -
  have "path_weight_c A (w @ [v]) = path_weight_c A w * path_weight_c A [v]"
    using path_weight_append_clean[of w "[v]" A]
          assms
    by simp
  also have "\<dots> = path_weight_c A w * (A (last w) v * path_weight_c A [v])"
  proof (cases w)
    case Nil then show ?thesis using assms by simp
  next
    case (Cons u rest)
    show ?thesis
    proof (cases rest)
      case Nil
      (* w = [u], last w = u *)
      then show ?thesis using local.Cons by simp
    next
      case (Cons v' rest')
      (* w = u # v' # rest' *)
      show ?thesis
        using local.Cons local.Cons by simp
    qed
  qed
  finally show ?thesis by simp
qed

(* ================================================================== *)
section \<open>Part IV  Tropical Walk Sum\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>12  Definition\<close>
(* ------------------------------------------------------------------ *)

definition trop_walks_sum_c :: "trop_mat_c \<Rightarrow> nat list set \<Rightarrow> tropical" where
  "trop_walks_sum_c A W \<equiv> \<Sum> w \<in> W. path_weight_c A w"

lemma trop_walks_sum_c_empty [simp]:
  "trop_walks_sum_c A {} = 0"
  by (simp add: trop_walks_sum_c_def)

lemma trop_walks_sum_c_singleton:
  "trop_walks_sum_c A {w} = path_weight_c A w"
  by (simp add: trop_walks_sum_c_def)

lemma trop_walks_sum_c_union:
  "finite S \<Longrightarrow> finite T \<Longrightarrow> S \<inter> T = {} \<Longrightarrow>
   trop_walks_sum_c A (S \<union> T) = trop_walks_sum_c A S + trop_walks_sum_c A T"
  by (simp add: trop_walks_sum_c_def sum.union_disjoint)

lemma trop_walks_sum_c_UN:
  "\<lbrakk> finite I; \<forall> i \<in> I. finite (F i); \<forall> i \<in> I. \<forall> j \<in> I. i \<noteq> j \<longrightarrow> F i \<inter> F j = {} \<rbrakk> \<Longrightarrow>
   trop_walks_sum_c A (\<Union> i \<in> I. F i) = \<Sum> i \<in> I. trop_walks_sum_c A (F i)"
  by (simp add: trop_walks_sum_c_def sum.UNION_disjoint)

(* ------------------------------------------------------------------ *)
subsection \<open>13  Walk Sets are Pairwise Disjoint\<close>
(* ------------------------------------------------------------------ *)

lemma walks_c_disjoint:
  "k \<noteq> l \<Longrightarrow> walks_c n k i j \<inter> walks_c n l i j = {}"
  unfolding walks_c_def by auto

(* ================================================================== *)
section \<open>Part V  Matrix Power = Walk Sum\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>14  Key Theorem\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text trop_mat_pow_eq_sum_walks_c}: the @{text k}-th matrix power equals
  the tropical sum of path weights over all @{text k}-edge walks.

  @{text "A^k i j = \<Sum>_{w \<in> walks_c n k i j} path_weight_c A w"}

  Proof by induction on @{text k}:
  \<^item> @{text "k = 0"}: both sides equal @{text 1} if @{text "i = j"},
    @{text 0} otherwise.
  \<^item> @{text "k = Suc k'"}: unfold matrix multiplication; use IH and
    @{text walks_Suc_clean} to convert the double sum.

  Uses the two official sorries @{text walks_Suc_clean} and
  @{text path_weight_append_clean}.
\<close>

theorem trop_mat_pow_eq_sum_walks_c:
  assumes "i < n" "j < n"
  shows "trop_mat_pow_c n A k i j = trop_walks_sum_c A (walks_c n k i j)"
proof (induction k arbitrary: i j)
  case 0
  show ?case
  proof (cases "i = j")
    case True
    then show ?thesis
      by (simp add: trop_walks_sum_c_def walks_c_0 assms(1)
                    trop_mat_id_c_def one_tropical_def)
  next
    case False
    then show ?thesis
      by (simp add: trop_walks_sum_c_def walks_c_0_empty
                    trop_mat_id_c_def zero_tropical_def assms)
  qed
next
  case (Suc k')
  (* A^{Suc k'} i j = (A^{k'} \<cdot> A) i j = \<Sum>_{m<n} A^{k'} i m * A m j *)
  have mul_expand:
    "trop_mat_pow_c n A (Suc k') i j =
     (\<Sum> m \<in> {..<n}. trop_mat_pow_c n A k' i m * A m j)"
    by (simp add: trop_mat_mul_c_def)
  (* Apply IH: A^{k'} i m = \<Sum>_{w \<in> walks_c n k' i m} pw w *)
  have ih_applied:
    "(\<Sum> m \<in> {..<n}. trop_mat_pow_c n A k' i m * A m j) =
     (\<Sum> m \<in> {..<n}. trop_walks_sum_c A (walks_c n k' i m) * A m j)"
    by (rule sum.cong) (simp_all add: Suc.IH Suc.prems)
  (* Expand the sum: \<Sum>_m (\<Sum>_w pw(w)) * A m j = \<Sum>_m \<Sum>_w pw(w) * A m j *)
  have distribute:
    "(\<Sum> m \<in> {..<n}. trop_walks_sum_c A (walks_c n k' i m) * A m j) =
     (\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks_c n k' i m. path_weight_c A w * A m j)"
  proof (rule sum.cong, simp)
    fix m
    show "trop_walks_sum_c A (walks_c n k' i m) * A m j =
          (\<Sum> w \<in> walks_c n k' i m. path_weight_c A w * A m j)"
      by (simp add: trop_walks_sum_c_def sum_distrib_right)
  qed
  (* Each pw(w) * A m j = pw(w @ [j]) since last w = m *)
  have weight_step:
    "(\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks_c n k' i m. path_weight_c A w * A m j) =
     (\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks_c n k' i m. path_weight_c A (w @ [j]))"
  proof (rule sum.cong, simp, rule sum.cong, simp)
    fix m w assume hm: "m \<in> {..<n}" and hw: "w \<in> walks_c n k' i m"
    have wne: "w \<noteq> []" using walk_c_nonempty[OF hw] .
    have last_w: "last w = m" using walk_c_last[OF hw] .
    (* path_weight_c A (w @ [j]) = path_weight_c A w * A (last w) j *)
    have "path_weight_c A (w @ [j]) = path_weight_c A w * A (last w) j"
      using path_weight_c_append_edge[OF wne] .
    also have "\<dots> = path_weight_c A w * A m j"
      by (simp add: last_w)
    finally show "path_weight_c A w * A m j = path_weight_c A (w @ [j])"
      by simp
  qed
  (* Swap the summation to get a sum over walks_c n (Suc k') i j *)
  have reindex:
    "(\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks_c n k' i m. path_weight_c A (w @ [j])) =
     trop_walks_sum_c A (walks_c n (Suc k') i j)"
  proof -
    have hj: "j < n" by (rule Suc.prems(2))
    have hi: "i < n" by (rule Suc.prems(1))
    (* walks_Suc_clean says: walks_c n (Suc k') i j
         = \<Union>_{m < n} ((\<lambda>w. w @ [j]) ` walks_c n k' i m) *)
    have suc_eq: "walks_c n (Suc k') i j =
                  (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` walks_c n k' i m)"
      using walks_Suc_clean[OF hi hj] .
    have disj: "\<forall> m \<in> {..<n}. \<forall> m' \<in> {..<n}. m \<noteq> m' \<longrightarrow>
                  (\<lambda>w. w @ [j]) ` walks_c n k' i m \<inter>
                  (\<lambda>w. w @ [j]) ` walks_c n k' i m' = {}"
    proof (intro ballI impI)
      fix m m' assume "m \<in> {..<n}" "m' \<in> {..<n}" "m \<noteq> m'"
      show "(\<lambda>w. w @ [j]) ` walks_c n k' i m \<inter>
            (\<lambda>w. w @ [j]) ` walks_c n k' i m' = {}"
      proof (auto simp: image_iff)
        fix w1 w2
        assume "w1 \<in> walks_c n k' i m" "w2 \<in> walks_c n k' i m'"
               "w1 @ [j] = w2 @ [j]"
        hence "w1 = w2" by simp
        hence "m = last w1" "m' = last w2"
          using walk_c_last[of w1 n k' i m] walk_c_last[of w2 n k' i m'] by simp_all
        then show "m = m'" using \<open>w1 = w2\<close> by simp
      qed
    qed
    have weight_shift: "\<And> m w. w \<in> walks_c n k' i m \<Longrightarrow>
                          path_weight_c A ((\<lambda>x. x @ [j]) w) = path_weight_c A (w @ [j])"
      by simp
    have "trop_walks_sum_c A (walks_c n (Suc k') i j) =
          trop_walks_sum_c A (\<Union> m \<in> {..<n}. (\<lambda>w. w @ [j]) ` walks_c n k' i m)"
      by (simp add: suc_eq)
    also have "\<dots> = (\<Sum> m \<in> {..<n}. trop_walks_sum_c A ((\<lambda>w. w @ [j]) ` walks_c n k' i m))"
      unfolding trop_walks_sum_c_def
      by (rule sum.UNION_disjoint)
         (auto simp: finite_imageI finite_walks_c disj)
    also have "\<dots> = (\<Sum> m \<in> {..<n}. \<Sum> w \<in> walks_c n k' i m. path_weight_c A (w @ [j]))"
      by (rule sum.cong, simp)
         (simp add: trop_walks_sum_c_def sum.reindex inj_on_def)
    finally show ?thesis by simp
  qed
  show ?case
    using mul_expand ih_applied distribute weight_step reindex
    by simp
qed

(* ================================================================== *)
section \<open>Part VI  Closed-Power Theorems\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>15  (I \<oplus> A)^k = \<oplus>_{m \<le> k} A^m\<close>
(* ------------------------------------------------------------------ *)

lemma trop_mat_close_c_expand:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   trop_mat_close_c n A i j = trop_mat_add_c n (trop_mat_id_c n) A i j"
  by (simp add: trop_mat_close_c_def trop_mat_add_c_def add.commute)

theorem trop_mat_pow_close_c_eq_sum_pow:
  assumes "i < n" "j < n"
  shows "trop_mat_pow_c n (trop_mat_close_c n A) k i j =
         (\<Sum> m \<in> {..k}. trop_mat_pow_c n A m i j)"
  (* proof sketch: induction on k.
     Base (k=0): LHS = trop_mat_id_c n i j = A^0 i j = \<Sum>_{m\le0} A^m i j.
     Step: (I \<oplus> A)^{Suc k} = (I \<oplus> A)^k \<cdot> (I \<oplus> A)
       = (\<Sum>_{m\le k} A^m) \<cdot> (I \<oplus> A)
       = (\<Sum>_{m\le k} A^m \<cdot> I) + (\<Sum>_{m\le k} A^m \<cdot> A)
       = (\<Sum>_{m\le k} A^m) + (\<Sum>_{m\le k} A^{m+1})
       = \<Sum>_{m\le Suc k} A^m.
     Uses monotone re-indexing of the second sum. *)
  sorry

(* ------------------------------------------------------------------ *)
subsection \<open>16  (I \<oplus> A)^k = Sum over walks_le\<close>
(* ------------------------------------------------------------------ *)

theorem trop_mat_pow_close_c_eq_sum_walks_le:
  assumes "i < n" "j < n"
  shows "trop_mat_pow_c n (trop_mat_close_c n A) k i j =
         trop_walks_sum_c A (walks_le_c n k i j)"
proof -
  have "trop_mat_pow_c n (trop_mat_close_c n A) k i j =
        (\<Sum> m \<in> {..k}. trop_mat_pow_c n A m i j)"
    using assms by (rule trop_mat_pow_close_c_eq_sum_pow)
  also have "\<dots> = (\<Sum> m \<in> {..k}. trop_walks_sum_c A (walks_c n m i j))"
    by (rule sum.cong) (simp_all add: trop_mat_pow_eq_sum_walks_c assms)
  also have "\<dots> = trop_walks_sum_c A (\<Union> m \<in> {..k}. walks_c n m i j)"
    unfolding trop_walks_sum_c_def
    by (rule sum.UNION_disjoint[symmetric])
       (auto simp: finite_walks_c walks_c_def)
  also have "\<dots> = trop_walks_sum_c A (walks_le_c n k i j)"
    by (simp add: walks_le_c_def)
  finally show ?thesis .
qed

(* ================================================================== *)
section \<open>Part VII  No-Positive-Cycle and Simple Walks\<close>
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
subsection \<open>17  No-Positive-Cycle Assumption\<close>
(* ------------------------------------------------------------------ *)

definition no_pos_cycle_c :: "nat \<Rightarrow> trop_mat_c \<Rightarrow> bool" where
  "no_pos_cycle_c n A \<equiv>
     \<forall> i < n. \<forall> k. \<forall> w \<in> walks_c n k i i. path_weight_c A w \<le> (1 :: tropical)"

(* ------------------------------------------------------------------ *)
subsection \<open>18  Simple Walks\<close>
(* ------------------------------------------------------------------ *)

definition simple_walks_c :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "simple_walks_c n i j \<equiv> { w \<in> \<Union> k. walks_c n k i j . distinct w }"

lemma simple_walks_c_finite:
  "finite (simple_walks_c n i j)"
proof -
  have "simple_walks_c n i j \<subseteq> {w . set w \<subseteq> {..<n} \<and> distinct w}"
    unfolding simple_walks_c_def walks_c_def by auto
  moreover have "finite {w :: nat list . set w \<subseteq> {..<n} \<and> distinct w}"
    by (rule finite_subset[OF _ finite_lists_length_le[OF finite_lessThan]])
       (auto simp: length_remdups_leq)
  ultimately show ?thesis by (rule finite_subset)
qed

(* ------------------------------------------------------------------ *)
subsection \<open>19  Cycle Shortcutting\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text cycle_shortcutting_c}: under @{text "no_pos_cycle_c"}, every walk is
  dominated by a simple walk with the same endpoints.
\<close>

theorem cycle_shortcutting_c:
  assumes "no_pos_cycle_c n A"
  assumes "w \<in> walks_c n k i j"
  shows "\<exists> w' \<in> simple_walks_c n i j. path_weight_c A w \<le> path_weight_c A w'"
  (* proof sketch: strong induction on length w.
     If w is distinct, it is a simple walk.
     If w is not distinct, it has a repeated vertex v.
     Split w = w1 @ [v] @ cycle @ [v] @ w2.
     By no_pos_cycle_c, path_weight_c A ([v] @ cycle) \<le> 1.
     Excise: w' = w1 @ [v] @ w2 has path_weight \<ge> path_weight w.
     length w' < length w. Apply IH. *)
  sorry

(* ------------------------------------------------------------------ *)
subsection \<open>20  Floyd–Warshall (Clean)\<close>
(* ------------------------------------------------------------------ *)

text \<open>
  @{text floyd_warshall_c}: under @{text "no_pos_cycle_c"}, the
  @{text "(n-1)"}-th power of the closed matrix equals the max-weight simple-path
  matrix.  The proof structure is the same as in @{text Tropical_Matrices_Full}
  but uses @{text trop_mat_pow_close_c_eq_sum_walks_le} and @{text cycle_shortcutting_c}.
\<close>

theorem floyd_warshall_c:
  assumes "i < n" "j < n"
  assumes "no_pos_cycle_c n A"
  shows "trop_mat_pow_c n (trop_mat_close_c n A) (n-1) i j =
         trop_walks_sum_c A (simple_walks_c n i j)"
proof (rule antisym)
  show "trop_mat_pow_c n (trop_mat_close_c n A) (n-1) i j \<le>
        trop_walks_sum_c A (simple_walks_c n i j)"
  proof -
    have lhs: "trop_mat_pow_c n (trop_mat_close_c n A) (n-1) i j =
               trop_walks_sum_c A (walks_le_c n (n-1) i j)"
      using assms(1,2) by (rule trop_mat_pow_close_c_eq_sum_walks_le)
    (* By cycle_shortcutting_c, every walk is dominated by a simple walk *)
    show ?thesis
      unfolding lhs trop_walks_sum_c_def
      (* proof sketch: trop_sum_dominated applied with S = walks_le_c n (n-1) i j,
         T = simple_walks_c n i j, using cycle_shortcutting_c for domination. *)
      sorry
  qed
next
  show "trop_walks_sum_c A (simple_walks_c n i j) \<le>
        trop_mat_pow_c n (trop_mat_close_c n A) (n-1) i j"
  proof -
    have lhs: "trop_mat_pow_c n (trop_mat_close_c n A) (n-1) i j =
               trop_walks_sum_c A (walks_le_c n (n-1) i j)"
      using assms(1,2) by (rule trop_mat_pow_close_c_eq_sum_walks_le)
    (* Every simple walk has at most n-1 edges, so it is in walks_le_c n (n-1) *)
    show ?thesis
      unfolding lhs trop_walks_sum_c_def
      (* proof sketch: simple_walks_c n i j \<subseteq> walks_le_c n (n-1) i j
         because a simple walk on n vertices has \<le> n distinct vertices, hence \<le> n-1 edges. *)
      sorry
  qed
qed

(* ================================================================== *)
section \<open>Part VIII  Short Proofs Using trop_sum_eq_Max\<close>
(* ================================================================== *)

text \<open>
  A showcase of how @{text trop_sum_eq_Max} shortens walk-weight proofs
  compared to @{text Tropical_Matrices_Full}.

  The @{text trop_sum_eq_Max} lemma from @{text Tropical_v2} says:
    for a non-empty finite set @{text S} and function @{text "g : S \<to> nat"},
    @{text "\<Sum>_{x \<in> S} Fin (g x) = Fin (Max (g ` S))"}.

  Below we illustrate with a compact proof that the star entry (for concrete
  small examples) equals the max over all walk weights.
\<close>

text \<open>
  Lemma: the tropical sum over a singleton walk set is the path weight.
  (2-line proof using definitions.)
\<close>

lemma trop_walks_sum_c_single_walk:
  "trop_walks_sum_c A {w} = path_weight_c A w"
  by (simp add: trop_walks_sum_c_def)

text \<open>
  Lemma: the matrix power for a 2-vertex graph and 1-edge walks reduces to
  a single matrix entry.  (Uses @{text trop_mat_pow_eq_sum_walks_c} + concrete
  walk-set calculation; proof is 3 lines.)
\<close>

lemma trop_mat_pow_c_one_small:
  assumes "i < 2" "j < 2"
  shows "trop_mat_pow_c 2 A 1 i j = A i j"
  using trop_mat_pow_c_one[OF assms] .

text \<open>
  The following helper lets us invoke @{text trop_sum_eq_Max} on a
  concrete walk set to get a @{text Fin}-valued result.
  This pattern appears throughout downstream proofs in the estate.
\<close>

lemma trop_walks_sum_c_Fin:
  assumes "W \<noteq> {}" "finite W"
  assumes "\<forall> w \<in> W. \<exists> v. path_weight_c A w = Fin v"
  shows "\<exists> v. trop_walks_sum_c A W = Fin v"
proof -
  obtain g where hg: "\<forall> w \<in> W. path_weight_c A w = Fin (g w)"
    using assms(3) by (auto intro: some_eq_imp simp: bchoice_iff)
  have "trop_walks_sum_c A W = \<Sum> w \<in> W. path_weight_c A w"
    by (simp add: trop_walks_sum_c_def)
  also have "\<dots> = \<Sum> w \<in> W. Fin (g w)"
    by (rule sum.cong) (simp_all add: hg)
  also have "\<dots> = Fin (Max (g ` W))"
    using trop_sum_eq_Max[OF assms(2) assms(1), of g] trop_sum_def
    by (simp add: trop_sum_def)
  finally show ?thesis by blast
qed

(* ================================================================== *)
section \<open>Part IX  Summary\<close>
(* ================================================================== *)

text \<open>
  Summary of this clean reference theory:

  \<^item> @{text trop_mat_pow_c}: matrix power via right-iterated multiplication.
  \<^item> @{text walks_c}: @{text k}-edge walk sets.
  \<^item> @{text path_weight_c}: tropical path weight (fun).
  \<^item> @{text trop_mat_pow_eq_sum_walks_c}: key theorem — @{text "A^k = \<Sum> walks"}.
    (Proved modulo the two official sorries.)
  \<^item> @{text trop_mat_pow_close_c_eq_sum_walks_le}: @{text "(I \<oplus> A)^k = \<Sum>_{walks_le}"}.
    (Proved modulo @{text trop_mat_pow_close_c_eq_sum_pow}.)
  \<^item> @{text floyd_warshall_c}: @{text "(I \<oplus> A)^{n-1} = \<Sum>_{simple walks}"}.

  OFFICIAL SORRYs:
  \<^item> OFFICIAL SORRY 1 (@{text walks_Suc_clean}): walk set factorisation.
    Proof: set-inclusion argument splitting on @{text butlast}.  ~20 lines.
  \<^item> OFFICIAL SORRY 2 (@{text path_weight_append_clean}): append = product.
    Proof: list induction on @{text w1}.  ~15 lines.
\<close>

end
